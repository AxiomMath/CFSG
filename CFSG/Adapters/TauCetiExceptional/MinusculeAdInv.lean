module

public import CFSG.Adapters.TauCetiExceptional.MinusculeCell
public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjoint

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} (D : MinData τ)

@[expose] def hCoef (j : Fin τ.rank) (a : Fin D.d) : ℤ :=
  ((D.pgen.getD j []).map fun p => if p.1 = (a : ℕ) then p.2 else 0).sum

open Classical in
@[expose] def rootPair (α : Fin τ.rank → ℤ) : Option (Fin D.d × Fin D.d) :=
  if h : ∃ p : Fin D.d × Fin D.d, rootMat D α p.1 p.2 ≠ 0 then some (Classical.choose h) else none

variable (R : Type*) [CommRing R]

@[expose] def rootCoord (S : AdjSigns τ) (α : Fin τ.rank → ℤ) (M : Matrix (Fin D.d) (Fin D.d) R) :
    R :=
  match rootPair D α with
  | none => 0
  | some p => ((S.sRoot α * rootMat D α p.1 p.2 : ℤ) : R) * M p.1 p.2

@[expose] def matCoord (S : AdjSigns τ) (M : Matrix (Fin D.d) (Fin D.d) R) : Label τ → R
  | .inl j => ((S.epsZ j : ℤ) : R) * ∑ a, (hCoef D j a : R) * M a a
  | .inr α => rootCoord D R S α.1 M

variable {D R}

theorem rootCoord_eq (S : AdjSigns τ) {α : Fin τ.rank → ℤ} {p : Fin D.d × Fin D.d}
    (hp : rootPair D α = some p) (M : Matrix (Fin D.d) (Fin D.d) R) :
    rootCoord D R S α M = ((S.sRoot α * rootMat D α p.1 p.2 : ℤ) : R) * M p.1 p.2 := by
  unfold rootCoord
  rw [hp]

theorem map_matCoord {R' : Type*} [CommRing R'] (f : R →+* R') (S : AdjSigns τ)
    (M : Matrix (Fin D.d) (Fin D.d) R) (l : Label τ) :
    f (matCoord D R S M l) = matCoord D R' S (f.mapMatrix M) l := by
  rcases l with j | ⟨α, hα⟩
  · simp only [matCoord, map_mul, map_sum, map_intCast, RingHom.mapMatrix_apply, Matrix.map_apply]
  · change f (rootCoord D R S α M) = rootCoord D R' S α (f.mapMatrix M)
    unfold rootCoord
    rcases rootPair D α with - | p
    · exact map_zero f
    · simp only [map_mul, map_intCast, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem matCoord_add (S : AdjSigns τ) (M N : Matrix (Fin D.d) (Fin D.d) R) (l : Label τ) :
    matCoord D R S (M + N) l = matCoord D R S M l + matCoord D R S N l := by
  rcases l with j | ⟨α, hα⟩
  · simp only [matCoord, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  · change rootCoord D R S α (M + N) = rootCoord D R S α M + rootCoord D R S α N
    unfold rootCoord
    rcases rootPair D α with - | p
    · exact (add_zero 0).symm
    · simp only [Matrix.add_apply, mul_add]

theorem matCoord_smul (S : AdjSigns τ) (c : R) (M : Matrix (Fin D.d) (Fin D.d) R) (l : Label τ) :
    matCoord D R S (c • M) l = c * matCoord D R S M l := by
  rcases l with j | ⟨α, hα⟩
  · simp only [matCoord, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · change rootCoord D R S α (c • M) = c * rootCoord D R S α M
    unfold rootCoord
    rcases rootPair D α with - | p
    · exact (mul_zero c).symm
    · simp only [Matrix.smul_apply, smul_eq_mul]
      ring

variable (R D)

@[expose] def adjInv (S : AdjSigns τ) (D : MinData τ) :
    Module.End R (Fin D.d →₀ R) →ₗ[R] RootModule τ R where
  toFun X := Finsupp.equivFunOnFinite.symm (matCoord D R S (natMat R X))
  map_add' X Y := by
    ext l
    simp only [map_add, Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_add, Pi.add_apply,
      matCoord_add]
  map_smul' c X := by
    ext l
    simp only [map_smul, Finsupp.coe_equivFunOnFinite_symm, matCoord_smul, RingHom.id_apply,
      Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem adjInv_apply
    (S : AdjSigns τ) (X : Module.End R (Fin D.d →₀ R)) (l : Label τ) :
    adjInv R S D X l = matCoord D R S (natMat R X) l := by
  simp [adjInv]

variable {D}

theorem natMat_cartanOp (k : Fin τ.rank) :
    natMat R (cartanOp R D k) = Matrix.diagonal fun a : Fin D.d => ((D.wt a k : ℤ) : R) := by
  ext r s
  rw [natMat_apply, cartanOp_single, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    Matrix.diagonal_apply]
  by_cases h : s = r
  · subst h
    simp
  · simp [h, Ne.symm h]

variable (hV : D.Valid)
include hV

theorem rootMat_ne_zero
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {a b : Fin D.d}
    (h : rootMat D β b a ≠ 0) :
    D.wt b = D.wt a + toWeight β ∧ rootMat D β b a * rootMat D β b a = 1 := by
  rw [rootMat, natMat_apply] at h ⊢
  rcases hV.isSignedMap_rootOp (R := ℤ) hβ a with h0 | ⟨c, hc, hs⟩
  · rw [h0] at h
    exact absurd rfl h
  · have hcb : c = b := by
      by_contra hne
      rcases hs with hs | hs <;> rw [hs] at h <;> simp [hne] at h
    subst hcb
    refine ⟨hc, ?_⟩
    rcases hs with hs | hs <;> rw [hs] <;> simp

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
include hpd

theorem rootMat_self
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (a : Fin D.d) :
    rootMat D β a a = 0 := by
  by_contra h
  have e := (rootMat_ne_zero hV hβ h).1
  have : toWeight β = toWeight 0 := by
    rw [show toWeight (0 : Fin τ.rank → ℤ) = 0 from funext fun j => by simp [toWeight]]
    exact add_eq_left.1 e.symm
  exact hβ.ne_zero (toWeight_injective hpd this)

theorem rootMat_eq_zero_of_ne
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : β ≠ α) {a b : Fin D.d} (h : rootMat D α b a ≠ 0) : rootMat D β b a = 0 := by
  by_contra h'
  have e := (rootMat_ne_zero hV hα h).1.symm.trans (rootMat_ne_zero hV hβ h').1
  exact hne (toWeight_injective hpd (add_left_cancel e)).symm

omit hpd in
theorem rootPair_spec
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ p, rootPair D β = some p ∧ rootMat D β p.1 p.2 ≠ 0 := by
  classical
  have hex : ∃ p : Fin D.d × Fin D.d, rootMat D β p.1 p.2 ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    refine hV.rootOp_ne_zero (R := ℤ) hβ (LinearMap.ext fun v => ?_)
    have : natMat ℤ (D.rootOp ℤ β) = 0 := Matrix.ext fun b a => hne (b, a)
    rw [(natMat ℤ).map_eq_zero_iff.1 this]
  refine ⟨Classical.choose hex, ?_, Classical.choose_spec hex⟩
  rw [rootPair, dite_eq_left hex]

omit hpd in
theorem sum_hCoef_mul_wt
    (j k : Fin τ.rank) :
    ∑ a : Fin D.d, hCoef D j a * D.wt a k = (Pi.single j 1 : Fin τ.rank → ℤ) k := by
  have key : ∀ L : List (ℕ × ℤ), (∀ p ∈ L, p.1 < D.d) →
      ∑ a : Fin D.d, (L.map fun p => if p.1 = (a : ℕ) then p.2 else 0).sum * D.wt a k =
        (L.map fun p => p.2 • D.wt p.1).sum k := by
    intro L hL
    induction L with
    | nil => simp
    | cons p L ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, Pi.add_apply]
      rw [ih fun q hq => hL q (List.mem_cons_of_mem _ hq)]
      congr 1
      have hp : p.1 < D.d := hL p List.mem_cons_self
      rw [Finset.sum_eq_single ⟨p.1, hp⟩]
      · simp
      · intro a _ ha
        rw [ite_eq_right (fun h => ha (Fin.ext h.symm)), zero_mul]
      · simp
  rw [← hV.pgen_sum j]
  exact key _ (hV.pgen_lt j)

theorem adjInv_adjMap
    (S : AdjSigns τ) (v : RootModule τ R) :
    adjInv R S D (adjMap R S D v) = v := by
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add v w hv hw => rw [map_add, map_add, hv, hw]
  | single l c =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul]
    congr 1
    ext l'
    rw [adjInv_apply, Finsupp.single_apply]
    rcases l with k | ⟨β, hβ⟩
    · rw [show (Finsupp.single (Sum.inl k) 1 : RootModule τ R) = hVec τ R k from rfl,
        adjMap_hVec, map_smul, natMat_cartanOp]
      rcases l' with j | ⟨α, hα⟩
      · have hsum : ∑ a : Fin D.d, (hCoef D j a : R) * (((S.epsZ k : ℤ) : R) *
            ((D.wt a k : ℤ) : R)) = ((S.epsZ k * (Pi.single j 1 : Fin τ.rank → ℤ) k : ℤ) : R) := by
          rw [← sum_hCoef_mul_wt hV j k, Finset.mul_sum]
          push_cast
          exact Finset.sum_congr rfl fun a _ => by ring
        simp only [matCoord, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        rw [hsum]
        by_cases hjk : j = k
        · subst hjk
          rw [Pi.single_eq_same, mul_one, ← Int.cast_mul, S.epsZ_mul_self, Int.cast_one,
            ite_eq_left rfl]
        · rw [Pi.single_eq_of_ne' hjk, mul_zero, Int.cast_zero, mul_zero,
            ite_eq_right fun h => hjk (Sum.inl_injective h).symm]
      · obtain ⟨p, hp, hp0⟩ := rootPair_spec hV hα
        have hba : p.1 ≠ p.2 := fun h => hp0 (by rw [h]; exact rootMat_self hV hpd hα p.2)
        change rootCoord D R S α _ = _
        rw [rootCoord_eq S hp, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hba, smul_zero,
          mul_zero, ite_eq_right Sum.inl_ne_inr]
    · rw [← rootVec_eq_single R hβ, adjMap_rootVec, map_smul, natMat_rootOp]
      rcases l' with j | ⟨α, hα⟩
      · simp only [matCoord, Matrix.smul_apply, Matrix.map_apply, rootMat_self hV hpd hβ,
          Int.cast_zero, smul_zero, mul_zero, Finset.sum_const_zero]
        exact (ite_eq_right Sum.inr_ne_inl).symm
      · obtain ⟨p, hp, hp0⟩ := rootPair_spec hV hα
        change rootCoord D R S α _ = _
        rw [rootCoord_eq S hp, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
        by_cases hαβ : β = α
        · subst hαβ
          rw [ite_eq_left rfl]
          have h1 := (rootMat_ne_zero hV hβ hp0).2
          have h2 := S.sRoot_mul_self β
          have : ((S.sRoot β * rootMat D β p.1 p.2 : ℤ) : R) * (((S.sRoot β : ℤ) : R) *
              ((rootMat D β p.1 p.2 : ℤ) : R)) =
                (((S.sRoot β * S.sRoot β) * (rootMat D β p.1 p.2 * rootMat D β p.1 p.2) : ℤ) :
                  R) := by
            push_cast
            ring
          rw [this, h1, h2, mul_one, Int.cast_one]
        · rw [rootMat_eq_zero_of_ne hV hpd hα hβ hαβ hp0, Int.cast_zero, mul_zero, mul_zero,
            ite_eq_right fun h => hαβ (congrArg Subtype.val (Sum.inr_injective h))]

theorem adjMap_injective
    (S : AdjSigns τ) : Function.Injective (adjMap R S D) :=
  Function.LeftInverse.injective (adjInv_adjMap R hV hpd S)

end CFSG.TauCetiBridge.Minuscule
