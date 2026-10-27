module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Levi
public import CFSG.LieType.Chevalley.E6GraphLeviUnitary

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley
open scoped MatrixGroups

section Matrix

variable {K : Type} [Field K]

theorem graphSL_tv {i j : Fin 6} (hij : i ≠ j) (c : K) :
    graphSL K (tv i j c) = tv (Fin.rev j) (Fin.rev i) (-c) := by
  have hij' : Fin.rev j ≠ Fin.rev i := fun h => hij (Fin.rev_injective h).symm
  rw [tv_of_ne hij, tv_of_ne hij']
  apply Subtype.ext
  rw [coe_graphSL, SpecialLinearGroup.transvection_inv]
  change antiId K * (Matrix.transvection i j (-c))ᵀ * antiId K = Matrix.transvection _ _ (-c)
  rw [antiId_mul_mul_antiId]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h1 : (Fin.rev b = Fin.rev a) ↔ (a = b) :=
    ⟨fun h => (Fin.rev_injective h).symm, fun h => h ▸ rfl⟩
  have h2' : (i = Fin.rev b ∧ j = Fin.rev a) ↔ (Fin.rev j = a ∧ Fin.rev i = b) := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> subst h₁ h₂ <;> simp
  simp only [h1, h2']

theorem unitaryTwist_tv (σ : K →+* K) {i j : Fin 6} (hij : i ≠ j) (c : K) :
    unitaryTwist σ (tv i j c) = tv (Fin.rev j) (Fin.rev i) (-σ c) := by
  rw [tv_of_ne hij]
  change graphSL K (Matrix.SpecialLinearGroup.map σ (SpecialLinearGroup.transvection hij c)) = _
  rw [map_transvection σ hij c, ← tv_of_ne hij, graphSL_tv hij]

@[expose] def dmat (d : Fin 6 → Kˣ) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal (fun i => (d i : K))

@[expose] def dmatInv (d : Fin 6 → Kˣ) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal (fun i => (((d i)⁻¹ : Kˣ) : K))

theorem dmat_mul_dmatInv (d : Fin 6 → Kˣ) :
    dmat d * dmatInv d = (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [dmat, dmatInv, Matrix.diagonal_mul_diagonal]
  ext a b
  simp [Matrix.diagonal_apply, Matrix.one_apply]

theorem dmatInv_mul_dmat (d : Fin 6 → Kˣ) :
    dmatInv d * dmat d = (1 : Matrix (Fin 6) (Fin 6) K) := by
  rw [dmat, dmatInv, Matrix.diagonal_mul_diagonal]
  ext a b
  simp [Matrix.diagonal_apply, Matrix.one_apply]

@[expose] def conjDiag (d : Fin 6 → Kˣ) : SL(6, K) →* SL(6, K) where
  toFun B := ⟨dmat d * (B : Matrix (Fin 6) (Fin 6) K) * dmatInv d, by
    rw [Matrix.det_mul, Matrix.det_mul, B.2, mul_one, dmat, dmatInv, Matrix.det_diagonal,
      Matrix.det_diagonal, ← Finset.prod_mul_distrib]
    simp⟩
  map_one' := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
    exact dmat_mul_dmatInv d
  map_mul' B C := by
    apply Subtype.ext
    change dmat d * ((B : Matrix (Fin 6) (Fin 6) K) * (C : Matrix (Fin 6) (Fin 6) K)) * dmatInv d =
      (dmat d * (B : Matrix (Fin 6) (Fin 6) K) * dmatInv d) *
        (dmat d * (C : Matrix (Fin 6) (Fin 6) K) * dmatInv d)
    calc _ = dmat d * (B : Matrix (Fin 6) (Fin 6) K) * (dmatInv d * dmat d) *
          (C : Matrix (Fin 6) (Fin 6) K) * dmatInv d := by
          rw [dmatInv_mul_dmat, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_conjDiag (d : Fin 6 → Kˣ) (B : SL(6, K)) :
    ((conjDiag d B : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) =
      dmat d * (B : Matrix (Fin 6) (Fin 6) K) * dmatInv d := rfl

theorem conjDiag_tv (d : Fin 6 → Kˣ) {i j : Fin 6} (hij : i ≠ j) (c : K) :
    conjDiag d (tv i j c) = tv i j ((d i : K) * c * (((d j)⁻¹ : Kˣ) : K)) := by
  rw [tv_of_ne hij, tv_of_ne hij]
  apply Subtype.ext
  rw [coe_conjDiag]
  change dmat d * Matrix.transvection i j c * dmatInv d = Matrix.transvection i j _
  ext a b
  simp only [dmat, dmatInv, Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have h2 : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [Matrix.diagonal_apply, h2]
  · by_cases h2 : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp [Matrix.diagonal_apply, hab]
    · simp [Matrix.diagonal_apply, hab, h2]

theorem eq_scalar_of_conjDiag (d : Fin 6 → Kˣ) {B : SL(6, K)} {r : K}
    (h : ((conjDiag d B : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) r) :
    (B : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) r := by
  rw [coe_conjDiag] at h
  have h1 : dmatInv d * (dmat d * (B : Matrix (Fin 6) (Fin 6) K) * dmatInv d) * dmat d =
      dmatInv d * Matrix.scalar (Fin 6) r * dmat d := by rw [h]
  have h2 : dmatInv d * (dmat d * (B : Matrix (Fin 6) (Fin 6) K) * dmatInv d) * dmat d =
      (B : Matrix (Fin 6) (Fin 6) K) := by
    calc _ = (dmatInv d * dmat d) * (B : Matrix (Fin 6) (Fin 6) K) * (dmatInv d * dmat d) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [dmatInv_mul_dmat, Matrix.one_mul, Matrix.mul_one]
  have h3 : dmatInv d * Matrix.scalar (Fin 6) r * dmat d = Matrix.scalar (Fin 6) r := by
    have hc : Matrix.scalar (Fin 6) r * dmat d = dmat d * Matrix.scalar (Fin 6) r :=
      Matrix.scalar_commute r (fun x => Commute.all r x) (dmat d)
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, dmatInv_mul_dmat, Matrix.one_mul]
  rw [← h2, h1, h3]

end Matrix

section Twist


variable {K : Type} [Field K] [Finite K]

@[expose] def dTw (ε : K) (hε : ε ≠ 0) : Fin 6 → Kˣ :=
  ![Units.mk0 ε hε, -Units.mk0 ε hε, Units.mk0 ε hε, 1, 1, 1]

@[expose] def eTw (ε : K) : Fin 5 → K := ![-1, -1, ε, 1, 1]

omit
  [Finite K] in
theorem dTw_ratio (ε : K) (hε : ε ≠ 0) (t : Fin 5) :
    ((dTw ε hε t.castSucc : Kˣ) : K) * (((dTw ε hε t.succ)⁻¹ : Kˣ) : K) = eTw ε t := by
  fin_cases t <;> simp [dTw, eTw, mul_inv_cancel₀ hε]

omit
  [Finite K] in
theorem eTw_sigma (σ : K →+* K) {ε : K} (hε : σ ε = -ε) (t : Fin 5) :
    σ (eTw ε t) = -eTw ε (Fin.rev t) := by
  fin_cases t <;> simp [eTw, hε]

theorem perm_a5Node : ∀ t : Fin 5, TwistTag.E6.perm (a5Node t) = a5Node (Fin.rev t) := by
  decide

theorem exists_psiTw (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) {ε : K} (hε0 : ε ≠ 0)
    (hε : σ ε = -ε) {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    ∃ Ψ : SL(6, K) →* ModGL TwistTag.E6.tag K,
      (∀ B, Ψ B = 1 →
        ∃ r : K, r ^ 6 = 1 ∧ (B : Matrix (Fin 6) (Fin 6) K) = Matrix.scalar (Fin 6) r) ∧
      Ψ.range ≤ Subgroup.closure (a5Gens K) ∧
      (∀ B, twistHom TwistTag.E6 K σ (Ψ B) = Ψ (unitaryTwist σ B)) ∧
      ∀ (t : Fin 5) (c : K),
        Ψ (tv t.castSucc t.succ c) = xUnit TwistTag.E6.tag K (a5Node t) (eTw ε t * c) ∧
          Ψ (tv t.succ t.castSucc c) = yUnit TwistTag.E6.tag K (a5Node t) ((eTw ε t)⁻¹ * c) := by
  obtain ⟨Ψ₀, hker, hrange, hval⟩ := exists_e6_sl6 (K := K) hp hf hK
  set d := dTw ε hε0 with hd
  have hval' : ∀ (t : Fin 5) (c : K),
      Ψ₀ (conjDiag d (tv t.castSucc t.succ c)) =
        xUnit TwistTag.E6.tag K (a5Node t) (eTw ε t * c) ∧
      Ψ₀ (conjDiag d (tv t.succ t.castSucc c)) =
        yUnit TwistTag.E6.tag K (a5Node t) ((eTw ε t)⁻¹ * c) := by
    intro t c
    have hne : t.castSucc ≠ t.succ := Fin.castSucc_lt_succ.ne
    rw [conjDiag_tv d hne, conjDiag_tv d hne.symm]
    have hr : ((d t.castSucc : Kˣ) : K) * (((d t.succ)⁻¹ : Kˣ) : K) = eTw ε t :=
      dTw_ratio ε hε0 t
    have ha : ((d t.castSucc : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hb : ((d t.succ : Kˣ) : K) ≠ 0 := Units.ne_zero _
    simp only [Units.val_inv_eq_inv_val] at hr ⊢
    refine ⟨?_, ?_⟩
    · have : (d t.castSucc : K) * c * ((d t.succ : K))⁻¹ = eTw ε t * c := by
        rw [← hr]; ring
      rw [this]
      exact (hval t _).1
    · have : (d t.succ : K) * c * ((d t.castSucc : K))⁻¹ = (eTw ε t)⁻¹ * c := by
        rw [← hr]; field_simp
      rw [this]
      exact (hval t _).2
  refine ⟨Ψ₀.comp (conjDiag d), ?_, ?_, ?_, fun t c => hval' t c⟩
  · intro B hB
    have h1 : conjDiag d B ∈ Ψ₀.ker := hB
    obtain ⟨r, hr, hrB⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hker h1)
    refine ⟨r, by simpa using hr, eq_scalar_of_conjDiag d ?_⟩
    rw [← hrB]
  · rintro _ ⟨B, rfl⟩
    exact hrange ⟨conjDiag d B, rfl⟩
  · intro B
    have h := DFunLike.congr_fun (MonoidHom.eq_of_eqOn_dense (closure_adjacentSet (E := K))
      (f := (twistHom TwistTag.E6 K σ).comp (Ψ₀.comp (conjDiag d)))
      (g := (Ψ₀.comp (conjDiag d)).comp (unitaryTwist σ)) (by
        rintro _ ⟨t, c, rfl | rfl⟩
        · have hne : t.castSucc ≠ t.succ := Fin.castSucc_lt_succ.ne
          rw [← tv_of_ne (castSucc_ne_succ t)]
          simp only [MonoidHom.comp_apply]
          rw [(hval' t c).1, twistHom_xUnit, unitaryTwist_tv σ hne, Fin.rev_succ, Fin.rev_castSucc,
            (hval' (Fin.rev t) _).1, perm_a5Node, map_mul, eTw_sigma σ hε]
          congr 1
          ring
        · have hne : t.castSucc ≠ t.succ := Fin.castSucc_lt_succ.ne
          rw [← tv_of_ne (castSucc_ne_succ t).symm]
          simp only [MonoidHom.comp_apply]
          rw [(hval' t c).2, twistHom_yUnit, unitaryTwist_tv σ hne.symm, Fin.rev_succ,
            Fin.rev_castSucc, (hval' (Fin.rev t) _).2, perm_a5Node, map_mul, map_inv₀,
            eTw_sigma σ hε]
          congr 1
          rw [inv_neg]
          ring)) B
    exact h

end Twist

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
