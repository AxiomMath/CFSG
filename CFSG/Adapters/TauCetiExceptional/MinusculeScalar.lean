module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdKer

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : Type*} [CommRing R]

include hV in
theorem rootOp_single_apply_sRefl
    (X : Fin D.d →₀ R) {i : Fin τ.rank} {a : Fin D.d}
    (ha : D.wt a i = -1) : D.rootOp R (Pi.single i 1) X (hV.sRefl i a) = X a := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X Y hX hY => rw [map_add, Finsupp.add_apply, hX, hY, Finsupp.add_apply]
  | single b c =>
    rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, hV.rootOp_single_apply,
      Finsupp.smul_apply]
    congr 1
    by_cases hba : b = a
    · subst hba
      rw [ite_eq_left ha, Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hba)]
      split_ifs
      · exact Finsupp.single_eq_of_ne fun h => hba (hV.sRefl_injective i h).symm
      · rfl

include hV in
theorem eq_smul_one_of_commute
    (hhw : ∀ a : Fin D.d, (a : ℕ) ≠ 0 → ∃ i, D.wt a i = -1)
    (hord : DegOrdered D) (hd : 0 < D.d) {z : Module.End R (Fin D.d →₀ R)}
    (hE : ∀ i, Commute z (D.rootOp R (Pi.single i 1)))
    (hF : ∀ i, Commute z (D.rootOp R (-Pi.single i 1))) :
    z = z (Finsupp.single ⟨0, hd⟩ 1) ⟨0, hd⟩ • 1 := by
  set c := z (Finsupp.single ⟨0, hd⟩ 1) ⟨0, hd⟩ with hc
  set z' := z - c • (1 : Module.End R (Fin D.d →₀ R)) with hz'
  have hE' : ∀ i, Commute z' (D.rootOp R (Pi.single i 1)) := fun i =>
    (hE i).sub_left ((Commute.one_left _).smul_left c)
  have hF' : ∀ i, Commute z' (D.rootOp R (-Pi.single i 1)) := fun i =>
    (hF i).sub_left ((Commute.one_left _).smul_left c)
  have hup : ∀ (a : Fin D.d) (i : Fin τ.rank), D.wt a i = -1 → hV.sRefl i a < a := by
    intro a i ha
    have hw : D.wt (hV.sRefl i a) = D.wt a + toWeight (Pi.single i 1) := by
      rw [hV.wt_sRefl, reflectWeight_eq_add_of_eq_neg_one ha]
    have hdeg := hV.deg_eq_add hw
    rw [ht_single, mul_one] at hdeg
    have hs := hV.scale_pos
    by_contra hlt
    have := hord a (hV.sRefl i a) (not_lt.1 hlt)
    omega
  have h0 : ∀ i, D.wt (⟨0, hd⟩ : Fin D.d) i ≠ -1 := fun i h =>
    absurd (Fin.lt_def.1 (hup _ i h)) (Nat.not_lt_zero _)
  have hv0 : z' (Finsupp.single ⟨0, hd⟩ 1) = 0 := by
    ext a
    by_cases ha : (a : ℕ) = 0
    · have e : a = ⟨0, hd⟩ := Fin.ext ha
      subst e
      rw [hz', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one,
        ← hc, sub_self, Finsupp.coe_zero, Pi.zero_apply]
    · obtain ⟨i, hi⟩ := hhw a ha
      rw [← rootOp_single_apply_sRefl hV (z' (Finsupp.single ⟨0, hd⟩ 1)) hi,
        ← Module.End.mul_apply, ← (hE' i).eq, Module.End.mul_apply, hV.rootOp_single_apply,
        ite_eq_right (h0 i), map_zero]
      rfl
  have key : ∀ m (a : Fin D.d), (a : ℕ) = m → z' (Finsupp.single a 1) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro a ham
      by_cases ha : (a : ℕ) = 0
      · rw [show a = ⟨0, hd⟩ from Fin.ext ha]
        exact hv0
      · obtain ⟨i, hi⟩ := hhw a ha
        have hb : D.wt (hV.sRefl i a) i = 1 := by rw [hV.wt_sRefl_self, hi, neg_neg]
        have hlt : (hV.sRefl i a : ℕ) < m := ham ▸ Fin.lt_def.1 (hup a i hi)
        have e : Finsupp.single a (1 : R) =
            D.rootOp R (-Pi.single i 1) (Finsupp.single (hV.sRefl i a) 1) := by
          rw [hV.rootOp_neg_single_apply, ite_eq_left hb, hV.sRefl_sRefl]
        rw [e, ← Module.End.mul_apply, (hF' i).eq, Module.End.mul_apply, ih _ hlt _ rfl,
          map_zero]
  have hz0 : z' = 0 := ext_single fun a => by rw [key _ a rfl, LinearMap.zero_apply]
  rw [hz', sub_eq_zero] at hz0
  exact hz0

theorem e6Data_dominant : ∀ a : Fin e6Data.d, (a : ℕ) ≠ 0 → ∃ i, e6Data.wt a i = -1 := by
  decide +kernel

theorem e7Data_dominant : ∀ a : Fin e7Data.d, (a : ℕ) ≠ 0 → ∃ i, e7Data.wt a i = -1 := by
  decide +kernel

section Carrier

variable {n : ℕ} {lab : Fin n ≃ Fin D.d} {L : Type} [Field L]
  {hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef} {S : AdjSigns τ} {hS : S.check D = true}
  {H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L)}
  {hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L)}

include hV in
theorem exists_eq_smul_one_of_adCarrier_eq_one
    (hhw : ∀ a : Fin D.d, (a : ℕ) ≠ 0 → ∃ i, D.wt a i = -1) (hord : DegOrdered D)
    (hd : 0 < D.d) {z : H} (hz : adCarrier hV hpd hS lab L H hH z = 1) :
    ∃ c : L, ((z : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      c • (1 : Matrix (Fin n) (Fin n) L) := by
  rw [adCarrier_eq_one_iff] at hz
  have hE := fun i => (commute_toMat_rootUnit_iff hV lab L _ _).1 (hz i).1
  have hF := fun i => (commute_toMat_rootUnit_iff hV lab L _ _).1 (hz i).2
  obtain ⟨c, hc⟩ : ∃ c : L, (((toMat lab L).symm (z : Matrix.GeneralLinearGroup (Fin n) L) :
      (Module.End L (Fin D.d →₀ L))ˣ) : Module.End L (Fin D.d →₀ L)) = c • 1 :=
    ⟨_, eq_smul_one_of_commute hV hhw hord hd hE hF⟩
  refine ⟨c, ?_⟩
  ext r s
  conv_lhs => rw [← (toMat lab L).apply_symm_apply (z : Matrix.GeneralLinearGroup (Fin n) L)]
  rw [toMat_apply, hc, LinearMap.smul_apply, Module.End.one_apply, Finsupp.smul_apply,
    Matrix.smul_apply, Matrix.one_apply, Finsupp.single_apply]
  by_cases hrs : r = s
  · subst hrs
    simp
  · simp [hrs, lab.injective.ne (Ne.symm hrs)]

end Carrier

end CFSG.TauCetiBridge.Minuscule
