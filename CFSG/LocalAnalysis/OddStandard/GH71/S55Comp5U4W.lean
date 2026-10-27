module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4WIso
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55.C5U

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.U
  CFSG.ComponentClassification.Burgoyne.Proj CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3U

theorem exists_lift_pow_eq_one {S : Type*} [Group S] {N : Subgroup S} [N.Normal] {m p : ℕ}
    (hp : p.Prime) (hm : ∀ z ∈ N, z ^ m = 1) (hpm : ¬ p ∣ m) {y : S ⧸ N} (hy : y ^ p = 1) :
    ∃ a : S, (a : S ⧸ N) = y ∧ a ^ p = 1 := by
  obtain ⟨a0, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : a0 ^ p ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy
  obtain ⟨k, hk⟩ := exists_pow_pow_eq hp hy hpm
  refine ⟨a0 ^ (m * k), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, pow_mul, hk]
  · rw [← pow_mul, show m * k * p = p * m * k by ring, pow_mul, pow_mul, hm _ h1, one_pow]

variable {r f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData r f K)

include h in
theorem scalar_pow_four (z : ↥(StatedSU 4 (r ^ f) K))
    (hz : z ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (r ^ f) K)) : z ^ 4 = 1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet := ((mem_unitarySU_iff h).mp z.2).1
  rw [← hc] at hdet
  have hc4 : (c : K) ^ 4 = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_smul] using hdet
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, ← hc, ← map_pow]
  have : c ^ 4 = 1 := Units.ext (by simpa using hc4)
  rw [this, map_one]
  rfl

include h in
theorem not_rFree_of_dvd_sq_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (r ^ f) ^ 2 + 1) {y : StatedProj (StatedSU 4 (r ^ f) K)} (hy : orderOf y = p) :
    ¬ RFree r y := by
  have : CharP K r := h.charP
  intro hyr
  have hp4 : ¬ p ∣ 4 := fun h4 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
  obtain ⟨A, hAy, hAp⟩ := exists_lift_pow_eq_one hp (scalar_pow_four h) hp4
    (show y ^ p = 1 by rw [← hy]; exact pow_orderOf_eq_one y)
  set M : Matrix (Fin 4) (Fin 4) K := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hM
  have hA1 : M ≠ 1 := by
    intro h1
    have h2 : A = 1 := Subtype.ext (Units.ext h1)
    rw [h2, QuotientGroup.mk_one] at hAy
    rw [← hAy, orderOf_one] at hy
    exact hp.one_lt.ne' hy.symm
  have hAG : (A : GL (Fin 4) K) ^ p = 1 := by rw [← SubgroupClass.coe_pow, hAp]; rfl
  have hApM : M ^ p = 1 := by rw [hM, ← Units.val_pow_eq_pow_val, hAG, Units.val_one]
  obtain ⟨W, hW0, hWiso, hAW⟩ :=
    exists_isotropic_invariant h hp hp2 hpq ((mem_unitarySU_iff h).mp A.2).2 hApM hA1
  have hpow : ∀ m : ℕ, ∀ w ∈ W, M ^ m *ᵥ w ∈ W := by
    intro m
    induction m with
    | zero => intro w hw; simpa using hw
    | succ m ih => intro w hw; rw [pow_succ, ← mulVec_mulVec]; exact ih _ (hAW w hw)
  have hAinv : (((A : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      M ^ (p - 1) := by
    have e : (A : GL (Fin 4) K)⁻¹ = (A : GL (Fin 4) K) ^ (p - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hAG]
    rw [e, Units.val_pow_eq_pow_val]
  have hn1 : 1 ≤ 4 := by norm_num
  set A' : uU h 4 := ⟨(A : GL (Fin 4) K), statedSU_le_uU h A.2⟩ with hA'
  set E := uElatImage (p := r) (f := f) W with hE
  have hE1 : E ≠ ⊥ := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hww : stdHermForm h 4 w w = 0 := hWiso w hwW w hwW
    obtain ⟨b, hb0, hb⟩ := exists_bar_eq_neg h
    intro hbot
    have hmem : projH _ (utvSU h hww hb) ∈ E :=
      proj_utvSU_mem_uElatImage h hwW (fun y' hy' => hWiso w hwW y' hy') hww hb
    rw [hbot, Subgroup.mem_bot] at hmem
    exact proj_utvSU_ne_one h hw0 hww hb0 hb hmem
  refine hE1 (hyr E (isPGroup_uElatImage W) ?_)
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hconj : y * projH _ g * y⁻¹ = uConjAut h hn1 A' (projH _ g) := by
    rw [uConjAut_proj, ← hAy]
    rfl
  rw [hconj]
  exact uConjAut_mem_uElatImage h hn1 A' (fun w hw => hAW w hw)
    (fun w hw => by rw [hAinv]; exact hpow _ w hw) ⟨g, hg, rfl⟩

end CFSG.OddStandard.GH71.S55.C5U
