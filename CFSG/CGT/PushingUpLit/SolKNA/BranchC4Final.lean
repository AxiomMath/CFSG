module

public import CFSG.CGT.PushingUpLit.SolKNA.BranchC4Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open C4Aux

variable {G : Type} [Group G]

namespace C4Data

variable [Finite G] {R T W Z P : Subgroup G} {c x : G} (D : C4Data R T W Z P c x)
include D

theorem false_of
    (hbasic : ¬ conjSubgroup x R ≤ Subgroup.normalizer (R : Set G) →
      ∀ T' : Subgroup G, T' = conjSubgroup x R ⊓ Subgroup.normalizer (R : Set G) → T' ≠ ⊥ →
        Nat.card ↥(R ⊓ Subgroup.normalizer (T' : Set G)) = Nat.card ↥T' ∧
          R ⊓ Subgroup.normalizer (T' : Set G) = R ⊓ Subgroup.centralizer (T' : Set G))
    (hL18 : Lemma18Trans G) : False := by
  have hTx := D.conj_H_inf_normalizer (D.conj_R_inf_normalizer hbasic)
  have hH2 : IsPGroup 2 ↥(W ⊓ R) := D.A.two_R.to_le inf_le_right
  have hZxne : conjSubgroup x Z ≠ ⊥ := by
    intro hbot
    have := D.card_Zx
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨z', hz', hz'1, hz'c⟩ : ∃ z' ∈ Z, z' ≠ 1 ∧ z' ≠ c := by
    by_contra hcon
    have hle : Z ≤ Subgroup.zpowers c := by
      intro z hz
      by_cases h1 : z = 1
      · rw [h1]
        exact Subgroup.one_mem _
      · have : z = c := by_contra fun h => hcon ⟨z, hz, h1, h⟩
        rw [this]
        exact Subgroup.mem_zpowers c
    have h2 : Nat.card ↥Z ≤ Nat.card ↥(Subgroup.zpowers c) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, D.card_Z] at h2
    have hord : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact D.Z_sq D.c_mem)
    have := Nat.le_of_dvd (by norm_num) hord
    omega
  have hinf : (W ⊓ R) ⊓ conjSubgroup x (W ⊓ R) = ⊥ := by
    rw [eq_bot_iff]
    calc (W ⊓ R) ⊓ conjSubgroup x (W ⊓ R) ≤ R ⊓ conjSubgroup x R :=
          inf_le_inf inf_le_right (conjSubgroup_mono inf_le_right)
      _ = ⊥ := D.inf_conj_R
      _ ≤ ⊥ := le_rfl
  have hΦ₁ : ∀ h ∈ W ⊓ R, h * h ∈ Z := fun h hh => D.sq_mem_Z hh.1
  have hΦ₂ : ∀ a ∈ W ⊓ R, ∀ b ∈ W ⊓ R, a * b * a⁻¹ * b⁻¹ ∈ Z :=
    fun a ha b hb => D.comm_mem_Z ha.1 hb.1
  have hCZ : ∀ n ∈ Z, ∀ h ∈ W ⊓ R, n * h = h * n := fun n hn h hh => D.Z_central hn hh.1
  have hCT : Nonempty (↥Z ≃* ↥(conjSubgroup x Z)) := ⟨(MulAut.conj x).subgroupMap Z⟩
  have hT2 : ∀ u ∈ conjSubgroup x Z, u * u = 1 := fun u hu => D.P_sq (D.Zx_le_P hu)
  have hCR : Z ≠ W ⊓ R := by
    intro h
    have := D.card_H
    rw [← h, D.card_Z] at this
    omega
  have hrel : Z.relIndex (W ⊓ R) = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := Z) (K := W ⊓ R)
    rw [inf_of_le_left D.Z_le_H, D.card_Z, D.card_H] at h1
    omega
  have hNnorm : (W ⊓ R) ⊔ conjSubgroup x (W ⊓ R) ≤
      Subgroup.normalizer ((Z ⊔ conjSubgroup x Z : Subgroup G) : Set G) := by
    rw [D.Z_sup_Zx]
    refine sup_le D.H_le_normalizer_P fun v hv => ?_
    have hv' : x⁻¹ * v * x ∈ W ⊓ R := mem_conjSubgroup.mp hv
    have hvN := D.H_le_normalizer_P hv'
    have e : v = x * (x⁻¹ * v * x) * x⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ D.x_norm hvN) (Subgroup.inv_mem _ D.x_norm)
  have hΦb₁ : ∀ v ∈ conjSubgroup x (W ⊓ R), v * v ∈ conjSubgroup x Z := by
    intro v hv
    have hv' : x⁻¹ * v * x ∈ W ⊓ R := mem_conjSubgroup.mp hv
    rw [mem_conjSubgroup]
    have e : x⁻¹ * (v * v) * x = (x⁻¹ * v * x) * (x⁻¹ * v * x) := by group
    rw [e]
    exact D.sq_mem_Z hv'.1
  have hΦb₂ : ∀ v ∈ conjSubgroup x (W ⊓ R), ∀ w ∈ conjSubgroup x (W ⊓ R),
      v * w * v⁻¹ * w⁻¹ ∈ conjSubgroup x Z := by
    intro v hv w hw
    have hv' : x⁻¹ * v * x ∈ W ⊓ R := mem_conjSubgroup.mp hv
    have hw' : x⁻¹ * w * x ∈ W ⊓ R := mem_conjSubgroup.mp hw
    rw [mem_conjSubgroup]
    have e : x⁻¹ * (v * w * v⁻¹ * w⁻¹) * x =
        (x⁻¹ * v * x) * (x⁻¹ * w * x) * (x⁻¹ * v * x)⁻¹ * (x⁻¹ * w * x)⁻¹ := by group
    rw [e]
    exact D.comm_mem_Z hv'.1 hw'.1
  have hTZ : ∀ t ∈ conjSubgroup x Z, ∀ v ∈ conjSubgroup x (W ⊓ R), t * v = v * t := by
    intro t ht v hv
    have ht' : x⁻¹ * t * x ∈ Z := mem_conjSubgroup.mp ht
    have hv' : x⁻¹ * v * x ∈ W ⊓ R := mem_conjSubgroup.mp hv
    have h1 := D.Z_central ht' hv'.1
    calc t * v = x * ((x⁻¹ * t * x) * (x⁻¹ * v * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * v * x) * (x⁻¹ * t * x)) * x⁻¹ := by rw [h1]
      _ = v * t := by group
  obtain ⟨k, -, hkN, hk⟩ := hL18 (W ⊓ R) x (Subgroup.normalizer (P : Set G)) D.x_norm
    D.H_le_normalizer_P hH2 D.tiRel (conjSubgroup x Z) Z (Z ⊔ conjSubgroup x Z) hTx.symm hZxne
    hinf D.cent_eq.symm hΦ₁ hΦ₂ hCZ hCT hT2 hCR hrel D.card_Zx rfl hNnorm hΦb₁ hΦb₂ hTZ
    c D.c_mem D.c_ne z' hz' hz'1
  have hfix := D.fix_c hkN
  rw [hfix] at hk
  exact hz'c hk.symm

end C4Data

end CFSG.CGT.PushingUpLit.SolKNA
