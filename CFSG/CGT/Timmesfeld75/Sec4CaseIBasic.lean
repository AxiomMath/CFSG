module

public import CFSG.CGT.Timmesfeld75.Sec6Four
public import CFSG.CGT.Timmesfeld75.Sec4TwoStruct

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

section Setup

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G}

@[expose] def sec4R (T T₁ T₂ : Subgroup G) : Subgroup G := T ⊔ sec4N T T₁ T₂

theorem left_le_sec4R : T ≤ sec4R T T₁ T₂ := le_sup_left

theorem sec4N_le_sec4R : sec4N T T₁ T₂ ≤ sec4R T T₁ T₂ := le_sup_right

theorem normIn_mid_le_sec4R : normIn T₁ T ≤ sec4R T T₁ T₂ :=
  normIn_le_sec4N_mid.trans sec4N_le_sec4R

theorem normIn_right_le_sec4R : normIn T₂ T ≤ sec4R T T₁ T₂ :=
  normIn_le_sec4N_right.trans sec4N_le_sec4R

theorem sec4R_le_normalizer_left : sec4R T T₁ T₂ ≤ Subgroup.normalizer (T : Set G) :=
  sup_le Subgroup.le_normalizer sec4N_le_normalizer_left

end Setup

section Hyp

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.left_le_normalizer_sec4N (h : Sec4Hyp T T₁ a T₂) :
    T ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := fun _ hx =>
  h.sec4Y_le_normalizer (left_le_sec4Y hx)

theorem Sec4Hyp.isPGroup_sec4R (h : Sec4Hyp T T₁ a T₂) : IsPGroup 2 (sec4R T T₁ T₂) :=
  (isPGroup_two_of_isElemAbelian h.pair.wc.1).to_sup_of_normal_right' h.isPGroup_sec4N
    h.left_le_normalizer_sec4N

omit [Finite G] in
theorem Sec4Hyp.exists_sec4Hyp_of_mem_normD (h : Sec4Hyp T T₁ a T₂) {d : G} (hd : d ∈ normD T)
    (hdL : d ∉ T ⊔ normIn T₁ T) (hcomm : ∀ l ∈ normIn T₁ T, ⁅d, l⁆ ∈ T) :
    ∃ T₂' : Subgroup G, Sec4Hyp T T₁ d T₂' := by
  obtain ⟨k, t, htT, ht1, hdk⟩ := hd.1
  refine ⟨conjSubgroup k⁻¹ T, h.pair, h.glob, h.iso, hd, hdL, hcomm, ⟨k⁻¹, rfl⟩, ?_⟩
  refine mem_conjSubgroup.mpr ?_
  rw [inv_inv, hdk]
  have e : k * (k⁻¹ * t * k) * k⁻¹ = t := by group
  rw [e]
  exact htT

theorem Sec4Hyp.commutator_mul_sec4N (h : Sec4Hyp T T₁ a T₂) {t n l : G} (hn : n ∈ sec4N T T₁ T₂)
    (hl : l ∈ normIn T₁ T) : ⁅t * n, l⁆ = ⁅t, l⁆ := by
  have hnl : n * l = l * n :=
    elemAbelian_mul_comm h.isElemAbelian_sec4N hn (normIn_le_sec4N_mid hl)
  simp only [commutatorElement_def]
  calc t * n * l * (t * n)⁻¹ * l⁻¹ = t * (n * l * n⁻¹) * t⁻¹ * l⁻¹ := by group
    _ = t * l * t⁻¹ * l⁻¹ := by rw [hnl]; group

theorem Sec4Hyp.mem_or_mem_sec4N_of_mem_sec4R (h : Sec4Hyp T T₁ a T₂) {d : G} (hd : d ∈ normD T)
    (hdR : d ∈ sec4R T T₁ T₂) : d ∈ T ∨ d ∈ sec4N T T₁ T₂ := by
  have hTab := h.pair.wc.1
  have hdd : d * d = 1 := mul_self_eq_one_of_mem_classD hTab hd.1
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right T (sec4N T T₁ T₂)
    h.left_le_normalizer_sec4N
  have hdR' : d ∈ ((T : Set G) * (sec4N T T₁ T₂ : Set G)) := by
    rw [← hmul]
    exact hdR
  obtain ⟨t, htT, n, hn, hdtn⟩ := hdR'
  have hdtn' : d = t * n := hdtn.symm
  subst hdtn'
  by_cases htL : t ∈ normIn T T₁
  · exact Or.inr ((sec4N T T₁ T₂).mul_mem (normIn_le_sec4N_left htL) hn)
  have hcommL : ∀ l ∈ normIn T₁ T, ⁅t * n, l⁆ ∈ T := fun l hl => by
    rw [h.commutator_mul_sec4N hn hl]
    have hlN : l ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hl).2
    simp only [commutatorElement_def]
    have := T.mul_mem htT ((Subgroup.mem_normalizer_iff.1 hlN _).1 (T.inv_mem htT))
    simpa [mul_assoc] using this
  by_cases hdL : t * n ∈ T ⊔ normIn T₁ T
  · by_cases hdT : t * n ∈ T
    · exact Or.inl hdT
    · refine Or.inr (cfgM_le_sec4N ?_)
      exact h.sec3.cfg.mem_cfgM_of_mul_self_eq_one_of_mem_sup hdd (by rwa [sup_comm] at hdL) hdT
  · exfalso
    obtain ⟨T₂', h'⟩ := h.exists_sec4Hyp_of_mem_normD hd hdL hcommL
    have hB : t * n ∈ Subgroup.normalizer (normIn T₁ T : Set G) := by
      by_contra hA
      exact h'.false_of_not_normalizer hA
    have htC : t ∈ T ⊓ Subgroup.centralizer (normIn T₁ T : Set G) := by
      refine ⟨htT, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have h1 := h'.comm_of_mem_normalizer hB hl
      have h2 := h.commutator_mul_sec4N (t := t) hn hl
      have h3 : ⁅t * n, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h1
      rw [h3] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.1 h2.symm).symm
    rw [h.sec3.cfg.inf_centralizer_normIn] at htC
    exact htL htC

end Hyp

end CFSG.CGT.Timmesfeld75
