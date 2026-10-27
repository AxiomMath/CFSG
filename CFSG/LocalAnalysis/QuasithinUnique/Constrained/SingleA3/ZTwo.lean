module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Case2
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Fusion

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}

omit [Finite G] in
theorem commutator_eq_top_of_nonabelian [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact (hab ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) a b)).elim
  · exact h

theorem zTwoConfig_false (h : ZTwoConfig T S U R y x c) : False := by
  classical
  have := h.simple
  obtain ⟨z, hd⟩ := h.exists_d8
  have hcomm : commutator G = ⊤ := commutator_eq_top_of_nonabelian h.nonabelian
  have hyc : y ∈ commutator G := hcomm ▸ Subgroup.mem_top y
  have hindex : Nat.Coprime 2 T.index := by
    have h1 := h.sylowT.2.2
    rw [index_subgroupOf_top] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h1
  have hyT : y ∈ T := h.S_le h.y_mem
  have hRT : R ≤ T := h.R_le.trans h.S_le
  by_cases hcase : ∀ a : G, a⁻¹ * y * a ∈ T → a⁻¹ * y * a ∈ S
  · exact generalized_thompson_transfer_two hindex
      ⟨hRT, Subgroup.normal_subgroupOf_of_le_normalizer (h.T_norm_R hd)⟩
      (h.commutator_T_le_R hd) hyT h.y_not_mem_R h.y_order
      (fun a ha => h.fusion_S hd (hcase a ha)) hyc
  · push Not at hcase
    obtain ⟨a, haT, haS⟩ := hcase
    have he2 : (a⁻¹ * y * a) ^ 2 = 1 := by
      have e : (a⁻¹ * y * a) ^ 2 = a⁻¹ * (y * y) * a := by
        rw [pow_two]; group
      rw [e]
      have : y * y = 1 := by simpa [pow_two] using h.y_sq
      rw [this]; group
    obtain ⟨s₁, hs₁, hes⟩ := (h.T_decomp hd haT).resolve_left haS
    have hes' : ∃ s₁ ∈ S, a⁻¹ * y * a = x * s₁ := ⟨s₁, hs₁, hes⟩
    refine generalized_thompson_transfer_two (H := T) (K := R ⊔ zpowers (a⁻¹ * y * a * y))
      hindex ⟨h.K_le_T haT, Subgroup.normal_subgroupOf_of_le_normalizer
        (h.T_le_normalizer_K hd haT)⟩
      ((h.commutator_T_le_R hd).trans le_sup_left) hyT
      (h.y_not_mem_K hd hes' he2 haT haS) h.y_order ?_ hyc
    intro b hb
    by_cases hbS : b⁻¹ * y * b ∈ S
    · exact Subgroup.mem_sup_left (h.fusion_S hd hbS)
    · have hw2 : (b⁻¹ * y * b) ^ 2 = 1 := by
        have e : (b⁻¹ * y * b) ^ 2 = b⁻¹ * (y * y) * b := by
          rw [pow_two]; group
        rw [e]
        have : y * y = 1 := by simpa [pow_two] using h.y_sq
        rw [this]; group
      exact h.inv_mul_mem_K hd hes' he2 haT hb hbS hw2

end CFSG.QuasithinUnique
