module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_2_trans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 →
      u ≠ z → u * u = 1 → ∀ J ∈ dstarComp Ω K,
        ∃ h ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G),
          conjSub h K = J

@[expose] def C23_2_fuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23Setting p f Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → ∀ u ∈ K ⊔ K', u ∈ W → u ≠ 1 →
      u ≠ z → u * u = 1 → ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
        IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
          orderOf x = 4 → orderOf y = 4 →
            ∃ c ∈ Subgroup.centralizer ({z} : Set G), c * u * c⁻¹ = x * y

variable {p f}

theorem c23_2_of (hE : ThmEWithSylow p f) (htr : C23_2_trans p f) (hfuse : C23_2_fuse p f) :
    C23_2 p f := by
  intro G _ _ _ Ω K K' z h W hW hzW u hu huW hu1 huz hu2
  have hs := h.setting
  have hstd : StdCent Ω K
      (Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G)) z :=
    hs.stdCent_of_twin le_sup_right fun L hL L' hL' hne R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy => by
      obtain ⟨c, hcz, hcu⟩ := hfuse G Ω K K' z hs W hW hzW u hu huW hu1 huz hu2 L hL L' hL' hne
        R₁ R₂ hR₁ hR₂ hc x hx y hy ox oy
      intro a ha
      have ha' : a * (x * y) = (x * y) * a := Subgroup.mem_centralizer_singleton_iff.mp ha
      have hu' : u = c⁻¹ * (x * y) * c := by rw [← hcu]; group
      have hcomm : (c⁻¹ * a * c) * u = u * (c⁻¹ * a * c) := by
        have e1 : c⁻¹ * (a * (x * y)) * c = c⁻¹ * ((x * y) * a) * c := by rw [ha']
        calc (c⁻¹ * a * c) * u = c⁻¹ * (a * (x * y)) * c := by rw [hu']; group
          _ = c⁻¹ * ((x * y) * a) * c := e1
          _ = u * (c⁻¹ * a * c) := by rw [hu']; group
      have hcH : c ∈ Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_right hcz
      have ha'H : c⁻¹ * a * c ∈
          Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({z} : Set G) :=
        Subgroup.mem_sup_left (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      have : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcH ha'H) (Subgroup.inv_mem _ hcH)
  exact thmE_apply hE hs.stand hs.hz hs.hK' hs.hne hstd
    (htr G Ω K K' z hs W hW hzW u hu huW hu1 huz hu2)

end CFSG.ClassicalInvolution.Asc77
