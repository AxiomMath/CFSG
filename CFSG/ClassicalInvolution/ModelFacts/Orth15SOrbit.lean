module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64I
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64J

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

section Orbit

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

omit [Finite G] in
theorem sup_inf_normalizer_le_normalizer (K J : Subgroup G) :
    (J ⊓ Subgroup.normalizer (K : Set G)) ⊔ (K ⊓ Subgroup.normalizer (J : Set G)) ≤
      Subgroup.normalizer (K : Set G) :=
  sup_le inf_le_right (inf_le_left.trans Subgroup.le_normalizer)

theorem exists_mem_sup_conj_of_cfg64 (c : Cfg64 Ω K J z j u v R T) {g : G}
    (hg : g ∈ pairNormalizers K J z j) (hgK : conjSub g K = J) :
    ∃ ρ ∈ R ⊔ T, conjSub ρ K = J := by
  obtain ⟨N₀K, hK0⟩ := exists_oddCompl c.sylow_U inferInstance
  obtain ⟨N₀J, hJ0⟩ := exists_oddCompl c.sylow_V inferInstance
  set X : Subgroup G := (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
    (K ⊓ Subgroup.normalizer (J : Set G)) with hX
  have hYN := c.Y_le_normalizer_X hK0 hJ0
  have hRT : R ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (c.R_le_Y.trans hYN) (c.T_le_Y.trans hYN)
  have hgmem : g ∈ X ⊔ (R ⊔ T) := by
    have h := c.Y_le hg
    rwa [sup_assoc] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hRT hgmem
  refine ⟨b, hb, ?_⟩
  have hbinv : b⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).inv_mem (hRT hb)
  have ha' : b⁻¹ * a * b ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp hbinv a).mp ha
    simpa using this
  have hKX : b⁻¹ * a * b ∈ Subgroup.normalizer (K : Set G) :=
    sup_inf_normalizer_le_normalizer K J ha'
  have e : a * b = b * (b⁻¹ * a * b) := by group
  rw [← hgK, e, conjSub_mul, conjSub_eq_of_mem_normalizer hKX]

end Orbit

end CFSG.ClassicalInvolution.Asc77
