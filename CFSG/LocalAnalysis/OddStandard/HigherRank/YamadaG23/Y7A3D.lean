module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3CM
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3A0

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_normM6_A (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    normIn (M6 c.e) c.s.fr.A = AV1 c.e := by
  have h := c.y7acfg hH
  have hVA : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hAM6 : c.s.fr.A ≤ M6 c.e := le_sup_left.trans (y7a_AV1_le_M6 c hH hF)
  apply le_antisymm
  · intro m hm
    obtain ⟨hmM6, hmN⟩ := Subgroup.mem_inf.mp hm
    have hc : ∀ a ∈ c.s.fr.A, ⁅a, m⁆ ∈ zpowers c.s.fr.z := by
      intro a ha
      have hA : ⁅a, m⁆ ∈ c.s.fr.A := by
        have h1 : m * a⁻¹ * m⁻¹ ∈ c.s.fr.A :=
          (Subgroup.mem_set_normalizer_iff.mp hmN a⁻¹).mp (c.s.fr.A.inv_mem ha)
        have heq : ⁅a, m⁆ = a * (m * a⁻¹ * m⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [heq]
        exact c.s.fr.A.mul_mem ha h1
      have hV : ⁅a, m⁆ ∈ V1 c.e := by
        have h1 : ⁅m, a⁆ ∈ V1 c.e :=
          y7a_comm_M6_AV c hH hF (Subgroup.commutator_mem_commutator hmM6
            (Subgroup.mem_sup_left ha))
        have h2 : ⁅a, m⁆ = ⁅m, a⁆⁻¹ := (commutatorElement_inv (g₁ := m) (g₂ := a)).symm
        rw [h2]
        exact (V1 c.e).inv_mem h1
      rw [← y7a_A_inf_V h]
      exact Subgroup.mem_inf.mpr ⟨hA, hV⟩
    obtain ⟨a₀, ha₀, hcent⟩ := y7a_exists_a0 c hH hc
    have hmem : a₀⁻¹ * m ∈ centIn (M6 c.e) c.s.fr.A :=
      Subgroup.mem_inf.mpr ⟨(M6 c.e).mul_mem ((M6 c.e).inv_mem (hAM6 ha₀)) hmM6, hcent⟩
    rw [y7a_cent_M6_A c hH hF] at hmem
    have heq : m = a₀ * (a₀⁻¹ * m) := by group
    rw [heq]
    exact Subgroup.mul_mem_sup ha₀ hmem
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨y7a_AV1_le_M6 c hH hF hx, ?_⟩
    have hAVn : ∀ g ∈ AV1 c.e, ∀ y ∈ c.s.fr.A, g * y * g⁻¹ ∈ c.s.fr.A := by
      intro g hg y hy
      obtain ⟨a, ha, v, hv, rfl⟩ := y7a_AV_elems h g hg
      have hvy : v * y = y * v := (hVA y hy v hv).symm
      have heq : a * v * y * (a * v)⁻¹ = a * y * a⁻¹ := by
        calc a * v * y * (a * v)⁻¹ = a * (v * y) * v⁻¹ * a⁻¹ := by group
          _ = a * (y * v) * v⁻¹ * a⁻¹ := by rw [hvy]
          _ = a * y * a⁻¹ := by group
      rw [heq]
      exact c.s.fr.A.mul_mem (c.s.fr.A.mul_mem ha hy) (c.s.fr.A.inv_mem ha)
    rw [Subgroup.mem_set_normalizer_iff]
    intro y
    constructor
    · exact hAVn x hx y
    · intro hy
      have hmem := hAVn x⁻¹ ((AV1 c.e).inv_mem hx) _ hy
      have heq : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rw [heq] at hmem
      exact hmem

end CFSG.OddStandard.HigherRank.YamadaG23
