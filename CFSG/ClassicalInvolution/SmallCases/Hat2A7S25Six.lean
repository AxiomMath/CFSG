module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Z
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8LayerRes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Six


theorem conjSub_eq_of_centralizes_sylow_gen {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : AschTight.HypOmegaGen Ω) {J R : Subgroup G} (hJ : J ∈ Ω) (hR : IsSylow2In R J) {x : G}
    (hRx : ∀ r ∈ R, r * x = x * r) : conjSub x J = J := by
  have hJ' : conjSub x J ∈ Ω := hΩ.conjInvariant x J hJ
  have h8 : 8 ≤ Nat.card R :=
    AschTight.Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ hR)
  have hRle : R ≤ conjSub x J := by
    intro r hr
    have h1 : x * r * x⁻¹ = r := by
      calc x * r * x⁻¹ = (r * x) * x⁻¹ := by rw [hRx r hr]
        _ = r := by group
    rw [← h1]
    exact conj_mem_conjSub (hR.1 hr)
  exact (AschTight.Sec6Gen.eq_of_le_of_le hΩ hJ hJ' hR.2.1 (by omega) hR.1 hRle).symm

theorem a7C25_6_proved : A7C25_6 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ h a ha2 ha1 haSC
  have hΩ : AschTight.HypOmegaGen Ω := h.hΩ
  have hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u := h.std.1.stand.classical
  have haR : ∀ r ∈ R, r * a = a * r := fun r hr =>
    (Subgroup.mem_centralizer_iff.mp haSC.2) r ((le_sup_left : R ≤ R ⊔ R') hr)
  have hRa : R ≤ Asc77.T8.cenZ a := fun r hr =>
    Asc77.T8.mem_cenZ_iff.mpr (haR r hr)
  have hnorm : conjSub a K = K := conjSub_eq_of_centralizes_sylow_gen hΩ h.hK h.hRsyl haR
  have hX : Asc77.T8.XMem Ω a K :=
    ⟨h.hK, mem_normalizer_iff_conjSub_eq.mpr hnorm, R, h.hRsyl, haR⟩
  have hzK : Hat2A7.IsClassical2A7 ⊤ K z :=
    Hat2A7S8.Asc77.T8.isClassical2A7_of_isUniqueInvolution hcls h.hK h.std.1.hz
  have hL := Hat2A7S8.Asc77.T8.XMem.isClassical2A7 hΩ ha2 hX hzK
  rw [Asc77.T8.cenZ_eq_centralizer] at hL
  have hRL : R ≤ Asc77.T8.layerRes a K :=
    (Hat2A7S8.Asc77.T8.XMem.isSylow2In_layerRes_of_le hΩ hcls ha2 hX h.hRsyl hRa).1
  exact mem_zStarOf_of_classical_layer h ha1 hRL hL

end Six

end CFSG.ClassicalInvolution.Hat2A7S
