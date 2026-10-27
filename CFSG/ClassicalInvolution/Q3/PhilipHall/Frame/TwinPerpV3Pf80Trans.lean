module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance (oddQuotMk)

section Glue

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem isUniqueInvolution_map_mulEquiv {X Z : Type} [Group X] [Group Z] (e : X ≃* Z)
    {K : Subgroup X} {z : X} (h : IsUniqueInvolution K z) :
    IsUniqueInvolution (K.map e.toMonoidHom) (e z) where
  mem := ⟨z, h.mem, rfl⟩
  ne_one := fun h1 => h.ne_one (e.map_eq_one_iff.mp h1)
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨k, hk, rfl⟩ hk2
    have hkk : k * k = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact hk2
    rcases h.unique k hk hkk with rfl | rfl
    · left
      exact map_one e
    · right
      rfl

end Glue

section Glue2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem oddQuot_comm_of_transitive (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ tqMembers3 Ω c)
    {tb : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)}
    (hz : IsUniqueInvolution (secImg Ω c K₃) tb)
    (htr : ∀ M ∈ TwinDisc.secFam Ω c, ∀ N ∈ TwinDisc.secFam Ω c,
      ∃ y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c), conjSub y M = N)
    (hcen : ∀ y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c), y * tb = tb * y)
    (g : ↥(Subgroup.centralizer ({c} : Set G))) :
    oddQuotMk c g * TwinExitPf6.secMap Ω c hΩ hc2 tb =
      TwinExitPf6.secMap Ω c hΩ hc2 tb * oddQuotMk c g := by
  have hA := secImg_mem_secFam hK₃
  have hmap := TwinExitPf10.secAut_map_secFam hΩ hc2 g hA
  obtain ⟨y, hy⟩ := htr _ hA _ hmap
  have h1 := isUniqueInvolution_map_mulEquiv (TwinExitPf6.secAut Ω c hΩ hc2 g) hz
  have h2 := hz.conj y
  rw [hy] at h2
  have h3 : TwinExitPf6.secAut Ω c hΩ hc2 g tb = y * tb * y⁻¹ := h1.eq h2
  have h4 : y * tb * y⁻¹ = tb := by rw [hcen y]; group
  rw [h4] at h3
  have h5 := TwinExitPf6.secMap_secAut hΩ hc2 g tb
  rw [h3] at h5
  calc oddQuotMk c g * TwinExitPf6.secMap Ω c hΩ hc2 tb
      = oddQuotMk c g * TwinExitPf6.secMap Ω c hΩ hc2 tb * (oddQuotMk c g)⁻¹ * oddQuotMk c g := by group
    _ = TwinExitPf6.secMap Ω c hΩ hc2 tb * oddQuotMk c g := by rw [← h5]

theorem mem_zStarOf_of_secCentral (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ tqMembers3 Ω c) {t : G}
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hz : IsUniqueInvolution (secImg Ω c K₃)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c))))
    (htr : ∀ M ∈ TwinDisc.secFam Ω c, ∀ N ∈ TwinDisc.secFam Ω c,
      ∃ y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c), conjSub y M = N)
    (hcen : ∀ y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
          (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
          (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) * y) :
    t ∈ zStarOf (Subgroup.centralizer ({c} : Set G)) := by
  refine ⟨⟨t, htC⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))) q
  have h := oddQuot_comm_of_transitive hΩ hc2 hK₃ hz htr hcen g
  exact h

end Glue2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
