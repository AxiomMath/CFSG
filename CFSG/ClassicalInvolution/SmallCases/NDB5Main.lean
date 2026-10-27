module

public import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
public import CFSG.ClassicalInvolution.SmallCases.NDBStmt
public import CFSG.ClassicalInvolution.SmallCases.NDB3Vertex
public import CFSG.ClassicalInvolution.SmallCases.NDB2Main
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.AschTight.S1911C8c
public import CFSG.ClassicalInvolution.AschTight.S1911Case2a
public import CFSG.ClassicalInvolution.AschTight.S1911E2c
public import CFSG.ClassicalInvolution.AschTight.S1911FusA
public import CFSG.ClassicalInvolution.AschTight.Sec19Targets3
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight3
public import CFSG.ClassicalInvolution.SmallCases.NDB5Layer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Outer
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def IsVertexLayer {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ : G) (L : Subgroup G) : Prop :=
  ∃ (hN : NormalizesLayer (exactFamily Ω z₁) z₁)
    (D : LocalLieSystemAt p f (exactFamily Ω z₁) z₁) (i₀ i₁ : Fin D.card)
    (R₂ R₃ : Subgroup (compModel D i₁).K) (r₂ r₃ : (compModel D i₁).K)
    (ι : SL(2, GaloisField p (D.exp i₁)) →* (compModel D i₁).K),
    VertexLayer Ω K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ hN D i₀ i₁ R₂ R₃ r₂ r₃ ι L

@[expose] def SAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Setting p f K z → PSpEverywhere p f (𝒞 K) →
      ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
        PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
        ∀ L₁ L₂ : Subgroup G, IsVertexLayer p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ L₁ →
          IsVertexLayer p f (𝒞 K) K₂ K₁ K₃ z₂ z₁ z₃ t₂ t₁ t₃ L₂ →
          ∀ (hN : NormalizesLayer (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
            (D : LocalLieSystemAt p f (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
            (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
            S.SComponent (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) z₁ z₂ L₁ L₂ hN D j₀
              R₁ R₂ →
            CFSG.IsComponent (secComponentHom hN D j₀).range →
            MovedByAll (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃)
              (secComponentHom hN D j₀).range →
            alphaOf (inducedImage (secComponentHom hN D j₀).range
              (modOdd (t₁ * t₂ * t₃) (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃))) = ⊥

@[expose] def SAlphaOn {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G),
    PSpAxis p f Ω K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ →
    ∀ L₁ L₂ : Subgroup G, IsVertexLayer p f Ω K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ L₁ →
      IsVertexLayer p f Ω K₂ K₁ K₃ z₂ z₁ z₃ t₂ t₁ t₃ L₂ →
      ∀ (hN : NormalizesLayer (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
        (D : LocalLieSystemAt p f (S.sFamily (t₁ * t₂ * t₃) L₁ L₂) (t₁ * t₂ * t₃))
        (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
        S.SComponent (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) z₁ z₂ L₁ L₂ hN D j₀
          R₁ R₂ →
        CFSG.IsComponent (secComponentHom hN D j₀).range →
        MovedByAll (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃)
          (secComponentHom hN D j₀).range →
        alphaOf (inducedImage (secComponentHom hN D j₀).range
          (modOdd (t₁ * t₂ * t₃) (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃))) = ⊥

@[expose] def SAlphaCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    SettingCore p f K z → PSpEverywhere p f (𝒞 K) → SAlphaOn p f (𝒞 K)

theorem SAlpha.of_core (h : SAlphaCore p f) : SAlpha p f :=
  fun G _ _ _ K z hS hpsp => h G K z hS.toCore hpsp

namespace S5

variable {G : Type} [Group G]

theorem exists_mul_of_not_mem {z₁ z₂ t₁ t₂ t₃ : G}
    (hA : CFSG.Open.IsElemAbelian 2 (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃)) {c : G}
    (hc : c ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃)
    (hcZ : c ∉ Subgroup.closure ({z₁, z₂} : Set G)) :
    ∃ d ∈ Subgroup.closure ({z₁, z₂} : Set G), c = d * (t₁ * t₂ * t₃) := by
  have hset : ({z₁, z₂, t₁ * t₂ * t₃} : Set G) = ({z₁, z₂} : Set G) ∪ {t₁ * t₂ * t₃} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  have hsup : TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ = Subgroup.closure ({z₁, z₂} : Set G) ⊔
      Subgroup.closure ({t₁ * t₂ * t₃} : Set G) := by
    show Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G) = _
    rw [hset, Subgroup.closure_union]
  have hle₁ : Subgroup.closure ({z₁, z₂} : Set G) ≤ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := by
    rw [hsup]
    exact le_sup_left
  have hle₂ : Subgroup.closure ({t₁ * t₂ * t₃} : Set G) ≤ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := by
    rw [hsup]
    exact le_sup_right
  rw [hsup] at hc
  obtain ⟨a, ha, b, hb, rfl⟩ := ModelFacts.Orth15.InnerL4.mem_sup_of_comm
    (fun a ha b hb => comm_of_mem_elemAbelian hA (hle₁ ha) (hle₂ hb)) hc
  have hs2 : t₁ * t₂ * t₃ * (t₁ * t₂ * t₃) = 1 := by
    rw [← pow_two]
    exact hA.2 _ (hle₂ (Subgroup.subset_closure rfl))
  have hb2 : b ∈ Subgroup.closure ({t₁ * t₂ * t₃, t₁ * t₂ * t₃} : Set G) := by
    rwa [Set.pair_eq_singleton]
  rcases TypeCSetup.mem_closure_pair hs2 hs2 rfl hb2 with h | h | h | h
  · exact absurd (show a * b ∈ _ by rw [h, mul_one]; exact ha) hcZ
  · exact ⟨a, ha, by rw [h]⟩
  · exact ⟨a, ha, by rw [h]⟩
  · exact absurd (show a * b ∈ _ by rw [h, hs2, mul_one]; exact ha) hcZ

theorem mem_normalizer_axis [Finite G] {z₁ z₂ t₁ t₂ t₃ w : G}
    (h₁ : w * z₁ * w⁻¹ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃)
    (h₂ : w * z₂ * w⁻¹ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃)
    (hs : w * (t₁ * t₂ * t₃) * w⁻¹ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) :
    w ∈ Subgroup.normalizer ((TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ : Subgroup G) : Set G) := by
  have hle : (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃).map (MulAut.conj w).toMonoidHom ≤
      TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := by
    show (Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G)).map (MulAut.conj w).toMonoidHom ≤ _
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact hs
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj w).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end S5

theorem hyp51At_sOn {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (hS : SettingCore p f K z) (hpsp : PSpEverywhere p f (𝒞 K))
    (hα : SAlphaOn p f (𝒞 K)) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G}
    (hA : PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂) :
    Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) := by
  have hΩ : HypOmegaMod p f (𝒞 K) :=
    Asc77.hypOmegaModAll_of_fusionCore (Asc77.AscFusion.fusionCoreStmt p f) G hS.nonabelian
      hS.odd hS.five K z hS.member hS.below
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hA.cls₃
  have hct : Commute t₁ t₂ := hA.ct₁₂
  have hcomm12 : z₁ * z₂ = z₂ * z₁ := by
    rw [← hA.sq₁, ← hA.sq₂]
    exact ((hct.mul_left hct).mul_right (hct.mul_left hct)).eq
  have hz₁A : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂A : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsA : t₁ * t₂ * t₃ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hsZ := Vertex.s_not_mem_closure (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) hz₁c.sq hz₂c.sq
    hcomm12 hA.card
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h => hsZ (h ▸ Subgroup.one_mem _)
  have hz₁s : z₁ ≠ t₁ * t₂ * t₃ := fun h =>
    hsZ (h ▸ Subgroup.subset_closure (Set.mem_insert _ _))
  have hz₂s : z₂ ≠ t₁ * t₂ * t₃ := fun h =>
    hsZ (h ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hz₁₂ : z₁ ≠ z₂ := fun h => hz₃c.ne_one (by rw [← hA.prod, h, hz₂c.sq])
  have hs2 : t₁ * t₂ * t₃ * (t₁ * t₂ * t₃) = 1 := by
    rw [← pow_two]
    exact hA.elem.2 _ hsA
  have hst : t₂ * t₁ * t₃ = t₁ * t₂ * t₃ := by rw [hA.ct₁₂]
  obtain ⟨D₁, i₀, i₁, Ra, Rb, ra, rb, ι₁, L₁, hV₁⟩ := exists_vertexLayer hΩ hS.odd hS.five
    hA.mem₁ hA.cls₁ (hpsp K₁ hA.mem₁ z₁ hA.cls₁) ⟨hA.mem₂, hA.tq₂₁⟩ hA.cls₂
    ⟨hA.mem₃, hA.tq₃₁⟩ hA.cls₃ hA.prod hA.ht₁ hA.ht₂ hA.ht₃ hA.sq₁ hA.sq₂ hA.sq₃ hA.ct₁₂
    hA.ct₁₃ hs2
  obtain ⟨D₂, i₀', i₁', Rc, Rd, rc, rd, ι₂, L₂, hV₂⟩ := exists_vertexLayer hΩ hS.odd hS.five
    hA.mem₂ hA.cls₂ (hpsp K₂ hA.mem₂ z₂ hA.cls₂) ⟨hA.mem₁, hA.tq₁₂⟩ hA.cls₁
    ⟨hA.mem₃, hA.tq₃₂⟩ hA.cls₃ (hcomm12.symm.trans hA.prod) hA.ht₂ hA.ht₁ hA.ht₃ hA.sq₂
    hA.sq₁ hA.sq₃ hA.ct₁₂.symm hA.ct₂₃ (by rw [hst]; exact hs2)
  have hsec₂ : IsSectionMember p f (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L₂ z₂ :=
    hst ▸ hV₂.sec
  have hs := S.secData_sFamily hV₁.sec hsec₂
  obtain ⟨D⟩ := hs.nonempty_lieSystem hS.below (Vertex.not_subset_center hS.nonabelian hs1)
  have key : ∀ L : Subgroup (OddQuot (t₁ * t₂ * t₃)), CFSG.IsComponent L →
      MovedByAll (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) L →
      ∃ (j₀ : Fin D.card) (R₁ R₂ : Subgroup (compModel D j₀).K),
        S.SComponent (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (t₁ * t₂ * t₃) z₁ z₂ L₁ L₂ hs.normalizes D
          j₀ R₁ R₂ := fun L hL hmov =>
    S.exists_sComponent hS.odd hS.five hA.elem hsA hz₁A hz₂A hs1 hz₁c.ne_one hz₂c.ne_one hz₁s
      hz₂s hz₁₂ hV₁.sec hsec₂ D hL hmov
  refine ⟨fun L L' hL hL' hm hm' => ?_, fun L hL hm => ?_⟩
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    rw [hC.moved L hL hm, hC.moved L' hL' hm']
  · obtain ⟨j₀, R₁, R₂, hC⟩ := key L hL hm
    have hLe := hC.moved L hL hm
    rw [hLe] at hL hm ⊢
    exact hα K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA L₁ L₂
      ⟨_, D₁, i₀, i₁, Ra, Rb, ra, rb, ι₁, hV₁⟩ ⟨_, D₂, i₀', i₁', Rc, Rd, rc, rd, ι₂, hV₂⟩
      hs.normalizes D j₀ R₁ R₂ hC hL hm

theorem axisHyp51S_on {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (hS : SettingCore p f K z) (hpsp : PSpEverywhere p f (𝒞 K))
    (hα : SAlphaOn p f (𝒞 K)) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ : G}
    (hA : PSpAxis p f (𝒞 K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂) {c : G}
    (hc : c ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (hcZ : c ∉ Subgroup.closure ({z₁, z₂} : Set G)) :
    Hyp51At (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) c := by
  have h0 := hyp51At_sOn p f hS hpsp hα hA
  obtain ⟨d, hd, rfl⟩ := S5.exists_mul_of_not_mem hA.elem hc hcZ
  have hz₁c := isCentralInvolution_of_isClassicalMember hA.cls₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hA.cls₂
  have hct : Commute t₁ t₂ := hA.ct₁₂
  have hcomm12 : z₁ * z₂ = z₂ * z₁ := by
    rw [← hA.sq₁, ← hA.sq₂]
    exact ((hct.mul_left hct).mul_right (hct.mul_left hct)).eq
  have hz₁A : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂A : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsA : t₁ * t₂ * t₃ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hz₁t₁ : t₁ * z₁ = z₁ * t₁ := by rw [← hA.sq₁, mul_assoc]
  have hz₂t₃ : z₂ * t₃ = t₃ * z₂ := by rw [← hA.sq₂]; exact Axis.comm_sq hA.ct₂₃
  have hz₂s : z₂ * (t₁ * t₂ * t₃) = t₁ * t₂ * t₃ * z₂ :=
    comm_of_mem_elemAbelian hA.elem hz₂A hsA
  have hw₁s : w₁ * (t₁ * t₂ * t₃) * w₁⁻¹ = z₁ * (t₁ * t₂ * t₃) := by
    have h1 : w₁ * (t₁ * t₂ * t₃) = z₁ * (t₁ * t₂ * t₃) * w₁ := by
      calc w₁ * (t₁ * t₂ * t₃) = w₁ * t₁ * t₂ * t₃ := by group
        _ = t₁ * z₁ * (w₁ * t₂) * t₃ := by rw [hA.inv₁]; group
        _ = t₁ * z₁ * t₂ * (w₁ * t₃) := by rw [hA.cw₁₂]; group
        _ = t₁ * z₁ * t₂ * t₃ * w₁ := by rw [hA.cw₁₃]; group
        _ = z₁ * (t₁ * t₂ * t₃) * w₁ := by rw [hz₁t₁]; group
    rw [h1, mul_inv_cancel_right]
  have hw₂s : w₂ * (t₁ * t₂ * t₃) * w₂⁻¹ = z₂ * (t₁ * t₂ * t₃) := by
    have h1 : w₂ * (t₁ * t₂ * t₃) = z₂ * (t₁ * t₂ * t₃) * w₂ := by
      calc w₂ * (t₁ * t₂ * t₃) = w₂ * t₁ * t₂ * t₃ := by group
        _ = t₁ * (w₂ * t₂) * t₃ := by rw [hA.cw₂₁]; group
        _ = t₁ * t₂ * z₂ * (w₂ * t₃) := by rw [hA.inv₂]; group
        _ = t₁ * t₂ * (z₂ * t₃) * w₂ := by rw [hA.cw₂₃]; group
        _ = t₁ * t₂ * t₃ * z₂ * w₂ := by rw [hz₂t₃]; group
        _ = z₂ * (t₁ * t₂ * t₃) * w₂ := by rw [hz₂s]
    rw [h1, mul_inv_cancel_right]
  have hw₁z₁ : w₁ * z₁ * w₁⁻¹ = z₁ := by
    rw [← hz₁c.central w₁ hA.hw₁, mul_inv_cancel_right]
  have hw₂z₂ : w₂ * z₂ * w₂⁻¹ = z₂ := by
    rw [← hz₂c.central w₂ hA.hw₂, mul_inv_cancel_right]
  have hw₁z₂ : w₁ * z₂ * w₁⁻¹ = z₂ := by
    rw [← hA.sq₂, ← Axis.comm_sq hA.cw₁₂.symm, mul_inv_cancel_right]
  have hw₂z₁ : w₂ * z₁ * w₂⁻¹ = z₁ := by
    rw [← hA.sq₁, ← Axis.comm_sq hA.cw₂₁.symm, mul_inv_cancel_right]
  have hn₁ := S5.mem_normalizer_axis (w := w₁) (by rw [hw₁z₁]; exact hz₁A)
    (by rw [hw₁z₂]; exact hz₂A) (by rw [hw₁s]; exact Subgroup.mul_mem _ hz₁A hsA)
  have hn₂ := S5.mem_normalizer_axis (w := w₂) (by rw [hw₂z₁]; exact hz₁A)
    (by rw [hw₂z₂]; exact hz₂A) (by rw [hw₂s]; exact Subgroup.mul_mem _ hz₂A hsA)
  rcases TypeCSetup.mem_closure_pair hz₁c.sq hz₂c.sq hcomm12 hd with rfl | rfl | rfl | rfl
  · rw [one_mul]
    exact h0
  · rw [← hw₁s]
    exact hyp51At_of_normalizes hn₁ h0
  · rw [← hw₂s]
    exact hyp51At_of_normalizes hn₂ h0
  · have e : z₁ * z₂ * (t₁ * t₂ * t₃) =
        w₁ * (w₂ * (t₁ * t₂ * t₃) * w₂⁻¹) * w₁⁻¹ := by
      rw [hw₂s, show w₁ * (z₂ * (t₁ * t₂ * t₃)) * w₁⁻¹ =
        w₁ * z₂ * w₁⁻¹ * (w₁ * (t₁ * t₂ * t₃) * w₁⁻¹) by group, hw₁z₂, hw₁s, hcomm12]
      group
    rw [e]
    exact hyp51At_of_normalizes hn₁ (hyp51At_of_normalizes hn₂ h0)

theorem axisHyp51S_of_sAlpha (hα : SAlpha p f) : AxisHyp51S p f := by
  intro G _ _ _ K z hS hpsp K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hc hcZ
  exact axisHyp51S_on p f hS.toCore hpsp (hα G K z hS hpsp) hA hc hcZ

theorem axisHyp51S_of_sAlphaCore (hα : SAlphaCore p f) : AxisHyp51SCore p f := by
  intro G _ _ _ K z hS hpsp K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w₁ w₂ hA c hc hcZ
  exact axisHyp51S_on p f hS hpsp (hα G K z hS hpsp) hA hc hcZ

end CFSG.ClassicalInvolution.NDB
