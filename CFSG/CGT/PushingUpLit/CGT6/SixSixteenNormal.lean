module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourNormal
public import CFSG.CGT.PushingUpLit.CGT6.SixSixteenPR

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel CFSG.CGT.PushingUpLit.Glue
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

@[expose] def AschbacherSixSixteenNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsCharacteristicP 2 G →
    ∀ (Y : Subgroup G) (T : Sylow 2 G), InClassX ↥Y → Y = ⁅jIn (T : Subgroup G), Y⁆ →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) → R.Normal →
        ∀ U₀ : Subgroup G, ⁅oTwoIn Y, Y⁆ ≤ U₀ → U₀ ≤ (T : Subgroup G) →
          Y ≤ Subgroup.normalizer (U₀ : Set G) →
          (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G))).IsSubnormal →
          ∀ S : Subgroup G, IsSylowOf 2 S (Subgroup.normalizer (R : Set G)) →
            IsSylowOf 2 (S ⊓ Subgroup.normalizer (Y : Set G)) (Subgroup.normalizer (Y : Set G)) →
            ⁅omegaOneCenterIn S, Y⁆ ≠ ⊥ →
            ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ Arrow Y X

theorem aschbacherSixSixteenNormal_of_sixFourNormal (h : AschbacherSixFourNormal) :
    AschbacherSixSixteenNormal :=
  fun G _ _ hK hchar Y T hY hYT R hR hRn U₀ hU hU₀T hYU hYs S hS hSY hZ =>
    h G hK hchar Y T hY hYT R hR
      (aschbacherSixSixteenPR_holds G hK hchar Y T hY hYT R hR U₀ hU hU₀T hYU hYs S hS hSY hZ)
      hRn U₀ hU hU₀T hYU hYs

section Rel

variable {G : Type} [Group G] [Finite G]

theorem AschbacherSixSixteenNormal.rel (h : AschbacherSixSixteenNormal) (hK : KProper InCatalog G)
    {K Y T R U₀ S : Subgroup G} (hKc : IsCharacteristicP 2 ↥K) (hYK : Y ≤ K)
    (hY : InClassX ↥Y) (hT : IsSylowOf 2 T K) (hYT : Y = ⁅jIn T, Y⁆)
    (hR : IsSylowOf 2 R (centralizerModCore Y ⊓ K)) (hRn : K ≤ Subgroup.normalizer (R : Set G))
    (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀) (hUT : U₀ ≤ T)
    (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYUs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G) ⊓ K)).IsSubnormal)
    (hS : IsSylowOf 2 S (Subgroup.normalizer (R : Set G) ⊓ K))
    (hSY : IsSylowOf 2 (S ⊓ Subgroup.normalizer (Y : Set G))
      (Subgroup.normalizer (Y : Set G) ⊓ K))
    (hZ : ⁅omegaOneCenterIn S, Y⁆ ≠ ⊥) :
    ∃ X : Subgroup G, Y ≤ X ∧ X ≤ K ∧ (X.subgroupOf K).IsSubnormal ∧ InClassX ↥X := by
  have hTK : T ≤ K := hT.1
  have hRK : R ≤ K := hR.1.trans inf_le_right
  have hSK : S ≤ K := hS.1.trans inf_le_right
  have hUK : U₀ ≤ K := hUT.trans hTK
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf hT
  have hjT : jIn (T' : Subgroup ↥K) = (jIn T).subgroupOf K := by
    rw [hT']
    exact jIn_subgroupOf hTK
  have hY' : InClassX ↥(Y.subgroupOf K) := (inClassX_subgroupOf_iff hYK).mpr hY
  have hcomm : Y.subgroupOf K = ⁅jIn (T' : Subgroup ↥K), Y.subgroupOf K⁆ := by
    rw [hjT, subgroupOf_commutator_eq ((jIn_le T).trans hTK) hYK, ← hYT]
  have hR' : IsSylowOf 2 (R.subgroupOf K) (centralizerModCore (Y.subgroupOf K)) :=
    (isSylowOf_subgroupOf_iff hYK hRK).mpr hR
  have hRn' : (R.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRK).mpr hRn
  have hU' : ⁅oTwoIn (Y.subgroupOf K), Y.subgroupOf K⁆ ≤ U₀.subgroupOf K := by
    intro x hx
    have hx' : (x : G) ∈ ⁅oTwoIn Y, Y⁆ := by
      have := Subgroup.mem_map_of_mem K.subtype hx
      rwa [Subgroup.map_commutator, map_oTwoIn_subgroupOf hYK,
        Subgroup.map_subgroupOf_eq_of_le hYK] at this
    exact hU hx'
  have hUT' : U₀.subgroupOf K ≤ (T' : Subgroup ↥K) := by
    rw [hT']
    exact Subgroup.comap_mono hUT
  obtain ⟨hYU', hYUs'⟩ := (sylowClause_subgroupOf_iff hYK hUK).mpr ⟨hYU, hYUs⟩
  have hS' : IsSylowOf 2 (S.subgroupOf K)
      (Subgroup.normalizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [normalizer_subgroupOf_eq hRK]
    exact (isSylowOf_subgroupOf_iff' hSK inf_le_right).mpr hS
  have hSY' : IsSylowOf 2 (S.subgroupOf K ⊓ Subgroup.normalizer
      ((Y.subgroupOf K : Subgroup ↥K) : Set ↥K)) (Subgroup.normalizer
      ((Y.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [normalizer_subgroupOf_eq hYK]
    have e : S.subgroupOf K ⊓ (Subgroup.normalizer (Y : Set G) ⊓ K).subgroupOf K =
        (S ⊓ Subgroup.normalizer (Y : Set G)).subgroupOf K := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, x.2⟩⟩
    rw [e]
    exact (isSylowOf_subgroupOf_iff' (inf_le_left.trans hSK) inf_le_right).mpr hSY
  have hZ' : ⁅omegaOneCenterIn (S.subgroupOf K), Y.subgroupOf K⁆ ≠ ⊥ := by
    intro hb
    apply hZ
    have := congrArg (Subgroup.map K.subtype) hb
    rwa [Subgroup.map_commutator, map_omegaOneCenterIn_subgroupOf hSK,
      Subgroup.map_subgroupOf_eq_of_le hYK, Subgroup.map_bot] at this
  obtain ⟨X', hYX', hsub, hcl, -⟩ := h ↥K
    (CFSG.ComponentClassification.CatalogueKProper.subgroup hK K) hKc (Y.subgroupOf K) T' hY'
    (by rw [hT'] at hcomm ⊢; exact hcomm) (R.subgroupOf K) hR' hRn' (U₀.subgroupOf K) hU' hUT'
    hYU' hYUs' (S.subgroupOf K) hS' hSY' hZ'
  have hX'sub : (X'.map K.subtype).subgroupOf K = X' :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective X'
  refine ⟨X'.map K.subtype, ?_, Subgroup.map_subtype_le X', ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hYK]
    exact Subgroup.map_mono hYX'
  · rw [hX'sub]
    exact hsub
  · exact InClassX.of_mulEquiv (X'.equivMapOfInjective K.subtype K.subtype_injective) hcl

theorem AschbacherSixSixteenPR.rel (h : AschbacherSixSixteenPR) (hK : KProper InCatalog G)
    {K Y T R U₀ S : Subgroup G} (hKc : IsCharacteristicP 2 ↥K) (hYK : Y ≤ K)
    (hY : InClassX ↥Y) (hT : IsSylowOf 2 T K) (hYT : Y = ⁅jIn T, Y⁆)
    (hR : IsSylowOf 2 R (centralizerModCore Y ⊓ K)) (hRn : K ≤ Subgroup.normalizer (R : Set G))
    (hU : ⁅oTwoIn Y, Y⁆ ≤ U₀) (hUT : U₀ ≤ T)
    (hYU : Y ≤ Subgroup.normalizer (U₀ : Set G))
    (hYUs : (Y.subgroupOf (Subgroup.normalizer (U₀ : Set G) ⊓ K)).IsSubnormal)
    (hS : IsSylowOf 2 S (Subgroup.normalizer (R : Set G) ⊓ K))
    (hSY : IsSylowOf 2 (S ⊓ Subgroup.normalizer (Y : Set G))
      (Subgroup.normalizer (Y : Set G) ⊓ K))
    (hZ : ⁅omegaOneCenterIn S, Y⁆ ≠ ⊥) :
    oTwoIn K = R := by
  have hTK : T ≤ K := hT.1
  have hRK : R ≤ K := hR.1.trans inf_le_right
  have hSK : S ≤ K := hS.1.trans inf_le_right
  have hUK : U₀ ≤ K := hUT.trans hTK
  obtain ⟨T', hT'⟩ := sylow_of_isSylowOf hT
  have hjT : jIn (T' : Subgroup ↥K) = (jIn T).subgroupOf K := by
    rw [hT']
    exact jIn_subgroupOf hTK
  have hY' : InClassX ↥(Y.subgroupOf K) := (inClassX_subgroupOf_iff hYK).mpr hY
  have hcomm : Y.subgroupOf K = ⁅jIn (T' : Subgroup ↥K), Y.subgroupOf K⁆ := by
    rw [hjT, subgroupOf_commutator_eq ((jIn_le T).trans hTK) hYK, ← hYT]
  have hR' : IsSylowOf 2 (R.subgroupOf K) (centralizerModCore (Y.subgroupOf K)) :=
    (isSylowOf_subgroupOf_iff hYK hRK).mpr hR
  have hU' : ⁅oTwoIn (Y.subgroupOf K), Y.subgroupOf K⁆ ≤ U₀.subgroupOf K := by
    intro x hx
    have hx' : (x : G) ∈ ⁅oTwoIn Y, Y⁆ := by
      have := Subgroup.mem_map_of_mem K.subtype hx
      rwa [Subgroup.map_commutator, map_oTwoIn_subgroupOf hYK,
        Subgroup.map_subgroupOf_eq_of_le hYK] at this
    exact hU hx'
  have hUT' : U₀.subgroupOf K ≤ (T' : Subgroup ↥K) := by
    rw [hT']
    exact Subgroup.comap_mono hUT
  obtain ⟨hYU', hYUs'⟩ := (sylowClause_subgroupOf_iff hYK hUK).mpr ⟨hYU, hYUs⟩
  have hS' : IsSylowOf 2 (S.subgroupOf K)
      (Subgroup.normalizer ((R.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [normalizer_subgroupOf_eq hRK]
    exact (isSylowOf_subgroupOf_iff' hSK inf_le_right).mpr hS
  have hSY' : IsSylowOf 2 (S.subgroupOf K ⊓ Subgroup.normalizer
      ((Y.subgroupOf K : Subgroup ↥K) : Set ↥K)) (Subgroup.normalizer
      ((Y.subgroupOf K : Subgroup ↥K) : Set ↥K)) := by
    rw [normalizer_subgroupOf_eq hYK]
    have e : S.subgroupOf K ⊓ (Subgroup.normalizer (Y : Set G) ⊓ K).subgroupOf K =
        (S ⊓ Subgroup.normalizer (Y : Set G)).subgroupOf K := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, x.2⟩⟩
    rw [e]
    exact (isSylowOf_subgroupOf_iff' (inf_le_left.trans hSK) inf_le_right).mpr hSY
  have hZ' : ⁅omegaOneCenterIn (S.subgroupOf K), Y.subgroupOf K⁆ ≠ ⊥ := by
    intro hb
    apply hZ
    have := congrArg (Subgroup.map K.subtype) hb
    rwa [Subgroup.map_commutator, map_omegaOneCenterIn_subgroupOf hSK,
      Subgroup.map_subgroupOf_eq_of_le hYK, Subgroup.map_bot] at this
  have hPR := h ↥K (CFSG.ComponentClassification.CatalogueKProper.subgroup hK K) hKc
    (Y.subgroupOf K) T' hY' (by rw [hT'] at hcomm ⊢; exact hcomm) (R.subgroupOf K) hR'
    (U₀.subgroupOf K) hU' hUT' hYU' hYUs' (S.subgroupOf K) hS' hSY' hZ'
  rw [normalizer_subgroupOf_eq hRK, inf_eq_right.mpr hRn, Subgroup.subgroupOf_self] at hPR
  have h1 := congrArg (Subgroup.map K.subtype) hPR
  rw [Subgroup.map_subgroupOf_eq_of_le hRK] at h1
  have h2 := map_oTwoIn_subgroupOf (A := K) (K := K) le_rfl
  rw [Subgroup.subgroupOf_self] at h2
  rw [← h2]
  exact h1

end Rel

end CFSG.CGT.PushingUpLit.CGT6
