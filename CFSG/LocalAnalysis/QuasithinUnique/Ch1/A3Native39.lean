module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.Quasithin.Background.A3Structure39

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.Quasithin.A38

theorem a39_part1_of_outSolvable {G : Type} [Group G] [Finite G] (h37 : A37Statement G)
    (h38 : A38Part3 G)
    (hOut : ∀ K : Subgroup (G ⧸ CFSG.solvableRadical G), CFSG.IsComponent K →
      OutSolvable ↥K) :
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
  refine le_antisymm (le_perfectCore_of_perfect le_top cCompSpan_perfect) ?_
  rw [(cComp_part_five (G := G)).2]
  refine le_perfectCore_of_perfect ?_ (perfectCore_perfect _)
  show perfectCore (⊤ : Subgroup G) ≤
    (CFSG.layer (G ⧸ CFSG.solvableRadical G)).comap (QuotientGroup.mk' _)
  rw [← Subgroup.map_le_iff_le_comap, map_perfectCore,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := A3.solvableRadical_isSolvable
  refine perfectCore_le_layer (A3.solvableRadical_quotient_eq_bot G) ?_ ?_
  · intro K hK
    have hKc : K ∈ cComp (⊤ : Subgroup (G ⧸ CFSG.solvableRadical G)) :=
      mem_cComp_top_of_isComponent hK
    rw [← image_cComp_quotient (CFSG.solvableRadical G) hRs] at hKc
    obtain ⟨L, hL, rfl⟩ := hKc
    have h1 := perfectCore_le_normalizer h37 h38 hL
    have h2 := Subgroup.map_mono (f := QuotientGroup.mk' (CFSG.solvableRadical G)) h1
    rw [map_perfectCore, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    exact h2.trans (map_normalizer_le _ _)
  · intro K hK
    exact hOut K hK

theorem a39_part2_of_common {G : Type} [Group G] [Finite G]
    (hcommon : ∀ L ∈ cComp (⊤ : Subgroup G), A36Common ↥L) :
    CFSG.layer (↥(cCompSpan (⊤ : Subgroup G)) ⧸ CFSG.oddCore ↥(cCompSpan (⊤ : Subgroup G))) =
      ⊤ := by
  set H := cCompSpan (⊤ : Subgroup G) with hH
  let ρ : ↥H →* ↥H ⧸ CFSG.oddCore ↥H := QuotientGroup.mk' (CFSG.oddCore ↥H)
  have hcomp : ∀ L ∈ cComp (⊤ : Subgroup G), CFSG.IsComponent ((L.subgroupOf H).map ρ) := by
    intro L hL
    obtain ⟨hLH, hLn⟩ := cComp_normal_span hL
    have hq : CFSG.IsQuasisimple (↥(L.subgroupOf H) ⧸ CFSG.oddCore ↥(L.subgroupOf H)) := by
      obtain ⟨hFO, hqs, -⟩ := hcommon L hL
      have hqs' : CFSG.IsQuasisimple (↥L ⧸ CFSG.oddCore ↥L) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hFO) hqs
      exact isQuasisimple_quot_oddCore_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm hqs'
    exact ⟨isQuasisimple_map_oddCore (L.subgroupOf H) hq,
      (Subgroup.Normal.map hLn ρ (QuotientGroup.mk'_surjective _)).isSubnormal⟩
  have hgen : (⨆ L ∈ cComp (⊤ : Subgroup G), L.subgroupOf H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_iSup]
    have h1 : ∀ L ∈ cComp (⊤ : Subgroup G), (L.subgroupOf H).map H.subtype = L :=
      fun L hL => Subgroup.map_subgroupOf_eq_of_le (cComp_normal_span hL).1
    have h2 : (⨆ L ∈ cComp (⊤ : Subgroup G), ((L.subgroupOf H).map H.subtype)) = H := by
      calc (⨆ L ∈ cComp (⊤ : Subgroup G), ((L.subgroupOf H).map H.subtype))
          = ⨆ L ∈ cComp (⊤ : Subgroup G), L := by
            refine iSup_congr fun L => iSup_congr fun hL => h1 L hL
        _ = H := (sSup_eq_iSup).symm
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [eq_top_iff]
  calc (⊤ : Subgroup (↥H ⧸ CFSG.oddCore ↥H)) = (⊤ : Subgroup ↥H).map ρ :=
        (Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective _)).symm
    _ = (⨆ L ∈ cComp (⊤ : Subgroup G), L.subgroupOf H).map ρ := by rw [hgen]
    _ ≤ CFSG.layer (↥H ⧸ CFSG.oddCore ↥H) := by
        rw [Subgroup.map_iSup]
        refine iSup_le fun L => ?_
        rw [Subgroup.map_iSup]
        exact iSup_le fun hL => le_sSup (hcomp L hL)

theorem list_of_component_quotient
    {G : Type} [Group G] (hG : SQTKHypCat G)
    {K : Subgroup (G ⧸ CFSG.solvableRadical G)} (hK : CFSG.IsComponent K) :
    A23ListCat (↥K ⧸ Subgroup.center ↥K) := by
  have := hG.finite
  let π : G →* G ⧸ CFSG.solvableRadical G := QuotientGroup.mk' _
  let H : Subgroup G := K.comap π
  let ψ : ↥H →* ↥K := (π.comp H.subtype).codRestrict K (fun x => x.2)
  let φ : ↥H →* ↥K ⧸ Subgroup.center ↥K := (QuotientGroup.mk' _).comp ψ
  have hψ : Function.Surjective ψ := by
    intro k
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical G) k.1
    exact ⟨⟨g, by show π g ∈ K; rw [hg]; exact k.2⟩, Subtype.ext hg⟩
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hψ
  let e : ↥H ⧸ φ.ker ≃* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hsimple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.1.2.1
  have : IsSimpleGroup (↥H ⧸ φ.ker) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥H ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hlist := CFSG.Milestones.cl_lit_sqtk_simple_list_section G hG.isSQTKCat H φ.ker hnonab
  exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv e.symm hlist

theorem a39_part1_of_schreier
    (hS : SchreierFactListCat) {G : Type} [Group G] (hG : SQTKHypCat G)
    (h37 : A37Statement G) (h38 : A38Part3 G) :
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
  have := hG.finite
  exact a39_part1_of_outSolvable h37 h38 fun K hK =>
    hS ↥K hK.1 (list_of_component_quotient hG hK)

theorem a39_part1_of_schreierCat (hS : SchreierFactCat) {G : Type} [Group G] (hG : SQTKHypCat G)
    (h37 : A37Statement G) (h38 : A38Part3 G) :
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
  have := hG.finite
  have hqK : IsKGroupCat (G ⧸ CFSG.solvableRadical G) := hG.kgroup.quotient _
  exact a39_part1_of_outSolvable h37 h38 fun K hK => hS ↥K hK.1 (hqK.subgroup K)

theorem a39_part2_cat {G : Type} [Group G] (hG : SQTKHypCat G) (h36 : A36CoreStatementCat G) :
    CFSG.layer (↥(cCompSpan (⊤ : Subgroup G)) ⧸ CFSG.oddCore ↥(cCompSpan (⊤ : Subgroup G))) =
      ⊤ := by
  have := hG.finite
  exact a39_part2_of_common fun L hL => (h36 L hL).2.1

theorem a39ForSQTKCat_of_facts
    (hS : SchreierFactListCat) (h36 : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : A39ForSQTKCat := fun Q _ hQ =>
  ⟨a39_part1_of_schreier hS hQ (h37 Q hQ) (h38 Q hQ), a39_part2_cat hQ (h36 Q hQ)⟩

theorem a39ForSQTKCat_of_schreierCat (hS : SchreierFactCat) (h36 : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : A39ForSQTKCat := fun Q _ hQ =>
  ⟨a39_part1_of_schreierCat hS hQ (h37 Q hQ) (h38 Q hQ), a39_part2_cat hQ (h36 Q hQ)⟩

end CFSG.QuasithinUnique.Vol2Native
