module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native39
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.Quasithin

theorem a39ForSQTKCat_proved
    : A39ForSQTKCat := by
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.1
  have : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_injective (fun α : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4) =>
      (α : CFSG.Blueprint.NativeSporadic.Carrier .J4 → CFSG.Blueprint.NativeSporadic.Carrier .J4))
      DFunLike.coe_injective
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hJ4 : Ch1.J4OutOdd := Setup.X1.j4OuterOdd
  exact a39ForSQTKCat_of_facts
    (schreierFactListCat_of_J4
      (CFSG.ComponentClassification.SporadicSchreierDispatch.sporadicSchreierCase_of_outer
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hJ4)))
    a36CoreForSQTKCat_proved a37ForSQTKCat_proved
    (a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact a134SQTKFactCat a36CoreForSQTKCat_proved
      a37ForSQTKCat_proved)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjClosure_eq_of_le_normalizer {L S : Subgroup G}
    (h : S ≤ Subgroup.normalizer (L : Set G)) : conjClosure L S = L := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) fun l hl => ?_
  · rintro _ ⟨s, hs, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (h hs) l).mp hl
  · exact Subgroup.subset_closure ⟨1, S.one_mem, l, hl, by group⟩

theorem isLocal_of_mem_cComp {H S L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥)
    (hS : IsSylowTwoOf S H) (hL : L ∈ cComp H) : quasithinIsLocal S L := by
  have hLS : L ⊔ S ≤ H := sup_le (le_of_mem_cComp hL) hS.1
  refine ⟨hS.2.1, cComp_subset_lFamily hS.1 hL, fun h2 => hS.2.2 ?_, fun hbot => hH ?_⟩
  · have hmul : (S.subgroupOf (L ⊔ S)).index * ((L ⊔ S).subgroupOf H).index =
        (S.subgroupOf H).index := Subgroup.relIndex_mul_relIndex S (L ⊔ S) H le_sup_right hLS
    rw [← hmul]
    exact Dvd.dvd.mul_right h2 _
  · have hO : pCoreOf 2 H ≤ pCoreOf 2 (L ⊔ S) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS).trans le_sup_right)
        (hLS.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    exact eq_bot_iff.2 (hbot ▸ hO)

theorem existsUnique_cComp_ge_of_isLocal
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : quasithinIsLocal S B) : ∃! L, L ∈ cComp H ∧ B ≤ L :=
  lemma_1_2_4_existsUnique (qtkeCore_of_cat hnonab hQ).1 a37ForSQTKCat_proved
    a39ForSQTKCat_proved hH hS hBH hB.2.1

theorem normal_containing_cComp_of_le_normalizer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : quasithinIsLocal S B) (hSB : S ≤ Subgroup.normalizer (B : Set G)) :
    (∃ L ∈ cComp H, B ≤ L ∧ (L.subgroupOf H).Normal ∧ ∀ L' ∈ cComp H, B ≤ L' → L' = L) ∧
      (quasithinIsMaximalLocal S B → B ∈ cComp H ∧ (B.subgroupOf H).Normal) := by
  have hK := (qtkeCore_of_cat hnonab hQ).1
  have h38 := a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact a134SQTKFactCat
    a36CoreForSQTKCat_proved a37ForSQTKCat_proved
  obtain ⟨L, ⟨hL, hBL⟩, huniq⟩ := existsUnique_cComp_ge_of_isLocal hnonab hQ hH hS hBH hB
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := by
    intro s hs
    have hBs : B.map (MulAut.conj s).toMonoidHom = B := A38.map_conj_eq_iff.mpr (hSB hs)
    refine A38.map_conj_eq_iff.mp (huniq _ ⟨map_conj_mem_cComp hL (hS.1 hs), ?_⟩)
    rw [← hBs]
    exact Subgroup.map_mono hBL
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    have hn := normal_conjClosure_of_pCoreOf_ne_bot hK a37ForSQTKCat_proved h38 hH hS hL
    rwa [conjClosure_eq_of_le_normalizer hSL] at hn
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL)).mpr hHL
  refine ⟨⟨L, hL, hBL, hLn, fun L' hL' hBL' => huniq L' ⟨hL', hBL'⟩⟩, fun hmax => ?_⟩
  obtain rfl : L = B := hmax.2 L (isLocal_of_mem_cComp hH hS hL) hBL
  exact ⟨hL, hLn⟩

end CFSG.QuasithinUnique.Vol2Native
