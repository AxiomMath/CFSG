module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Delta
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65MultiMain
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8 smallRankR SmallRankSylowTwo)

theorem unique_component_of_uniquePComponent {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hcore : primeComplementCore (G := Y) p = ⊥)
    (h : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧
      ∀ K : Subgroup Y, IsComponentOf K ⊤ → p ∣ Nat.card K → K = L) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L := by
  obtain ⟨L, hL, -, hu⟩ := h
  exact ⟨L, hL, fun K hK => hu K hK
    (CFSG.LocalAnalysis.RankFourTheoremC.Lemma213.dvd_card_comp hcore
      ⟨K, (CFSG.isComponent_iff_open K).2 hK⟩)⟩

theorem rankThreePrimeCore_eq_map {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    (X : Subgroup A) :
    rankThreePrimeCore p X = (primeComplementCore (G := ↥X) p).map X.subtype :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map hp X

theorem centralizer_pCore_le {A : Type} [Group A] [Finite A] {X : Subgroup A}
    (hC2 : X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X) :
    centralizer ((CFSG.pCore 2 ↥X : Subgroup ↥X) : Set ↥X) ≤ CFSG.pCore 2 ↥X := by
  intro g hg
  have hmem : (g : A) ∈ X ⊓ centralizer (pCoreOf 2 X : Set A) := by
    refine ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg q hq)
  obtain ⟨q, hq, hqg⟩ := hC2 hmem
  have : q = g := Subtype.ext hqg
  exact this ▸ hq

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup I291P65
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankR)

theorem kFactP65Single_of_kdata (hCase2 : SCCaseTwo) (hLin : KD29LinUni)
    (h309 : KD309) : KFactP65Single := by
  intro A _ _ p P X x z T hpl hC2 hp5 hT hR hU W hWX hWcop hBW
  subst hp5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPX : (P : Subgroup A) ≤ X := hpl.sylow_le
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup A) := hpl.plane.isIsolatedPlane.1
  have hxX : x ∈ X := hPX (hBP (Subgroup.mem_sup_left (mem_zpowers x)))
  have hzX : z ∈ X := hPX (hBP (Subgroup.mem_sup_right (mem_zpowers z)))
  have hpl63 := plane63_of_plane65 hpl hxX hzX
  obtain ⟨L, hL, hLu⟩ :=
    unique_component_of_uniquePComponent (primeComplementCore_quotient_eq_bot 5) hU
  have hW'cop : Nat.Coprime 5 (Nat.card (W.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv]
  have hBmap : (zpowers (⟨x, hxX⟩ : ↥X) ⊔ zpowers (⟨z, hzX⟩ : ↥X)).map X.subtype =
      zpowers x ⊔ zpowers z := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hBW' : zpowers (⟨x, hxX⟩ : ↥X) ⊔ zpowers (⟨z, hzX⟩ : ↥X) ≤
      normalizer ((W.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro b hb
    have hb' : (b : A) ∈ zpowers x ⊔ zpowers z := hBmap ▸ mem_map_of_mem X.subtype hb
    have hn := Subgroup.mem_normalizer_iff.mp (hBW hb')
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    exact hn (h : A)
  by_cases hlu : IsLinearOrUnitaryAt 5 (↥L ⧸ center ↥L)
  ·
    exfalso
    have hTX : T ≤ X := hT.le_core.trans (by
      rw [rankThreePrimeCore_eq_map (by norm_num : Nat.Prime 5)]
      exact Subgroup.map_subtype_le _)
    have hsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (rankThreePrimeCore 5 X) :=
      CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨hT.le_core, hT.isPGroup, hT.index_odd⟩
    have hsyl' : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf X)
        (primeComplementCore (G := ↥X) 5) := by
      rw [rankThreePrimeCore_eq_map (by norm_num : Nat.Prime 5), ← Subgroup.map_subgroupOf_eq_of_le
        hTX] at hsyl
      exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff X).1 hsyl
    have hRmap : (Rsub (T.subgroupOf X) (⟨z, hzX⟩ : ↥X) (⟨x, hxX⟩ : ↥X)).map X.subtype =
        smallRankR x z T := by
      unfold Rsub smallRankR
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      have hS : ((T.subgroupOf X) ⊓ centralizer ({(⟨x, hxX⟩ : ↥X)} : Set ↥X)).map X.subtype =
          CFSG.LocalAnalysis.RankThreeTheoremC.smallRankS x T := by
        ext y
        constructor
        · rintro ⟨y', ⟨hyT, hyC⟩, rfl⟩
          exact ⟨hyT, mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hyC))⟩
        · rintro ⟨hyT, hyC⟩
          exact ⟨⟨y, hTX hyT⟩, ⟨hyT, mem_centralizer_singleton_iff.mpr
            (Subtype.ext (mem_centralizer_singleton_iff.mp hyC))⟩, rfl⟩
      rw [hS]
      rfl
    obtain ⟨hcard, r, hrR, hr⟩ := q8d8_facts hR
    have hR32 : Nat.card (Rsub (T.subgroupOf X) (⟨z, hzX⟩ : ↥X) (⟨x, hxX⟩ : ↥X)) ≤ 32 := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, hRmap, hcard]
    have hsq : ∃ r' ∈ Rsub (T.subgroupOf X) (⟨z, hzX⟩ : ↥X) (⟨x, hxX⟩ : ↥X), r' ^ 2 ≠ 1 := by
      rw [← hRmap] at hrR
      obtain ⟨r', hr', rfl⟩ := hrR
      refine ⟨r', hr', fun h => hr ?_⟩
      have := congrArg X.subtype h
      simpa using this
    exact delta_false h309 hpl63 (centralizer_pCore_le hC2) hsyl' hR32 hsq hL hLu
      (hLin ↥X (P.subtype hPX) ⟨x, hxX⟩ ⟨z, hzX⟩ hpl63 L hL hLu hlu)
  ·
    have hW := hCase2 5 ↥X (P.subtype hPX) ⟨x, hxX⟩ ⟨z, hzX⟩ hpl63 L hL hLu hlu
      (W.subgroupOf X) hW'cop hBW'
    intro w hw
    rw [rankThreePrimeCore_eq_map (by norm_num : Nat.Prime 5)]
    exact ⟨⟨w, hWX hw⟩, hW hw, rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
