module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeStar
import CFSG.GroupTheory.ConjugatePairSubnormality
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Layer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott

variable {G : Type} [Group G] [Finite G]

@[expose] def NineSixMoreoverGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G),
    NineSettingGen G M 3 Q H E 2 → H ∈ H2Fam M Q →
      3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M → ¬ pLayerIn 3 H ≤ M →
      ∀ L : Subgroup G, IsKComp M H L → (IsL34Type (threeStar L) ∨ IsA11Star L) →
        kSub 3 M H = L ∨
          ∃ I : Subgroup G, I ≠ L ∧ IsKComp M H I ∧ kSub 3 M H = L ⊔ I ∧
            (∀ J : Subgroup G, IsKComp M H J → J = L ∨ J = I) ∧
            IsSL34Star L ∧ (IsSL34Star I ∨ Is3A6Star I)

theorem isKComp_of_isPComponentIn {M H J : Subgroup G} (hJ : IsPComponentIn 3 J H)
    (hJM : ¬ J ≤ M) (hL : ¬ pLayerIn 3 H ≤ M) : IsKComp M H J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJK : J ≤ kSub 3 M H := by
    unfold kSub
    rw [if_neg hL]
    exact le_sSup ⟨hJ, hJM⟩
  obtain ⟨hsubH, hgen, hq⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
      3 J H hJ.1).mp hJ.2
  have hsub : (J.subgroupOf (kSub 3 M H)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le (kSub_le 3 M H) hsubH
  exact ⟨hJK,
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff
      3 J (kSub 3 M H) hJK).mpr ⟨hsub, hgen, hq⟩⟩

theorem nonempty_threeStar_mulEquiv_map {H : Subgroup G} {J₀ : Subgroup ↥H}
    (hJ₀ : CFSG.IsPComponent 3 J₀) :
    Nonempty (threeStar (J₀.map H.subtype) ≃*
      ↥(J₀.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ O) := QuotientGroup.mk' O
  let K : Subgroup (↥H ⧸ O) := J₀.map π
  let f : J₀ →* (↥H ⧸ O) := π.comp J₀.subtype
  let ψ : J₀ →* K := f.codRestrict K fun j => Subgroup.mem_map_of_mem π j.2
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨j, hj⟩, rfl⟩
  have hJ₀sub : J₀.IsSubnormal :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple
      (G := ↥H) (p := 3) J₀).mp hJ₀ |>.1
  have hcore : (CFSG.pPrimeCore 3 J₀).map J₀.subtype = J₀ ⊓ O := by
    change (CFSG.pPrimeCore 3 J₀).map J₀.subtype = J₀ ⊓ CFSG.pPrimeCore 3 ↥H
    rw [CFSG.pPrimeCore_eq_piCore (G := J₀) 3,
      CFSG.pPrimeCore_eq_piCore (G := ↥H) 3]
    exact CFSG.LocalCores.prime_set_core_subnormal_intersection _ hJ₀sub
  have hker : ψ.ker = CFSG.pPrimeCore 3 J₀ := by
    have hcomap : ψ.ker = O.comap J₀.subtype := by
      ext j
      simp [ψ, f, π, O, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [hcomap]
    have hchange : O.comap J₀.subtype =
        ((CFSG.pPrimeCore 3 J₀).map J₀.subtype).comap J₀.subtype := by
      rw [hcore]
      ext j
      simp only [Subgroup.mem_comap, Subgroup.mem_inf]
      exact ⟨fun h => ⟨j.2, h⟩, fun h => h.2⟩
    rw [hchange,
      Subgroup.comap_map_eq_self_of_injective (H := CFSG.pPrimeCore 3 J₀)
        (f := J₀.subtype) J₀.subtype_injective]
  let eJ : J₀ ≃* (J₀.map H.subtype) := J₀.equivMapOfInjective H.subtype H.subtype_injective
  let e₁ : J₀ ⧸ ψ.ker ≃* K := QuotientGroup.quotientKerEquivOfSurjective ψ hsurj
  let e₂ : J₀ ⧸ CFSG.pPrimeCore 3 J₀ ≃* J₀ ⧸ ψ.ker :=
    QuotientGroup.quotientMulEquivOfEq hker.symm
  let e₃ : J₀ ⧸ CFSG.pPrimeCore 3 J₀ ≃*
      (J₀.map H.subtype) ⧸ CFSG.pPrimeCore 3 (J₀.map H.subtype) :=
    QuotientGroup.congr (CFSG.pPrimeCore 3 J₀)
      (CFSG.pPrimeCore 3 (J₀.map H.subtype)) eJ (CFSG.pPrimeCore_map_iso 3 eJ)
  exact ⟨e₃.symm.trans (e₂.trans e₁)⟩

theorem exists_isKComp_of_isComponent {M H : Subgroup G}
    {L : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)} (hL : CFSG.IsComponent L)
    (hLM : ¬ L ≤ barInf 3 M H) :
    ∃ J : Subgroup G, IsKComp M H J ∧ ¬ J ≤ M ∧ Nonempty (threeStar J ≃* ↥L) := by
  obtain ⟨J₀, hJ₀, hJ₀map⟩ := P614.P614K136.exists_isPComponent_map_eq 3 hL
  have hJsub : IsPComponentIn 3 (J₀.map H.subtype) H := by
    refine ⟨Subgroup.map_subtype_le J₀, ?_⟩
    have hEq : ((J₀.map H.subtype).subgroupOf H) = J₀ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le J₀)]
    rwa [hEq]
  have hple : ¬ pLayerIn 3 H ≤ M := not_pLayerIn_le_of_component hL hLM
  have hJM : ¬ J₀.map H.subtype ≤ M := by
    intro hle
    apply hLM
    rw [← hJ₀map]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨x.2, hle (Subgroup.mem_map_of_mem H.subtype hx)⟩
  have hK : IsKComp M H (J₀.map H.subtype) := isKComp_of_isPComponentIn hJsub hJM hple
  refine ⟨J₀.map H.subtype, hK, hJM, ?_⟩
  rw [← hJ₀map]
  exact nonempty_threeStar_mulEquiv_map (H := H) (J₀ := J₀) hJ₀

theorem HypCGen.exists_isKComp_not_le (h1210 : TwelveTenThree)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen) {M E H : Subgroup G}
    (h : HypCGen G M 3 E H) (hU : NineNineOne M 3) :
    ∃ L : Subgroup G, IsKComp M H L ∧ ¬ L ≤ M ∧ (IsL34Type (threeStar L) ∨ IsA11Star L) := by
  obtain ⟨L₀, hL₀, hL₀M, htype⟩ := h.exists_component_not_le h1210 h97 hU
  obtain ⟨J, hJ, hJM, ⟨e⟩⟩ := exists_isKComp_of_isComponent hL₀ hL₀M
  refine ⟨J, hJ, hJM, ?_⟩
  rcases htype with h34 | h11
  · exact Or.inl (IsL34Type.of_mulEquiv e.symm h34)
  · exact Or.inr (IsA11Type.of_mulEquiv e.symm h11)

theorem HypCGen.fiveTypes
    (h1210 : TwelveTenThree) (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen) {M E H : Subgroup G} (h : HypCGen G M 3 E H)
    (hU : NineNineOne M 3) : FiveTypes M H := by
  obtain ⟨L, hL, hLM, htype⟩ := h.exists_isKComp_not_le h1210 h97 hU
  have hple : ¬ pLayerIn 3 H ≤ M := fun hle => hLM (hL.le_pLayerIn.trans hle)
  have hσ : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
    simpa [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
      CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.not_mem_sigmaSet
  rcases h96 G M E H E h.toNineSettingGen h.mem_H2Fam hσ hple L hL htype with hsingle | hdouble
  · unfold FiveTypes
    refine Or.inl ⟨?_, ?_⟩
    · simpa [hsingle] using hL
    · rcases htype with h34 | h11
      · rcases hL.isL34Star_or_isSL34Star h34 with hL34 | hSL
        · exact Or.inl (by simpa [hsingle] using hL34)
        · exact Or.inr (Or.inl (by simpa [hsingle] using hSL))
      · exact Or.inr (Or.inr (by simpa [hsingle] using h11))
  · obtain ⟨I, hIne, hI, hkeq, huniq, hSL, hrest⟩ := hdouble
    unfold FiveTypes
    exact Or.inr ⟨L, I, hIne.symm, hL, hI, hkeq, huniq, hSL, hrest⟩

theorem preambleFiveTypes_of
    (h1210 : TwelveTenThree) (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (h96 : NineSixMoreoverGen) {M : Subgroup G} (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (hU : NineNineOneAt M) : PreambleFiveTypes M := by
  intro Q hQ H hH
  obtain ⟨E, -, hdata⟩ := exists_hypCGen_of_mem hC hM hσ hQ hH
  exact hdata.fiveTypes h1210 h97 h96 (hU 3 E H hdata)

theorem FiveTypes.exists_isKComp {M H : Subgroup G} (h : FiveTypes M H) :
    ∃ J, IsKComp M H J ∧ (IsL34Type (threeStar J) ∨ IsA11Star J) := by
  unfold FiveTypes at h
  rcases h with ⟨hK, hL | hSL | hA⟩ | ⟨J₁, -, -, hJ₁, -, -, -, hSL₁, -⟩
  · exact ⟨kSub 3 M H, hK, Or.inl hL.1⟩
  · exact ⟨kSub 3 M H, hK, Or.inl hSL.1⟩
  · exact ⟨kSub 3 M H, hK, Or.inr hA⟩
  · exact ⟨J₁, hJ₁, Or.inl hSL₁.1⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
