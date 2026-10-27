module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily
import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZFStar

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem le_normalizer_sSup {𝒦 : Set (Subgroup G)} {X : Subgroup G}
    (h : ∀ K ∈ 𝒦, X ≤ normalizer (K : Set G)) :
    X ≤ normalizer ((sSup 𝒦 : Subgroup G) : Set G) := by
  have hX : X ≤ ⨅ K : 𝒦, normalizer ((K : Subgroup G) : Set G) :=
    le_iInf fun K => h K K.2
  have hN := hX.trans (Subgroup.iInf_normalizer_le_normalizer_iSup (fun K : 𝒦 => (K : Subgroup G)))
  simpa only [sSup_eq_iSup'] using hN

variable [Finite G]

theorem exists_involution_of_isTwoComponentIn {K X : Subgroup G}
    (hK : FooteLit.IsTwoComponentIn K X) : ∃ b ∈ K, orderOf b = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hodd : Odd (Nat.card ↥K) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    haveI : Fintype ↥K := Fintype.ofFinite ↥K
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥K) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    exact hno x x.2 (by rw [orderOf_coe]; exact hx)
  have htop : pPrimeCore 2 ↥K = ⊤ :=
    eq_top_iff.mpr
      (le_sSup ⟨inferInstance, by rw [card_top]; exact Nat.coprime_two_left.mpr hodd⟩)
  have hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    FooteLit.isQuasisimple_quotient_of_isPComponent hK.1 hK.2
  have hnt : Nontrivial (↥K ⧸ pPrimeCore 2 ↥K) := LocalCores.isQuasisimple_nontrivial hq
  haveI : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.subsingleton_iff.mpr htop
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem le_centralizer_of_isTwoComponentIn {A J X : Subgroup G}
    (hA : FooteLit.IsTwoComponentIn A X) (hAq : CFSG.IsQuasisimple ↥A)
    (hJ : FooteLit.IsTwoComponentIn J X) (hne : A ≠ J) : J ≤ centralizer (A : Set G) := by
  have hAc : IsComponent (A.subgroupOf X) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA.1).symm hAq,
      hA.2.choose_spec.2.1⟩
  have hne' : A.subgroupOf X ≠ J.subgroupOf X := by
    intro h
    apply hne
    have h1 := congrArg (Subgroup.map X.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1,
      Subgroup.map_subgroupOf_eq_of_le hJ.1] at h1
  obtain ⟨-, h2⟩ :=
    CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
      (A.subgroupOf X) (J.subgroupOf X) hA.2 hJ.2
  have hbot : ⁅A.subgroupOf X, J.subgroupOf X⁆ = ⊥ :=
    (h2 hne').2.2.2 (Or.inl hAc.1)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hm := Subgroup.commutator_mem_commutator
    (show (⟨x, hA.1 hx⟩ : ↥X) ∈ A.subgroupOf X from hx)
    (show (⟨y, hJ.1 hy⟩ : ↥X) ∈ J.subgroupOf X from hy)
  rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
  exact congrArg Subtype.val hm

theorem isTwoComponentIn_of_le_normalizer {A D H : Subgroup G} (hAD : A ≤ D) (hDH : D ≤ H)
    (hDA : D ≤ normalizer (A : Set G)) (hHD : H ≤ normalizer (D : Set G))
    (hA : CFSG.IsQuasisimple ↥A) (hAO : Nontrivial (↥A ⧸ pPrimeCore 2 ↥A)) :
    FooteLit.IsTwoComponentIn A H := by
  have hAH : A ≤ H := hAD.trans hDH
  have hADn : (A.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAD).2 hDA
  have hDHn : (D.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).2 hHD
  have hsn : (A.subgroupOf H).IsSubnormal :=
    ((CFSG.Assembly.IsSubnormal.step hAD hADn (CFSG.Assembly.IsSubnormal.refl D)).trans
      (CFSG.Assembly.IsSubnormal.step hDH hDHn (CFSG.Assembly.IsSubnormal.refl H))).subgroupOf
  exact ⟨hAH,
    CFSG.OddStandard.Solomon75.isPComponent_two_of_isQuasisimple_of_subnormal hA hAH hsn⟩

private theorem normalizer_subgroupOf_map_le {K N : Subgroup G} (hK : K ≤ N) :
    ((Subgroup.normalizer (K.subgroupOf N : Set ↥N)).map N.subtype) ≤
      Subgroup.normalizer (K : Set G) := by
  simpa only [Subgroup.map_subgroupOf_eq_of_le hK] using
    (Subgroup.le_normalizer_map (H := K.subgroupOf N) N.subtype)

theorem base_le_normalizer_of_isTwoComponentIn {K N : Subgroup G}
    (hK : FooteLit.IsTwoComponentIn K N) : base N ≤ normalizer (K : Set G) := by
  have hNtwo : pLayer ↥N 2 ≤ normalizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    apply sSup_le
    intro L hL
    by_cases hLK : L = K.subgroupOf N
    · rw [hLK]
      exact Subgroup.le_normalizer
    · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
        (K.subgroupOf N) L hK.2 hL).2 (Ne.symm hLK)).1
  have htwo : FooteLit.twoLayerIn N ≤ normalizer (K : Set G) := by
    calc FooteLit.twoLayerIn N = (pLayer ↥N 2).map N.subtype := rfl
      _ ≤ ((Subgroup.normalizer (K.subgroupOf N : Set ↥N)).map N.subtype) := map_mono hNtwo
      _ ≤ normalizer (K : Set G) := normalizer_subgroupOf_map_le hK.1
  have hNodd : (pCore 2 (↥N ⧸ pPrimeCore 2 ↥N)).comap
      (QuotientGroup.mk' (pPrimeCore 2 ↥N)) ≤
      normalizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
    intro y hy
    have hcomp : IsComponent ((K.subgroupOf N).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥N))) := by
      rw [hK.2.choose_spec.2.2.1]
      exact hK.2.choose_spec.1
    refine UnbalancedLayer.mem_normalizer_of_map (p := 2) hK.2 ?_
    exact Subgroup.centralizer_le_normalizer _
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.pCore_le_centralizer_of_isComponent
        (C := (K.subgroupOf N).map (QuotientGroup.mk' (pPrimeCore 2 ↥N)))
        hcomp (Subgroup.mem_comap.mp hy))
  have hodd : FooteLit.oddTwoCoreIn N ≤ normalizer (K : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    exact normalizer_subgroupOf_map_le hK.1 (Subgroup.mem_map.mpr ⟨y, hNodd hy, rfl⟩)
  change FooteLit.oddTwoCoreIn N ⊔ FooteLit.twoLayerIn N ≤ normalizer (K : Set G)
  exact sup_le hodd htwo

theorem ne_top_of_balanced (hsimp : IsSimpleGroup G) {S : Set (Subgroup G)} {T : Type*}
    [Group T] {N : Subgroup G} (hN : Balanced S T N) : N ≠ ⊤ := by
  haveI : IsSimpleGroup G := hsimp
  haveI : IsSimpleGroup ↥(⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  rintro rfl
  have hle : markedCount S T ⊤ ≤ 1 := by
    rw [markedCount]
    have hsub : markedComponents S T ⊤ ⊆ ({⊤} : Set (Subgroup G)) := by
      intro K hK
      rw [Set.mem_singleton_iff]
      have htopK : K.subgroupOf ⊤ = ⊤ :=
        GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hK.1.2
      have hmap : (K.subgroupOf ⊤).map (⊤ : Subgroup G).subtype = K :=
        Subgroup.map_subgroupOf_eq_of_le (H := K) (K := (⊤ : Subgroup G)) le_top
      rw [htopK, Subgroup.map_top_of_surjective (⊤ : Subgroup G).subtype
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)] at hmap
      exact hmap.symm
    calc (markedComponents S T ⊤).ncard
        ≤ ({⊤} : Set (Subgroup G)).ncard := Set.ncard_le_ncard hsub
      _ = 1 := by simp
  have := hN.1
  omega

end CFSG.ComponentClassification.FooteMarked
