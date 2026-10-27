module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614FBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux2
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614F

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (pElementSubgroup)

variable {G : Type} [Group G] [Finite G] {Y H K : Subgroup G} {z : G}

theorem nonempty_mulEquiv_image {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ normalizer (K : Set G)) :
    Nonempty (↥((K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥X))) ≃*
      (↥K ⧸ CFSG.pPrimeCore p ↥K)) := by
  have hrange : ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥X)).comp (Subgroup.inclusion hKX)).range =
      (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥X)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ((QuotientGroup.mk' (CFSG.pPrimeCore p ↥X)).comp (Subgroup.inclusion hKX)).ker =
      CFSG.pPrimeCore p ↥K := by
    rw [← comap_inclusion_pPrimeCore_eq hKX hXK, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange _).symm.trans (QuotientGroup.quotientMulEquivOfEq hker))⟩

theorem isPComponent_subgroupOf (hK : PComp 3 Y H K z)
    (hD2 : IsPGroup 2 (rankThreePrimeCore 3 H)) {X : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ normalizer (K : Set G)) : CFSG.IsPComponent 3 (K.subgroupOf X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := isSimpleGroup_kbar hK
  have hn : (K.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  obtain ⟨e⟩ := nonempty_mulEquiv_image (p := 3) hKX hXK
  haveI : IsSimpleGroup ↥((K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X))) :=
    e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := kbar_nonabelian hK
  refine isPComponent_of_normal Nat.prime_three hn
    (zja_pElementSubgroup_subgroupOf hKX (pElementSubgroup_eq hK hD2))
    (L := (K.subgroupOf X).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥X))) ⟨?_, ?_⟩ rfl
  · exact zja_isQuasisimple_of_simple
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  · exact (Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)).isSubnormal

theorem centralizer_pCore_le_of_le {X : Subgroup G} (hXH : X ≤ H) (hDX : pCoreOf 2 H ≤ X)
    (hCT : H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) :
    centralizer (CFSG.pCore 2 ↥X : Set ↥X) ≤ CFSG.pCore 2 ↥X := by
  have hDn : ((pCoreOf 2 H).subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr (hXH.trans (le_normalizer_pCoreOf 2 H))
  have hDle : (pCoreOf 2 H).subgroupOf X ≤ CFSG.pCore 2 ↥X :=
    le_sSup ⟨hDn, (isPGroup_pCoreOf 2 H).comap_subtype⟩
  intro c hc
  have hmem : (c : G) ∈ H ⊓ centralizer (pCoreOf 2 H : Set G) := by
    refine ⟨hXH c.2, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hc ⟨d, hDX hd⟩ (hDle (Subgroup.mem_subgroupOf.mpr hd)))
  exact hDle (Subgroup.mem_subgroupOf.mpr (hCT hmem))

theorem isPGroup_pPrimeCore (hK : PComp 3 Y H K z) (hD2 : IsPGroup 2 (rankThreePrimeCore 3 H))
    {X T : Subgroup G} (hKX : K ≤ X) (hTX : T ≤ X) (hX : K ⊔ T = X) (hT2 : IsPGroup 2 T)
    (hXK : X ≤ normalizer (K : Set G)) : IsPGroup 2 ↥(CFSG.pPrimeCore 3 ↥X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (K.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have htop : K.subgroupOf X ⊔ T.subgroupOf X = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKX,
      Subgroup.map_subgroupOf_eq_of_le hTX, hX, Subgroup.map_top, Subgroup.range_subtype]
  refine isPGroup_of_quotient (isPGroup_quotient_of_sup htop hT2.comap_subtype) ?_
  intro w hwN hwK
  have hw : Subgroup.inclusion hKX ⟨(w : G), Subgroup.mem_subgroupOf.mp hwK⟩ = w :=
    Subtype.ext (Subgroup.coe_inclusion _ _)
  have h1 : (⟨(w : G), Subgroup.mem_subgroupOf.mp hwK⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K :=
    comap_inclusion_pPrimeCore_le hKX (Subgroup.mem_comap.mpr (by rw [hw]; exact hwN))
  have h2 : (w : G) ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := ⟨_, h1, rfl⟩
  rw [pPrimeCore_map_eq hK] at h2
  obtain ⟨k, hk⟩ := hD2 ⟨w, h2.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem pCore_le_subgroupOf {B S X : Subgroup G} (hK : PComp 3 Y H K z) (hX : K ⊔ S = X)
    (hBH : B ≤ H) (hS : IsMaxTwoInvariantIn B H S) : CFSG.pCore 2 ↥X ≤ S.subgroupOf X := by
  subst hX
  have hSX : S ≤ K ⊔ S := le_sup_right
  have hRX : (CFSG.pCore 2 ↥(K ⊔ S)).map (K ⊔ S).subtype ≤ K ⊔ S := Subgroup.map_subtype_le _
  have hXR : K ⊔ S ≤
      normalizer (((CFSG.pCore 2 ↥(K ⊔ S)).map (K ⊔ S).subtype : Subgroup G) : Set G) :=
    fun _ hg => mem_normalizer_map_of_characteristic (Subgroup.le_normalizer hg)
  have hBX : B ≤ normalizer ((K ⊔ S : Subgroup G) : Set G) := fun _ hg =>
    Subgroup.inf_normalizer_le_normalizer_sup K S ⟨hK.normal (hBH hg), hS.1.2.2 hg⟩
  have hinv : IsTwoInvariantIn B H ((CFSG.pCore 2 ↥(K ⊔ S)).map (K ⊔ S).subtype ⊔ S) :=
    ⟨sup_le (hRX.trans (sup_le hK.le hS.1.1)) hS.1.1,
      IsPGroup.to_sup_of_normal_left' (CFSG.pCore_isPGroup.map _) hS.1.2.1 (hSX.trans hXR),
      fun _ hg => Subgroup.inf_normalizer_le_normalizer_sup _ S
        ⟨mem_normalizer_map_of_characteristic (hBX hg), hS.1.2.2 hg⟩⟩
  have hRS : (CFSG.pCore 2 ↥(K ⊔ S)).map (K ⊔ S).subtype ≤ S :=
    le_sup_left.trans (hS.2 _ hinv le_sup_right).le
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (hRS ⟨x, hx, rfl⟩)

theorem not_le_normalizer_sup {M S X : Subgroup G} (hK : PComp 3 M H K z) (hKX : K ≤ X)
    (hSX : S ≤ X)
    (hchar : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M)
    (hcoreM : (CFSG.pPrimeCore 3 ↥X).map X.subtype ≤ M) :
    ∀ Z : Subgroup ↥X, Z ≤ S.subgroupOf X → Z ≠ ⊥ →
      (Z.subgroupOf (S.subgroupOf X)).Characteristic →
      ¬ K.subgroupOf X ≤ normalizer (Z : Set ↥X) ⊔ CFSG.pPrimeCore 3 ↥X := by
  intro Z hZS hZ1 hZc hcover
  have hZV : Z.map X.subtype ≤ S := by
    rintro _ ⟨w, hw, rfl⟩
    exact hZS hw
  have hZ1' : Z.map X.subtype ≠ ⊥ := fun h =>
    hZ1 ((Subgroup.map_eq_bot_iff_of_injective Z X.subtype_injective).mp h)
  have hZc' : ((Z.map X.subtype).subgroupOf S).Characteristic := by
    let e : ↥(S.subgroupOf X) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSX
    have hc := zja_characteristic_map e hZc
    have heq : (Z.subgroupOf (S.subgroupOf X)).map e.toMonoidHom =
        (Z.map X.subtype).subgroupOf S := by
      ext w
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
      · intro hw
        obtain ⟨y, hy, hyw⟩ := hw
        exact ⟨⟨y, hZS hy⟩, hy, Subtype.ext hyw⟩
    rw [← heq]
    exact hc
  apply hK.not_le
  have h1 := Subgroup.map_mono (f := X.subtype) hcover
  rw [Subgroup.map_subgroupOf_eq_of_le hKX, Subgroup.map_sup] at h1
  refine h1.trans (sup_le ?_ hcoreM)
  rintro _ ⟨g, hg, rfl⟩
  exact hchar _ hZV hZ1' hZc' (thg_mem_normalizer_map hg)

theorem nonempty_quotient_center_equiv (hK : PComp 3 Y H K z) {X : Subgroup G} (hKX : K ≤ X) :
    Nonempty ((↥(K.subgroupOf X) ⧸ CFSG.pPrimeCore 3 ↥(K.subgroupOf X)) ⧸
      center (↥(K.subgroupOf X) ⧸ CFSG.pPrimeCore 3 ↥(K.subgroupOf X)) ≃* Kbar K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := isSimpleGroup_kbar hK
  let ι : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hψ :
      Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp ι.toMonoidHom) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact ⟨ι.symm k, by simp⟩
  have hker : Nat.Coprime 3
      (Nat.card ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp ι.toMonoidHom).ker) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ ι.injective) CFSG.pPrimeCore_coprime_card
  exact zja_quotient_equiv Nat.prime_three (three_dvd_card_kbar hK) (center_kbar hK) _ hψ hker

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614F
