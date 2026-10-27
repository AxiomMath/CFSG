module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L44c
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_lemma44_image (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    ∀ r : ↥(centralizer ({x} : Set G)), (r : G) ∈ GLBPrimeCore 3 M →
      l34Hom x J r ∈
        rankThreePrimeCore 3 (rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J))) := by
  intro r hr
  have hΓW := l34l44_gamma_le hS hU0 hK1 hK2 hp hM hgen hJ
  have hWΓ := (l34l44_le_normalizer hS hU0 hK1 hK2 hp hM hgen hJ).trans
    (l34l44_normalizer_le hS hU0 hK1 hK2 hp hM hgen hJ)
  have hEW : l34Img x J (GLBPrimeCore 3 M) ≤ l34Img x J M :=
    Subgroup.map_mono (Subgroup.comap_mono (glbPrimeCore_le 3 M))
  have hWE : l34Img x J M ≤ normalizer ((l34Img x J (GLBPrimeCore 3 M) :
      Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    refine le_trans (Subgroup.map_mono fun m hm => ?_) (Subgroup.le_normalizer_map (l34Hom x J))
    rw [mem_normalizer_iff]
    intro c
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp
      (le_normalizer_glbPrimeCore 3 M (Subgroup.mem_subgroupOf.mp hm)) (c : G)
  have hEcop : Nat.Coprime 3 (Nat.card (l34Img x J (GLBPrimeCore 3 M))) := by
    have h1 := Subgroup.card_map_dvd ((GLBPrimeCore 3 M).subgroupOf (centralizer ({x} : Set G)))
      (l34Hom x J)
    have h2 : Nat.card ((GLBPrimeCore 3 M).subgroupOf (centralizer ({x} : Set G))) ∣
        Nat.card (GLBPrimeCore 3 M) := by
      rw [← Subgroup.card_map_of_injective (centralizer ({x} : Set G)).subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (glbPrimeCore_coprime 3 M).coprime_dvd_right (h1.trans h2)
  have hEn : ((l34Img x J (GLBPrimeCore 3 M)).subgroupOf
      (rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hEW.trans hWΓ)).mpr (hΓW.trans hWE)
  have hle : l34Img x J (GLBPrimeCore 3 M) ≤
      rankThreePrimeCore 3 (rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J))) :=
    le_sSup ⟨hEW.trans hWΓ, hEn, hEcop⟩
  exact hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))

private theorem l34l44_eq_one_of_two_pow {Y : Type*} [Group Y] {g : Y} {k n : ℕ}
    (hg : g ^ 2 ^ k = 1) (hn : ¬ 2 ∣ n) (hgn : orderOf g ∣ n) : g = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn))
    (orderOf_dvd_of_pow_eq_one hg) hgn)

theorem l34_lemma44_card (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hK3 : KFactL34Unitary)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    ∀ A : Subgroup G, IsPGroup 2 A → A ≤ GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G) →
      Nat.card A ≤ 2 := by
  intro A hA2 hA
  obtain ⟨hKn, hCK, hL⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hT, hTc, hTK⟩ := l34_T_data hS hU0 hK1 hK2 hp hM hgen hJ
  have hbound := (hK3 (L34Quot x J) (l34Img x J J) hKn hCK hL _ hT hTc hTK).1
  have hDp := l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2
  have hAC : A ≤ centralizer ({x} : Set G) := hA.trans inf_le_right
  set φ : A →* L34Quot x J := (l34Hom x J).comp (Subgroup.inclusion hAC)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨k, hk⟩ := hA2 a
    have hk' : (a : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hck : (Subgroup.inclusion hAC a) ^ 2 ^ k = 1 := Subtype.ext hk'
    have hyD : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        (Subgroup.inclusion hAC a) ∈ reducedCentralizerOfJ x J := by
      have h1 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
          (Subgroup.inclusion hAC a) ∈
            (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker := ha
      rw [QuotientGroup.ker_mk'] at h1
      exact Subgroup.normalCore_le _ h1
    obtain ⟨m, hm⟩ := hDp ⟨_, hyD⟩
    have hm' := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hm'
    have hy2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        (Subgroup.inclusion hAC a) ^ 2 ^ k = 1 := by rw [← map_pow, hck, map_one]
    have hy1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hy2)
      (orderOf_dvd_of_pow_eq_one hm'))
    have hcP : (a : G) ∈ CFSG.ABGTheoremB.pPrimeCoreIn 3 (centralizer ({x} : Set G)) :=
      glbPrimeCore_le_pPrimeCoreIn 3 _ ((mk'_primeComplementCore_eq_one_iff 3 _).mp hy1)
    exact Subtype.ext (l34l44_eq_one_of_two_pow hk' hodd (Subgroup.orderOf_dvd_natCard _ hcP))
  let f : A → ↥(rankThreePrimeCore 3 (rankThreeGamma 1 3 (l34Img x J ((P : Subgroup G) ⊓ J)))) :=
    fun a => ⟨φ a, l34_lemma44_image hS hU0 hK1 hK2 hp hM hgen hJ (Subgroup.inclusion hAC a)
      (hA a.2).1⟩
  exact (Nat.card_le_card_of_injective f fun a b hab => hinj (congrArg Subtype.val hab)).trans
    hbound

end CFSG.LocalAnalysis.RankThreeTheoremC
