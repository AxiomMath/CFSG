module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6L44b
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_lemma44_image (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : A6SylowData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J) :
    ∀ r : ↥(centralizer ({x} : Set G)), (r : G) ∈ GLBPrimeCore 3 M →
      l34Hom x J r ∈
        rankThreePrimeCore 3 (normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
          Subgroup (L34Quot x J)) : Set (L34Quot x J))) := by
  intro r hr
  have hNW := (a6l44_normalizer_le hS hU0 hK1 hp hM hgen hJ).trans
    (a6l44_gamma_le hS hU0 hK1 hp hM hgen hJ)
  have hWN := a6l44_le_normalizer hS hU0 hK1 hp hM hgen hJ
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
      (normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) : Subgroup (L34Quot x J)) :
        Set (L34Quot x J)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hEW.trans hWN)).mpr (hNW.trans hWE)
  have hle : l34Img x J (GLBPrimeCore 3 M) ≤
      rankThreePrimeCore 3 (normalizer ((l34Img x J ((P : Subgroup G) ⊓ J) :
        Subgroup (L34Quot x J)) : Set (L34Quot x J))) :=
    le_sSup ⟨hEW.trans hWN, hEn, hEcop⟩
  exact hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr))

theorem a6_not_two_dvd_card (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hK1 : A6SylowData) (hK3 : A6BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsA6Normal M x J) :
    ¬ 2 ∣ Nat.card ↥(GLBPrimeCore 3 M ⊓ centralizer ({x} : Set G)) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨hKn, hCK, hU⟩ := a6_quot_data hS hU0 hp hM hgen hJ
  obtain ⟨hT, -, -⟩ := a6_T_data hS hU0 hK1 hp hM hgen hJ
  have hTK : l34Img x J ((P : Subgroup G) ⊓ J) ≤ l34Img x J J := by
    obtain ⟨Q, hQ⟩ := hT
    exact hQ ▸ Subgroup.map_subtype_le _
  have hcore := hK3 _ _ hKn hCK hU _ hTK hT
  have hDp := a6_reducedCentralizer_isPGroup hS hU0 hK1 hp hM hgen hJ
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2
  let c : ↥(centralizer ({x} : Set G)) := ⟨a, a.2.2⟩
  have h1 : l34Hom x J c = 1 := by
    have h := a6_lemma44_image hS hU0 hK1 hp hM hgen hJ c a.2.1
    rwa [hcore, mem_bot] at h
  have hyD : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
      reducedCentralizerOfJ x J := by
    have h1' : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ∈
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker := h1
    rw [QuotientGroup.ker_mk'] at h1'
    exact Subgroup.normalCore_le _ h1'
  obtain ⟨m, hm⟩ := hDp ⟨_, hyD⟩
  have hm' := congrArg Subtype.val hm
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hm'
  have ha2 : (a : G) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a
    rw [ha] at h
    exact congrArg Subtype.val h
  have hy2 : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3) c ^ 2 =
      1 := by
    rw [← map_pow, show c ^ 2 = 1 from Subtype.ext ha2, map_one]
  have hy1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one hy2)
    (orderOf_dvd_of_pow_eq_one hm'))
  have hcP : (a : G) ∈ CFSG.ABGTheoremB.pPrimeCoreIn 3 (centralizer ({x} : Set G)) :=
    glbPrimeCore_le_pPrimeCoreIn 3 _ ((mk'_primeComplementCore_eq_one_iff 3 _).mp hy1)
  apply hodd
  have h := Subgroup.orderOf_dvd_natCard _ hcP
  rwa [Subgroup.orderOf_coe, ha] at h

end CFSG.LocalAnalysis.RankThreeTheoremC
