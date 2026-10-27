module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCentRankComp
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCoverShape
import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCoverCent
import CFSG.LocalAnalysis.AGLEmbedding.Sp48NCoverCyclic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem false_of_rankThree_component {X : Type} [Group X] [Finite X] {Rb : Sylow 3 X}
    {X₀ : Subgroup X} (h : ReducedNongeneration 3 X Rb X₀) (hX : CatalogSimpleSections X)
    (hβ : KFactBeta) (hS : KFactSeitzCyc) (hInv : KFactCaseTwoInv) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hCin : KFactChevTwoInnerGen)
    (hCout : KFactChevTwoOuterGen) (hSchur : KFactChevTwoSurvivorSchur)
    (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur) (hKT : KFactThreeCoverInvolve)
    (h3 : Open.pRank 3 (Rb : Subgroup X) = 3) (hRb : 3 ^ 6 ≤ Nat.card Rb) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (huniq : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K)
    {B : Subgroup K} {L : Type} [Group L] (hiso : IsCaseTwoGroup 3 L) (f : B →* L)
    (hf : Function.Surjective f) {Q : Subgroup X} (hQ : IsPGroup 3 Q)
    (hQcard : 3 ^ 5 ≤ Nat.card Q) {a : X} (haQ : a ∈ Q) (ha3 : a ^ 3 = 1)
    (hC : ∀ r ∈ Q, r * a = a * r → r ^ 3 = 1) : False := by
  by_cases hcyc : IsCyclic ((Rb : Subgroup X) ⊓ K : Subgroup X)
  · exact false_of_isCyclic_inf h hX hβ hS h3 hK huniq hcyc hRb hQ hQcard haQ ha3 hC
  rcases h.rankOne_or_center hK hcyc with ⟨z', hz'R, hz'K, hz'p, hz'c, -⟩ | hcent
  · exact false_of_rankOne_of_surjective h hX hInv h3.le hK hcyc ⟨z', hz'R, hz'K, hz'p, hz'c⟩
      hiso f hf
  · exact false_of_center_shape h hX hP1L hP1A hP1S hCin hCout hSchur hKU1 hKR1 hKT h3 hz hzp hK
      huniq hcyc hcent hiso f hf

theorem d1Sp48NCentRankCompResidue_of_kFacts (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hInv : KFactCaseTwoInv) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hCin : KFactChevTwoInnerGen) (hCout : KFactChevTwoOuterGen)
    (hSchur : KFactChevTwoSurvivorSchur) (hKU1 : KFactUnitarySchur) (hKR1 : KFactReeSchur)
    (hKT : KFactThreeCoverInvolve) : D1Sp48NCentRankCompResidue := by
  intro G _ _ P M H R X U A V d hloc hext hd hO3 hdZ hd1 hCH hY hinv hO Tb K hred hTb3 hcat
    hzZ hK hKn huniq hB
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set O := primeComplementCore (G := C) 3 with hOdef
  have hO' : (3 : ℕ).Coprime (Nat.card O) := primeComplementCore_coprime (G := C) 3
  obtain ⟨B, L, f, hf, hLiso⟩ := hB
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hd.elem_X.2 d (hd.center_le hdZ)) hd1
  have hzp : orderOf (QuotientGroup.mk' O ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
      = 3 := orderOf_mk_of_coprime hp _ hO' (by rw [← Subgroup.orderOf_coe]; exact hd3)
  have hRC : R ≤ C := fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hdZ.2 r hr)
  have hR3 : IsPGroup 3 R := hext.isPGroup
  obtain ⟨Y, hY3, hRY, hYC⟩ := hY
  have hYC' : Y ≤ C := hYC.trans inf_le_right
  have hY6 : 3 ^ 6 ≤ Nat.card Y := by
    obtain ⟨j, hj⟩ := hY3.exists_card_eq
    have hlt := Subgroup.card_lt_of_lt hRY
    rw [hd.card_R, hj] at hlt
    rw [hj]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt)
  have hYs : IsPGroup 3 (Y.subgroupOf C) := hY3.comap_subtype
  have hYcard : Nat.card ((Y.subgroupOf C).map (QuotientGroup.mk' O)) = Nat.card Y := by
    rw [card_map_mk_of_isPGroup hp O hO' hYs,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYC').toEquiv]
  obtain ⟨S, hS'⟩ := (hYs.map (QuotientGroup.mk' O)).exists_le_sylow
  have hTb6 : 3 ^ 6 ≤ Nat.card Tb := by
    have h1 := Subgroup.card_le_of_le hS'
    rw [hYcard] at h1
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S]
    omega
  obtain ⟨a, haR, ha3, hCa⟩ := D1Sp48NData.exists_pow_three_eq_one_of_commute hd
  have hRs : IsPGroup 3 (R.subgroupOf C) := hR3.comap_subtype
  set Q := (R.subgroupOf C).map (QuotientGroup.mk' O) with hQdef
  have hQ3 : IsPGroup 3 Q := hRs.map _
  have hQcard : 3 ^ 5 ≤ Nat.card Q := by
    rw [hQdef, card_map_mk_of_isPGroup hp O hO' hRs,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hd.card_R]
  set a₀ : C := ⟨a, hRC haR⟩
  have haQ : QuotientGroup.mk' O a₀ ∈ Q := Subgroup.mem_map_of_mem _ haR
  have ha3' : (QuotientGroup.mk' O a₀) ^ 3 = 1 := by
    rw [← map_pow, show a₀ ^ 3 = 1 from Subtype.ext (by simpa using ha3), map_one]
  have hC' : ∀ r ∈ Q, r * QuotientGroup.mk' O a₀ = QuotientGroup.mk' O a₀ * r → r ^ 3 = 1 := by
    rintro _ ⟨r, hr, rfl⟩ hra
    have hr' : ((r : C) : G) ∈ R := hr
    have hmul : r * a₀ = a₀ * r := by
      rw [← map_mul, ← map_mul] at hra
      exact eq_of_mk_primeComplementCore_eq hR3 (R.mul_mem hr' haR) (R.mul_mem haR hr') hra
    have hr3 : (r : G) ^ 3 = 1 := hCa _ hr' (by simpa using congrArg Subtype.val hmul)
    rw [← map_pow, show r ^ 3 = 1 from Subtype.ext (by simpa using hr3), map_one]
  exact false_of_rankThree_component hred hcat hβ hS hInv hP1L hP1A hP1S hCin hCout hSchur hKU1
    hKR1 hKT hTb3 hTb6 hzZ hzp hK huniq hLiso f hf hQ3 hQcard haQ ha3' hC'

end CFSG.AGLEmbedding
