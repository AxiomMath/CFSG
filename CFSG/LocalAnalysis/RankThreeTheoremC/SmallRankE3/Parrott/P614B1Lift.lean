module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Core

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

theorem hasNormalPComplement_of_map {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] (f : X →* Y) {K : Subgroup X} (hker : ¬ p ∣ Nat.card ↥(K ⊓ f.ker))
    (h : CFSG.HasNormalPComplement p ↥(K.map f)) : CFSG.HasNormalPComplement p ↥K := by
  obtain ⟨N', hN', hcop, hq⟩ := h
  let φ : ↥K →* ↥(K.map f) ⧸ N' := (QuotientGroup.mk' N').comp (f.subgroupMap K)
  refine ⟨φ.ker, inferInstance, ?_,
    hq.of_injective (QuotientGroup.kerLift φ) (QuotientGroup.kerLift_injective φ)⟩
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hnK : orderOf (n : ↥K) = p := by rw [Subgroup.orderOf_coe]; exact hn
  have hφn : φ (n : ↥K) = 1 := n.2
  have hmem : f.subgroupMap K (n : ↥K) ∈ N' := (QuotientGroup.eq_one_iff _).mp hφn
  have hpow : (⟨_, hmem⟩ : ↥N') ^ p = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← map_pow, ← hnK, pow_orderOf_eq_one, map_one]
    rfl
  have h1 : (⟨_, hmem⟩ : ↥N') = 1 := by
    have hd1 : orderOf (⟨_, hmem⟩ : ↥N') ∣ p := orderOf_dvd_of_pow_eq_one hpow
    have hd2 : orderOf (⟨_, hmem⟩ : ↥N') ∣ Nat.card N' := orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hfn : f ((n : ↥K) : X) = 1 := by
    have h2 := congrArg (fun y : ↥N' => ((y : ↥(K.map f)) : Y)) h1
    simpa using h2
  have hmem' : ((n : ↥K) : X) ∈ K ⊓ f.ker := mem_inf.mpr ⟨(n : ↥K).2, hfn⟩
  have hord : orderOf (⟨_, hmem'⟩ : ↥(K ⊓ f.ker)) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hnK
  exact hker (hord ▸ orderOf_dvd_natCard _)

theorem isSylowOf_map_hom {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K) (f : X →* Y) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem eq_top_of_isPGroup_quotient {X : Type*} [Group X] [Finite X]
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 3) (N : Subgroup X) [N.Normal]
    (hN : IsPGroup 3 (X ⧸ N)) : N = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  haveI : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hN
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := X ⧸ N) (n := n - 1)
    (by rw [hn]; exact pow_dvd_pow 3 (Nat.sub_le n 1))
  have hBi : B.index = 3 := by
    have h := B.card_mul_index
    have hpow : 3 ^ n = 3 ^ (n - 1) * 3 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
    rw [hB, hn, hpow] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h
  have hBn : B.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hBi, hn, Nat.pow_minFac hn0, Nat.prime_three.minFac_eq]
  exact hno (B.comap (QuotientGroup.mk' N)) (hBn.comap _)
    ((Subgroup.index_comap_of_surjective B (QuotientGroup.mk'_surjective N)).trans hBi)

theorem l62_unique_component (hNC : T29.NoncyclicCentreRank) (hQ : KFactThreeComponentsQRank)
    {X : Type} [Group X] [Finite X] {S : Sylow 3 X} {x z : X} (h : L62Data X S x z)
    {S' : Sylow 3 (Bar X)} {x' z' : Bar X} (hB : L62Bar (Bar X) S' x' z')
    {L : Subgroup (Bar X)} (hL : IsComponentOf L ⊤) :
    ∀ K : Subgroup (Bar X), IsComponentOf K ⊤ → K = L := by
  by_cases hinv : ∀ K : Subgroup (Bar X), IsComponentOf K ⊤ →
      (S' : Subgroup (Bar X)) ≤ normalizer (K : Set (Bar X))
  · intro K hK
    by_contra hne
    exact l62_false_of_two_fixed hB hNC hK hL hne (hinv K hK) (hinv L hL)
  · push Not at hinv
    obtain ⟨K, hK, hmoved⟩ := hinv
    exact (l62_false_of_moved hQ h hB hK hmoved).elim

theorem l62_bar_point {X : Type} [Group X] [Finite X] {S : Sylow 3 X} {x z : X}
    (h : L62Data X S x z) :
    orderOf (barMk X x) = 3 ∧
      centralizer ({barMk X x} : Set (Bar X)) = (centralizer ({x} : Set X)).map (barMk X) ∧
      ¬ 3 ∣ Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) ∧
      CFSG.Open.pRank 3 (centralizer ({barMk X x} : Set (Bar X))) = 2 := by
  have hxord : orderOf x = 3 := orderOf_eq_prime h.x_pow h.x_ne
  have hO : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := K2.qs_not_dvd_core
  have hx1 : barMk X x ≠ 1 := by
    intro h1
    have hk : x ∈ primeComplementCore (G := X) 3 := (QuotientGroup.eq_one_iff x).mp h1
    exact h.x_ne (K2.qs_eq_one_of_mem S.isPGroup' h.x_mem hk)
  have hxbar : orderOf (barMk X x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, h.x_pow, map_one]) hx1
  have hCmap : centralizer ({barMk X x} : Set (Bar X)) =
      (centralizer ({x} : Set X)).map (barMk X) :=
    K2.centralizer_map_quotient _ hO hxord
  have hker : ¬ 3 ∣ Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) := by
    intro hdvd
    have h1 : Nat.card ↥(centralizer ({x} : Set X) ⊓ (barMk X).ker) ∣
        Nat.card ↥(primeComplementCore (G := X) 3) :=
      Subgroup.card_dvd_of_le (inf_le_right.trans K2.qs_ker.le)
    exact hO (hdvd.trans h1)
  have hcent2 : CFSG.Open.pRank 3 (centralizer ({x} : Set X)) = 2 :=
    T29.pRank_centralizer_eq_two_of_sylow h.rank.ge h.x_mem hxord h.cent
  refine ⟨hxbar, hCmap, hker, ?_⟩
  rw [hCmap, K2.pRank_map_eq_of_coprime_ker (barMk X) Nat.prime_three hker, hcent2]

theorem l62_hasNormalPComplement_centralizer (hT : T29.GL83I291Three)
    (hNC : T29.NoncyclicCentreRank) (hQ : KFactThreeComponentsQRank) {X : Type} [Group X]
    [Finite X] {S : Sylow 3 X} {x z : X} (h : L62Data X S x z)
    (hnc : ¬ HasPrimeConstraint (G := X) 3) :
    CFSG.HasNormalPComplement 3 ↥(centralizer ({x} : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S', x', z', hB⟩ := l62Data_toBar h
  obtain ⟨L, hL⟩ :=
    Stroth.Bal3.exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hnc
  have huniq := l62_unique_component hNC hQ h hB hL
  obtain ⟨hxbar, hCmap, hker, hcent⟩ := l62_bar_point h
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) :=
    hB.rank.ge.trans (pRank_mono 3 (by norm_num) le_top)
  obtain ⟨-, -, -, hconc⟩ := hT (Bar X) hB.catalog hB.core L hL huniq hrank (barMk X x) hxbar hcent
  rcases hconc with ⟨-, -, -, hnpc, -⟩ | hb
  · rw [hCmap] at hnpc
    exact hasNormalPComplement_of_map (barMk X) hker hnpc
  · exfalso
    have hsetup : T29.T29Setup (Bar X) L (barMk X x) :=
      ⟨hB.catalog, hB.core, hL, huniq, hrank, hxbar, hcent⟩
    obtain ⟨e', -, -⟩ := id hb
    have hZ : center ↥L = ⊥ := T29.k3_center_eq_bot_of_psl227 hL.2.2.1 e'
    have hC : centralizer (L : Set (Bar X)) = ⊥ := hsetup.centralizer_eq_bot hZ
    haveI : L.Normal := hsetup.normal
    obtain ⟨N, hN, hNi⟩ := K2.exists_index_three_normal hsetup.normal ⟨e'⟩ hC
      (T29.index_eq_of_fieldAut_L227 hC hb)
    exact hB.no_normal_three N hN hNi

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614B1
