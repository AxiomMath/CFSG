module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeDiag
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroPerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatHelp
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMDataAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Layer

variable {Y : Type} [Group Y]

def threePrimeLayer (Y : Type) [Group Y] : Subgroup Y :=
  ⨆ (L : Subgroup Y) (_ : IsComponentOf L ⊤ ∧ Nat.Coprime 3 (Nat.card L)), L

theorem le_threePrimeLayer {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hc : Nat.Coprime 3 (Nat.card L)) : L ≤ threePrimeLayer Y :=
  le_iSup₂_of_le L ⟨hL, hc⟩ le_rfl

theorem threePrimeLayer_le_normalizer [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    threePrimeLayer Y ≤ Subgroup.normalizer (L : Set Y) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases heq : L' = L
  · rw [heq]; exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_mem_ne hL'.1 hL heq hx hy).symm

theorem coprime_card_threePrimeLayer [Finite Y] :
    Nat.Coprime 3 (Nat.card (threePrimeLayer Y)) := by
  have hle : threePrimeLayer Y ≤ GLBPrimeCore 3 (threePrimeLayer Y) :=
    iSup₂_le fun L hL => le_glbPrimeCore (le_threePrimeLayer hL.1 hL.2)
      (threePrimeLayer_le_normalizer hL.1) hL.2
  have heq : GLBPrimeCore 3 (threePrimeLayer Y) = threePrimeLayer Y :=
    le_antisymm (glbPrimeCore_le 3 _) hle
  rw [← heq]
  exact glbPrimeCore_coprime 3 _

theorem threePrimeLayer_normal : (threePrimeLayer Y).Normal := by
  constructor
  intro n hn g
  have hmap : (threePrimeLayer Y).map (MulAut.conj g).toMonoidHom ≤ threePrimeLayer Y := by
    rw [threePrimeLayer, Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    refine le_threePrimeLayer (isComponentOf_map_conj hL.1 g) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hL.2
  exact hmap ⟨n, hn, by simp [MulAut.conj_apply]⟩

end Layer

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem coprime_three_card_preimage {M : Subgroup G} {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hE : Nat.Coprime 3 (Nat.card E)) :
    Nat.Coprime 3 (Nat.card ((E.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)) := by
  set N := (E.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype with hN
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hdvd
  obtain ⟨m, hmE, hmx⟩ := x.2
  have hmo : orderOf m = 3 := by
    rw [← Subgroup.orderOf_coe m, show (m : G) = (x : G) from hmx, Subgroup.orderOf_coe x, hx]
  set mb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) m with hmb
  have hmb3 : mb ^ 3 = 1 := by rw [hmb, ← map_pow, ← hmo, pow_orderOf_eq_one, map_one]
  have hmb1 : mb ≠ 1 := by
    intro h1
    have hm2 : m ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff m).mp h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨m, hm2⟩
    have hk' : m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := hmo ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hord : orderOf mb = 3 := orderOf_eq_prime hmb3 hmb1
  have h3 : 3 ∣ Nat.card E := by
    have := Subgroup.orderOf_dvd_natCard E (show mb ∈ E from hmE)
    rwa [hord] at this
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hE h3

theorem D1OneSmallData.odd_card_primeComplementCore_cz (hd : D1OneSmallData 3 P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) :
    Odd (Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)) := by
  obtain ⟨-, -, -, -, hodd⟩ := hd.odd_card_primeCore_cz hz hSP
  have hOcard : Nat.card (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3) =
      Nat.card (GLBPrimeCore 3 (Subgroup.centralizer ({z} : Set G))) := by
    rw [← glbPrimeCore_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le 3 _)).toEquiv
  rw [hOcard]
  exact hodd

theorem D1OneSmallData.eq_bot_of_coprime_le_map_cz (hβ : KFactBeta) (hKO : KFactOneLie)
    (hTor : KFactOneLieTorus) (hd : D1OneSmallData 3 P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z)
    {W : Subgroup (D1CzQuot 3 z)}
    (hWY₀ : W ≤ ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)))
    (hY₀W : ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) 3)) ≤
      Subgroup.normalizer (W : Set (D1CzQuot 3 z)))
    (hWc : Nat.Coprime 3 (Nat.card W)) : W = ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨P', Pbar, KC, -, -, hRP', hRC⟩ := hd.exists_reducedCentralizer hz hSP
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hmk
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : mk ⟨z, hzC⟩ ∉ KC := hout KC hRC.comp
  have hKn := hRC.normal
  obtain ⟨hZK, hs, hnab, hcat, hbig, hnc, T₁, hT₁, hTnc, hΓ⟩ :=
    hRC.red.exists_sylow_facts_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp hKn
      hzK hβ
  have hF := hKO KC hs hnab hcat 3 hp3 (by norm_num) T₁ hTnc hΓ hbig
  obtain ⟨n, e, hTF⟩ := hTor KC hs hnab hcat 3 (by norm_num) T₁ hTnc hΓ hbig
  have hzPbar : mk ⟨z, hzC⟩ ∈ (Pbar : Subgroup (D1CzQuot 3 z)) := by
    rw [hRC.sylow_eq]
    exact ⟨⟨z, hzC⟩, Subgroup.mem_subgroupOf.mpr (hRP' hz.1), rfl⟩
  have hzc : mk ⟨z, hzC⟩ ∈ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) :=
    Subgroup.mem_centralizer_iff.mpr fun k _ => Subgroup.mem_center_iff.mp hzZ k
  have hz' : ∃ w ∈ (Pbar : Subgroup (D1CzQuot 3 z)), w ∉ KC ∧ orderOf w = 3 ∧
      w ∈ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) := ⟨_, hzPbar, hzK, hzp, hzc⟩
  have hY₀T := hRC.red.le_normalizer_of_borel_coatom hRC.comp hnc hz' T₁ hT₁ hTF.borel_coatom
  have hWK : W ≤ Subgroup.centralizer (KC : Set (D1CzQuot 3 z)) := by
    rcases hRC.red.dichotomy_of_torus hRC.comp hnc hz' hZK T₁ hT₁ hF hTF hY₀T W hWY₀ hY₀W with
      hle | hle
    · exfalso
      obtain ⟨ψ, hψinj, hψrange, -⟩ := hTF.torus
      set ζ : KC := ψ (Multiplicative.ofAdd 1) with hζ
      have hζ1 : ζ ≠ 1 := by
        intro h1
        have := hψinj (h1.trans (map_one ψ).symm)
        exact one_ne_zero (ofAdd_eq_one.mp this)
      have hζZ : (ζ : D1CzQuot 3 z) ∈ centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC) := by
        have h1 := map_subtype_centerOf (T₁ : Subgroup KC)
        rw [hT₁] at h1
        rw [← h1]
        have hmem : ζ ∈ ψ.range := ⟨_, rfl⟩
        rw [hψrange] at hmem
        exact ⟨ζ, hmem, rfl⟩
      have hζP : IsPGroup 3 (centerOf ((Pbar : Subgroup (D1CzQuot 3 z)) ⊓ KC)) :=
        Pbar.isPGroup'.to_le (inf_le_left.trans inf_le_left)
      have hbot := inf_eq_bot_of_isPGroup hp3 hζP hWc
      rw [inf_eq_left.mpr hle] at hbot
      have : (ζ : D1CzQuot 3 z) ∈ (⊥ : Subgroup (D1CzQuot 3 z)) := hbot ▸ hζZ
      rw [Subgroup.mem_bot] at this
      exact hζ1 (Subtype.ext this)
    · exact hle
  have hNorm : (⊤ : Subgroup (D1CzQuot 3 z)) ≤ Subgroup.normalizer (W : Set (D1CzQuot 3 z)) := by
    have : KC.Normal := hKn
    rw [← Sylow.normalizer_sup_eq_top T₁]
    refine sup_le ?_ ?_
    · have h1 : Subgroup.normalizer (((T₁ : Subgroup KC).map KC.subtype : Subgroup _) :
          Set (D1CzQuot 3 z)) ≤ ((C ⊓ M).subgroupOf C).map mk := by
        rw [hT₁]
        exact hRC.red.normalizer_inf_le_of_rankOne hnc hzPbar hzK hzp hzc
      exact h1.trans hY₀W
    · exact (Subgroup.le_centralizer_iff.mp hWK).trans (Subgroup.centralizer_le_normalizer _)
  have hWn : W.Normal := ⟨fun w hw g =>
    (Subgroup.mem_normalizer_iff.mp (hNorm (Subgroup.mem_top g)) w).mp hw⟩
  have h1 := normal_coprime_le_primeComplementCore 3 W hWn hWc
  rw [hRC.red.core_eq_bot] at h1
  exact le_bot_iff.mp h1

theorem D1OneSmallData.odd_card_inf_centralizer_of_coprime_normal (hβ : KFactBeta)
    (hKO : KFactOneLie) (hTor : KFactOneLieTorus) (hd : D1OneSmallData 3 P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z)
    {N : Subgroup G} (hNM : N ≤ M) (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hNc : Nat.Coprime 3 (Nat.card N)) :
    Odd (Nat.card (N ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) := by
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  set mk := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hmk
  set W : Subgroup (D1CzQuot 3 z) := ((N ⊓ C).subgroupOf C).map mk with hW
  have hWY₀ : W ≤ ((C ⊓ M).subgroupOf C).map mk :=
    Subgroup.map_mono fun c hc => Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp hc).2, hNM (Subgroup.mem_subgroupOf.mp hc).1⟩
  have hAJ : C ⊓ M ≤ Subgroup.normalizer ((N ⊓ C : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hMN hg.2, Subgroup.le_normalizer hg.1⟩
  have hY₀W : ((C ⊓ M).subgroupOf C).map mk ≤ Subgroup.normalizer (W : Set (D1CzQuot 3 z)) :=
    map_le_normalizer_map mk inf_le_right hAJ
  have hNCc : Nat.Coprime 3 (Nat.card ((N ⊓ C).subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hNc
  have hWc : Nat.Coprime 3 (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hNCc
  have hW1 := hd.eq_bot_of_coprime_le_map_cz hβ hKO hTor hz hSP hout hWY₀ hY₀W hWc
  have hker : (N ⊓ C).subgroupOf C ≤ primeComplementCore (G := C) 3 := by
    intro c hc
    have h1 : mk c ∈ W := Subgroup.mem_map_of_mem _ hc
    rw [hW1, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff c).mp h1
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ C ≤ C)).toEquiv]
  exact Odd.of_dvd_nat (hd.odd_card_primeComplementCore_cz hz hSP) (Subgroup.card_dvd_of_le hker)

theorem D1OneSmallData.odd_card_inf_centralizer_of_component (hβ : KFactBeta)
    (hKO : KFactOneLie) (hTor : KFactOneLieTorus) (hd : D1OneSmallData 3 P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z) (hout : D1CzOutside 3 z)
    (hzM : z ∈ M) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    (hcop : Nat.Coprime 3 (Nat.card Lb)) :
    Odd (Nat.card (Lb ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set E := threePrimeLayer (↥M ⧸ CFSG.pCore 2 ↥M) with hE
  have hEn : E.Normal := threePrimeLayer_normal
  set N : Subgroup G := (E.comap mkM).map M.subtype with hN
  have hNM : N ≤ M := Subgroup.map_subtype_le _
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp ?_
    have he : N.subgroupOf M = E.comap mkM :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    rw [he]
    exact Subgroup.Normal.comap hEn mkM
  have hNCodd := hd.odd_card_inf_centralizer_of_coprime_normal hβ hKO hTor hz hSP hout hNM hMN
    (coprime_three_card_preimage coprime_card_threePrimeLayer)
  set D := Lb ⊓ Subgroup.centralizer
    ({mkM ⟨z, hzM⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hD
  obtain ⟨φ, hφ⟩ := exists_surjective_of_le_centralizer Nat.prime_three (by norm_num) hzM hz.2.1
    (inf_le_right : D ≤ _)
  have hle : Subgroup.centralizer ({z} : Set G) ⊓ (D.comap mkM).map M.subtype ≤
      N ⊓ Subgroup.centralizer ({z} : Set G) :=
    fun x hx => ⟨Subgroup.map_mono (Subgroup.comap_mono
      (inf_le_left.trans (le_threePrimeLayer hLb hcop))) hx.2, hx.1⟩
  exact Odd.of_dvd_nat (Odd.of_dvd_nat hNCodd (Subgroup.card_dvd_of_le hle))
    (Subgroup.card_dvd_of_surjective hφ)

end CFSG.AGLEmbedding
