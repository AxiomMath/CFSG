module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbU3Core
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbLinTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbU3Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbExtra
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbU3Block

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_posZero_ib_unitary [Fact p.Prime] (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) (hKU2 : KFactUnitarySylowStructure) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentCycIb)
    (hK2s : KFactAltSixSevenAutFive) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizerSq) (hG1 : StmtFaithfulExtraspecialRank)
    (hd : D1OneSmallData p P M H R Rbar K) (hnIa : ¬ D1SmallIa p H K) (hp5 : 5 ≤ p)
    (hU : IsSmallUnitary p K) {z : G} (hz : D1SmallCZElt p H R K z) (hSP : D1CzSP p z)
    (hout : D1CzOutside p z) (hV : d1MapPCore p M H = ⊥) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  obtain ⟨T₁, hT₁, hF, hs, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 (Or.inr hU)
  obtain ⟨hzR, hzp, hzH, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set zb := mkM ⟨z, hzM⟩ with hzb
  set X := d1LiftX p H R K with hXdef
  set S := pCoreOf 2 H with hS
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨d, ⟨q, hqp, hqe, hdq⟩, ⟨he⟩⟩ := id hU
  have hdU : IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
  have hKe' : Nonempty (K ≃* CatGroup d) := ⟨he⟩
  have hn1 : d.1.fieldExponent = 1 := by
    obtain ⟨q', -, hq'd, hfe, -⟩ := hdU.exists_eq
    have : q' = q := by
      have h1 : TauCeti.LieTypeIndex.twistedA 2 q' = TauCeti.LieTypeIndex.twistedA 2 q :=
        hq'd.symm.trans hdq
      injection h1
    rw [hfe, this, hqe]
  obtain ⟨hTcard, hTcomm, hTpow, -⟩ := hKU2 K p d hp2 hdU hKe' T₁
  rw [hn1] at hTcard
  obtain ⟨hZC, hcommX, hcardX, hpowX⟩ := hd.unitary_sylow hT₁ hTcard hTcomm hTpow
  have hXcard : Nat.card X = p ^ 3 := by rw [hcardX]
  have hXZ : ⁅X, X⁆ = X ⊓ Subgroup.centralizer (X : Set G) := hcommX.trans hZC
  have hXnorm := fun N hNX hXN hN =>
    commutator_le_of_normal_of_extraspecial (X := X) (N := N) hXcard hXZ hNX hXN hN
  have hE := exists_elemAbelian_sq_of_extraspecial hXcard hXZ hpowX
  have hX1card := card_commutator_of_extraspecial hXcard hXZ
  have hX1 : ⁅X, X⁆ ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hX1card
    exact hp.one_lt.ne hX1card
  have hZ : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥ :=
    fun W hWp hWz => hd.eq_bot_of_perfect_le_centralizer hβ hKO hΓ hSch hz hSP hout hzM hWp hWz
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L :=
    fun L hL' => stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3' hK5' h3 hL'
  have hXz := hd.d1LiftX_le_centralizer hz
  obtain ⟨D, hDp, hDK, hXD, hzD, hDpart⟩ :=
    hd.exists_perfect_section h3 hT₁ hF.uPrime hF.outer_solvable hs hz hnIa hXz
  have hzbD : zb ∈ D := hzD hzM
  have hzbp : zb ^ p = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ p = 1 := Subtype.ext (by simp [← hzp, pow_orderOf_eq_one])
    rw [this, map_one]
  have hXK : X ≤ H ⊓ M := (d1LiftX_le p H R K).trans h3.le_inf
  have hXM : X ≤ M := hXK.trans inf_le_right
  have hXH : X ≤ H := hXK.trans inf_le_left
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hDS : D ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hDK.trans (barM_le_normalizer_barM (inf_le_left.trans hNSH.ge))
  have hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ d1PlusCore p H K := by
    intro L hL' hLL
    exact le_d1PlusCore_of_map_le (hL'.trans inf_le_left)
      (D1OneSmallData.le_centralizer_of_perfect hd hT₁ hF.uPrime hF.outer_solvable hs
        (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL'))
        (commutator_map_eq_self (hL'.trans inf_le_left) hLL))
  have hcyc : ∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A := fun Y' hY' hY'p A hAY hA =>
    hd.isCyclic_of_le_d1PlusCore (hAY.trans (hperf Y' (h3.inf_eq_inf_normalizer_twoCore ▸ hY')
      hY'p)) hA
  have hcommN : ∀ x ∈ X, ∀ c ∈ d1PlusCore p H K, x * c * x⁻¹ * c⁻¹ ∈ GLBPrimeCore p H := by
    intro x hx c hc
    obtain ⟨c', hc'C, rfl⟩ := hc
    have hxH := hXH hx
    have hxK : π ⟨x, hxH⟩ ∈ K := by
      have h1 : π ⟨x, hxH⟩ ∈ (X.subgroupOf H).map π :=
        ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hXdef, hd.cfg.map_d1LiftX_eq_inf] at h1
      exact h1.2
    have hcomm' := Subgroup.mem_centralizer_iff.mp hc'C _ hxK
    refine (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hxH⟩ * c' * (⟨x, hxH⟩ : H)⁻¹ * c'⁻¹)).mpr ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm'
  have hJM := perfectCyclicSylow_barM (S := S) (L := M) le_rfl hp hcyc
  have hNSM : Subgroup.normalizer (S : Set G) ⊓ M = H ⊓ M := by rw [hNSH]
  have hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup p A → IsCyclic A :=
    fun A hAD hA => hJM D (hNSM ▸ hDK) hDp A hAD hA
  have hblocks : ∀ L : Subgroup G, IsWeakSBlock M S L →
      barM M ⁅X, X⁆ ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L hL'
    have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      exact h3.mem_normalizer_block_of_five hd.cfg.ind h85 h86 h93 hD2 hK2 hC3' hK5' hp5
        (hXK hx) (orderOf_eq_prime (hpowX x hx) hx1) hL'
    have hDL := h3.le_normalizer_barM_of_perfect hd.cfg.ind hp5 hB3 hL' hDK hDp
    have hLb : barM M L ≠ ⊥ := fun hbot => h3.barM_ne_of_isWeakSBlock hL' (by
      have h1 : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
        barM_mono inf_le_right
      rw [hbot] at h1 ⊢
      exact le_bot_iff.mp h1)
    have hLperf : ⁅barM M L, barM M L⁆ = barM M L :=
      Subgroup.isPerfect_iff.mp (⟨hL'.component.2.2.1⟩ : Group.IsPerfect ↥(barM M L))
    have hzC : zb ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      intro hc
      refine hLb (hZ _ hLperf fun l hl => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hc l hl
    have hPLK : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M (H ⊓ M) :=
      barM_mono (by rw [hNSH]; exact inf_le_inf_left H hL'.le)
    exact h3.commutator_le_centralizer_block h84 h85 h86 h93 hD2 hSch hKF hK2s hK3 hK4 hp5 hcyc
      hL' hXK hXL hpowX hXcard hXnorm hDp hDL hDS hDcyc
      (fun V hVP hVp k hk => hDpart V (hVP.trans hPLK) hVp k hk) hzbD hzbp hzC hZ hXD
  have hcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      barM M ⁅X, X⁆ ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro Lb hLb
    obtain ⟨L, hL2, rfl, hw | hle⟩ := h3.exists_weakSBlock_or_le_inf hLb
    · exact hblocks L hw
    · by_cases hLN : L ≤ GLBPrimeCore p H
      · exact h3.commutator_le_centralizer_compFive hd.cfg.ind hα hβo hp5 hXK hpowX hXnorm hE
          hL2 hLN
      · have hLNp : L ≤ d1PlusCore p H K := hperf L hle hL2.perfect
        have hX1X : ⁅X, X⁆ ≤ X := Subgroup.commutator_le_self X
        exact barM_le_centralizer_of_commutator_mem h3 hL2 (hle.trans inf_le_left) hLN
          (hX1X.trans hXM) (hX1X.trans hXH) (fun x hx l hl => hcommN x (hX1X hx) l (hLNp hl))
  have hodd := fun (s : ℕ) (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p) =>
    h3.commutator_oddCore hG1 hp5 hXM hXcard hpowX (s := s) hs hs2 hsp
  have hY := hd.pCorePreimage_inf_ne_bot_of_core h3 hF.uPrime h84 hD2
    (Subgroup.commutator_le_self X) hX1 hcomp hodd
  obtain ⟨-, -, -, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  apply hWiff.mp hY
  rw [hV, bot_inf_eq]

end CFSG.AGLEmbedding
