module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbLinTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbSection
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroPerf
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbOrbit

public section
namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1PhaseThree.exists_pow_mem_normalizer_block (h : D1PhaseThree p P M H R)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) (hp5 : 5 ≤ p)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {t : G} (htK : t ∈ H ⊓ M) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 3 ∧ t ^ m ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hno
  push Not at hno
  have hmm : ∀ (a b : G) (X : Subgroup G), X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b X
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hinj : Function.Injective fun j : Fin 4 =>
      L.map (MulAut.conj (t ^ (j : ℕ))).toMonoidHom := by
    have hstep : ∀ i j : ℕ, i < j → j < 4 →
        L.map (MulAut.conj (t ^ i)).toMonoidHom = L.map (MulAut.conj (t ^ j)).toMonoidHom →
        False := by
      intro i j hij hj4 he
      have hj : t ^ j = t ^ i * t ^ (j - i) := by rw [← pow_add]; congr 1; omega
      rw [hj, hmm] at he
      have he' := Subgroup.map_injective (MulAut.conj (t ^ i)).injective he
      exact hno (j - i) (by omega) (by omega)
        (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he'.symm)
    intro i j hij
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hlt | heq | hgt
    · exact (hstep i j hlt j.2 hij).elim
    · exact Fin.ext heq
    · exact (hstep j i hgt i.2 hij.symm).elim
  have hle := h.le_pRank_three_of_injective_conj hB3 hL (fun j : Fin 4 => t ^ (j : ℕ))
    (fun j => (H ⊓ M).pow_mem htK _) hinj
  exact h.false_of_four_le_pRank' hind Nat.prime_three (by decide) (by omega) hle

theorem D1OneSmallData.d1LiftX_le_centralizer (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) :
    d1LiftX p H R K ≤ Subgroup.centralizer ({z} : Set G) := by
  have hp := hd.cfg.red.prime
  obtain ⟨hzR, -, hzH, hzc⟩ := hz
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxR : x ∈ R := d1LiftX_le p H R K hx
  have hxH : x ∈ H := d1LiftX_le_H p H R K hx
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hxK : π ⟨x, hxH⟩ ∈ K := by
    have h1 : π ⟨x, hxH⟩ ∈ ((d1LiftX p H R K).subgroupOf H).map π :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hd.cfg.map_d1LiftX_eq_inf] at h1
    exact h1.2
  set c : H := ⟨z, hzH⟩ * ⟨x, hxH⟩ * (⟨z, hzH⟩ : H)⁻¹ * (⟨x, hxH⟩ : H)⁻¹ with hc
  have hc1 : π c = 1 := by
    have hcomm := Subgroup.mem_centralizer_iff.mp hzc _ hxK
    rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hcO := (mk'_primeComplementCore_eq_one_iff p c).mp hc1
  have hcR : (c : G) ∈ R := by
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv]
    exact R.mul_mem (R.mul_mem (R.mul_mem hzR hxR) (R.inv_mem hzR)) (R.inv_mem hxR)
  obtain ⟨n, hn⟩ := hd.cfg.ext.isPGroup ⟨c, hcR⟩
  have hdvd1 : orderOf (c : G) ∣ p ^ n := orderOf_dvd_of_pow_eq_one (by
    simpa using congrArg Subtype.val hn)
  have hdvd2 : orderOf (c : G) ∣ Nat.card (GLBPrimeCore p H) := Subgroup.orderOf_dvd_natCard _ hcO
  have h1 : orderOf (c : G) = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left hdvd1 (Nat.Coprime.pow_left n (glbPrimeCore_coprime p H))) hdvd2
  have h2 : (c : G) = 1 := orderOf_eq_one_iff.mp h1
  simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  have h3 : z * x = x * z := by
    have := congrArg (· * x * z) h2
    simpa [mul_assoc] using this
  exact h3.symm

theorem D1OneSmallData.false_of_posZero_ib_linTwo [Fact p.Prime] (hK7 : KFactOneLieSmallLie)
    (hK8 : KFactSmallBorelSolvable) (hβ : KFactBeta) (hKO : KFactOneLie)
    (hΓ : KFactOneLieBorelSolvable) (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd)
    (hβo : KFactOutElemRank) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hKF : KFactBlockCentRankIb)
    (hK2s : KFactAltSixSevenAutFive) (hK3 : CitedBlockTransvectionCyclic)
    (hK4 : CitedBlockAltNormalizerSq) (hd : D1OneSmallData p P M H R Rbar K)
    (hnIa : ¬ D1SmallIa p H K) (hp7 : 7 ≤ p) (hL : IsSmallLinTwo p K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hSP : D1CzSP p z) (hout : D1CzOutside p z)
    (hV : d1MapPCore p M H = ⊥) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by omega
  obtain ⟨T₁, hT₁, hF, hs, h3⟩ := hd.exists_oneLieFacts hK7 hK8 hp5 (Or.inl hL)
  obtain ⟨t, hmd⟩ := hd.smallMDataP_linTwo hK7 hK8 hp7 hL
  obtain ⟨hzR, hzp, hzH, -⟩ := id hz
  have hzM : z ∈ M := hd.cfg.ext.le_M hzR
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set zb := mkM ⟨z, hzM⟩ with hzb
  set X := d1LiftX p H R K with hXdef
  set S := pCoreOf 2 H with hS
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
  obtain ⟨φ, -⟩ := hd.exists_torus_linTwo h3 hL
  have hXcard : Nat.card X = p ^ 2 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr Multiplicative.toAdd,
      GaloisField.card p 2 (by norm_num)]
  have hXK : X ≤ H ⊓ M := hmd.le_R.trans h3.le_inf
  have hNSH : Subgroup.normalizer (S : Set G) = H := h3.normalizer_twoCore_H
  have hDS : D ≤ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hDK.trans (barM_le_normalizer_barM (inf_le_left.trans hNSH.ge))
  have hJM := perfectCyclicSylow_barM (S := S) (L := M) le_rfl hp hmd.cyc
  have hNSM : Subgroup.normalizer (S : Set G) ⊓ M = H ⊓ M := by rw [hNSH]
  have hDcyc : ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup p A → IsCyclic A :=
    fun A hAD hA => hJM D (hNSM ▸ hDK) hDp A hAD hA
  have hblocks : ∀ L : Subgroup G, IsWeakSBlock M S L →
      barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L hL'
    have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Subgroup.one_mem _
      have hxp : orderOf x = p := by
        have h1 : x ^ p = 1 := hmd.elem.2 x hx
        exact orderOf_eq_prime h1 hx1
      exact h3.mem_normalizer_block_of_five hd.cfg.ind h85 h86 h93 hD2 hK2 hC3' hK5' hp5
        (hXK hx) hxp hL'
    obtain ⟨m, hm1, hm3, htm⟩ :=
      h3.exists_pow_mem_normalizer_block hd.cfg.ind hp5 hB3 hL' hmd.t_mem
    have hmr : ¬ (p + 1) / 2 ∣ m := by
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
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
    exact h3.barM_le_centralizer_of_irr h84 h85 h86 h93 hD2 hSch hKF hK2s hK3 hK4 hp5 hmd.cyc
      hL' hXK hXL hmd.elem hXcard ((H ⊓ M).pow_mem hmd.t_mem m) htm
      (Subgroup.pow_mem _ hmd.t_norm m) (hmd.irr m hmr) hDp hDL hDS hDcyc
      (fun V hVP hVp k hk => hDpart V (hVP.trans hPLK) hVp k hk) hzbD hzbp hzC hZ hXD
  obtain ⟨hcomp, hodd⟩ := hmd.core hα hβo hp5 hblocks
  have hY := hd.pCorePreimage_inf_ne_bot_of_core h3 hF.uPrime h84 hD2 le_rfl
    hd.d1LiftX_ne_bot hcomp hodd
  obtain ⟨-, -, -, -, hWiff⟩ := hd.d1MapPCore_facts h3 h84 hD2
  apply hWiff.mp hY
  rw [hV, bot_inf_eq]

end CFSG.AGLEmbedding
