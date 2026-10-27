module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericUnique
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCentralPoint
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTheoremE

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem generic_central_abelian (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hL : GL83GenericLayer G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G}
    {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hx : IsGenericPoint p P M x) :
    (∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) ∧
      (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧ IsMulCommutative (P : Subgroup G) := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hU := zpowers_eq_of_isGenericPoint hS hD1 hU0 hL hp hM hfail hIH hx
  have hPx := le_centralizer_of_unique_generic hPM hx hU
  obtain ⟨h5, hfx, mx, hmx, ⟨ex⟩⟩ := hL p hp P M hM hfail hIH x hx
  obtain ⟨hxP, ⟨-, hx1, hxp, -, -⟩, hsylx, hrkx⟩ := id hx
  have hSab : IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    isMulCommutative_of_isSylowOf_mulEquiv_psl h5 hsylx (rankThreeLayer_le _)
      (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
      (fun c hc => mem_centralizer_singleton_iff.mp hc) hrkx.le hmx ex
  rw [inf_of_le_left hPx] at hSab
  exact ⟨hU, hPx, hSab⟩

theorem centralizer_le_of_not_mem_zpowers (hS : Setting G) {p : ℕ}
    [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G}
    (hU : ∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x)
    (hPab : IsMulCommutative (P : Subgroup G))
    {y : G} (hyP : y ∈ (P : Subgroup G)) (hy1 : y ≠ 1) (hyp : y ^ p = 1) (hyx : y ∉ zpowers x) :
    centralizer ({y} : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hPC : (P : Subgroup G) ≤ centralizer ({y} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hPab.is_comm.comm ⟨g, hg⟩ ⟨y, hyP⟩))
  have hinf : (P : Subgroup G) ⊓ centralizer ({y} : Set G) = P := inf_of_le_left hPC
  by_contra hyM
  refine hyx (hU y ⟨hyP, ⟨hPM hyP, hy1, hyp, hP3.ge.trans (pRank_mono p hprime.one_lt hPC), hyM⟩,
    ?_, by rw [hinf, hP3]⟩ ▸ mem_zpowers y)
  rw [hinf]
  exact ⟨P.subtype hPC, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPC]⟩

theorem le_of_isTwoLocal_of_gamma_one_le (hS : Setting G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp5 : 5 ≤ p)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {R H : Subgroup G} (hH : IsTwoLocal H) (hRH : R ≤ H) (hRM : R ≤ M) (hRp : IsPGroup p R)
    (hRnc : ¬ IsCyclic R) (hΓ : rankThreeGamma 1 p R ≤ M) : H ≤ M :=
  hD2 M hM.1 (fun p' hp' P' hM' => hU0 p' hp' P' M hM')
    (fun h3 => absurd (eq_three_of_three_mem_sigmaA hS.rank h3 hp) (by omega))
    p hp P hM H R hH hRH hRM hRp hRnc hΓ

omit [Finite G] in
theorem not_isCyclic_of_elemAbelian {p k : ℕ} [Fact p.Prime] {R : Subgroup G}
    (hR : IsElemAbelian p R) (hc : Nat.card R = p ^ k) (hk : 2 ≤ k) : ¬ IsCyclic R := by
  have hprime : p.Prime := Fact.out
  intro hcyclic
  obtain ⟨g, hg⟩ := hcyclic.exists_generator
  have hdvd : p ^ k ∣ p := by
    rw [← hc, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (hR.2 g g.2))
  have hle := (Nat.pow_le_pow_right hprime.pos hk).trans (Nat.le_of_dvd hprime.pos hdvd)
  nlinarith [hprime.two_le]

theorem mem_zpowers_layer_eq_one {p : ℕ} [Fact p.Prime] {x y : G}
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) {L : Subgroup G} (hxL : x ∉ L) (hyL : y ∈ L)
    (hyx : y ∈ zpowers x) : y = 1 := by
  by_contra hy1
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hzg : zpowers x = zpowers y := eq_zpowers_of_card_eq_prime hXc hyx hy1
  exact hxL (zpowers_le.mpr hyL (hzg ▸ mem_zpowers x))

theorem layer_le_of_isTwoLocal (hS : Setting G) (hD1 : TheoremD1 G)
    (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hx : IsGenericPoint p P M x) {H : Subgroup G} (hH : IsTwoLocal H)
    (hLH : rankThreeLayer (centralizer ({x} : Set G)) ≤ H) : False := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hU, hPx, hPab⟩ := generic_central_abelian hS hD1 hU0 hL hp hM hfail hIH hx
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨h5, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hx
  obtain ⟨hxL, hpos⟩ := layer_data_of_isGenericPoint hx hm2 e
  obtain ⟨hxP, ⟨-, hx1, hxp, -, hxCM⟩, hsyl, -⟩ := id hx
  have hLM : ¬ rankThreeLayer (centralizer ({x} : Set G)) ≤ M :=
    not_rankThreeLayer_le_of_mulEquiv_psl hS hU0 hp hM hxCM hsyl hm2 e
  obtain ⟨R, hRU, hRe, hRc⟩ := pRank_attained p
    (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓ rankThreeLayer (centralizer ({x} : Set G)))
    (by omega)
  have hRP : R ≤ (P : Subgroup G) := hRU.trans (inf_le_left.trans inf_le_left)
  have hRL : R ≤ rankThreeLayer (centralizer ({x} : Set G)) := hRU.trans inf_le_right
  have hΓ : rankThreeGamma 1 p R ≤ M := by
    refine gamma_one_le_of_forall_centralizer_le hS hU0 hp hM hRP fun y hyR hy1 hyp => ?_
    refine centralizer_le_of_not_mem_zpowers hS hp hM hU hPab (hRP hyR) hy1 hyp fun hyx => hy1 ?_
    exact mem_zpowers_layer_eq_one hx1 hxp hxL (hRL hyR) hyx
  have hRnc : ¬ IsCyclic R := not_isCyclic_of_elemAbelian hRe hRc (by omega)
  exact hLM (hLH.trans (le_of_isTwoLocal_of_gamma_one_le hS hD2 hU0 hp h5 hM hH (hRL.trans hLH)
    (hRP.trans hPM) (elementary_isPGroup p R hRe) hRnc hΓ))

theorem eq_bot_of_isPGroup_two_of_layer_le_normalizer (hS : Setting G) (hD1 : TheoremD1 G)
    (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hx : IsGenericPoint p P M x) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hN : rankThreeLayer (centralizer ({x} : Set G)) ≤ normalizer (W : Set G)) : W = ⊥ := by
  by_contra hWne
  exact layer_le_of_isTwoLocal hS hD1 hD2 hU0 hL hp hM hfail hIH hx
    (H := normalizer (W : Set G)) ⟨W, hWne, hW, rfl⟩ hN

theorem not_two_dvd_card_centralizer_layer (hS : Setting G) (hD1 : TheoremD1 G)
    (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p) {x : G}
    (hx : IsGenericPoint p P M x) :
    ¬ 2 ∣ Nat.card ↥(centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
      Set G)) := by
  intro heven
  obtain ⟨W, hW⟩ := exists_isSylowOf 2 (centralizer ((rankThreeLayer (centralizer ({x} : Set G)) :
    Subgroup G) : Set G))
  have hWne : W ≠ ⊥ := by
    intro hW1
    have hcard := hW.card_eq
    rw [hW1, card_bot] at hcard
    have hpos2 : 0 < (Nat.card ↥(centralizer ((rankThreeLayer (centralizer ({x} : Set G)) :
        Subgroup G) : Set G))).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' heven
    exact (Nat.one_lt_two_pow hpos2.ne').ne' hcard.symm
  have hLW : rankThreeLayer (centralizer ({x} : Set G)) ≤ centralizer (W : Set G) :=
    Subgroup.le_centralizer_iff.mp hW.le
  exact hWne (eq_bot_of_isPGroup_two_of_layer_le_normalizer hS hD1 hD2 hU0 hL hp hM hfail hIH hx
    hW.isPGroup (hLW.trans (centralizer_le_normalizer _)))

end CFSG.LocalAnalysis.RankThreeTheoremC
