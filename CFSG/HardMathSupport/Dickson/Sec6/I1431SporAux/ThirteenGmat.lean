module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.InvolutionsZStar
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenCongruence
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThirteenGraph
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenA
public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.CentralizerCIsolation
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

theorem involution_of_isConj_tGmat {t : Gmat} (ht : IsConj tGmat t) : t * t = 1 ∧ t ≠ 1 := by
  have h2 : orderOf t = 2 :=
    (orderOf_eq_of_isConj_thirteen ht).symm.trans CFSG.Monster.Tri.orderOf_tGmat
  refine ⟨?_, ?_⟩
  · have := pow_orderOf_eq_one t
    rw [h2, pow_two] at this
    exact this
  · intro h1
    rw [h1, orderOf_one] at h2
    omega

theorem not_commute_c_of_twoA {t : Gmat} (ht : IsConj tGmat t) :
    t * gw genD13W1 ≠ gw genD13W1 * t := by
  intro htc
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨htt, ht1⟩ := involution_of_isConj_tGmat ht
  have hcx : gw genD13W1 * xGmat = xGmat * gw genD13W1 :=
    Subgroup.mem_centralizer_singleton_iff.1 c_mem_cent
  have hxC : xGmat ∈ Subgroup.centralizer ({gw genD13W1} : Set Gmat) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
  have htH : t ∈ Subgroup.centralizer ({gw genD13W1} : Set Gmat) :=
    Subgroup.mem_centralizer_singleton_iff.2 htc
  have hv : (⟨xGmat, hxC⟩ : Subgroup.centralizer ({gw genD13W1} : Set Gmat)) * ⟨xGmat, hxC⟩ = 1 :=
    Subtype.ext xGmat_mul_self'
  have hv1 : (⟨xGmat, hxC⟩ : Subgroup.centralizer ({gw genD13W1} : Set Gmat)) ≠ 1 := fun h =>
    xGmat_ne_one' (congrArg Subtype.val h)
  have huniq : ∀ s : Subgroup.centralizer ({gw genD13W1} : Set Gmat), s * s = 1 →
      s * ⟨xGmat, hxC⟩ = ⟨xGmat, hxC⟩ * s → s = 1 ∨ s = ⟨xGmat, hxC⟩ := by
    intro s hs hsx
    have hs' : (s : Gmat) * s = 1 := congrArg Subtype.val hs
    have hsx' : (s : Gmat) * xGmat = xGmat * s := congrArg Subtype.val hsx
    have hsc : (s : Gmat) * gw genD13W1 = gw genD13W1 * s :=
      Subgroup.mem_centralizer_singleton_iff.1 s.2
    rcases eq_one_or_eq_xGmat_of_involution hs' hsx' hsc with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hconj := isConj_of_involution_of_zStar hv hv1 huniq (t := ⟨t, htH⟩) (Subtype.ext htt)
    (fun h => ht1 (congrArg Subtype.val h))
  have hconj' : IsConj xGmat t :=
    (Subgroup.subtype (Subgroup.centralizer ({gw genD13W1} : Set Gmat))).map_isConj hconj
  exact not_isConj_xGmat_tGmat (hconj'.trans ht.symm)

theorem isConj_tGmat_of_commute_xE {u : Gmat} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hux : u * gw thirteenX = gw thirteenX * u) : IsConj tGmat u := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hu : orderOf u = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  rcases CFSG.Monster.Existence.Census.generated_group_two_involution_classes u hu with h | h
  swap
  · exact h
  exfalso
  obtain ⟨h, hh⟩ := isConj_iff.1 h
  have hy : h⁻¹ * gw thirteenX * h ∈ cent xGmat := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : xGmat = h⁻¹ * u * h := by rw [← hh]; group
    rw [hx]
    calc h⁻¹ * gw thirteenX * h * (h⁻¹ * u * h) = h⁻¹ * (gw thirteenX * u) * h := by group
      _ = h⁻¹ * (u * gw thirteenX) * h := by rw [hux]
      _ = h⁻¹ * u * h * (h⁻¹ * gw thirteenX * h) := by group
  have hyo : orderOf (h⁻¹ * gw thirteenX * h) = 13 := by
    have := orderOf_conj_eq' h⁻¹ (gw thirteenX)
    rw [inv_inv] at this
    rw [this, orderOf_xE]
  obtain ⟨g, hg, k, hk⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_mem_conj_pow_of_factorization_eq_one
    (K := cent xGmat) factorization_cent_xGmat_thirteen c_mem_cent hy orderOf_c13 hyo
  have hk13 : k % 13 ≠ 0 := by
    intro h0
    have hck : gw genD13W1 ^ k = 1 := by
      rw [← pow_mod_orderOf, orderOf_c13, h0, pow_zero]
    rw [hck, mul_one, mul_inv_cancel] at hk
    have := orderOf_xE
    have hxe : gw thirteenX = 1 := by
      have h1 : gw thirteenX = h * (h⁻¹ * gw thirteenX * h) * h⁻¹ := by group
      rw [h1, hk]
      group
    rw [hxe, orderOf_one] at this
    omega
  obtain ⟨hj1sq, -, -, hj1x, -, hT1, -, -, hj1ne, -, -, -⟩ := thirteen_a_facts
  have hj1t : gw tj1W * gw j1W * (gw tj1W)⁻¹ = tGmat := by
    rw [hT1, mul_inv_cancel_right, gw_tStarW]
  set j := (h * g)⁻¹ * gw j1W * (h * g) with hj
  have hjconj : IsConj tGmat j := by
    have h1 : IsConj tGmat (gw j1W) := (isConj_iff.2 ⟨gw tj1W, hj1t⟩).symm
    exact h1.trans (isConj_iff.2 ⟨(h * g)⁻¹, by rw [hj]; group⟩)
  have hxE : gw thirteenX = (h * g) * gw genD13W1 ^ k * (h * g)⁻¹ := by
    have h1 : gw thirteenX = h * (h⁻¹ * gw thirteenX * h) * h⁻¹ := by group
    rw [h1, hk]
    group
  have hjk : j * gw genD13W1 ^ k = gw genD13W1 ^ k * j := by
    have e1 : j * gw genD13W1 ^ k = (h * g)⁻¹ * (gw j1W * gw thirteenX) * (h * g) := by
      rw [hj, hxE]; group
    have e2 : gw genD13W1 ^ k * j = (h * g)⁻¹ * (gw thirteenX * gw j1W) * (h * g) := by
      rw [hj, hxE]; group
    rw [e1, e2, hj1x]
  have hjc : j * gw genD13W1 = gw genD13W1 * j :=
    commute_of_commute_pow_thirteen orderOf_c13 hk13 hjk
  exact not_commute_c_of_twoA hjconj hjc

theorem hlines_Gmat : ∀ e ∈ censusLines, ∃ W : Gmat,
    W * (gw genD13W0 ^ e.a * gw genD13W2 ^ e.b) * W⁻¹ =
      (if e.toC then gw genD13W1 else gw thirteenX) ^ e.lam := by
  intro e he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlines⟩ := thirteen_a_facts
  refine ⟨gw (lineConjW e), ?_⟩
  have h := hlines e he
  have hrep : gw (lineRepW e) = gw genD13W0 ^ e.a * gw genD13W2 ^ e.b := by
    rw [lineRepW, gw_append, gw_powL13, gw_powL13]
  have htgt : gw (lineTargetW e) = if e.toC then gw genD13W1 else gw thirteenX := by
    unfold lineTargetW
    split_ifs <;> rfl
  rw [← hrep, h, ← htgt, mul_inv_cancel_right]

theorem ncard_twoA_class : {t : Gmat | IsConj tGmat t}.ncard = 97239461142009186000 := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  have h1 := card_isConj_mul_card_centralizer tGmat
  rw [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.natCard_centralizer_tGmat,
    CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder] at h1
  have h2 : {t : Gmat | IsConj tGmat t}.ncard = Nat.card {h : Gmat // IsConj tGmat h} := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h3 : Nat.card {h : Gmat // IsConj tGmat h} = monsterOrder / (2 * monsterBabyOrder) :=
    (Nat.div_eq_of_eq_mul_left (by norm_num [monsterBabyOrder]) h1.symm).symm
  rw [h2, h3]
  norm_num [monsterOrder, monsterBabyOrder]

theorem invComm_xE_congruence :
    ∃ K : ℕ, 12 * 97239461142009186000 = 1248 * (invComm (gw thirteenX)).ncard + 13 ^ 3 * K := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨hg13, hd13, hc13, hcg, hcd, hdg, hc1, -⟩ := d13_gw_facts
  have hD : ∀ w t : Gmat, t ∈ {t : Gmat | IsConj tGmat t} →
      w * t * w⁻¹ ∈ {t : Gmat | IsConj tGmat t} :=
    fun w t ht => ht.trans (isConj_iff.2 ⟨w, rfl⟩)
  have hDstab : ∀ t ∈ {t : Gmat | IsConj tGmat t},
      ¬ 13 ^ 2 ∣ Nat.card (Subgroup.centralizer ({t} : Set Gmat)) := by
    intro t ht
    obtain ⟨w, hw⟩ := isConj_iff.1 ht
    rw [← hw, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.card_centralizer_conj_eq,
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.natCard_centralizer_tGmat]
    norm_num [monsterBabyOrder]
  obtain ⟨K, hK⟩ := congruence_of_heis hg13 hd13 hc13 hc1 hcg hcd hdg orderOf_xE hlines_Gmat hD
    hDstab (fun t ht => not_commute_c_of_twoA ht)
  have hset : {t | t ∈ {t : Gmat | IsConj tGmat t} ∧ t * gw thirteenX = gw thirteenX * t} =
      invComm (gw thirteenX) := by
    ext t
    constructor
    · rintro ⟨ht, htx⟩
      obtain ⟨htt, ht1⟩ := involution_of_isConj_tGmat ht
      exact ⟨htt, ht1, htx⟩
    · rintro ⟨ht2, ht1, htx⟩
      exact ⟨isConj_tGmat_of_commute_xE ht2 ht1 htx, htx⟩
  rw [ncard_twoA_class, hset] at hK
  exact ⟨K, hK⟩

theorem invComm_xE_mod : (invComm (gw thirteenX)).ncard % 169 = 117 := by
  obtain ⟨K, hK⟩ := invComm_xE_congruence
  omega

theorem not_five_dvd_invComm_xE (hle : (invComm (gw thirteenX)).ncard ≤ 451) :
    ¬ 5 ∣ (invComm (gw thirteenX)).ncard := by
  have := invComm_xE_mod
  omega

end CFSG.HardMathSupport.Dickson.Sec6.I1431
