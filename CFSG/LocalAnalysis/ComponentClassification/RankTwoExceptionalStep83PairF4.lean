module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83PairReduce
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4Two
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.PairF4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover (xr)
open CFSG.LieType.Ree (ReeTag)
open scoped commutatorElement

variable {K : Type} [Field K]

theorem commute_of_mem_closure {G : Type*} [Group G] {s y : G} (hD : Step83Pair.OddCommute s y)
    {x : G} (hx : x ∈ closure {c : G | c * s = s * c ∧ Odd (orderOf c)}) : x * y = y * x := by
  have h : Commute x y := by
    induction hx using closure_induction with
    | mem c hc => exact hD c hc.1 hc.2
    | one => exact Commute.one_left y
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  exact h.eq

theorem odd_orderOf_of_pow_three {G : Type*} [Group G] {g : G} (h : g ^ 3 = 1) :
    Odd (orderOf g) :=
  Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h)

theorem units_neg_one [CharP K 2] : (-1 : Kˣ) = 1 :=
  Units.ext (by rw [Units.val_neg, Units.val_one, CharTwo.neg_eq])

theorem weylElt_mul_self_two
    [CharP K 2] (i : Fin Tag.F4.rank) :
    weylElt .F4 K i 1 * weylElt .F4 K i 1 = 1 := by
  rw [weylElt_one_mul_self, units_neg_one, torusElt_one]

theorem weylElt_eq_xyx
    [CharP K 2] {j a b : ℕ}
    (ha : orbitCertRoot .F4 a = Pi.single (f4CollNode j) 1)
    (hb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1) :
    weylElt .F4 K (f4CollNode j) 1 = f4x K a 1 * f4x K b 1 * f4x K a 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, f4x, f4x, ha, hb, pinnedX_single,
    pinnedX_neg_single, inv_one, Units.val_one, CharTwo.neg_eq]

theorem weylElt_eq_yxy
    [CharP K 2] {j a b : ℕ}
    (ha : orbitCertRoot .F4 a = Pi.single (f4CollNode j) 1)
    (hb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1) :
    weylElt .F4 K (f4CollNode j) 1 = f4x K b 1 * f4x K a 1 * f4x K b 1 := by
  rw [weylElt_eq_yUnit_mul, f4x, f4x, ha, hb, pinnedX_single, pinnedX_neg_single,
    CharTwo.neg_eq]

theorem f4x_mul_f4x_pow_three
    [CharP K 2] {j a b : ℕ}
    (ha : orbitCertRoot .F4 a = Pi.single (f4CollNode j) 1)
    (hb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1) :
    (f4x K a 1 * f4x K b 1) ^ 3 = 1 := by
  calc (f4x K a 1 * f4x K b 1) ^ 3 =
      (f4x K a 1 * f4x K b 1 * f4x K a 1) * (f4x K b 1 * f4x K a 1 * f4x K b 1) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [← weylElt_eq_xyx ha hb, ← weylElt_eq_yxy ha hb, weylElt_mul_self_two]

theorem weylElt_mul_f4x
    [CharP K 2] {j a b : ℕ}
    (ha : orbitCertRoot .F4 a = Pi.single (f4CollNode j) 1)
    (hb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1) :
    weylElt .F4 K (f4CollNode j) 1 * f4x K a 1 = f4x K a 1 * f4x K b 1 := by
  rw [weylElt_eq_xyx ha hb, mul_assoc, f4x_one_mul_self, mul_one]

theorem root24 : orbitCertRoot .F4 24 = Pi.single (f4CollNode 3) 1 := by decide
theorem root23 : orbitCertRoot .F4 23 = -Pi.single (f4CollNode 3) 1 := by decide
theorem root33 : orbitCertRoot .F4 33 = Pi.single (f4CollNode 0) 1 := by decide
theorem root14 : orbitCertRoot .F4 14 = -Pi.single (f4CollNode 0) 1 := by decide

theorem commute_f4x_of_rule
    (hK : Nat.card K = 2) {a b : ℕ} (ha : a < 48) (hb : b < 48)
    (h : f4CommuteRule a b = true) (s t : K) : f4x K a s * f4x K b t = f4x K b t * f4x K a s := by
  have e := congrArg Subtype.val (f4_commute_sound (K := K) hK ha hb h)
  simp only [Subgroup.coe_mul] at e
  rcases eq_zero_or_eq_one_of_card_two hK s with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card_two hK t with rfl | rfl
  · rw [f4x_zero, f4x_zero]
  · rw [f4x_zero, one_mul, mul_one]
  · rw [f4x_zero, one_mul, mul_one]
  · exact e


theorem eq_of_oddCommute_t
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y : adjointGroup .F4 K} (hD : Step83Pair.OddCommute (xr (orbitCertRoot .F4 47)) y) :
    y = 1 ∨ y = xr (orbitCertRoot .F4 47) := by
  have hU : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ posUnipotent .F4 K → u * y = y * u :=
    fun u hu => commute_of_mem_closure hD (posUnipotent_le_closure_odd_longRoot_two hK hu)
  have hyU := mem_posUnipotent_of_commute_heightSeries hK fun u hu =>
    (hU u (heightSeries_le_posUnipotent 3 hu)).symm
  obtain ⟨c, d, hcd⟩ := CFSG.Monster.B.GSide.f4_mem_of_commute_rootElts hyU fun p hp hp' => by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val
      (hU ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩ (f4x_mem_posUnipotent ⟨hp, hp'⟩ 1))).symm
  set h : adjointGroup .F4 K := xr (orbitCertRoot .F4 24) * xr (orbitCertRoot .F4 23) with hh
  have hh3 : h ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hh, Subgroup.coe_mul]
    exact f4x_mul_f4x_pow_three root24 root23)
  have hht : h * xr (orbitCertRoot .F4 47) = xr (orbitCertRoot .F4 47) * h := by
    rw [hh, mul_assoc, f4_commute_sound hK (by norm_num) (by norm_num) (by decide +kernel),
      ← mul_assoc, f4_commute_sound hK (by norm_num) (by norm_num) (by decide +kernel), mul_assoc]
  have hhy := hD h hht (odd_orderOf_of_pow_three hh3)
  have h24y := hU (xr (orbitCertRoot .F4 24)) (f4x_mem_posUnipotent ⟨le_rfl, by norm_num⟩ 1)
  have hn : weylElt .F4 K (f4CollNode 3) 1 * (y : ModGL .F4 K) =
      (y : ModGL .F4 K) * weylElt .F4 K (f4CollNode 3) 1 := by
    have e : weylElt .F4 K (f4CollNode 3) 1 =
        (h * xr (orbitCertRoot .F4 24) : adjointGroup .F4 K) := by
      rw [hh, Subgroup.coe_mul, Subgroup.coe_mul, weylElt_eq_xyx root24 root23]
      rfl
    rw [e, ← Subgroup.coe_mul, ← Subgroup.coe_mul, mul_assoc, h24y, ← mul_assoc, hhy, mul_assoc]
  have key : weylElt .F4 K (f4CollNode 3) 1 * (y : ModGL .F4 K) *
      (weylElt .F4 K (f4CollNode 3) 1)⁻¹ = y := by
    rw [hn, mul_inv_cancel_right]
  have e44 := weylElt_mul_f4x_mul_inv (K := K) (j := 3) (p := 44) (by norm_num) (by norm_num) c
  have e47 := weylElt_mul_f4x_mul_inv (K := K) (j := 3) (p := 47) (by norm_num) (by norm_num) d
  rw [show f4CollRefl 3 44 = 43 from rfl] at e44
  rw [show f4CollRefl 3 47 = 47 from rfl] at e47
  have hprod : weylElt .F4 K (f4CollNode 3) 1 * (f4x K 44 c * f4x K 47 d) *
      (weylElt .F4 K (f4CollNode 3) 1)⁻¹ =
      (weylElt .F4 K (f4CollNode 3) 1 * f4x K 44 c * (weylElt .F4 K (f4CollNode 3) 1)⁻¹) *
        (weylElt .F4 K (f4CollNode 3) 1 * f4x K 47 d * (weylElt .F4 K (f4CollNode 3) 1)⁻¹) := by
    group
  rw [e44, e47, hcd, key] at hprod
  have hconj : f4x K 43 c * f4x K 47 d = f4x K 44 c * f4x K 47 d := hprod.symm.trans hcd.symm
  have hc : c = 0 := eq_zero_of_f4x_eq ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num) (by decide +kernel) (mul_right_cancel hconj)
  subst hc
  rw [f4x_zero, one_mul] at hcd
  rcases eq_zero_or_eq_one_of_card_two hK d with rfl | rfl
  · exact Or.inl (Subtype.ext (by rw [← hcd, f4x_zero]; rfl))
  · exact Or.inr (Subtype.ext (by rw [← hcd]; rfl))

theorem eq_of_oddCommute_u
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y : adjointGroup .F4 K} (hD : Step83Pair.OddCommute (xr (orbitCertRoot .F4 44)) y) :
    y = 1 ∨ y = xr (orbitCertRoot .F4 44) := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have h44 : (f4Phi (K := K)) (xr (orbitCertRoot .F4 44)) = xr (orbitCertRoot .F4 47) :=
    (f4Phi_f4x_47_44 (K := K)).2
  have hD' := Step83Pair.oddCommute_map (f4Phi (K := K)) hD
  rw [h44] at hD'
  rcases eq_of_oddCommute_t hK hD' with h | h
  · left
    exact (f4Phi (K := K)).injective (by rw [h, map_one])
  · right
    exact (f4Phi (K := K)).injective (by rw [h, h44])


theorem eq_of_oddCommute_tu
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y : adjointGroup .F4 K}
    (hD : Step83Pair.OddCommute (xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)) y) :
    y = 1 ∨ y = xr (orbitCertRoot .F4 47) ∨ y = xr (orbitCertRoot .F4 44) ∨
      y = xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : (f4MidJ : Set (Fin (f4RootDatum K).rank)) ≠ Set.univ := by
    intro h
    have h0 := Set.eq_univ_iff_forall.1 h
      (⟨0, CFSG.Blueprint.Chevalley.Tag.rank_pos .F4⟩ : Fin (f4RootDatum K).rank)
    change (0 : ℕ) = 1 ∨ (0 : ℕ) = 2 at h0
    omega
  set t' : (f4RootDatum K).group := xr (orbitCertRoot .F4 47) * xr (orbitCertRoot .F4 44)
  set y' : (f4RootDatum K).group := y with hy'
  have hD' : Step83Pair.OddCommute t' y' := hD
  have hR : ∀ u ∈ ((f4RootDatum K).radicalIn f4MidJ).map
      (MulAut.conj (1 : (f4RootDatum K).group)).toMonoidHom, u * y' = y' * u :=
    fun u hu => commute_of_mem_closure hD'
      (parabolicRadical_mid_le_closure_odd hK (mem_map_radicalIn_one_iff.1 hu))
  obtain ⟨hZ, -, -, hpt⟩ := (f4RootDatum K).radical_facts 2 hJ
  have hpt' := pointwise_stabilizer_map_conj (f4RootDatum K).conj_range_le_actors hpt 1
  obtain ⟨z, hz, hzy⟩ := (hpt' (MulAut.conj y')).1
    ⟨(f4RootDatum K).conj_range_le_actors ⟨y', rfl⟩, fun q hq => by
      rw [MulAut.conj_apply, ← hR q hq, mul_inv_cancel_right]⟩
  have hyz : z = y' := UnbalancedCatalog.conj_injective hZ hzy
  obtain ⟨hzR, hzc⟩ := mem_map_center_subtype_iff.1 hz
  obtain ⟨c, d, hcd⟩ := exists_of_commute_parabolicRadical_mid (mem_map_radicalIn_one_iff.1 hzR)
    fun p hp => congrArg Subtype.val (hzc ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩
      (mem_map_radicalIn_one_iff.2 (f4x_mem_parabolicRadical_mid hp 1)))
  have hy : (y : ModGL .F4 K) = f4x K 44 c * f4x K 47 d := by
    rw [hcd, hyz]
  have hcomm : f4x K 44 1 * f4x K 47 1 = f4x K 47 1 * f4x K 44 1 :=
    (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 44) (q := 47)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1).eq
  rcases eq_zero_or_eq_one_of_card_two hK c with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card_two hK d with rfl | rfl
  · exact Or.inl (Subtype.ext (by rw [hy, f4x_zero, f4x_zero, one_mul]; rfl))
  · exact Or.inr (Or.inl (Subtype.ext (by rw [hy, f4x_zero, one_mul]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hy, f4x_zero, mul_one]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [hy, hcomm]; rfl))))


theorem pair_kill
    [Finite K] [CharP K 2] {j g b p q : ℕ} (hj : j < 4)
    (hg : orbitCertRoot .F4 g = Pi.single (f4CollNode j) 1)
    (hb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1)
    (hp : 24 ≤ p ∧ p ≤ 47) (hq : 24 ≤ q ∧ q ≤ 47) (hpq : q ≠ p)
    (hcomm : ∀ c : K, ⁅f4x K g 1, f4x K p c⁆ = f4x K q c)
    (hgq : ∀ d : K, f4x K g 1 * f4x K q d = f4x K q d * f4x K g 1)
    (hsp : f4CollRefl j p = q) (hsq : f4CollRefl j q = p)
    (hht : height (orbitCertRoot .F4 p) ≤ height (orbitCertRoot .F4 q)) {c d : K}
    (h : f4x K g 1 * f4x K b 1 * (f4x K p c * f4x K q d) =
      f4x K p c * f4x K q d * (f4x K g 1 * f4x K b 1)) : c = 0 ∧ d = 0 := by
  set n := weylElt .F4 K (f4CollNode j) 1 with hn
  have hng : n * f4x K g 1 = f4x K g 1 * f4x K b 1 := weylElt_mul_f4x hg hb
  have hgp : f4x K g 1 * f4x K p c * (f4x K g 1)⁻¹ = f4x K q c * f4x K p c := by
    rw [← hcomm c, commutatorElement_def, inv_mul_cancel_right]
  have hgq' : f4x K g 1 * f4x K q d * (f4x K g 1)⁻¹ = f4x K q d := by
    rw [hgq d, mul_inv_cancel_right]
  have ep := weylElt_mul_f4x_mul_inv (K := K) hj (by omega : p < 48) c
  have eq' := weylElt_mul_f4x_mul_inv (K := K) hj (by omega : q < 48) c
  have ed := weylElt_mul_f4x_mul_inv (K := K) hj (by omega : q < 48) d
  rw [hsp] at ep
  rw [hsq] at eq' ed
  have hconj : (n * f4x K g 1) * (f4x K p c * f4x K q d) * (n * f4x K g 1)⁻¹ =
      f4x K p c * f4x K q d := by
    rw [hng, h, mul_inv_cancel_right]
  have hcalc : (n * f4x K g 1) * (f4x K p c * f4x K q d) * (n * f4x K g 1)⁻¹ =
      f4x K p c * f4x K q c * f4x K p d := by
    calc (n * f4x K g 1) * (f4x K p c * f4x K q d) * (n * f4x K g 1)⁻¹ =
        n * ((f4x K g 1 * f4x K p c * (f4x K g 1)⁻¹) *
          (f4x K g 1 * f4x K q d * (f4x K g 1)⁻¹)) * n⁻¹ := by group
      _ = (n * f4x K q c * n⁻¹) * (n * f4x K p c * n⁻¹) * (n * f4x K q d * n⁻¹) := by
        rw [hgp, hgq']
        group
      _ = f4x K p c * f4x K q c * f4x K p d := by rw [ep, eq', ed]
  have e1 : f4x K q c * f4x K p d = f4x K q d := by
    have e := hcalc.symm.trans hconj
    rw [mul_assoc] at e
    exact mul_left_cancel e
  have hd : d = 0 := by
    have e := congrArg (rootCoord (f4_isRoot_pos hp)) e1
    rw [rootCoord_mul _ (f4x_mem_heightSeries hq hht c) (f4x_mem_heightSeries hp le_rfl d),
      rootCoord_f4x hp hq hht, rootCoord_f4x hp hp le_rfl, rootCoord_f4x hp hq hht,
      ite_eq_right hpq, ite_eq_left rfl, ite_eq_right hpq, zero_add] at e
    exact e
  subst hd
  refine ⟨?_, rfl⟩
  rw [f4x_zero, f4x_zero, mul_one] at e1
  have e := congrArg (rootCoord (f4_isRoot_pos hq)) e1
  rw [rootCoord_f4x hq hq le_rfl, ite_eq_left rfl, rootCoord_one] at e
  exact e

theorem f4x_comm_24_43
    [CharP K 2] (c : K) : ⁅f4x K 24 1, f4x K 43 c⁆ = f4x K 44 c := by
  have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K 24 43 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 c
  have e : (f4OddCommutatorFactors.lookup (24, 43)).getD [] = [(1, 1, 44)] := by decide +kernel
  rw [e] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    pow_one, one_mul] at h
  exact h

theorem f4x_comm_33_46
    [CharP K 2] (c : K) : ⁅f4x K 33 1, f4x K 46 c⁆ = f4x K 47 c := by
  have h := f4_even_positive_root_commutator_table.{0}.2.2.2.2 K 33 46 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 c
  have e : (f4OddCommutatorFactors.lookup (33, 46)).getD [] = [(1, 1, 47)] := by decide +kernel
  rw [e] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow,
    pow_one, one_mul] at h
  exact h


theorem commute_pair_rule
    (hK : Nat.card K = 2) {a b p : ℕ} (ha : a < 48) (hb : b < 48)
    (hp : p < 48) (h1 : f4CommuteRule a p = true) (h2 : f4CommuteRule b p = true) (c : K) :
    Commute (f4x K a 1 * f4x K b 1) (f4x K p c) := by
  change f4x K a 1 * f4x K b 1 * f4x K p c = f4x K p c * (f4x K a 1 * f4x K b 1)
  rw [mul_assoc, commute_f4x_of_rule hK hb hp h2, ← mul_assoc, commute_f4x_of_rule hK ha hp h1,
    mul_assoc]

theorem commute_of_commute_mul {G : Type*} [Group G] {h A B : G} (hA : Commute h A)
    (hAB : Commute h (A * B)) : Commute h B := by
  have e : A * (h * B) = A * (B * h) := by
    rw [← mul_assoc, ← hA.eq, mul_assoc, hAB.eq, mul_assoc]
  exact mul_left_cancel e

theorem commute_of_commute_mul_right {G : Type*} [Group G] {h A B : G} (hB : Commute h B)
    (hAB : Commute h (A * B)) : Commute h A := by
  have e : h * A * B = A * h * B := by
    calc h * A * B = h * (A * B) := mul_assoc _ _ _
      _ = A * B * h := hAB.eq
      _ = A * (h * B) := by rw [mul_assoc, ← hB.eq]
      _ = A * h * B := (mul_assoc _ _ _).symm
  exact mul_right_cancel e

theorem commute_of_oddCommute_v
    [CharP K 2] (hK : Nat.card K = 2) {a b j : ℕ} (ha : a < 48)
    (hb : b < 48) (hra : orbitCertRoot .F4 a = Pi.single (f4CollNode j) 1)
    (hrb : orbitCertRoot .F4 b = -Pi.single (f4CollNode j) 1) (ha1 : f4CommuteRule a 41 = true)
    (ha2 : f4CommuteRule a 45 = true) (hb1 : f4CommuteRule b 41 = true)
    (hb2 : f4CommuteRule b 45 = true) {y : adjointGroup .F4 K}
    (hD : Step83Pair.OddCommute (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) y) :
    Commute (f4x K a 1 * f4x K b 1) (y : ModGL .F4 K) := by
  set h : adjointGroup .F4 K := xr (orbitCertRoot .F4 a) * xr (orbitCertRoot .F4 b) with hh
  have h3 : h ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hh, Subgroup.coe_mul]
    exact f4x_mul_f4x_pow_three hra hrb)
  have hv : h * (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) =
      (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) * h := by
    refine Subtype.ext ?_
    simp only [hh, Subgroup.coe_mul]
    exact ((commute_pair_rule hK ha hb (by norm_num) ha1 hb1 1).mul_right
      (commute_pair_rule hK ha hb (by norm_num) ha2 hb2 1)).eq
  have e := congrArg Subtype.val (hD h hv (odd_orderOf_of_pow_three h3))
  simp only [hh, Subgroup.coe_mul] at e
  exact e

theorem eq_of_oddCommute_v
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {y : adjointGroup .F4 K}
    (hD : Step83Pair.OddCommute (xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45)) y) :
    y = 1 ∨ y = xr (orbitCertRoot .F4 41) ∨ y = xr (orbitCertRoot .F4 45) ∨
      y = xr (orbitCertRoot .F4 41) * xr (orbitCertRoot .F4 45) := by
  have hU3 : ∀ u : adjointGroup .F4 K, (u : ModGL .F4 K) ∈ heightSeries .F4 K 3 →
      u * y = y * u :=
    fun u hu => commute_of_mem_closure hD (heightSeries_three_le_closure_odd_classV_two hK hu)
  have hyU := mem_posUnipotent_of_commute_heightSeries hK fun u hu => (hU3 u hu).symm
  obtain ⟨c, hc⟩ := exists_f4_coords hyU
  have h0 := f4_coords_eq_zero_of_commute_classV c fun p hp => by
    have hp' : 24 ≤ p ∧ p ≤ 47 ∧ 3 ≤ height (orbitCertRoot .F4 p) := by
      revert p hp
      decide +kernel
    rw [← hc, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val (hU3 ⟨f4x K p 1, pinnedX_mem_adjointGroup _ _⟩
      (f4x_mem_heightSeries (k := 29) ⟨hp'.1, hp'.2.1⟩
        (le_trans (by decide +kernel) hp'.2.2) 1))).symm
  have hcover : ∀ i ∈ f4PosList, decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ)) = false →
      i ∈ f4KillOrderV := by
    decide
  have hy6 : (y : ModGL .F4 K) = f4x K 41 (c 41) * f4x K 43 (c 43) * f4x K 44 (c 44) *
      f4x K 45 (c 45) * (f4x K 46 (c 46) * f4x K 47 (c 47)) := by
    rw [hc, ← list_prod_map_filter_of_eq_one f4PosList
      (fun i => decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ))) _ (fun i hi hne => by
        rw [h0 i (hcover i hi hne), f4x_zero]),
      show f4PosList.filter (fun i => decide (i ∈ ([41, 43, 44, 45, 46, 47] : List ℕ))) =
        [41, 43, 44, 45, 46, 47] by decide]
    simp [mul_assoc]
  have h1 := commute_of_oddCommute_v hK (by norm_num) (by norm_num) root33 root14
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD
  rw [hy6] at h1
  have hA1 := commute_of_commute_mul (((((commute_pair_rule hK (a := 33) (b := 14) (p := 41)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
      (c 41)).mul_right
    (commute_pair_rule hK (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (c 43))).mul_right
    (commute_pair_rule hK (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (c 44))).mul_right
    (commute_pair_rule hK (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (c 45)))) h1
  obtain ⟨k46, k47⟩ := pair_kill (j := 0) (by norm_num) root33 root14 ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) f4x_comm_33_46
    (fun d => (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 33) (q := 47)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 d).eq)
    rfl rfl (by decide +kernel) hA1.eq
  rw [k46, k47, f4x_zero, f4x_zero, mul_one, mul_one] at hy6
  have h4 := commute_of_oddCommute_v hK (by norm_num) (by norm_num) root24 root23
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hD
  rw [hy6, mul_assoc (f4x K 41 (c 41)), mul_assoc (f4x K 41 (c 41))] at h4
  have h4' := commute_of_commute_mul (commute_pair_rule hK (a := 24) (b := 23) (p := 41)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (c 41)) h4
  have hB4 := commute_of_commute_mul_right (commute_pair_rule hK (a := 24) (b := 23) (p := 45)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (c 45)) h4'
  obtain ⟨k43, k44⟩ := pair_kill (j := 3) (by norm_num) root24 root23 ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num) f4x_comm_24_43
    (fun d => (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 24) (q := 44)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 d).eq)
    rfl rfl (by decide +kernel) hB4.eq
  rw [k43, k44, f4x_zero, f4x_zero, mul_one, mul_one] at hy6
  have h41 : ((xr (K := K) (orbitCertRoot .F4 41) : adjointGroup .F4 K) : ModGL .F4 K) =
      f4x K 41 1 := rfl
  have h45 : ((xr (K := K) (orbitCertRoot .F4 45) : adjointGroup .F4 K) : ModGL .F4 K) =
      f4x K 45 1 := rfl
  rcases eq_zero_or_eq_one_of_card_two hK (c 41) with e1 | e1 <;>
    rcases eq_zero_or_eq_one_of_card_two hK (c 45) with e2 | e2 <;> rw [e1, e2] at hy6
  · exact Or.inl (Subtype.ext (by rw [hy6, f4x_zero, f4x_zero, one_mul]; rfl))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by rw [hy6, f4x_zero, one_mul, h45]))))
  · exact Or.inr (Or.inl (Subtype.ext (by rw [hy6, f4x_zero, mul_one, h41])))
  · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by rw [hy6, Subgroup.coe_mul, h41, h45]))))


theorem f4Rep_single
    [CharP K 2] (p : ℕ) : f4Rep K [p] = xr (orbitCertRoot .F4 p) :=
  Subtype.ext (coe_f4Rep_singleton p)

theorem isConj_45
    [CharP K 2] :
    IsConj (xr (K := K) (orbitCertRoot .F4 47)) (xr (orbitCertRoot .F4 45)) := by
  refine isConj_iff.2 ⟨⟨f4CollWeylElt K [1, 0], f4CollWeylElt_mem _⟩, Subtype.ext ?_⟩
  have h := f4CollWeylElt_conj_prod (K := K) (ω := [1, 0]) (by decide) [47] (by decide)
  simp only [f4CollProd_cons, f4CollProd_nil, mul_one, List.map_cons, List.map_nil] at h
  rw [show f4CollWeylPerm [1, 0] 47 = 45 from rfl] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

theorem isConj_41
    [CharP K 2] :
    IsConj (xr (K := K) (orbitCertRoot .F4 44)) (xr (orbitCertRoot .F4 41)) := by
  refine isConj_iff.2 ⟨⟨f4CollWeylElt K [2, 3], f4CollWeylElt_mem _⟩, Subtype.ext ?_⟩
  have h := f4CollWeylElt_conj_prod (K := K) (ω := [2, 3]) (by decide) [44] (by decide)
  simp only [f4CollProd_cons, f4CollProd_nil, mul_one, List.map_cons, List.map_nil] at h
  rw [show f4CollWeylPerm [2, 3] 44 = 41 from rfl] at h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

theorem xr_mul_self
    [CharP K 2] (p : ℕ) :
    xr (K := K) (orbitCertRoot .F4 p) * xr (orbitCertRoot .F4 p) = 1 :=
  Subtype.ext (f4x_one_mul_self p)

theorem xr_commute
    [CharP K 2] {p q : ℕ} (hp : 24 ≤ p ∧ p ≤ 47) (hq : 24 ≤ q ∧ q ≤ 47)
    (h : p ≠ q → f4CollComm p q = []) :
    xr (K := K) (orbitCertRoot .F4 p) * xr (orbitCertRoot .F4 q) =
      xr (orbitCertRoot .F4 q) * xr (orbitCertRoot .F4 p) :=
  Subtype.ext (commute_f4x_of_f4CollComm_eq_nil hp hq h 1 1).eq

theorem ne_one_of_orderOf_two {G : Type*} [Group G] {y : G} (hy : orderOf y = 2) : y ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem eq_of_oddCommute_root
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {r y : adjointGroup .F4 K}
    (hr : IsConj (xr (orbitCertRoot .F4 47)) r ∨ IsConj (xr (orbitCertRoot .F4 44)) r)
    (hy : orderOf y = 2) (hD : Step83Pair.OddCommute r y) : y = r := by
  have key : ∀ {s g : adjointGroup .F4 K}, g * s * g⁻¹ = r →
      (∀ y' : adjointGroup .F4 K, Step83Pair.OddCommute s y' → y' = 1 ∨ y' = s) → y = r := by
    intro s g hg hs
    have hD' := Step83Pair.oddCommute_conj g⁻¹ hD
    rw [← hg, show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group] at hD'
    rcases hs _ hD' with h | h
    · exact absurd (conj_eq_one_iff.1 h) (ne_one_of_orderOf_two hy)
    · rw [← hg, ← h]
      group
  rcases hr with hr | hr <;> obtain ⟨g, hg⟩ := isConj_iff.1 hr
  · exact key hg fun y' h => eq_of_oddCommute_t hK h
  · exact key hg fun y' h => eq_of_oddCommute_u hK h


@[expose] def rootInv
    (K : Type) [Field K] : Set (adjointGroup .F4 K) :=
  {r | IsConj (xr (orbitCertRoot .F4 47)) r ∨ IsConj (xr (orbitCertRoot .F4 44)) r}

theorem conj_mem_rootInv
    {r : adjointGroup .F4 K} (hr : r ∈ rootInv K) (g : adjointGroup .F4 K) :
    g * r * g⁻¹ ∈ rootInv K := by
  have hc : IsConj r (g * r * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  rcases hr with hr | hr
  · exact Or.inl (hr.trans hc)
  · exact Or.inr (hr.trans hc)

theorem mul_mem_rootInv
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x y : adjointGroup .F4 K} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hne : x ≠ y) (hD : Step83Pair.OddCommute x y) : x * y ∈ rootInv K := by
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  obtain ⟨s, hs, hsx⟩ := classesCover_AS (K := K) x hx2 (ne_one_of_orderOf_two hx)
  obtain ⟨g, rfl⟩ := isConj_iff.1 hsx
  set y' := g⁻¹ * y * g with hy'
  have hyy : y = g * y' * g⁻¹ := by rw [hy']; group
  have hD' : Step83Pair.OddCommute s y' := by
    have h := Step83Pair.oddCommute_conj g⁻¹ hD
    rwa [show g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s by group,
      show g⁻¹ * y * g⁻¹⁻¹ = y' by rw [hy', inv_inv]] at h
  have hy'1 : y' ≠ 1 := fun h => ne_one_of_orderOf_two hy (by rw [hyy, h]; group)
  have hy's : y' ≠ s := fun h => hne (by rw [hyy, h])
  have hmul : g * s * g⁻¹ * y = g * (s * y') * g⁻¹ := by rw [hyy]; group
  rw [hmul]
  refine conj_mem_rootInv ?_ g
  have t2 := xr_mul_self (K := K) 47
  have u2 := xr_mul_self (K := K) 44
  have a2 := xr_mul_self (K := K) 41
  have b2 := xr_mul_self (K := K) 45
  have tu := xr_commute (K := K) (p := 47) (q := 44) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (fun _ => by decide)
  have ab := xr_commute (K := K) (p := 41) (q := 45) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (fun _ => by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · rw [f4Rep_single] at hD' hy's
    rcases eq_of_oddCommute_t hK hD' with h | h
    · exact absurd h hy'1
    · exact absurd h hy's
  · rw [f4Rep_single] at hD' hy's
    rcases eq_of_oddCommute_u hK hD' with h | h
    · exact absurd h hy'1
    · exact absurd h hy's
  · rw [f4Rep_pair, f4Rep_single, f4Rep_single] at hD' hy's ⊢
    rcases eq_of_oddCommute_tu hK hD' with h | h | h | h
    · exact absurd h hy'1
    · refine Or.inr (isConj_iff.2 ⟨1, ?_⟩)
      rw [h, one_mul, inv_one, mul_one, tu, mul_assoc, t2, mul_one]
    · refine Or.inl (isConj_iff.2 ⟨1, ?_⟩)
      rw [h, one_mul, inv_one, mul_one, mul_assoc, u2, mul_one]
    · exact absurd h hy's
  · rw [f4Rep_pair, f4Rep_single, f4Rep_single] at hD' hy's ⊢
    rcases eq_of_oddCommute_v hK hD' with h | h | h | h
    · exact absurd h hy'1
    · refine Or.inl (isConj_45.trans (isConj_iff.2 ⟨1, ?_⟩))
      rw [h, one_mul, inv_one, mul_one, ab, mul_assoc, a2, mul_one]
    · refine Or.inr (isConj_41.trans (isConj_iff.2 ⟨1, ?_⟩))
      rw [h, one_mul, inv_one, mul_one, mul_assoc, b2, mul_one]
    · exact absurd h hy's

theorem false_of_oddCommute
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {x y : adjointGroup .F4 K} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hne : x ≠ y) (h1 : Step83Pair.OddCommute x y) (h2 : Step83Pair.OddCommute (x * y) y) :
    False := by
  have hyx := eq_of_oddCommute_root hK (mul_mem_rootInv hK hx hy hxy hne h1) hy h2
  have hx1 : x = 1 := by
    have h := congrArg (· * y⁻¹) hyx
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h
    exact h.symm
  exact ne_one_of_orderOf_two hx hx1

theorem not_pairCent_F4
    {S : Type} [Group S]
    (h : ChevalleyExceptionalModel S .F4 2 1) {x y : S} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    ¬(AS76b.oUpperTwo (centralizer ({x} : Set S)) ≤ centralizer ({y} : Set S) ∧
      AS76b.oUpperTwo (centralizer ({x * y} : Set S)) ≤ centralizer ({y} : Set S)) := by
  rintro ⟨h1, h2⟩
  have hmod : UntwistedChevalleyModel S .F4 (2 ^ 1) := h.2
  obtain ⟨L, _, _, hL, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hmod
  have : CharP L 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hL
  have hD1 := Step83Pair.oddCommute_map e (Step83Pair.oddCommute_of_oUpperTwo_le h1)
  have hD2 := Step83Pair.oddCommute_map e (Step83Pair.oddCommute_of_oUpperTwo_le h2)
  rw [map_mul] at hD2
  refine false_of_oddCommute (by rw [hL, pow_one]) ?_ ?_ ?_ ?_ hD1 hD2
  · rwa [MulEquiv.orderOf_eq]
  · rwa [MulEquiv.orderOf_eq]
  · rw [← map_mul, hxy, map_mul]
  · exact fun h' => hne (e.injective h')

end CFSG.ComponentClassification.RankTwoExceptional.PairF4
