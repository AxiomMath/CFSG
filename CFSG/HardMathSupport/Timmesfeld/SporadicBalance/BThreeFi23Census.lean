module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeKlein
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeAssemble
public import Certificates.Certificate13652

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Perm CFSG.Perm.Native CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native CFSG.Sporadic.Bridge
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
  CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Th.Native hiding letters
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Words


theorem applyW_spec : ∀ w : List ℕ, (∀ l ∈ w, l < letters.size) → ∀ p < 31671,
    applyW letters w p = idx 31671 (w.map (pairG gs)).prod p
  | [], _, p, _ => by
    rw [List.map_nil, List.prod_nil, idx_one]
    rfl
  | l :: w, hw, p, hp => by
    have hl := hw l List.mem_cons_self
    have ih := applyW_spec w (fun z hz => hw z (List.mem_cons_of_mem _ hz)) p hp
    change ap letters[l]! (applyW letters w p) = _
    rw [ih, List.map_cons, List.prod_cons, idx_mul]
    exact rep_pairG_all l hl _ (idx_lt _ hp)

theorem applyInvW_spec : ∀ w : List ℕ, (∀ l ∈ w, l < letters.size) → ∀ p < 31671,
    applyInvW letters w p = idx 31671 ((w.map (pairG gs)).prod)⁻¹ p
  | [], _, p, _ => by
    rw [List.map_nil, List.prod_nil, inv_one, idx_one]
    rfl
  | l :: w, hw, p, hp => by
    have hl := hw l List.mem_cons_self
    have hil : invL l < letters.size := invL_lt (by rw [letters_size]; omega) hl
    have h1 : ap letters[invL l]! p = idx 31671 (pairG gs l)⁻¹ p := by
      rw [← pairG_invL]
      exact rep_pairG_all _ hil p hp
    have hp' : ap letters[invL l]! p < 31671 := by rw [h1]; exact idx_lt _ hp
    have ih := applyInvW_spec w (fun z hz => hw z (List.mem_cons_of_mem _ hz)) _ hp'
    change applyInvW letters w (ap letters[invL l]! p) = _
    rw [ih, h1, ← idx_mul, List.map_cons, List.prod_cons, mul_inv_rev]

end Words

section Tables


theorem rep_imgTab {k : ℕ} (hk : k < 10) : Rep 31671 (imgTab orb k) (Fi23.img k) := by
  have e : imgTab orb k = Fi23.imgT[k]! := (Fi23.imgT_getElem hk).symm
  rw [e]
  exact Fi23.rep_img hk

theorem kleinZ_lt : ∀ l ∈ kleinZ, l < letters.size := by
  rw [letters_size, chainWords_size]
  decide

theorem getElem!_four {α : Type*} [Inhabited α] (a b c d : α) :
    #[a, b, c, d][0]! = a ∧ #[a, b, c, d][1]! = b ∧ #[a, b, c, d][2]! = c ∧
      #[a, b, c, d][3]! = d :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem t3Tabs_get (O : WOrbit) (L : Array Table) :
    (t3Tabs O L)[0]! = compT 31671 (imgTab O 2) (imgTab O 3) ∧
    (t3Tabs O L)[1]! = qLettersT L kleinZ ∧
    (t3Tabs O L)[2]! =
      compT 31671 (compT 31671 (compT 31671 (imgTab O 4) (imgTab O 5)) (imgTab O 2)) (imgTab O 1) ∧
    (t3Tabs O L)[3]! = compT 31671 (compT 31671 (compT 31671 (compT 31671 (compT 31671
      (imgTab O 5) (imgTab O 3)) (imgTab O 7)) (imgTab O 0)) (imgTab O 6)) (imgTab O 1) := by
  unfold t3Tabs
  exact getElem!_four _ _ _ _

theorem rep_t3Tabs (i : Fin 4) : Rep 31671 (t3Tabs orb letters)[i.val]! (t3 i) := by
  obtain ⟨e0, e1, e2, e3⟩ := t3Tabs_get orb letters
  have h2 := rep_imgTab (k := 2) (by norm_num)
  have h3 := rep_imgTab (k := 3) (by norm_num)
  fin_cases i
  · show Rep 31671 (t3Tabs orb letters)[0]! (Fi23.img 2 * Fi23.img 3)
    rw [e0]
    exact h2.compT h3
  · show Rep 31671 (t3Tabs orb letters)[1]! zJ
    rw [e1]
    exact rep_qLettersT kleinZ kleinZ_lt
  · show Rep 31671 (t3Tabs orb letters)[2]!
      (Fi23.img 4 * Fi23.img 5 * Fi23.img 2 * Fi23.img 1)
    rw [e2]
    exact (((rep_imgTab (by norm_num)).compT (rep_imgTab (by norm_num))).compT h2).compT
      (rep_imgTab (by norm_num))
  · show Rep 31671 (t3Tabs orb letters)[3]!
      (Fi23.img 5 * Fi23.img 3 * Fi23.img 7 * Fi23.img 0 * Fi23.img 6 * Fi23.img 1)
    rw [e3]
    exact (((((rep_imgTab (by norm_num)).compT h3).compT (rep_imgTab (by norm_num))).compT
      (rep_imgTab (by norm_num))).compT (rep_imgTab (by norm_num))).compT
      (rep_imgTab (by norm_num))

end Tables

section Census


theorem fi23_three_classes (s : CFSG.Sporadic.Fi23.J) (hs : orderOf s = 3) : ∃ i : Fin 4, IsConj s (t3 i) :=
  Certificates.certificate13652.1 s hs

theorem exists_sylow_le_centralizer_zJ :
    ∃ T : Subgroup CFSG.Sporadic.Fi23.J, Nat.card T = 3 ^ 13 ∧ T ≤ Subgroup.centralizer ({zJ} : Set CFSG.Sporadic.Fi23.J) := by
  obtain ⟨T, hT⟩ := Certificates.certificate13652.2.1
  refine ⟨T, ?_, hT⟩
  rw [Sylow.card_eq_multiplicity, card_J,
    show (4089470473293004800 : ℕ) = 3 ^ 13 * 2565020057600 by norm_num,
    factorization_three_pow_mul 13 _ (by norm_num)]

end Census

section Transposition


theorem rep_genTables_neg_two' : Rep 31671 (genTables orb (-2)) b⁻¹ := by
  have h := rep_gen (-2)
  have e : genG (-2) = b⁻¹ := by
    unfold genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rw [e] at h
  exact h

theorem t2_isConj_d : IsConj d (Fi23.img 2) :=
  Certificates.certificate13652.2.2

end Transposition

section Baby


theorem three_pow_dvd_card_centralizer_phiB_t3_one :
    3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({phiB (t3 1)} : Set B)) := by
  obtain ⟨T, hT, hTC⟩ := exists_sylow_le_centralizer_zJ
  have hle : T.map phiB ≤ Subgroup.centralizer ({phiB (t3 1)} : Set B) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.1 (hTC hx)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show phiB x * phiB zJ = phiB zJ * phiB x
    rw [← map_mul, ← map_mul, hx']
  have hcard : Nat.card (T.map phiB) = 3 ^ 13 := by
    rw [Subgroup.card_map_of_injective phiB_injective, hT]
  exact hcard ▸ Subgroup.card_dvd_of_le hle


theorem factorization_card_B_three : (Nat.card B).factorization 3 = 13 := by
  rw [CFSG.Monster.Existence.card_nativeB, CFSG.Open.monsterBabyOrder,
    show (2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 : ℕ) =
      3 ^ 13 * (2 ^ 41 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47) by ring,
    factorization_three_pow_mul 13 _ (by norm_num)]

theorem bThree_classes (s : B) (hs : orderOf s = 3) : ∃ i : Fin 4, IsConj s (phiB (t3 i)) := by
  have : Finite B := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Monster.Existence.card_nativeB, CFSG.Open.monsterBabyOrder]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT, -⟩ := exists_sylow_le_centralizer_zJ
  have hcardTB : Nat.card (T.map phiB) = 3 ^ (Nat.card B).factorization 3 := by
    rw [Subgroup.card_map_of_injective phiB_injective, hT, factorization_card_B_three]
  let TB : Sylow 3 B := Sylow.ofCard (T.map phiB) hcardTB
  have hsp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B Q TB
  have hsT : g * s * g⁻¹ ∈ (TB : Subgroup B) := by
    have h1 : s ∈ (Q : Subgroup B) := hQ (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (Q : Set B)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ TB := by simpa [MulAut.conj_apply] using h2
    exact h3
  rw [Sylow.coe_ofCard] at hsT
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hsT
  have hyo : orderOf y = 3 := by
    rw [← orderOf_injective phiB phiB_injective y, hy]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj g) s).trans hs
  obtain ⟨i, hi⟩ := fi23_three_classes y hyo
  refine ⟨i, ?_⟩
  have h1 : IsConj s (phiB y) := by
    rw [hy]
    exact isConj_iff.2 ⟨g, rfl⟩
  exact h1.trans (phiB.map_isConj hi)

end Baby

section Assembly


theorem phiB_t3_zero_inverted :
    ∃ d : B, BabyInv 0 d ∧ d * phiB (t3 0) * d⁻¹ = (phiB (t3 0))⁻¹ := by
  refine ⟨phiB (Fi23.img 2), babyInv_zero_map_of_isConj_d phiB phiB_injective t2_isConj_d, ?_⟩
  show phiB (Fi23.img 2) * phiB (Fi23.img 2 * Fi23.img 3) * (phiB (Fi23.img 2))⁻¹ =
    (phiB (Fi23.img 2 * Fi23.img 3))⁻¹
  rw [map_mul, phiB_img (by norm_num), phiB_img (by norm_num)]
  have hx : Fi23InB.img 2 * Fi23InB.img 2 = 1 := by
    rw [← sq]; exact Fi23InB.img_sq (by norm_num)
  calc Fi23InB.img 2 * (Fi23InB.img 2 * Fi23InB.img 3) * (Fi23InB.img 2)⁻¹
      = Fi23InB.img 2 * Fi23InB.img 2 * Fi23InB.img 3 * (Fi23InB.img 2)⁻¹ := by
        rw [mul_assoc (Fi23InB.img 2) (Fi23InB.img 2)]
    _ = (Fi23InB.img 2 * Fi23InB.img 3)⁻¹ := by
        rw [hx, one_mul, mul_inv_rev, Fi23InB.img_inv (k := 3) (by norm_num)]

@[expose] def BThreeRc : Prop := IsConj (phiB (t3 2)) (phiB (t3 0))

@[expose] def BThreeRd : Prop := IsConj (phiB (t3 3)) (phiB (t3 1))

theorem oPrimeCoreTrivialAt_B_three_of_fi23 (hc : BThreeRc) (hd : BThreeRd) :
    OPrimeCoreTrivialAt 3 B :=
  oPrimeCoreTrivialAt_B_three_of_reps (fun i => phiB (t3 i)) bThree_classes
    phiB_t3_zero_inverted three_pow_dvd_card_centralizer_phiB_t3_one
    (exists_twoB_four_kleinZ phiB phiB_injective) hc hd

end Assembly

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
