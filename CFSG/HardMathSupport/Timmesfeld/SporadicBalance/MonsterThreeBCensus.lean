module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBRoots
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCQ

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open _root_.Timmesfeld.M3B (Mat B0 LA LM sigW tMats matOf mone fibreOK fT fLam tD adOf adMat)

section Census


theorem tMats_get {j : ℕ} (hj : j < 3) : (tMats ())[j]! = matOf (LM ()) sigW[j]! := by
  have hs : sigW.size = 3 := rfl
  unfold tMats
  rw [getElem!_pos _ j (by rw [Array.size_map, hs]; exact hj), Array.getElem_map,
    getElem!_pos sigW j (by rw [hs]; exact hj)]

theorem tD_succ (j : ℕ) : tD (j + 1) = adOf (B0 ()) (LA ()) sigW[j]! := by
  unfold tD
  rw [Nat.add_sub_cancel]

end Census

section Final


theorem goodK_of_mem_tbL (hinv : letterInvCheck () = true) (hsyl : SylFact)
    (hP : ∀ P : Subgroup Gmat, P ≤ CQ → IsPGroup 3 P → P ≤ Subgroup.zpowers tbw) [Finite Gmat]
    (hroots : rootsOK () = true) (hfib : ∀ k < 4, FibreRoots k) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGood c) {x : Gmat} (hx : x ∈ tbL) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : GoodK x := by
  by_cases hρ : CommData.actMat 3 tbq tbw tbM x = 1
  · obtain ⟨D, hD⟩ := exists_isAct hx
    have hl := lam_eq_one hD hx3
    have hm : (Matrix.of fun i => (D.1 i).1) = toMatrix (fT 0) := by
      rw [← actMat_of_isAct hD, hρ]
      unfold fT
      rw [ite_eq_left rfl, toMatrix_mone]
    have hT : ∀ i, (D.1 i).1 = toMat (fT 0) i := fun i => congrFun hm i
    have hL : D.2 = toZ (fLam 0) := by
      unfold fLam
      rw [ite_eq_left rfl, hl, toZ_one]
    obtain ⟨p, hp, hxp⟩ := exists_fpt_of_isAct hD hT hL
    exact goodK_of_fibre hinv hP hroots ht3 hgood (k := 0) (by norm_num) (hfib 0 (by norm_num))
      hp hx hx3 hx1 hxp
  · obtain ⟨g, hg, j, hj, hgx⟩ := exists_conj_tMats hsyl hx hx3 hρ
    obtain ⟨y, hydef⟩ : ∃ y, y = g⁻¹ * x * g := ⟨_, rfl⟩
    rw [← hydef] at hgx
    have hy : y ∈ tbL := by
      rw [hydef]; exact tbL.mul_mem (tbL.mul_mem (tbL.inv_mem hg) hx) hg
    have hy3 : y ^ 3 = 1 := by rw [hydef, conj_pow_inv, hx3]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply hx1
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [← hydef, h]; group
    obtain ⟨D, hD⟩ := exists_isAct hy
    have hl := lam_eq_one hD hy3
    have htD := isAct_evalG hinv sigW[j]!
    have ht3' : evalG letterG sigW[j]! ^ 3 = 1 := by
      have := ht3 (j + 1) (by omega)
      unfold tG at this
      rwa [ite_eq_right (by omega), Nat.add_sub_cancel] at this
    have hm : (Matrix.of fun i => (D.1 i).1) =
        Matrix.of fun i => ((toD (adOf (B0 ()) (LA ()) sigW[j]!)).1 i).1 := by
      rw [← actMat_of_isAct hD, hgx, tMats_get hj, ← actMat_evalG, actMat_of_isAct htD]
    have hfT : fT (j + 1) = adMat (tD (j + 1)) := by
      unfold fT; rw [ite_eq_right (by omega)]
    have hT : ∀ i, (D.1 i).1 = toMat (fT (j + 1)) i := by
      intro i
      rw [hfT, toMat_adMat_row, tD_succ]
      exact congrFun hm i
    have hL : D.2 = toZ (fLam (j + 1)) := by
      have h2 : fLam (j + 1) = (tD (j + 1)).2 := by
        unfold fLam; rw [ite_eq_right (by omega)]
      rw [h2, hl, tD_succ]
      exact (lam_eq_one htD ht3').symm
    obtain ⟨p, hp, hyp⟩ := exists_fpt_of_isAct hD hT hL
    have hyg := goodK_of_fibre hinv hP hroots ht3 hgood (k := j + 1) (by omega)
      (hfib _ (by omega)) hp hy hy3 hy1 hyp
    rw [hydef] at hyg
    have := goodK_conj hyg g
    simpa [mul_assoc] using this

theorem factorization_Gmat : (Nat.card Gmat).factorization 3 = 20 := by
  have : Finite Gmat := finite_Gmat
  have hpos : Nat.card Gmat ≠ 0 := Nat.card_pos.ne'
  have h20 : 3 ^ 20 ∣ Nat.card Gmat := by
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    unfold CFSG.Open.monsterOrder
    decide
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 h20
  have hlt : ¬ 21 ≤ (Nat.card Gmat).factorization 3 := fun h21 => not_three_pow_21_dvd (by
    rw [← CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).2 h21)
  omega

theorem exists_conj_mem_tbL (h : SylFact) {x : Gmat} (hx : orderOf x = 3) :
    ∃ g : Gmat, g * x * g⁻¹ ∈ tbL := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Gmat := finite_Gmat
  obtain ⟨P⟩ : Nonempty (Sylow 3 tbL) := inferInstance
  have hPcard : Nat.card (P : Subgroup tbL) = 3 ^ 20 := by
    rw [P.card_eq_multiplicity, factorization_tbL h]
  have hP'card : Nat.card ((P : Subgroup tbL).map tbL.subtype) = 3 ^ 20 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hPcard]
  let S : Sylow 3 Gmat :=
    Sylow.ofCard ((P : Subgroup tbL).map tbL.subtype) (by rw [hP'card, factorization_Gmat])
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_three' S hx
  refine ⟨g, ?_⟩
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hg
  rw [← hy]
  exact y.2

theorem goodK_of_pow_three (hinv : letterInvCheck () = true) (hsyl : SylFact)
    (hroots : rootsOK () = true) (hfib : ∀ k < 4, FibreRoots k) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGood c) {x : Gmat} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    GoodK x := by
  have : Finite Gmat := finite_Gmat
  have hx : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  obtain ⟨g, hg⟩ := exists_conj_mem_tbL hsyl hx
  have hy3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3]; group
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have h := goodK_of_mem_tbL hinv hsyl (le_zpowers_of_le_CQ hsyl) hroots hfib ht3 hgood hg hy3
    hy1
  exact (goodK_iff_conj x g).1 h

theorem twoAPureKlein_three_of (hinv : letterInvCheck () = true) (hsyl : SylFact)
    (hroots : rootsOK () = true) (hfib : ∀ k < 4, FibreRoots k) (ht3 : ∀ k < 4, tG k ^ 3 = 1)
    (hgood : ∀ c ∈ rootClaims, RootGood c) : TwoAPureKlein 3 Gmat := by
  intro s hs hn
  have h3 : s ^ 3 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have h1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  rcases goodK_of_pow_three hinv hsyl hroots hfib ht3 hgood h3 h1 with h | h
  · exact absurd h hn
  · exact h

end Final

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
