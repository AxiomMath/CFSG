module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Minus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.Quasithin (perfectCore)

section RootGroup

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem card_le_stabPairsBar_of_injective {S : Type*} [Finite S] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {a a' b b' c c' : Fin d} (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hc : IsHypCoord Q c c') (hac : PairDisjoint a a' c c') (hbc : PairDisjoint b b' c c')
    (w : S → Fin d → K) (hw : Function.Injective w)
    (hw0 : ∀ x, w x a = 0 ∧ w x a' = 0 ∧ w x b = 0 ∧ w x b' = 0 ∧ w x c = 0 ∧ w x c' = 0) :
    Nat.card S ≤ Nat.card (stabPairsBar Q a a' b b') := by
  classical
  have hEstab : ∀ x, eichler Q (Pi.single c 1) (w x) ∈ stabSub a a' ⊓ stabSub b b' := by
    intro x
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hw0 x
    refine ⟨⟨eichler_apply_of_polar_eq_zero ?_ ?_, eichler_apply_of_polar_eq_zero ?_ ?_⟩,
      eichler_apply_of_polar_eq_zero ?_ ?_, eichler_apply_of_polar_eq_zero ?_ ?_⟩
    · rw [ha.polar_left]; exact Pi.single_eq_of_ne hac.left_ne_right.symm _
    · rw [ha.polar_left]; exact h2
    · rw [ha.polar_right]; exact Pi.single_eq_of_ne hac.left_ne_left.symm _
    · rw [ha.polar_right]; exact h1
    · rw [hb.polar_left]; exact Pi.single_eq_of_ne hbc.left_ne_right.symm _
    · rw [hb.polar_left]; exact h4
    · rw [hb.polar_right]; exact Pi.single_eq_of_ne hbc.left_ne_left.symm _
    · rw [hb.polar_right]; exact h3
  have hEΩ : ∀ x, eichler Q (Pi.single c 1) (w x) ∈ orthDerived Q :=
    fun x => eichler_mem_orthDerived hQ hT _ _
  have hEf : ∀ x, eichler Q (Pi.single c 1) (w x) (Pi.single c' 1) =
      Pi.single c' 1 + w x - Q (w x) • Pi.single c 1 := by
    intro x
    obtain ⟨-, -, -, -, h5, h6⟩ := hw0 x
    rw [eichler_apply hc.map_left (by rw [hc.polar_left]; exact h6), hc.polar_right,
      hc.polar_right, Pi.single_eq_same, h5]
    module
  let φ : S → stabPairsBar Q a a' b b' :=
    fun x => ⟨projHom _ ⟨_, hEΩ x⟩, ⟨⟨_, hEΩ x⟩, mem_subgroupOf.mpr (hEstab x), rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : (⟨_, hEΩ x⟩ : orthDerived Q) = ⟨_, hEΩ y⟩ :=
      projHom_injective hc.exists_ne_zero (congrArg Subtype.val hxy)
    have h2 := congrArg (fun z : orthDerived Q =>
      (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single c' 1)) h1
    simp only [hEf] at h2
    apply hw
    funext v
    by_cases hv : v = c
    · rw [hv, (hw0 x).2.2.2.2.1, (hw0 y).2.2.2.2.1]
    · have := congrFun h2 v
      simpa [hv] using this
  exact Nat.card_le_card_of_injective φ hφ

theorem exists_ne_three_fin {m : ℕ} (hm : 4 ≤ m) (i j k : Fin m) :
    ∃ g : Fin m, i ≠ g ∧ j ≠ g ∧ k ≠ g := by
  classical
  have hcard : 0 < ((Finset.univ : Finset (Fin m)) \ {i, j, k}).card := by
    have h1 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m)) {i, j, k}
    have h2 : ((Finset.univ : Finset (Fin m)) ∩ {i, j, k}).card ≤ 3 := by
      rw [Finset.univ_inter]
      exact Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨g, hg⟩ := Finset.card_pos.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hg
  exact ⟨g, fun e => hg.1 e.symm, fun e => hg.2.1 e.symm, fun e => hg.2.2 e.symm⟩

theorem card_le_minusStabPairsBar (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j k : Fin (n - 1)} (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card K ^ 4 ≤ Nat.card (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  obtain ⟨g, hig, hjg, hkg⟩ := exists_ne_three_fin (by omega : 4 ≤ n - 1) i j k
  set e := minusIndexEquiv n hn1 with he
  let w : K × K × K × K → Fin (2 * n) → K := fun x =>
    x.1 • Pi.single (e (.inl g)) 1 + x.2.1 • Pi.single (e (.inr (.inl g))) 1 +
      x.2.2.1 • Pi.single (e (.inr (.inr 0))) 1 + x.2.2.2 • Pi.single (e (.inr (.inr 1))) 1
  have hw0 : ∀ x (m : Fin (n - 1)), m ≠ g → w x (e (.inl m)) = 0 ∧ w x (e (.inr (.inl m))) = 0 := by
    intro x m hmg
    constructor <;> simp [w, he, hmg]
  have hwinj : Function.Injective w := by
    intro x y hxy
    have e1 := congrFun hxy (e (.inl g))
    have e2 := congrFun hxy (e (.inr (.inl g)))
    have e3 := congrFun hxy (e (.inr (.inr 0)))
    have e4 := congrFun hxy (e (.inr (.inr 1)))
    simp [w, he] at e1 e2 e3 e4
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
  have := card_le_stabPairsBar_of_injective hQ hT (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) (isHypCoord_coordinateQuadMinus hn1 b c k)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk) w hwinj
    (fun x => ⟨(hw0 x i hig).1, (hw0 x i hig).2, (hw0 x j hjg).1,
      (hw0 x j hjg).2, (hw0 x k hkg).1, (hw0 x k hkg).2⟩)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod] at this
  calc Nat.card K ^ 4 = Nat.card K * (Nat.card K * (Nat.card K * Nat.card K)) := by ring
    _ ≤ _ := this

end RootGroup

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem centralizer_longRoot_decomp_minus_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    ∃ (z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
      (Qz Mz : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))),
      z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ z ∧
        perfectCore (centralizer ({z} : Set _)) = centralizer {z} ∧
        centralizer {z} = Qz ⊔ Mz ∧ IsPGroup 2 Qz ∧
        Mz ≤ normalizer (Qz : Set (matrixProjectiveDerived
          (coordinateQuadMinus n K (by omega) b c))) ∧
        Disjoint Qz Mz ∧ (∀ N : Subgroup Mz, N.Normal → IsPGroup 2 N → N = ⊥) ∧
        minusPairTorus (by omega) b c k ≤ Mz := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne_fin (by omega : 3 ≤ n - 1) k
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, rootRadicalBar _ hi.hypPair hj.hypPair,
    rootLeviBar _ hi.hypPair hj.hypPair, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1)),
    centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inr rfl)⟩

theorem minusRootElt_decomp_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ z : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c),
      z ∈ minusPairPerp (by omega) b c k ∧ IsLongRoot _ z ∧ z ≠ 1 ∧
      perfectCore (centralizer ({z} : Set (matrixProjectiveDerived
        (coordinateQuadMinus n K (by omega) b c)))) =
        minusRadical (by omega) b c i j ⊔ minusLevi (by omega) b c i j ∧
      IsPGroup 2 (minusRadical (K := K) (by omega) b c i j) ∧
      minusLevi (by omega) b c i j ≤ normalizer (minusRadical (by omega) b c i j :
        Set (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) ∧
      Disjoint (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j) ∧
      (∀ N : Subgroup (minusLevi (K := K) (by omega) b c i j), N.Normal → IsPGroup 2 N →
        N = ⊥) ∧
      minusPairTorus (by omega) b c k ≤ minusLevi (by omega) b c i j := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hi := isHypCoord_coordinateQuadMinus (K := K) hn1 b c i
  have hj := isHypCoord_coordinateQuadMinus (K := K) hn1 b c j
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hd := pairDisjoint_minus hn1 hij
  have h₁₂ := hi.orth hj hd
  have h₁₃ := hi.orth hk (pairDisjoint_minus hn1 hik)
  have h₂₃ := hj.orth hk (pairDisjoint_minus hn1 hjk)
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  have hS := isQuasisimple_minusStabPairsBar_of_five_le (K := K) hn hirr hij
  refine ⟨rootPairElt hQ h₁₂ h₁₃ h₂₃, ?_, isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃,
    rootPairElt_ne_one hQ h₁₂ h₁₃ h₂₃, ?_, isPGroup_rootRadicalBar _ _,
    rootLeviBar_le_normalizer h₁₂, disjoint_rootRadicalBar_rootLeviBar h₁₂,
    fun N hN h2 => rootLeviBar_normal_isPGroup_eq_bot_of hi hj hd hQ hT hS N hN h2, ?_⟩
  · exact rootPairElt_mem_pairPerpOf hQ h₁₂ h₁₃ h₂₃ hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
  · rw [CFSG.Quasithin.perfectCore_eq_self_of_perfect
      (commutator_centralizer_rootPairElt_of hi hj hd hQ h₁₃ h₂₃ hl0 hl1
        (Subgroup.isPerfect_iff.mp hS.1.1))]
    exact centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  · exact pairTorusOf_le_rootLeviBar hk
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hik _ _ (.inr rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inl rfl) (.inr rfl)⟩
      ⟨single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inl rfl),
        single_minus_apply_eq_zero hn1 hjk _ _ (.inr rfl) (.inr rfl)⟩

theorem refinedF6_minusPairTorus_of_five_le (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j k : Fin (n - 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    RefinedF6 (minusRadical (K := K) (by omega) b c i j) (minusLevi (by omega) b c i j)
      (minusPairTorus (by omega) b c k) (minusPairPerp (K := K) (by omega) b c k) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus n K b c (by omega) hirr
  have hk := isHypCoord_coordinateQuadMinus (K := K) hn1 b c k
  have hD : ⁅minusPairPerp (K := K) hn1 b c k, minusPairPerp (K := K) hn1 b c k⁆ =
      minusPairPerp (K := K) hn1 b c k :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_minusPairPerp hn hirr k).1
  exact refinedF6_pairTorusOf hQ hT hq (isHypCoord_coordinateQuadMinus hn1 b c i)
    (isHypCoord_coordinateQuadMinus hn1 b c j) hk (pairDisjoint_minus hn1 hij)
    (pairDisjoint_minus hn1 hik) (pairDisjoint_minus hn1 hjk)
    (isQuasisimple_minusStabPairsBar_of_five_le hn hirr hij)
    (card_le_minusStabPairsBar hn hirr hik hjk) hD

end Main

end CFSG.SeitzReduction.OmegaPilot
