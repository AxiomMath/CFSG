module

public import CFSG.GF2Type.Smith1979.CaseIIExclU43Comm
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Grp

variable {G X : Type} [Group G] [Group X]

namespace LiftSetup

variable (D : LiftSetup G X)

theorem beta_conj {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (yl : G) {y : X}
    (hyl : D.ψ yl = y) {x x' : X} (hx : x ∈ S) (hx' : x' ∈ S) :
    D.beta (y * x * y⁻¹) (y * x' * y⁻¹) = D.beta x x' := by
  have hL : D.ψ (yl * D.lift x * yl⁻¹) = y * x * y⁻¹ := by
    rw [map_mul, map_mul, map_inv, hyl, D.hlift]
  have hL' : D.ψ (yl * D.lift x' * yl⁻¹) = y * x' * y⁻¹ := by
    rw [map_mul, map_mul, map_inv, hyl, D.hlift]
  have hz : D.ψ ((yl * D.lift x * yl⁻¹)⁻¹ * D.lift (y * x * y⁻¹)) = 1 := by
    rw [map_mul, map_inv, hL, D.hlift, inv_mul_cancel]
  have hz' : D.ψ ((yl * D.lift x' * yl⁻¹)⁻¹ * D.lift (y * x' * y⁻¹)) = 1 := by
    rw [map_mul, map_inv, hL', D.hlift, inv_mul_cancel]
  have hzc := D.ker_central _ hz
  have hzc' := D.ker_central _ hz'
  have e1 : D.lift (y * x * y⁻¹) =
      (yl * D.lift x * yl⁻¹) * ((yl * D.lift x * yl⁻¹)⁻¹ * D.lift (y * x * y⁻¹)) := by
    group
  have e2 : D.lift (y * x' * y⁻¹) =
      (yl * D.lift x' * yl⁻¹) * ((yl * D.lift x' * yl⁻¹)⁻¹ * D.lift (y * x' * y⁻¹)) := by
    group
  have hcen := D.beta_central hS2 hx hx' yl
  calc D.beta (y * x * y⁻¹) (y * x' * y⁻¹)
      = cmG (D.lift (y * x * y⁻¹)) (D.lift (y * x' * y⁻¹)) := rfl
    _ = cmG (yl * D.lift x * yl⁻¹) (yl * D.lift x' * yl⁻¹) := by
        rw [e1, e2, cmG_mul_central hzc, cmG_mul_central_right hzc']
    _ = yl * D.beta x x' * yl⁻¹ := by
        simp only [beta, cmG]
        group
    _ = D.beta x x' := by
        rw [← hcen, mul_inv_cancel_right]

theorem radical_eq_all {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8)
    {w x x' : X} (hw : w ∈ S) (hx : x ∈ S) (hx' : x' ∈ S) (hwx : D.beta w x = 1)
    (hwx' : D.beta w x' = 1) (h1x : (1 : X) ≠ x) (h1x' : (1 : X) ≠ x') (h1xx' : (1 : X) ≠ x * x')
    (h1w : (1 : X) ≠ w) (hxx' : x ≠ x') (hxxx' : x ≠ x * x') (hxw : x ≠ w)
    (hx'xx' : x' ≠ x * x') (hx'w : x' ≠ w) (hxx'w : x * x' ≠ w) :
    ∀ s ∈ S, D.beta w s = 1 := by
  classical
  let Rw : Subgroup X :=
    { carrier := {s | s ∈ S ∧ D.beta w s = 1}
      mul_mem' := fun {s t} hs ht => ⟨S.mul_mem hs.1 ht.1, by
        rw [D.beta_mul_right hS2 hw hs.1 ht.1, hs.2, ht.2, one_mul]⟩
      one_mem' := ⟨S.one_mem, D.beta_one_right w⟩
      inv_mem' := fun {s} hs => by
        have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hS2 s hs.1)
        show s⁻¹ ∈ S ∧ D.beta w s⁻¹ = 1
        rw [hinv]
        exact hs }
  have hRS : Rw ≤ S := fun s hs => hs.1
  have m1 : (1 : X) ∉ ({x, x', x * x', w} : Finset X) := by
    simp [h1x, h1x', h1xx', h1w]
  have m2 : x ∉ ({x', x * x', w} : Finset X) := by
    simp [hxx', hxxx', hxw]
  have m3 : x' ∉ ({x * x', w} : Finset X) := by
    simp [hx'xx', hx'w]
  have m4 : x * x' ∉ ({w} : Finset X) := by
    simp [hxx'w]
  have hT : ({1, x, x', x * x', w} : Finset X).card = 5 := by
    rw [Finset.card_insert_of_notMem m1, Finset.card_insert_of_notMem m2,
      Finset.card_insert_of_notMem m3, Finset.card_insert_of_notMem m4, Finset.card_singleton]
  have hsub : (({1, x, x', x * x', w} : Finset X) : Set X) ⊆ (Rw : Set X) := by
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hs
    rcases hs with h | h | h | h | h
    · rw [h]
      exact ⟨S.one_mem, D.beta_one_right w⟩
    · rw [h]
      exact ⟨hx, hwx⟩
    · rw [h]
      exact ⟨hx', hwx'⟩
    · rw [h]
      exact ⟨S.mul_mem hx hx', by
        rw [D.beta_mul_right hS2 hw hx hx', hwx, hwx', one_mul]⟩
    · rw [h]
      exact ⟨hw, D.beta_self w⟩
  have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [hS8]; norm_num)
  have h5 : 5 ≤ Nat.card Rw := by
    have hfinR : Finite Rw := Finite.Set.subset (S : Set X) hRS
    have h1 : (({1, x, x', x * x', w} : Finset X) : Set X).ncard ≤ (Rw : Set X).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hT] at h1
    exact h1
  have hdvd : Nat.card Rw ∣ 8 := by
    have := Subgroup.card_dvd_of_le hRS
    rwa [hS8] at this
  have hle8 : Nat.card Rw ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hRw8 : Nat.card Rw = 8 := by
    generalize hn : Nat.card Rw = n at h5 hdvd hle8
    interval_cases n <;> first | rfl | exact absurd hdvd (by norm_num)
  have hEq : Rw = S := Subgroup.eq_of_le_of_card_ge hRS (by rw [hS8, hRw8])
  intro s hs
  have hsR : s ∈ Rw := by
    rw [hEq]
    exact hs
  exact hsR.2

theorem beta_eq_zero_of_orbit {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8)
    (yl : G) {y : X} (hyl : D.ψ yl = y) (hy : orderOf y = 7)
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1)
    {w : X} (hw : w ∈ S) (hw1 : w ≠ 1) (hwrad : ∀ s ∈ S, D.beta w s = 1) {x x' : X}
    (hx : x ∈ S) (hx' : x' ∈ S) : D.beta x x' = 1 := by
  have hy7 : y ^ 7 = 1 := by rw [← hy, pow_orderOf_eq_one]
  have hinv : y ^ 6 = y⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← pow_succ', hy7]
  have hpropagate : ∀ u ∈ S, (∀ s ∈ S, D.beta u s = 1) →
      ∀ s ∈ S, D.beta (y * u * y⁻¹) s = 1 := by
    intro u hu hus s hs
    have hy6 : y ^ 6 * s * (y ^ 6)⁻¹ ∈ S := conj_pow_mem hyS hs 6
    have hs' : y⁻¹ * s * y ∈ S := by
      have e : y⁻¹ * s * y = y ^ 6 * s * (y ^ 6)⁻¹ := by
        rw [hinv, inv_inv]
      rw [e]
      exact hy6
    have hs_eq : s = y * (y⁻¹ * s * y) * y⁻¹ := by group
    have hconj := D.beta_conj hS2 yl hyl hu hs'
    rw [hs_eq]
    rw [← hs_eq]
    rw [show s = y * (y⁻¹ * s * y) * y⁻¹ from hs_eq]
    exact hconj.trans (hus _ hs')
  have hall : ∀ k : ℕ, ∀ s ∈ S, D.beta (y ^ k * w * (y ^ k)⁻¹) s = 1 := by
    intro k
    induction k with
    | zero => simpa using hwrad
    | succ k ih =>
      have e : y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      exact hpropagate _ (conj_pow_mem hyS hw k) ih
  rcases orbit_of_ne_one hy hS8 hyS hfpf hw hw1 hx with h | ⟨k, -, h⟩
  · rw [h]
    exact D.beta_one_left x'
  · rw [h]
    exact hall k x' hx'

theorem beta_eq_one {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8)
    (yl : G) {y : X} (hyl : D.ψ yl = y) (hy : orderOf y = 7)
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1)
    {x x' : X} (hx : x ∈ S) (hx' : x' ∈ S) : D.beta x x' = 1 := by
  classical
  by_contra hne
  have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [hS8]; norm_num)
  haveI : Fintype S := Fintype.ofFinite S
  have hcardS : Fintype.card S = 8 := by rw [← Nat.card_eq_fintype_card, hS8]
  have hdec : ∀ p q : G, (p = 1 ∨ p = D.neg) → (q = 1 ∨ q = D.neg) →
      (p = 1 ↔ q = 1) → p = q := by
    intro p q hp hq hpq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · exact absurd (hpq.1 rfl) D.neg_ne_one
    · exact absurd (hpq.2 rfl) D.neg_ne_one
    · rfl
  obtain ⟨u, u', hne', heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun u : S => (decide (D.beta u.1 x = 1), decide (D.beta u.1 x' = 1)))
    (by rw [hcardS]; simp)
  have hu1 : D.beta u.1 x = D.beta u'.1 x :=
    hdec _ _ (D.beta_val hS2 u.2 hx) (D.beta_val hS2 u'.2 hx)
      (decide_eq_decide.1 (congrArg Prod.fst heq))
  have hu2 : D.beta u.1 x' = D.beta u'.1 x' :=
    hdec _ _ (D.beta_val hS2 u.2 hx') (D.beta_val hS2 u'.2 hx')
      (decide_eq_decide.1 (congrArg Prod.snd heq))
  have hwS : u.1 * u'.1 ∈ S := S.mul_mem u.2 u'.2
  have hw1 : u.1 * u'.1 ≠ 1 := by
    intro h
    apply hne'
    apply Subtype.ext
    have e : u'.1 = u.1⁻¹ * (u.1 * u'.1) := by group
    rw [e, h, mul_one, inv_eq_of_mul_eq_one_right (hS2 u.1 u.2)]
  have hwx : D.beta (u.1 * u'.1) x = 1 := by
    rw [D.beta_mul_left hS2 u.2 u'.2 hx, ← hu1]
    exact D.beta_sq hS2 u.2 hx
  have hwx' : D.beta (u.1 * u'.1) x' = 1 := by
    rw [D.beta_mul_left hS2 u.2 u'.2 hx', ← hu2]
    exact D.beta_sq hS2 u.2 hx'
  generalize hw : u.1 * u'.1 = w at hwS hw1 hwx hwx'
  have h1x : (1 : X) ≠ x := by
    intro h
    apply hne
    rw [← h]
    exact D.beta_one_left x'
  have h1x' : (1 : X) ≠ x' := by
    intro h
    apply hne
    rw [← h]
    exact D.beta_one_right x
  have h1xx' : (1 : X) ≠ x * x' := by
    intro h
    have hxx : x' = x := by
      calc x' = x⁻¹ * (x * x') := by group
        _ = x⁻¹ * 1 := by rw [← h]
        _ = x := by rw [mul_one, inv_eq_of_mul_eq_one_right (hS2 x hx)]
    apply hne
    rw [hxx]
    exact D.beta_self x
  have hxx' : x ≠ x' := by
    intro h
    apply hne
    rw [h]
    exact D.beta_self x'
  have hxxx' : x ≠ x * x' := by
    intro h
    have hx'1 : x' = 1 := by
      calc x' = x⁻¹ * (x * x') := by group
        _ = x⁻¹ * x := by rw [← h]
        _ = 1 := by group
    exact h1x' hx'1.symm
  have hx'xx' : x' ≠ x * x' := by
    intro h
    have hx1 : x = 1 := by
      calc x = x * x' * x'⁻¹ := by group
        _ = x' * x'⁻¹ := by rw [← h]
        _ = 1 := by group
    exact h1x hx1.symm
  have hxw : x ≠ w := by
    intro h
    apply hne
    rw [h]
    exact hwx'
  have hx'w : x' ≠ w := by
    intro h
    apply hne
    rw [← D.beta_symm hS2 hx hx', h]
    exact hwx
  have hxx'w : x * x' ≠ w := by
    intro h
    have hwx_eq : D.beta w x = D.beta x x' := by
      rw [← h, D.beta_mul_left hS2 hx hx' hx, D.beta_self, one_mul,
        D.beta_symm hS2 hx hx']
    apply hne
    rw [← hwx_eq]
    exact hwx
  have h1w : (1 : X) ≠ w := fun h => hw1 h.symm
  have hrad : ∀ s ∈ S, D.beta w s = 1 :=
    radical_eq_all D hS2 hS8 hwS hx hx' hwx hwx' h1x h1x' h1xx' h1w hxx' hxxx' hxw hx'xx' hx'w
      hxx'w
  exact hne (beta_eq_zero_of_orbit D hS2 hS8 yl hyl hy hyS hfpf hwS hw1 hrad hx hx')

end LiftSetup

end CFSG.GF2Type.Smith1979.Case2.U43Grp
