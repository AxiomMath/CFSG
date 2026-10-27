module

public import CFSG.Holt.StarCase.Defs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.Holt.StarLemma26

open MulAction Equiv Equiv.Perm
open scoped Pointwise

section FourGroup

variable {X : Type*} [Group X]

def fourSubgroup {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup X where
  carrier := {1, a, b, a * b}
  mul_mem' := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
    have h3 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
    have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
    have h6 : b * a = a * b := hab.symm
    rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, one_mul, mul_one, ha, hb, h1, h2, h3,
        h4, h5, h6, true_or, or_true]
  one_mem' := Or.inl rfl
  inv_mem' := by
    have h5 : a * b * (a * b) = 1 := by
      rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]
    rintro x (rfl | rfl | rfl | rfl)
    · simp
    · rw [inv_eq_of_mul_eq_one_right ha]
      exact Or.inr (Or.inl rfl)
    · rw [inv_eq_of_mul_eq_one_right hb]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [inv_eq_of_mul_eq_one_right h5]
      exact Or.inr (Or.inr (Or.inr rfl))

variable {a b : X} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}

theorem mem_fourSubgroup {x : X} :
    x ∈ fourSubgroup ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem mul_self_of_mem_fourSubgroup {x : X} (hx : x ∈ fourSubgroup ha hb hab) : x * x = 1 := by
  rcases hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact ha
  · exact hb
  · rw [← mul_assoc, mul_assoc a b a, ← hab, ← mul_assoc, ha, one_mul, hb]

theorem card_fourSubgroup (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (fourSubgroup ha hb hab) = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [← mul_one a, ← h, ← mul_assoc, ha, one_mul])
  have haab : a ≠ a * b := fun h => hb1 (by
    rw [← one_mul b, ← ha, mul_assoc, ← h, ha])
  have hbab : b ≠ a * b := fun h => ha1 (by
    rw [← mul_one a, ← hb, ← mul_assoc, ← h, hb])
  change Nat.card ({1, a, b, a * b} : Set X) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_pair hbab]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, haab⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩

theorem le_of_forall_commute_mem [Finite X] {N K : Subgroup X} (hN : Odd (Nat.card N))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (haN : a ∈ Subgroup.normalizer (N : Set X)) (hbN : b ∈ Subgroup.normalizer (N : Set X))
    (hK : ∀ w ∈ ({a, b, a * b} : Set X), ∀ n ∈ N, w * n = n * w → n ∈ K) : N ≤ K := by
  by_cases ha1 : a = 1
  · exact fun n hn => hK a (Or.inl rfl) n hn (by rw [ha1, one_mul, mul_one])
  by_cases hb1 : b = 1
  · exact fun n hn => hK b (Or.inr (Or.inl rfl)) n hn (by rw [hb1, one_mul, mul_one])
  by_cases hne : a = b
  · refine fun n hn => hK (a * b) (Or.inr (Or.inr rfl)) n hn ?_
    rw [hne, hb, one_mul, mul_one]
  set W := fourSubgroup ha hb hab
  have hWN : W ≤ Subgroup.normalizer (N : Set X) := by
    rintro w (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact haN
    · exact hbN
    · exact mul_mem haN hbN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction ↥W ↥N := MulDistribMulAction.compHom ↥N (Subgroup.inclusion hWN)
  have hsmul : ∀ (w : ↥W) (y : ↥N), ((w • y : ↥N) : X) = w * y * (w : X)⁻¹ := fun _ _ => rfl
  have hWinv : ∀ w : ↥W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (Subtype.ext (mul_self_of_mem_fourSubgroup w.2))
  have : CFSG.IsElementaryAbelian 2 ↥W :=
    { toIsMulCommutative := ⟨⟨fun v w => by
        calc v * w = (v * w)⁻¹ := (hWinv _).symm
          _ = w⁻¹ * v⁻¹ := mul_inv_rev v w
          _ = w * v := by rw [hWinv, hWinv]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun w => by
        rw [sq]
        exact Subtype.ext (mul_self_of_mem_fourSubgroup w.2) }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := ↥W) (H := ↥N)
    (by rw [card_fourSubgroup ha1 hb1 hne]; norm_num) (fun h => (Nat.not_even_iff_odd.mpr hN)
      (even_iff_two_dvd.mpr h))
  intro n hn
  have hmem : (⟨n, hn⟩ : ↥N) ∈ ⨆ (w : ↥W) (_ : w ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers w) ↥N := by
    rw [hgen]
    exact Subgroup.mem_top _
  refine Subgroup.iSup_induction _ (C := fun z : ↥N => (z : X) ∈ K) hmem ?_ (one_mem K)
    fun _ _ hx hy => mul_mem hx hy
  intro w z hz
  by_cases hw : w = 1
  · rw [iSup_neg (not_not.mpr hw), Subgroup.mem_bot] at hz
    rw [hz]
    exact one_mem K
  rw [iSup_pos hw, CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hz
  have hz' : (w : X) * z * (w : X)⁻¹ = z := by rw [← hsmul, hz]
  have hwmem : (w : X) ∈ ({a, b, a * b} : Set X) := by
    rcases w.2 with h | h | h | h
    · exact absurd (Subtype.ext h) hw
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  refine hK _ hwmem z z.2 ?_
  calc (w : X) * z = (w : X) * z * (w : X)⁻¹ * w := by group
    _ = z * w := by rw [hz']

end FourGroup

section OddCore

theorem oddCore_eq_pPrimeCore_two (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  simp_rw [Nat.coprime_two_left]

theorem odd_card_oddCore (H : Type*) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

end OddCore

section StarDataFacts

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω]
  (D : StarData G Ω)

@[expose] def bar (g : G) (hg : g ∈ stabilizer G D.Δ) : Perm D.Δ :=
  inducedHom (stabilizer G D.Δ) D.Δ le_rfl ⟨g, hg⟩

@[simp] theorem coe_bar_apply {g : G} (hg : g ∈ stabilizer G D.Δ) (δ : D.Δ) :
    (bar D g hg δ : Ω) = g • (δ : Ω) := rfl

end StarDataFacts

end CFSG.Holt.StarLemma26
