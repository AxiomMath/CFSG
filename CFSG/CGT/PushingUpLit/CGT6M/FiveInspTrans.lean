module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspCover

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement

section Map

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem heisInv_map (κ : Q →* Q') (hκ : Function.Injective κ) {w : Q} (h : HeisInv Q w) :
    HeisInv Q' (κ w) := by
  obtain ⟨X, Y, hX5, hY5, hZX, hZY, hZ1, hinv⟩ := h
  refine ⟨κ X, κ Y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hX5, map_one]
  · rw [← map_pow, hY5, map_one]
  · rw [← map_commutatorElement]
    exact hZX.map κ
  · rw [← map_commutatorElement]
    exact hZY.map κ
  · rw [← map_commutatorElement]
    intro h1
    exact hZ1 (hκ (h1.trans (map_one κ).symm))
  · have := congrArg κ hinv
    simpa using this

theorem invData_map (κ : Q →* Q') (hκ : Function.Injective κ) {w : Q} (h : InvData Q w) :
    InvData Q' (κ w) := by
  rcases h with ⟨Φ, hΦ, hinv⟩ | h
  · refine Or.inl ⟨κ.comp Φ, hκ.comp hΦ, fun u => ?_⟩
    have := congrArg κ (hinv u)
    simpa using this
  · exact Or.inr (heisInv_map κ hκ h)

end Map

section Pair

variable {Q : Type*} [Group Q]

theorem invData_of_pair {w X Y : Q} (hX : X ^ 5 = 1) (hY : Y ^ 5 = 1) (hXY : Commute X Y)
    (hind : ∀ i j : ZMod 5, X ^ i.val * Y ^ j.val = 1 → i = 0 ∧ j = 0)
    (hwX : w * X * w⁻¹ = X⁻¹) (hwY : w * Y * w⁻¹ = Y⁻¹) : InvData Q w := by
  refine Or.inl ⟨phi X Y hX hY hXY, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ v, u = Multiplicative.ofAdd v := ⟨Multiplicative.toAdd u, rfl⟩
    rw [phi_ofAdd] at hu
    obtain ⟨rfl, rfl⟩ := hind i j hu
    rfl
  · intro u
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ v, u = Multiplicative.ofAdd v := ⟨Multiplicative.toAdd u, rfl⟩
    rw [phi_ofAdd]
    have h1 : w * (X ^ i.val * Y ^ j.val) * w⁻¹ =
        (w * X * w⁻¹) ^ i.val * (w * Y * w⁻¹) ^ j.val := by
      rw [conj_pow, conj_pow]
      group
    rw [h1, hwX, hwY, mul_inv_rev, inv_pow, inv_pow]
    exact ((hXY.pow_pow i.val j.val).inv_inv).eq

end Pair

section Conj

variable {Q M : Type*} [Group Q] [Group M]

theorem invData_of_conj (ι : Q →* M) (hι : Function.Injective ι) (h : M)
    (hN : ∀ q : Q, ∃ q' : Q, ι q' = h⁻¹ * ι q * h) {t w : Q} (htw : ι t = h⁻¹ * ι w * h)
    (hw : InvData Q w) : InvData Q t := by
  choose κ hκ using hN
  let κ' : Q →* Q := MonoidHom.mk' κ fun a b => hι (by
    rw [hκ, map_mul ι (κ a) (κ b), hκ, hκ, map_mul]
    group)
  have hκ' : Function.Injective κ' := fun a b hab => hι (by
    have h1 := hκ a
    have h2 := hκ b
    have h3 : h⁻¹ * ι a * h = h⁻¹ * ι b * h := by rw [← h1, ← h2]; exact congrArg ι hab
    exact mul_left_cancel (mul_right_cancel h3))
  have hκw : κ' w = t := hι (by rw [htw]; exact hκ w)
  rw [← hκw]
  exact invData_map κ' hκ' hw

end Conj

section Field

variable {K : Type*} [Field K] [CharP K 5]

theorem zmod_eq_zero_of_cast_eq_zero {i : ZMod 5} (h : ((i.val : ℕ) : K) = 0) : i = 0 := by
  have h5 : 5 ∣ i.val := (CharP.cast_eq_zero_iff K 5 i.val).1 h
  have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h5 (ZMod.val_lt i)
  exact (ZMod.val_eq_zero i).1 h0

theorem exists_pair_indep [Finite K] (hK : 5 < Nat.card K) :
    ∃ c : K, ∀ i j : ZMod 5, ((i.val : ℕ) : K) + ((j.val : ℕ) : K) * c = 0 → i = 0 ∧ j = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : Algebra (ZMod 5) K := ZMod.algebra K 5
  have : Module.Finite (ZMod 5) K := Module.Finite.of_finite
  have hrank : 1 < Module.finrank (ZMod 5) K := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 5) (V := K)
    rw [Nat.card_zmod] at h1
    by_contra hle
    push Not at hle
    have : Nat.card K ≤ 5 ^ 1 := by
      rw [h1]
      exact Nat.pow_le_pow_right (by norm_num) hle
    omega
  obtain ⟨c, hc⟩ :=
    exists_linearIndependent_pair_of_one_lt_finrank hrank (one_ne_zero : (1 : K) ≠ 0)
  refine ⟨c, fun i j h => hc.eq_zero_of_pair ?_⟩
  show (ZMod.cast i : K) * 1 + (ZMod.cast j : K) * c = 0
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val, mul_one]
  exact h

end Field

end CFSG.CGT.PushingUpLit.CGT6M
