module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.CGT.PushingUpLit.CGT6.TwoFiveAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv
open CFSG.ComponentClassification.OutcomeLocal

variable {n : ℕ}

theorem mem_fixSub_coreAct {σ : Perm (Fin n)} {x : coreMod n} :
    x ∈ fixSub (coreAct n σ) ↔ ∀ k, Multiplicative.toAdd (x : PermMod n) (σ⁻¹ k) =
      Multiplicative.toAdd (x : PermMod n) k := by
  rw [mem_fixSub]
  constructor
  · intro h k
    have := congrArg (fun y : coreMod n => Multiplicative.toAdd (y : PermMod n) k) h
    exact this
  · intro h
    exact Subtype.ext (Multiplicative.toAdd.injective (funext h))

theorem exists_mem_coreMod_apply_ne {i j : Fin n} (hij : i ≠ j) (hn : 3 ≤ n) :
    ∃ x : coreMod n, Multiplicative.toAdd (x : PermMod n) i + Multiplicative.toAdd (x : PermMod n) j
      = 1 := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin n))) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by simpa using (by omega : 2 < n)))
  have hki : k ≠ i := fun e => hk (by simp [e])
  have hkj : k ≠ j := fun e => hk (by simp [e])
  refine ⟨⟨Multiplicative.ofAdd (Pi.single i 1 + Pi.single k 1), ?_⟩, ?_⟩
  · rw [mem_coreMod]
    simp [Finset.sum_add_distrib]
    decide
  · simp [hki.symm, hkj.symm, hij.symm]

theorem card_coreMod_eq_two_mul_fix_swap {i j : Fin n} (hij : i ≠ j) (hn : 3 ≤ n) :
    Nat.card (coreMod n) = 2 * Nat.card (fixSub (coreAct n (swap i j))) := by
  let f : coreMod n →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd
        (Multiplicative.toAdd (x : PermMod n) i + Multiplicative.toAdd (x : PermMod n) j)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, toAdd_mul, Pi.add_apply, ofAdd_add]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : f.ker = fixSub (coreAct n (swap i j)) := by
    ext x
    rw [MonoidHom.mem_ker, mem_fixSub_coreAct]
    have hf : f x = Multiplicative.ofAdd (Multiplicative.toAdd (x : PermMod n) i +
        Multiplicative.toAdd (x : PermMod n) j) := rfl
    rw [hf, ofAdd_eq_one]
    constructor
    · intro h k
      have e : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      by_cases hki : k = i
      · subst hki
        rw [Equiv.swap_inv, swap_apply_left]
        exact (e _ _ h).symm
      · by_cases hkj : k = j
        · subst hkj
          rw [Equiv.swap_inv, swap_apply_right]
          exact e _ _ h
        · rw [Equiv.swap_inv, swap_apply_of_ne_of_ne hki hkj]
    · intro h
      have := h i
      rw [Equiv.swap_inv, swap_apply_left] at this
      rw [this]
      exact zmod2_scalar_add_self _
  have hrange : f.range = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, hx⟩ := exists_mem_coreMod_apply_ne hij hn
    rcases zmod2_eq_zero_or_one (Multiplicative.toAdd y) with h0 | h1
    · have : y = 1 := by
        rw [← ofAdd_toAdd y, h0]
        rfl
      rw [this]
      exact Subgroup.one_mem _
    · refine ⟨x, ?_⟩
      have : y = Multiplicative.ofAdd 1 := by rw [← h1]; rfl
      rw [this]
      change Multiplicative.ofAdd (Multiplicative.toAdd (x : PermMod n) i +
        Multiplicative.toAdd (x : PermMod n) j) = _
      rw [hx]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, Subgroup.card_top] at hcard
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [← hcard, h2, mul_comm]

theorem sum_one_sub_single (hn : Odd n) (x : Fin n) :
    ∑ k, (1 - (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k) = 0 := by
  have h1 : ∑ k : Fin n, (1 - (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k) =
      ∑ k : Fin n, (1 : ZMod 2) - ∑ k : Fin n, (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k :=
    Finset.sum_sub_distrib (fun _ => (1 : ZMod 2)) (fun k => (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k)
  rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∑ k : Fin n, (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k = 1 := by
    rw [Finset.sum_pi_single']
    simp
  rw [h2]
  have : (n : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 hn
  rw [nsmul_eq_mul, mul_one, this]
  decide

@[expose] def wvec (hn : Odd n) (x : Fin n) : coreMod n :=
  ⟨Multiplicative.ofAdd (fun k => 1 - (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k), by
    rw [mem_coreMod]
    exact sum_one_sub_single hn x⟩

theorem toAdd_wvec (hn : Odd n) (x k : Fin n) :
    Multiplicative.toAdd ((wvec hn x : coreMod n) : PermMod n) k =
      1 - (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k := rfl

theorem wvec_shift (hn : Odd n) (π : Perm (Fin n)) (x k : Fin n) :
    Multiplicative.toAdd ((wvec hn x : coreMod n) : PermMod n) k +
      Multiplicative.toAdd ((wvec hn x : coreMod n) : PermMod n) (π⁻¹ k) =
    (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k +
      (Pi.single (π x) (1 : ZMod 2) : Fin n → ZMod 2) k := by
  rw [toAdd_wvec, toAdd_wvec]
  have hk : π⁻¹ k = x ↔ k = π x := by
    rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]
  have hc : (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) (π⁻¹ k) =
      (Pi.single (π x) (1 : ZMod 2) : Fin n → ZMod 2) k := by
    simp only [Pi.single_apply]
    exact if_congr hk rfl rfl
  rw [hc]
  generalize (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k = a
  generalize (Pi.single (π x) (1 : ZMod 2) : Fin n → ZMod 2) k = b
  revert a b
  decide

theorem coe_mul_apply (a b : coreMod n) (k : Fin n) :
    Multiplicative.toAdd ((a * b : coreMod n) : PermMod n) k =
      Multiplicative.toAdd (a : PermMod n) k + Multiplicative.toAdd (b : PermMod n) k := rfl

theorem wvec_notMem_fix (hn : Odd n) {π : Perm (Fin n)} {x : Fin n} (hx : π x ≠ x) :
    wvec hn x ∉ fixSub (coreAct n π) := by
  intro h
  have := (mem_fixSub_coreAct.1 h) (π x)
  simp [toAdd_wvec, hx] at this
  revert this
  decide

theorem isSwap_of_card_le_two_mul_fix {π : Perm (Fin n)} (hn : Odd n) (hπ : π ≠ 1)
    (h : Nat.card (coreMod n) ≤ 2 * Nat.card (fixSub (coreAct n π))) : π.IsSwap := by
  by_contra hns
  set K := fixSub (coreAct n π) with hK
  have hsupp : 3 ≤ π.support.card := by
    have h0 : π.support.card ≠ 0 := fun h0 => hπ (Equiv.Perm.support_eq_empty_iff.1
      (Finset.card_eq_zero.1 h0))
    have h1 : π.support.card ≠ 1 := Equiv.Perm.card_support_ne_one π
    have h2 : π.support.card ≠ 2 := fun h2 => hns (Equiv.Perm.card_support_eq_two.1 h2)
    omega
  obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
    by_contra hall
    push Not at hall
    exact hπ (Equiv.ext hall)
  obtain ⟨x', hx'S, hx'n⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, π x} : Finset (Fin n))) (t := π.support)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hx'm : π x' ≠ x' := Equiv.Perm.mem_support.1 hx'S
  have hx'x : x' ≠ x := fun e => hx'n (by simp [e])
  have hx'πx : x' ≠ π x := fun e => hx'n (by simp [e])
  have hmul2 : ∀ w : coreMod n, w * w = 1 := fun w => by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext k
    simp only [coe_mul_apply, OneMemClass.coe_one, toAdd_one, Pi.zero_apply]
    exact zmod2_scalar_add_self _
  have hcomm : ∀ a b : coreMod n, a * b = b * a := fun a b => by
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext k
    simp only [coe_mul_apply]
    exact add_comm _ _
  have hidx : K.index ≤ 2 := by
    have h1 := Subgroup.card_mul_index K
    have hpos : 0 < Nat.card K := Nat.card_pos
    by_contra hgt
    push Not at hgt
    have : Nat.card K * 3 ≤ Nat.card K * K.index := Nat.mul_le_mul_left _ hgt
    omega
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hkey : ∀ a b : coreMod n, a ∈ K ∨ b ∈ K ∨ a * b ∈ K := by
    intro a b
    have hi : K.index = 1 ∨ K.index = 2 := by omega
    rcases hi with h1 | h2
    · left
      rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top a
    · obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.1 h2
      by_cases ha : a ∈ K
      · exact Or.inl ha
      by_cases hb : b ∈ K
      · exact Or.inr (Or.inl hb)
      right
      right
      have hac : a * c ∈ K := by
        rcases hc a with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h ha
      have hbc : b * c ∈ K := by
        rcases hc b with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hb
      have : a * b = (a * c) * (b * c) := by
        calc a * b = a * b * (c * c) := by rw [hmul2 c, mul_one]
          _ = (a * c) * (b * c) := by
            calc a * b * (c * c) = a * (b * c) * c := by group
              _ = a * (c * b) * c := by rw [hcomm b c]
              _ = (a * c) * (b * c) := by group
      rw [this]
      exact K.mul_mem hac hbc
  have ha := wvec_notMem_fix hn hx
  have hb := wvec_notMem_fix hn hx'm
  have hab : wvec hn x * wvec hn x' ∉ K := by
    intro hmem
    have hf := mem_fixSub_coreAct.1 hmem
    have hsum : ∀ k : Fin n, (Pi.single x (1 : ZMod 2) : Fin n → ZMod 2) k +
        (Pi.single (π x) (1 : ZMod 2) : Fin n → ZMod 2) k +
        ((Pi.single x' (1 : ZMod 2) : Fin n → ZMod 2) k +
        (Pi.single (π x') (1 : ZMod 2) : Fin n → ZMod 2) k) = 0 := by
      intro k
      rw [← wvec_shift hn π x k, ← wvec_shift hn π x' k]
      have := hf k
      rw [coe_mul_apply, coe_mul_apply] at this
      generalize Multiplicative.toAdd ((wvec hn x : coreMod n) : PermMod n) k = a1 at this ⊢
      generalize Multiplicative.toAdd ((wvec hn x : coreMod n) : PermMod n) (π⁻¹ k) = a2 at this ⊢
      generalize Multiplicative.toAdd ((wvec hn x' : coreMod n) : PermMod n) k = b1 at this ⊢
      generalize Multiplicative.toAdd ((wvec hn x' : coreMod n) : PermMod n) (π⁻¹ k) = b2 at this ⊢
      revert a1 a2 b1 b2
      decide
    by_cases hc : x = π x'
    · have := hsum (π x)
      simp [hx, hx'πx.symm, hc.symm] at this
    · have := hsum x
      simp [hx.symm, hx'x.symm, hc] at this
  rcases hkey (wvec hn x) (wvec hn x') with h1 | h1 | h1
  · exact ha h1
  · exact hb h1
  · exact hab h1

end CFSG.CGT.PushingUpLit.CGT6
