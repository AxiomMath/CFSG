module

public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

section Vectors

variable {n : ℕ}

private theorem natCast_two_of_odd (hn : Odd n) : ((n : ℕ) : ZMod 2) = 1 :=
  (ZMod.natCast_eq_one_iff_odd).2 hn

@[expose] def altBaumY (hn : Odd n) (x : Fin n) : evenWeight n :=
  ⟨fun i => if i = x then 0 else 1, by
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    have h1 : ∑ i : Fin n, (if i = x then (0 : ZMod 2) else 1) = ((n : ℕ) : ZMod 2) - 1 := by
      rw [Finset.sum_ite]
      simp [Finset.filter_ne', Finset.card_erase_of_mem]
      rw [Nat.cast_sub (Fin.pos x), Nat.cast_one]
    rw [h1, natCast_two_of_odd hn]; simp⟩

theorem altBaumY_apply (hn : Odd n) (x i : Fin n) :
    ((altBaumY hn x : evenWeight n) : Fin n → ZMod 2) i = if i = x then 0 else 1 := rfl

theorem evenWeightPerm_altBaumY (hn : Odd n) (σ : Perm (Fin n)) (x : Fin n) :
    evenWeightPerm σ (altBaumY hn x) = altBaumY hn (σ x) := by
  apply Subtype.ext
  funext i
  show ((altBaumY hn x : evenWeight n) : Fin n → ZMod 2) (σ⁻¹ i) =
    ((altBaumY hn (σ x) : evenWeight n) : Fin n → ZMod 2) i
  rw [altBaumY_apply, altBaumY_apply]
  by_cases h : i = σ x
  · subst h; simp
  · have : σ⁻¹ i ≠ x := fun h' => h (by rw [← h']; simp)
    rw [if_neg h, if_neg this]

theorem altBaumY_ne_zero (hn : Odd n) (h2 : 2 ≤ n) (x : Fin n) : altBaumY hn x ≠ 0 := by
  intro h
  have h1 : ((altBaumY hn x : evenWeight n) : Fin n → ZMod 2)
      (if x.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩) = 0 := by
    rw [h]; rfl
  split_ifs at h1 with hx
  · rw [altBaumY_apply] at h1
    have : (⟨1, by omega⟩ : Fin n) ≠ x := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    simp [this] at h1
  · rw [altBaumY_apply] at h1
    have : (⟨0, by omega⟩ : Fin n) ≠ x := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    simp [this] at h1

theorem altHeart_mk_injective (hn : Odd n) :
    Function.Injective (QuotientAddGroup.mk : evenWeight n → altHeart n) := by
  intro a b hab
  have h := (QuotientAddGroup.eq).1 hab
  simp only [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at h
  obtain ⟨k, hk⟩ := h
  have hc : ∀ i, ((-a + b : evenWeight n) : Fin n → ZMod 2) i = (k : ZMod 2) := fun i => by
    rw [← hk]; simp [allOnes]
  have hsum : ∑ i : Fin n, ((-a + b : evenWeight n) : Fin n → ZMod 2) i = 0 := by
    exact AddMonoidHom.mem_ker.1 (-a + b : evenWeight n).2
  have hs2 : ∑ i : Fin n, ((-a + b : evenWeight n) : Fin n → ZMod 2) i =
      ((n : ℕ) : ZMod 2) * (k : ZMod 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hc i)]; simp
  rw [hs2, natCast_two_of_odd hn, one_mul] at hsum
  have h0 : ((-a + b : evenWeight n) : Fin n → ZMod 2) = 0 := by
    funext i; rw [hc, hsum]; rfl
  have : -a + b = 0 := Subtype.ext h0
  exact (neg_add_eq_zero.1 this)

theorem sum_val_smul_altBaumY (hn : Odd n) (v : evenWeight n) :
    ∑ x : Fin n, ((v : Fin n → ZMod 2) x).val • altBaumY hn x = v := by
  apply Subtype.ext
  funext i
  have hsum : ∑ x : Fin n, (v : Fin n → ZMod 2) x = 0 := AddMonoidHom.mem_ker.1 v.2
  have h1 : ((∑ x : Fin n, ((v : Fin n → ZMod 2) x).val • altBaumY hn x : evenWeight n) :
      Fin n → ZMod 2) i = ∑ x : Fin n, ((v : Fin n → ZMod 2) x) * (if i = x then 0 else 1) := by
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [AddSubgroup.coe_nsmul, Pi.smul_apply, altBaumY_apply, nsmul_eq_mul,
      ZMod.natCast_zmod_val]
  rw [h1]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, mul_zero, zero_add]
  have h2 : ∑ x ∈ Finset.univ.erase i, (v : Fin n → ZMod 2) x =
      ∑ x : Fin n, (v : Fin n → ZMod 2) x - (v : Fin n → ZMod 2) i :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  have h3 : ∑ x ∈ Finset.univ.erase i, (v : Fin n → ZMod 2) x * (if i = x then 0 else 1) =
      ∑ x ∈ Finset.univ.erase i, (v : Fin n → ZMod 2) x :=
    Finset.sum_congr rfl (fun x hx => by
      rw [if_neg (Finset.ne_of_mem_erase hx |>.symm), mul_one])
  rw [h3, h2, hsum]
  have : ∀ z : ZMod 2, 0 - z = z := by decide
  exact this _

private theorem exists_ne_three {n : ℕ} (h : 4 ≤ n) (a b c : Fin n) :
    ∃ d : Fin n, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  have hcard : ({a, b, c} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({a, b, c} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact ⟨d, hd.1, hd.2.1, hd.2.2⟩

private theorem swap_mul_swap_even {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    swap a b * swap b c ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
  decide

theorem eq_zero_or_eq_altBaumY_of_fixed (hn : Odd n) (h4 : 4 ≤ n) {x₀ : Fin n}
    {v : evenWeight n}
    (h : ∀ σ ∈ alternatingGroup (Fin n), σ x₀ = x₀ → evenWeightPerm σ v = v) :
    v = 0 ∨ v = altBaumY hn x₀ := by
  have hconst : ∀ a b : Fin n, a ≠ x₀ → b ≠ x₀ →
      (v : Fin n → ZMod 2) a = (v : Fin n → ZMod 2) b := by
    intro a b ha hb
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨c, hca, hcb, hcx⟩ := exists_ne_three h4 a b x₀
    have hσ : swap a b * swap b c ∈ alternatingGroup (Fin n) :=
      swap_mul_swap_even hab (Ne.symm hcb)
    have hσx : (swap a b * swap b c) x₀ = x₀ := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hb) (Ne.symm hcx),
        swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
    have hσa : (swap a b * swap b c) a = b := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab (Ne.symm hca), swap_apply_left]
    have h1 := congrArg (fun w : evenWeight n => (w : Fin n → ZMod 2) b) (h _ hσ hσx)
    have hinv : (swap a b * swap b c)⁻¹ b = a := by
      rw [Perm.inv_eq_iff_eq]; exact hσa.symm
    have : ((evenWeightPerm (swap a b * swap b c) v : evenWeight n) : Fin n → ZMod 2) b =
        (v : Fin n → ZMod 2) a := by
      show (v : Fin n → ZMod 2) ((swap a b * swap b c)⁻¹ b) = _
      rw [hinv]
    rw [this] at h1
    exact h1
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin n, i₁ ≠ x₀ := by
    by_contra hcon
    push Not at hcon
    have : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := (hcon _).trans (hcon _).symm
    simp at this
  set l : ZMod 2 := (v : Fin n → ZMod 2) i₁ with hl
  have hv : ∀ i, (v : Fin n → ZMod 2) i =
      if i = x₀ then (v : Fin n → ZMod 2) x₀ else l := by
    intro i
    by_cases hi : i = x₀
    · rw [if_pos hi, hi]
    · rw [if_neg hi]; exact hconst i i₁ hi hi₁
  have hsum : ∑ i : Fin n, (v : Fin n → ZMod 2) i = 0 := AddMonoidHom.mem_ker.1 v.2
  have hx0 : (v : Fin n → ZMod 2) x₀ = 0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x₀)] at hsum
    have : ∑ i ∈ Finset.univ.erase x₀, (v : Fin n → ZMod 2) i =
        ∑ i ∈ Finset.univ.erase x₀, l :=
      Finset.sum_congr rfl fun i hi => by
        rw [hv i, if_neg (Finset.ne_of_mem_erase hi)]
    rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have heven : ((n - 1 : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]
      obtain ⟨m, hm⟩ := hn
      exact ⟨m, by omega⟩
    rw [heven, zero_mul, add_zero] at hsum
    exact hsum
  have hl2 : l = 0 ∨ l = 1 := by
    generalize l = z; revert z; decide
  rcases hl2 with h0 | h1
  · left
    apply Subtype.ext
    funext i
    rw [hv i]
    by_cases hi : i = x₀
    · rw [if_pos hi, hx0]; rfl
    · rw [if_neg hi, h0]; rfl
  · right
    apply Subtype.ext
    funext i
    rw [hv i, altBaumY_apply]
    by_cases hi : i = x₀
    · rw [if_pos hi, if_pos hi, hx0]
    · rw [if_neg hi, if_neg hi, h1]

end Vectors

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
