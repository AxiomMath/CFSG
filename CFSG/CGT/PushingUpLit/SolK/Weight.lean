module

public import CFSG.CGT.PushingUpLit.SolK.Vec

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ}

theorem card_vsupp_mul_of_disjoint {v w : ↥(coreMod d)}
    (h : ∀ i, vcoord v i = 1 → vcoord w i = 0) (h' : ∀ i, vcoord w i = 1 → vcoord v i = 0) :
    (vsupp (v * w)).card = (vsupp v).card + (vsupp w).card := by
  classical
  have hdisj : Disjoint (vsupp v) (vsupp w) := by
    rw [Finset.disjoint_left]
    intro i hv hw
    rw [mem_vsupp] at hv hw
    have := h i hv
    rw [hw] at this
    exact one_ne_zero this
  have hunion : vsupp (v * w) = vsupp v ∪ vsupp w := by
    ext i
    simp only [Finset.mem_union, mem_vsupp, vcoord_mul]
    constructor
    · intro hi
      by_contra hcon
      push Not at hcon
      have h1 : vcoord v i = 0 := by
        generalize vcoord v i = a at hcon ⊢
        generalize vcoord w i = b at hcon ⊢
        revert a b
        decide
      have h2 : vcoord w i = 0 := by
        generalize vcoord v i = a at hcon ⊢
        generalize vcoord w i = b at hcon ⊢
        revert a b
        decide
      rw [h1, h2] at hi
      exact zero_ne_one hi
    · rintro (hi | hi)
      · rw [hi, h i hi, add_zero]
      · rw [hi, h' i hi, zero_add]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem card_le_four_of_weight_two (V : Subgroup ↥(coreMod d))
    (h : ∀ v ∈ V, v ≠ 1 → (vsupp v).card = 2) : Nat.card ↥V ≤ 4 := by
  classical
  by_cases hV : ∀ v ∈ V, v = 1
  · have : Nat.card ↥V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hV a a.2).trans (hV b b.2).symm)⟩, ⟨1⟩⟩
    omega
  · push Not at hV
    obtain ⟨v, hvV, hv1⟩ := hV
    obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.1 (h v hvV hv1)
    have ha : vcoord v a = 1 := by
      have : a ∈ vsupp v := by rw [hsupp]; simp
      exact mem_vsupp.1 this
    have hb : vcoord v b = 1 := by
      have : b ∈ vsupp v := by rw [hsupp]; simp
      exact mem_vsupp.1 this
    have hvab : ∀ i, vcoord v i = 1 → i = a ∨ i = b := by
      intro i hi
      have : i ∈ vsupp v := mem_vsupp.2 hi
      rw [hsupp] at this
      simpa using this
    let φ : ↥V → ZMod 2 × ZMod 2 := fun u =>
      (vcoord (u : ↥(coreMod d)) a, vcoord (u : ↥(coreMod d)) b)
    have hφ : Function.Injective φ := by
      intro u u' huu'
      have h1 : vcoord (u : ↥(coreMod d)) a = vcoord (u' : ↥(coreMod d)) a := congrArg Prod.fst huu'
      have h2 : vcoord (u : ↥(coreMod d)) b = vcoord (u' : ↥(coreMod d)) b := congrArg Prod.snd huu'
      set u0 : ↥(coreMod d) := u.1 with hu0
      set u1 : ↥(coreMod d) := u'.1 with hu1
      set w : ↥(coreMod d) := u0 * u1⁻¹ with hw
      have hwV : w ∈ V := V.mul_mem u.2 (V.inv_mem u'.2)
      have hwc : ∀ i, vcoord w i = vcoord u0 i + vcoord u1 i := fun i => by
        rw [hw, vcoord_mul, vcoord_inv]
      have hwa : vcoord w a = 0 := by
        rw [hwc, h1]
        exact CharTwo.add_self_eq_zero _
      have hwb : vcoord w b = 0 := by
        rw [hwc, h2]
        exact CharTwo.add_self_eq_zero _
      have hw1 : w = 1 := by
        by_contra hw1
        have hw2 := h w hwV hw1
        have hvw : v * w ∈ V := V.mul_mem hvV hwV
        have hvw1 : v * w ≠ 1 := by
          intro hvw1
          have := congrArg (fun z => vcoord z a) hvw1
          simp only [vcoord_mul, vcoord_one, hwa, ha, add_zero] at this
          exact one_ne_zero this
        have hvw2 := h _ hvw hvw1
        have hd1 : ∀ i, vcoord v i = 1 → vcoord w i = 0 := fun i hi => by
          rcases hvab i hi with rfl | rfl
          · exact hwa
          · exact hwb
        have hd2 : ∀ i, vcoord w i = 1 → vcoord v i = 0 := fun i hi => by
          by_contra hcon
          have hvi : vcoord v i = 1 := by
            generalize vcoord v i = c at hcon ⊢
            revert c
            decide
          have := hd1 i hvi
          rw [hi] at this
          exact one_ne_zero this
        have := card_vsupp_mul_of_disjoint hd1 hd2
        rw [hvw2, hw2, h v hvV hv1] at this
        omega
      have : u0 = u1 := by
        have h2' : u0 * u1⁻¹ = 1 := hw1
        exact mul_inv_eq_one.1 h2'
      exact Subtype.ext this
    have := Nat.card_le_card_of_injective φ hφ
    rwa [Nat.card_prod, Nat.card_zmod] at this

end CFSG.CGT.PushingUpLit.SolK
