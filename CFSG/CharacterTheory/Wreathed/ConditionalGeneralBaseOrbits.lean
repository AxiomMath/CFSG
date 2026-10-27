module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Wreathed.ConditionalGeneralBase

@[expose] def dualSwap (m : ℕ) : Equiv.Perm (ZMod m × ZMod m) := Equiv.prodComm (ZMod m) (ZMod m)

@[expose] def dualRotation (m : ℕ) : Equiv.Perm (ZMod m × ZMod m) where
  toFun I := (I.2, -I.1 - I.2)
  invFun I := (-I.1 - I.2, I.1)
  left_inv I := Prod.ext (by
    change -I.2 - (-I.1 - I.2) = I.1
    ring) rfl
  right_inv I := Prod.ext rfl (by
    change -(-I.1 - I.2) - I.1 = I.2
    ring)

@[expose] def dualGroup (m : ℕ) : Subgroup (Equiv.Perm (ZMod m × ZMod m)) :=
  Subgroup.closure {dualSwap m, dualRotation m}

@[expose] def dualSix {m : ℕ} (I : ZMod m × ZMod m) : List (ZMod m × ZMod m) :=
  [I, (I.2, I.1), (I.2, -I.1 - I.2), (-I.1 - I.2, I.1), (I.1, -I.1 - I.2), (-I.1 - I.2, I.2)]

variable {m : ℕ}

theorem dualSwap_apply (I : ZMod m × ZMod m) : dualSwap m I = (I.2, I.1) := rfl

theorem dualRotation_apply (I : ZMod m × ZMod m) : dualRotation m I = (I.2, -I.1 - I.2) := rfl

theorem dualRotation_inv_apply (I : ZMod m × ZMod m) :
    (dualRotation m)⁻¹ I = (-I.1 - I.2, I.1) := rfl

theorem dualSwap_inv : (dualSwap m)⁻¹ = dualSwap m := rfl

theorem mem_dualSix_iff {I J : ZMod m × ZMod m} :
    J ∈ dualSix I ↔ J = I ∨ J = (I.2, I.1) ∨ J = (I.2, -I.1 - I.2) ∨ J = (-I.1 - I.2, I.1) ∨
      J = (I.1, -I.1 - I.2) ∨ J = (-I.1 - I.2, I.2) := by
  simp [dualSix]

theorem mem_dualSix_self (I : ZMod m × ZMod m) : I ∈ dualSix I :=
  mem_dualSix_iff.mpr (Or.inl rfl)

theorem dualSwap_mem_dualSix {I K : ZMod m × ZMod m} (hK : K ∈ dualSix I) :
    dualSwap m K ∈ dualSix I := by
  rw [mem_dualSix_iff] at hK
  rw [mem_dualSix_iff]
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem dualRotation_mem_dualSix {I K : ZMod m × ZMod m} (hK : K ∈ dualSix I) :
    dualRotation m K ∈ dualSix I := by
  rw [mem_dualSix_iff] at hK
  rw [mem_dualSix_iff]
  rcases hK with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext rfl ?_)))))
    change -I.2 - I.1 = -I.1 - I.2
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext rfl ?_))))
    change -I.2 - (-I.1 - I.2) = I.1
    ring
  · refine Or.inl (Prod.ext rfl ?_)
    change -(-I.1 - I.2) - I.1 = I.2
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Prod.ext rfl ?_)))))
    change -I.1 - (-I.1 - I.2) = I.2
    ring
  · refine Or.inr (Or.inl (Prod.ext rfl ?_))
    change -(-I.1 - I.2) - I.2 = I.1
    ring

theorem dualRotation_inv : (dualRotation m)⁻¹ = dualRotation m * dualRotation m :=
  Equiv.ext fun I => Prod.ext rfl (by
    change I.1 = -I.2 - (-I.1 - I.2)
    ring)

theorem dualRotation_inv_mem_dualSix {I K : ZMod m × ZMod m} (hK : K ∈ dualSix I) :
    (dualRotation m)⁻¹ K ∈ dualSix I := by
  rw [dualRotation_inv]
  exact dualRotation_mem_dualSix (dualRotation_mem_dualSix hK)

theorem mem_orbit_dualGroup_iff (I J : ZMod m × ZMod m) :
    J ∈ MulAction.orbit (dualGroup m) I ↔ J ∈ dualSix I := by
  have hswap : dualSwap m ∈ dualGroup m := Subgroup.subset_closure (by simp)
  have hrot : dualRotation m ∈ dualGroup m := Subgroup.subset_closure (by simp)
  constructor
  · rintro ⟨g, rfl⟩
    have key : ∀ g ∈ dualGroup m, ∀ K ∈ dualSix I, g K ∈ dualSix I := by
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem x hx =>
        rcases hx with rfl | rfl
        · exact fun K hK => dualSwap_mem_dualSix hK
        · exact fun K hK => dualRotation_mem_dualSix hK
      | inv_mem x hx =>
        rcases hx with rfl | rfl
        · exact fun K hK => dualSwap_mem_dualSix hK
        · exact fun K hK => dualRotation_inv_mem_dualSix hK
      | one => exact fun K hK => hK
      | mul x y _ _ hx hy => exact fun K hK => hx _ (hy K hK)
    exact key g.1 g.2 I (mem_dualSix_self I)
  · intro hJ
    rw [mem_dualSix_iff] at hJ
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact MulAction.mem_orbit_self _
    · exact ⟨⟨dualSwap m, hswap⟩, rfl⟩
    · exact ⟨⟨dualRotation m, hrot⟩, rfl⟩
    · exact ⟨⟨dualRotation m * dualRotation m, mul_mem hrot hrot⟩, Prod.ext rfl (by
        change -I.2 - (-I.1 - I.2) = I.1
        ring)⟩
    · exact ⟨⟨dualSwap m * (dualRotation m * dualRotation m),
        mul_mem hswap (mul_mem hrot hrot)⟩, Prod.ext (by
        change -I.2 - (-I.1 - I.2) = I.1
        ring) rfl⟩
    · exact ⟨⟨dualSwap m * dualRotation m, mul_mem hswap hrot⟩, rfl⟩

theorem orbit_zero : MulAction.orbit (dualGroup m) ((0, 0) : ZMod m × ZMod m) = {(0, 0)} := by
  ext J
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff, Set.mem_singleton_iff]
  simp

theorem orbit_eq_toFinset (I : ZMod m × ZMod m) :
    MulAction.orbit (dualGroup m) I = ((dualSix I).toFinset : Set (ZMod m × ZMod m)) := by
  ext J
  rw [mem_orbit_dualGroup_iff, Finset.mem_coe, List.mem_toFinset]

theorem nodup_dualSix_iff (I : ZMod m × ZMod m) :
    (dualSix I).Nodup ↔ I.1 ≠ I.2 ∧ I.2 ≠ -I.1 - I.2 ∧ I.1 ≠ -I.1 - I.2 := by
  obtain ⟨i, j⟩ := I
  constructor
  · intro h
    have h0 := (List.nodup_cons.mp h).1
    refine ⟨fun hij => h0 ?_, fun hjk => h0 ?_, fun hik => h0 ?_⟩
    · exact List.mem_cons.mpr (Or.inl (Prod.ext hij hij.symm))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_cons.mpr (Or.inl (Prod.ext rfl hjk))))))))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (Prod.ext hik rfl))))))))))
  · rintro ⟨hij, hjk, hik⟩
    simp only at hij hjk hik
    simp [dualSix, hij, hjk, hik, Ne.symm hij, Ne.symm hjk, Ne.symm hik]

theorem ncard_orbit_eq_six_iff (I : ZMod m × ZMod m) :
    (MulAction.orbit (dualGroup m) I).ncard = 6 ↔ (dualSix I).Nodup := by
  rw [orbit_eq_toFinset, Set.ncard_coe_finset]
  constructor
  · intro h
    rw [List.card_toFinset] at h
    exact List.dedup_eq_self.mp ((List.dedup_sublist _).eq_of_length h)
  · intro h
    rw [List.toFinset_card_of_nodup h]
    rfl

theorem orbit_diag_injOn :
    Set.InjOn (fun r : ZMod m => MulAction.orbit (dualGroup m) (r, r)) {r | r ≠ 0} := by
  intro r _ s _ h
  have hs : (s, s) ∈ MulAction.orbit (dualGroup m) (r, r) := by
    have h' : MulAction.orbit (dualGroup m) (r, r) = MulAction.orbit (dualGroup m) (s, s) := h
    rw [h']
    exact MulAction.mem_orbit_self _
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff] at hs
  simp only [Prod.mk.injEq] at hs
  rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨-, h1⟩ <;> exact h1.symm

theorem orbit_trichotomy (I : ZMod m × ZMod m) :
    MulAction.orbit (dualGroup m) I = {(0, 0)} ∨
      (∃ r, r ≠ 0 ∧ MulAction.orbit (dualGroup m) I = MulAction.orbit (dualGroup m) (r, r)) ∨
      (MulAction.orbit (dualGroup m) I).ncard = 6 := by
  have hdiag : ∀ r : ZMod m, I ∈ MulAction.orbit (dualGroup m) (r, r) →
      MulAction.orbit (dualGroup m) I = {(0, 0)} ∨
        ∃ r, r ≠ 0 ∧ MulAction.orbit (dualGroup m) I = MulAction.orbit (dualGroup m) (r, r) := by
    intro r hr
    have heq := MulAction.orbit_eq_iff.mpr hr
    by_cases h0 : r = 0
    · left
      rw [heq, h0, orbit_zero]
    · exact Or.inr ⟨r, h0, heq⟩
  by_cases h : (dualSix I).Nodup
  · exact Or.inr (Or.inr ((ncard_orbit_eq_six_iff I).mpr h))
  simp only [nodup_dualSix_iff, not_and_or, ne_eq, not_not] at h
  obtain ⟨i, j⟩ := I
  rcases h with h | h | h
  · simp only at h
    subst h
    exact (hdiag i (MulAction.mem_orbit_self _)).elim Or.inl fun h' => Or.inr (Or.inl h')
  · have hI : (i, j) ∈ MulAction.orbit (dualGroup m) (j, j) := by
      rw [mem_orbit_dualGroup_iff, mem_dualSix_iff]
      refine Or.inr (Or.inr (Or.inr (Or.inl (Prod.ext ?_ rfl))))
      change i = -j - j
      simp only at h
      linear_combination h
    exact (hdiag j hI).elim Or.inl fun h' => Or.inr (Or.inl h')
  · have hI : (i, j) ∈ MulAction.orbit (dualGroup m) (i, i) := by
      rw [mem_orbit_dualGroup_iff, mem_dualSix_iff]
      refine Or.inr (Or.inr (Or.inl (Prod.ext rfl ?_)))
      change j = -i - i
      simp only at h
      linear_combination h
    exact (hdiag i hI).elim Or.inl fun h' => Or.inr (Or.inl h')

theorem count_dualSix_self (I : ZMod m × ZMod m)
    (h : (MulAction.orbit (dualGroup m) I).ncard = 6) : (dualSix I).count I = 1 :=
  List.count_eq_one_of_mem ((ncard_orbit_eq_six_iff I).mp h) (mem_dualSix_self I)

theorem count_dualSix_eq_zero (I J : ZMod m × ZMod m)
    (h : I ∉ MulAction.orbit (dualGroup m) J) : (dualSix J).count I = 0 :=
  List.count_eq_zero_of_not_mem fun hI => h ((mem_orbit_dualGroup_iff J I).mpr hI)

section TwoPower

variable {n : ℕ}

theorem three_mul_ne_zero {r : ZMod (2 ^ n)} (hr : r ≠ 0) : 3 * r ≠ 0 := by
  have hu : IsUnit (3 : ZMod (2 ^ n)) := by
    have h := (ZMod.isUnit_iff_coprime 3 (2 ^ n)).mpr (Nat.Coprime.pow_right n (by decide))
    simpa using h
  intro h
  exact hr (hu.mul_right_eq_zero.mp h)

theorem neg_sub_self_ne {r : ZMod (2 ^ n)} (hr : r ≠ 0) : -r - r ≠ r := by
  intro h
  apply three_mul_ne_zero hr
  linear_combination -h

theorem ncard_orbit_diag (r : ZMod (2 ^ n)) (hr : r ≠ 0) :
    (MulAction.orbit (dualGroup (2 ^ n)) (r, r)).ncard = 3 := by
  have hne := neg_sub_self_ne hr
  rw [Set.ncard_eq_three]
  refine ⟨(r, r), (r, -r - r), (-r - r, r), fun h => hne (congrArg Prod.snd h).symm,
    fun h => hne (congrArg Prod.fst h).symm, fun h => hne (congrArg Prod.fst h).symm, ?_⟩
  ext J
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem count_dualSix_diag (r : ZMod (2 ^ n)) (hr : r ≠ 0) :
    (dualSix (r, r)).count (r, r) = 2 := by
  have hne := neg_sub_self_ne hr
  have h1 : (r, -r - r) ≠ (r, r) := fun h => hne (congrArg Prod.snd h)
  have h2 : (-r - r, r) ≠ (r, r) := fun h => hne (congrArg Prod.fst h)
  simp [dualSix, h1, h2, hne]

theorem ncard_orbits_three :
    ((fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) I) ''
      {I | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 3}).ncard = 2 ^ n - 1 := by
  have hset : (fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) I) ''
      {I | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 3} =
      (fun r : ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) (r, r)) '' {r | r ≠ 0} := by
    ext X
    constructor
    · rintro ⟨I, hI, rfl⟩
      rcases orbit_trichotomy I with h | ⟨r, hr, h⟩ | h
      · rw [Set.mem_ofPred_eq, h, Set.ncard_singleton] at hI
        omega
      · exact ⟨r, hr, h.symm⟩
      · rw [Set.mem_ofPred_eq, h] at hI
        omega
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r, r), ncard_orbit_diag r hr, rfl⟩
  rw [hset, orbit_diag_injOn.ncard_image]
  have h := Set.ncard_add_ncard_compl ({0} : Set (ZMod (2 ^ n)))
  rw [Set.ncard_singleton, Nat.card_zmod] at h
  have hc : ({0}ᶜ : Set (ZMod (2 ^ n))) = {r | r ≠ 0} := by
    ext r
    simp
  rw [← hc]
  omega

theorem eq_sub_mul_sub_of_add_eq {m c : ℕ} (hm : 1 ≤ m) (h : 3 * m - 2 + c = m * m) :
    c = (m - 1) * (m - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases k with _ | k
  · norm_num at h ⊢
    omega
  · rw [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 - 2 = k by omega]
    rw [show 3 * (k + 1 + 1) - 2 = 3 * k + 4 by omega] at h
    ring_nf at h ⊢
    linarith

theorem ncard_six_points :
    {I : ZMod (2 ^ n) × ZMod (2 ^ n) | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6}.ncard =
      (2 ^ n - 1) * (2 ^ n - 2) := by
  set A : Set (ZMod (2 ^ n) × ZMod (2 ^ n)) := {I | I.1 = I.2} with hA
  set B : Set (ZMod (2 ^ n) × ZMod (2 ^ n)) := {I | I.2 = -I.1 - I.2} with hB
  set C : Set (ZMod (2 ^ n) × ZMod (2 ^ n)) := {I | I.1 = -I.1 - I.2} with hC
  have hS : {I : ZMod (2 ^ n) × ZMod (2 ^ n) |
      (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6} = (A ∪ B ∪ C)ᶜ := by
    ext I
    simp only [Set.mem_ofPred_eq, ncard_orbit_eq_six_iff, nodup_dualSix_iff, Set.mem_compl_iff,
      Set.mem_union, hA, hB, hC]
    tauto
  have hAc : A.ncard = 2 ^ n := by
    have h : A = Set.range (fun r : ZMod (2 ^ n) => (r, r)) := by
      ext I
      constructor
      · intro h
        exact ⟨I.1, Prod.ext rfl h⟩
      · rintro ⟨r, rfl⟩
        rfl
    rw [h, Set.ncard_range_of_injective (fun r s h => congrArg Prod.fst h), Nat.card_zmod]
  have hBc : B.ncard = 2 ^ n := by
    have h : B = Set.range (fun r : ZMod (2 ^ n) => (-r - r, r)) := by
      ext I
      constructor
      · intro h
        refine ⟨I.2, Prod.ext ?_ rfl⟩
        change -I.2 - I.2 = I.1
        have h' : I.2 = -I.1 - I.2 := h
        linear_combination -h'
      · rintro ⟨r, rfl⟩
        change r = -(-r - r) - r
        ring
    rw [h, Set.ncard_range_of_injective (fun r s h => congrArg Prod.snd h), Nat.card_zmod]
  have hCc : C.ncard = 2 ^ n := by
    have h : C = Set.range (fun r : ZMod (2 ^ n) => (r, -r - r)) := by
      ext I
      constructor
      · intro h
        refine ⟨I.1, Prod.ext rfl ?_⟩
        change -I.1 - I.1 = I.2
        have h' : I.1 = -I.1 - I.2 := h
        linear_combination -h'
      · rintro ⟨r, rfl⟩
        change r = -r - (-r - r)
        ring
    rw [h, Set.ncard_range_of_injective (fun r s h => congrArg Prod.fst h), Nat.card_zmod]
  have hzero : ∀ {r : ZMod (2 ^ n)}, -r - r = r → r = 0 := fun h => by
    by_contra hr
    exact neg_sub_self_ne hr h
  have hAB : A ∩ B = {(0, 0)} := by
    ext I
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, hA, hB, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1] at h2
      have h0 : I.2 = 0 := hzero h2.symm
      exact Prod.ext (h1.trans h0) h0
    · rintro rfl
      simp
  have hAC : A ∩ C = {(0, 0)} := by
    ext I
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, hA, hC, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [← h1] at h2
      have h0 : I.1 = 0 := hzero h2.symm
      exact Prod.ext h0 (h1.symm.trans h0)
    · rintro rfl
      simp
  have hBC : B ∩ C = {(0, 0)} := by
    ext I
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, hB, hC, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h12 : I.2 = I.1 := h1.trans h2.symm
      rw [h12] at h2
      have h0 : I.1 = 0 := hzero h2.symm
      exact Prod.ext h0 (h12.trans h0)
    · rintro rfl
      simp
  have h1 := Set.ncard_union_add_ncard_inter A B
  have h2 := Set.ncard_union_add_ncard_inter (A ∪ B) C
  rw [hAB, Set.ncard_singleton, hAc, hBc] at h1
  rw [Set.union_inter_distrib_right, hAC, hBC, Set.union_self, Set.ncard_singleton, hCc] at h2
  have h3 := Set.ncard_add_ncard_compl (A ∪ B ∪ C)
  rw [Nat.card_prod, Nat.card_zmod] at h3
  rw [hS]
  apply eq_sub_mul_sub_of_add_eq Nat.one_le_two_pow
  generalize 2 ^ n * 2 ^ n = M at h3 ⊢
  omega

theorem ncard_orbits_six :
    ((fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => MulAction.orbit (dualGroup (2 ^ n)) I) ''
      {I | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6}).ncard =
      (2 ^ n - 1) * (2 ^ n - 2) / 6 := by
  classical
  set S : Set (ZMod (2 ^ n) × ZMod (2 ^ n)) :=
    {I | (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6} with hS
  set o : ZMod (2 ^ n) × ZMod (2 ^ n) → Set (ZMod (2 ^ n) × ZMod (2 ^ n)) :=
    fun I => MulAction.orbit (dualGroup (2 ^ n)) I with ho
  have hfin : S.Finite := Set.toFinite _
  set s := hfin.toFinset with hs
  have hsum := Finset.card_eq_sum_card_image o s
  have hfib : ∀ b ∈ s.image o, (s.filter (fun x => o x = b)).card = 6 := by
    intro b hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hb
    have hx₀' : x₀ ∈ S := by
      rw [hs, Set.Finite.mem_toFinset] at hx₀
      exact hx₀
    have hfilter : s.filter (fun x => o x = o x₀) = (Set.toFinite (o x₀)).toFinset := by
      ext x
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨_, hx⟩
        exact MulAction.orbit_eq_iff.mp hx
      · intro hx
        have heq : o x = o x₀ := MulAction.orbit_eq_iff.mpr hx
        refine ⟨?_, heq⟩
        change (o x).ncard = 6
        rw [heq]
        exact hx₀'
    rw [hfilter, ← Set.ncard_eq_toFinset_card _ _]
    exact hx₀'
  rw [Finset.sum_const_nat hfib] at hsum
  have hscard : s.card = (2 ^ n - 1) * (2 ^ n - 2) := by
    rw [hs, ← Set.ncard_eq_toFinset_card _ _, hS, ncard_six_points]
  have himage : (o '' S).ncard = (s.image o).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_image, hs, Set.Finite.coe_toFinset]
  rw [himage]
  omega

end TwoPower

end CFSG.Wreathed.ConditionalGeneralBase
