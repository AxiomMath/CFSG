module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral

open DihedralGroup Subgroup

variable {k : ℕ}

theorem zmod_double_eq_zero [NeZero k] (hk : 2 ∣ k) {i : ZMod k} (h : i + i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  obtain ⟨m, rfl⟩ := hk
  have hm : 0 < m := by
    have := NeZero.pos (2 * m)
    omega
  have hn : i = ((i.val : ℕ) : ZMod (2 * m)) := (ZMod.natCast_zmod_val i).symm
  have hlt : i.val < 2 * m := ZMod.val_lt i
  have h2 : (((2 * i.val : ℕ)) : ZMod (2 * m)) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    have h2i : (2 : ZMod (2 * m)) * i = 0 := (two_mul i).trans h
    simpa using h2i
  have hdvd : 2 * m ∣ 2 * i.val := (ZMod.natCast_eq_zero_iff _ _).1 h2
  have hmdvd : m ∣ i.val := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 hdvd
  obtain ⟨c, hc⟩ := hmdvd
  have hc2 : c < 2 := by
    by_contra hcc
    push Not at hcc
    have : m * 2 ≤ m * c := Nat.mul_le_mul_left m hcc
    omega
  interval_cases c
  · left
    rw [hn]
    have : i.val = 0 := by omega
    rw [this]; simp
  · right
    rw [hn]
    have : i.val = m := by omega
    rw [this]
    congr 2
    omega


theorem half_ne_zero [NeZero k] (hk : 2 ∣ k) (hk2 : 2 ≤ k) : ((k / 2 : ℕ) : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 : k / 2 < k := Nat.div_lt_self (by omega) (by norm_num)
  have h2 : 0 < k / 2 := Nat.div_pos hk2 (by norm_num)
  exact absurd (Nat.le_of_dvd h2 h) (by omega)

theorem half_add_half (hk : 2 ∣ k) : ((k / 2 : ℕ) : ZMod k) + ((k / 2 : ℕ) : ZMod k) = 0 := by
  rw [← Nat.cast_add]
  have : k / 2 + k / 2 = k := by omega
  rw [this]
  exact ZMod.natCast_self k

abbrev z₀ (k : ℕ) : DihedralGroup k := r ((k / 2 : ℕ) : ZMod k)

theorem z₀_mul_self (hk : 2 ∣ k) : z₀ k * z₀ k = 1 := by
  rw [z₀, r_mul_r, half_add_half hk, ← r_zero]

theorem sq_eq_one_cases [NeZero k] (hk : 2 ∣ k) {a : DihedralGroup k} (h : a * a = 1) :
    a = 1 ∨ a = z₀ k ∨ ∃ j, a = sr j := by
  cases a with
  | r i =>
    rw [r_mul_r] at h
    have hi : i + i = 0 := by
      have h' : r (i + i) = r 0 := by rw [r_zero]; exact h
      exact DihedralGroup.r.inj h'
    rcases zmod_double_eq_zero hk hi with h0 | h0
    · left; rw [h0, r_zero]
    · right; left; rw [h0]
  | sr j => right; right; exact ⟨j, rfl⟩

theorem central_mem_of_comm [NeZero k] (hk : 2 ∣ k) {a b : DihedralGroup k} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    a = z₀ k ∨ b = z₀ k ∨ a * b = z₀ k := by
  rcases sq_eq_one_cases hk ha with h | h | ⟨i, hi⟩
  · exact absurd h ha1
  · exact Or.inl h
  rcases sq_eq_one_cases hk hb with h | h | ⟨j, hj⟩
  · exact absurd h hb1
  · exact Or.inr (Or.inl h)
  right; right
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, mul_one]
  rw [hi, hj, sr_mul_sr] at hab2 ⊢
  rw [r_mul_r] at hab2
  have hd : (j - i) + (j - i) = 0 := by
    have h' : r ((j - i) + (j - i)) = r 0 := by rw [r_zero]; exact hab2
    exact DihedralGroup.r.inj h'
  rcases zmod_double_eq_zero hk hd with h0 | h0
  · exfalso
    apply hne
    rw [hi, hj]
    have : j = i := sub_eq_zero.1 h0
    rw [this]
  · rw [h0]


theorem eq_z₀_of_central [NeZero k] (hk : 2 ∣ k) (hk2 : k ≠ 2) {z : DihedralGroup k}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ y : DihedralGroup k, z * y = y * z) : z = z₀ k := by
  rcases sq_eq_one_cases hk hz2 with h | h | ⟨j, hj⟩
  · exact absurd h hz1
  · exact h
  · exfalso
    have h1 := hzc (r 1)
    rw [hj, sr_mul_r, r_mul_sr] at h1
    have h2 : j + 1 = j - 1 := DihedralGroup.sr.inj h1
    have h3 : (2 : ZMod k) = 0 := by
      have h4 : (j + 1) - (j - 1) = 0 := sub_eq_zero.2 h2
      have h5 : (j + 1) - (j - 1) = 2 := by ring
      rw [h5] at h4
      exact h4
    rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff] at h3
    exact hk2 (Nat.dvd_antisymm h3 hk)

theorem exists_two_ne_one {Y : Type*} [Group Y] (V : Subgroup Y) (h : Nat.card V = 4) :
    ∃ a ∈ V, ∃ b ∈ V, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite V
  have hcard : 2 < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h]; norm_num
  obtain ⟨a, -, b, -, c, -, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcard
  by_cases ha : a = 1
  · have hb1 : b ≠ 1 := fun h => hab (ha.trans h.symm)
    have hc1 : c ≠ 1 := fun h => hac (ha.trans h.symm)
    exact ⟨b, b.2, c, c.2, fun h => hb1 (Subtype.ext h), fun h => hc1 (Subtype.ext h),
      fun h => hbc (Subtype.ext h)⟩
  · by_cases hb : b = 1
    · have hc1 : c ≠ 1 := fun h => hbc (hb.trans h.symm)
      exact ⟨a, a.2, c, c.2, fun h => ha (Subtype.ext h), fun h => hc1 (Subtype.ext h),
        fun h => hac (Subtype.ext h)⟩
    · exact ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb (Subtype.ext h),
        fun h => hab (Subtype.ext h)⟩

@[expose] def IsEA {A : Type*} [Group A] (E : Subgroup A) : Prop :=
  ∀ a ∈ E, a * a = 1 ∧ ∀ b ∈ E, a * b = b * a

@[expose] def fourSub (k : ℕ) [NeZero k] (hk : 2 ∣ k) : Subgroup (DihedralGroup k) where
  carrier := {g | g = r 0 ∨ g = r ((k / 2 : ℕ) : ZMod k) ∨ g = sr 0 ∨ g = sr ((k / 2 : ℕ) : ZMod k)}
  one_mem' := Or.inl (DihedralGroup.one_def).symm
  mul_mem' := by
    intro a b ha hb
    have hh := half_add_half hk
    have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, hh, hneg]
  inv_mem' := by
    intro a ha
    have hh := half_add_half hk
    have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hneg]

theorem card_fourSub (k : ℕ) [NeZero k] (hk : 2 ∣ k) (hk2 : 2 ≤ k) :
    Nat.card (fourSub k hk) = 4 := by
  have hne := half_ne_zero hk hk2
  have hset : ((fourSub k hk : Subgroup (DihedralGroup k)) : Set (DihedralGroup k)) =
      {r 0, r ((k / 2 : ℕ) : ZMod k), sr 0, sr ((k / 2 : ℕ) : ZMod k)} := by
    ext g
    simp [fourSub]
  have h1 : Nat.card (fourSub k hk) = ((fourSub k hk : Subgroup (DihedralGroup k)) :
      Set (DihedralGroup k)).ncard := Nat.card_coe_set_eq _
  rw [h1, hset]
  have d1 : r (0 : ZMod k) ≠ r ((k / 2 : ℕ) : ZMod k) := fun h => hne (DihedralGroup.r.inj h).symm
  have d2 : sr (0 : ZMod k) ≠ sr ((k / 2 : ℕ) : ZMod k) := fun h => hne (DihedralGroup.sr.inj h).symm
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d2]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨by simp, by simp⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨d1, ?_, ?_⟩ <;> intro h <;> cases h

theorem isEA_fourSub (k : ℕ) [NeZero k] (hk : 2 ∣ k) : IsEA (fourSub k hk) := by
  have hh := half_add_half hk
  have hneg : -((k / 2 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := neg_eq_of_add_eq_zero_left hh
  intro a ha
  simp only [fourSub, Subgroup.mem_mk] at ha
  refine ⟨?_, fun b hb => ?_⟩
  · rcases ha with rfl | rfl | rfl | rfl <;> simp [r_mul_r, sr_mul_sr, hh]
  · simp only [fourSub, Subgroup.mem_mk] at hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, hh, hneg, add_comm]

theorem z₀_mem_four [NeZero k] (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)} (hV : IsEA V)
    (hc : Nat.card V = 4) : z₀ k ∈ V := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one V hc
  rcases central_mem_of_comm hk (hV a ha).1 (hV b hb).1 ((hV a ha).2 b hb) ha1 hb1 hab with
    h | h | h
  · rw [← h]; exact ha
  · rw [← h]; exact hb
  · rw [← h]; exact V.mul_mem ha hb

section Transport

variable {Y : Type*} [Group Y]

theorem isEA_map {V : Subgroup Y} (hV : IsEA V) (e : Y ≃* DihedralGroup k) :
    IsEA (V.map e.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · simpa using congrArg e.toMonoidHom (( hV a ha).1)
  · rintro _ ⟨b, hb, rfl⟩
    simpa using congrArg e.toMonoidHom ((hV a ha).2 b hb)

theorem isEA_map_symm {V : Subgroup (DihedralGroup k)} (hV : IsEA V) (e : Y ≃* DihedralGroup k) :
    IsEA (V.map e.symm.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · simpa using congrArg e.symm.toMonoidHom ((hV a ha).1)
  · rintro _ ⟨b, hb, rfl⟩
    simpa using congrArg e.symm.toMonoidHom ((hV a ha).2 b hb)

theorem exists_four_of_equiv [NeZero k] (e : Y ≃* DihedralGroup k) (hk : 2 ∣ k) (hk2 : 2 ≤ k) :
    ∃ V : Subgroup Y, IsEA V ∧ Nat.card V = 4 := by
  refine ⟨(fourSub k hk).map e.symm.toMonoidHom, isEA_map_symm (isEA_fourSub k hk) e, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact card_fourSub k hk hk2

theorem central_mem_four_of_equiv [NeZero k] (e : Y ≃* DihedralGroup k) (hk : 2 ∣ k)
    {V : Subgroup Y} (hV : IsEA V) (hc : Nat.card V = 4) {z : Y} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ y, z * y = y * z) : z ∈ V := by
  by_cases hk2' : k = 2
  · have hY : Nat.card Y = 4 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk2']
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have : V = ⊤ := Subgroup.eq_top_of_card_eq V (by rw [hc, hY])
    rw [this]; exact Subgroup.mem_top z
  · have hz0 : e z = z₀ k := by
      refine eq_z₀_of_central hk hk2' ?_ ?_ ?_
      · rw [← map_mul, hz2, map_one]
      · intro h; exact hz1 (e.injective (by rw [h, map_one]))
      · intro y
        have := congrArg e (hzc (e.symm y))
        simpa using this
    have hVe := isEA_map hV e
    have hce : Nat.card (V.map e.toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective e.injective]; exact hc
    have hmem := z₀_mem_four hk hVe hce
    rw [← hz0] at hmem
    obtain ⟨v, hv, hve⟩ := hmem
    have hvz : v = z := e.injective hve
    rw [← hvz]; exact hv

end Transport

@[expose] def par (hk : 2 ∣ k) : ZMod k →+* ZMod 2 := ZMod.castHom hk (ZMod 2)

theorem exists_double_of_par_zero [NeZero k] (hk : 2 ∣ k) {i : ZMod k} (h : par hk i = 0) :
    ∃ u : ZMod k, i = u + u := by
  have hv : ((i.val : ℕ) : ZMod k) = i := ZMod.natCast_zmod_val i
  have h2 : ((i.val : ℕ) : ZMod 2) = 0 := by
    have := map_natCast (par hk) i.val
    rw [hv] at this
    rw [← this]; exact h
  obtain ⟨w, hw⟩ := (ZMod.natCast_eq_zero_iff i.val 2).1 h2
  refine ⟨(w : ZMod k), ?_⟩
  rw [← hv, hw]; push_cast; ring

variable [NeZero k]

theorem r_mem_iff (hk : 2 ∣ k) {Y' : Subgroup (DihedralGroup k)} (hi : Y'.index = 2)
    (hr : r 1 ∉ Y') (i : ZMod k) : r i ∈ Y' ↔ par hk i = 0 := by
  constructor
  · intro h
    by_contra hne
    have h1 : par hk i = 1 := by
      have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact this _ hne
    have h0 : par hk (i - 1) = 0 := by rw [map_sub, h1, map_one]; exact sub_self _
    have hm : r (i - 1) ∈ Y' := by
      obtain ⟨u, hu⟩ := exists_double_of_par_zero hk h0
      rw [hu, ← r_mul_r]
      exact Subgroup.mul_self_mem_of_index_two hi _
    have hprod : r 1 * r (i - 1) ∈ Y' := by
      rw [r_mul_r]; convert h using 2; ring
    exact hr ((Subgroup.mul_mem_iff_of_index_two hi).1 hprod |>.2 hm |> fun h => h)
  · intro h
    obtain ⟨u, hu⟩ := exists_double_of_par_zero hk h
    rw [hu, ← r_mul_r]
    exact Subgroup.mul_self_mem_of_index_two hi _

theorem sr_notMem_iff (hk : 2 ∣ k) {Y' : Subgroup (DihedralGroup k)} (hi : Y'.index = 2)
    (hr : r 1 ∉ Y') {a : ZMod k} (hsa : sr a ∉ Y') (x : ZMod k) :
    sr x ∉ Y' ↔ par hk x = par hk a := by
  have h1 : sr x * sr a ∈ Y' ↔ (sr x ∈ Y' ↔ sr a ∈ Y') := Subgroup.mul_mem_iff_of_index_two hi
  have h2 : par hk (a - x) = 0 ↔ par hk a = par hk x := by
    rw [map_sub]; exact sub_eq_zero
  rw [sr_mul_sr, r_mem_iff hk hi hr, h2] at h1
  constructor
  · intro hx
    exact (h1.2 (iff_of_false hx hsa)).symm
  · intro h hmem
    have := h1.1 h.symm
    exact hsa (this.1 hmem)

theorem r_one_notMem {Y' : Subgroup (DihedralGroup k)} (hi : Y'.index = 2) (hnc : ¬ IsCyclic Y') :
    r 1 ∉ Y' := by
  intro h
  have hcard : Nat.card Y' = k := by
    have := Subgroup.card_mul_index Y'
    rw [hi, DihedralGroup.nat_card] at this
    omega
  have hle : Subgroup.zpowers (r 1 : DihedralGroup k) ≤ Y' := (Subgroup.zpowers_le).2 h
  have hfin : Finite Y' := Nat.finite_of_card_ne_zero (by rw [hcard]; exact NeZero.ne k)
  have heq : Subgroup.zpowers (r 1 : DihedralGroup k) = Y' := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  apply hnc
  rw [← heq]
  infer_instance

theorem exists_conj_of_index_two (hk : 4 ∣ k) {Y' : Subgroup (DihedralGroup k)}
    (hi : Y'.index = 2) (hnc : ¬ IsCyclic Y') {σ τ : DihedralGroup k} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hσY : σ ∉ Y') (hτY : τ ∉ Y') : ∃ p ∈ Y', p * σ * p⁻¹ = τ := by
  have hk2 : 2 ∣ k := dvd_trans (by norm_num) hk
  have hr1 := r_one_notMem hi hnc
  have hz0 : z₀ k ∈ Y' := by
    obtain ⟨m, hm⟩ := hk
    have : ((k / 2 : ℕ) : ZMod k) = ((k / 4 : ℕ) : ZMod k) + ((k / 4 : ℕ) : ZMod k) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [z₀, this, ← r_mul_r]
    exact Subgroup.mul_self_mem_of_index_two hi _
  have h1 : (1 : DihedralGroup k) ∈ Y' := Y'.one_mem
  have hrefl : ∀ ρ : DihedralGroup k, ρ * ρ = 1 → ρ ∉ Y' → ∃ a, ρ = sr a := by
    intro ρ hρ hρY
    rcases sq_eq_one_cases hk2 hρ with h | h | h
    · exact absurd (h ▸ h1) hρY
    · exact absurd (h ▸ hz0) hρY
    · exact h
  obtain ⟨a, rfl⟩ := hrefl σ hσ hσY
  obtain ⟨b, rfl⟩ := hrefl τ hτ hτY
  have hpb : par hk2 b = par hk2 a := (sr_notMem_iff hk2 hi hr1 hσY b).1 hτY
  have hab0 : par hk2 (a - b) = 0 := by rw [map_sub, hpb]; exact sub_self _
  obtain ⟨u, hu⟩ := exists_double_of_par_zero hk2 hab0
  have ha : a = b + (u + u) := by rw [← hu]; ring
  have hpar2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hpar2 (par hk2 u) with hu0 | hu1
  · refine ⟨r u, (r_mem_iff hk2 hi hr1 u).2 hu0, ?_⟩
    rw [inv_r, r_mul_sr, sr_mul_r, ha]
    congr 1; ring
  · have hd : sr (b + u) ∈ Y' := by
      by_contra hcon
      have := (sr_notMem_iff hk2 hi hr1 hσY (b + u)).1 hcon
      rw [map_add, hu1, hpb] at this
      have h2 : (1 : ZMod 2) = 0 := by
        have : par hk2 a + 1 = par hk2 a + 0 := by rw [add_zero]; exact this
        exact add_left_cancel this
      exact absurd h2 (by decide)
    refine ⟨sr (b + u), hd, ?_⟩
    rw [inv_sr, sr_mul_sr, r_mul_sr, ha]
    congr 1; ring

theorem exists_refl_mem_four (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)} (hV : IsEA V)
    (hc : Nat.card V = 4) : ∃ i, sr i ∈ V := by
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one V hc
  rcases sq_eq_one_cases hk (hV a ha).1 with h | h | ⟨i, hi⟩
  · exact absurd h ha1
  · rcases sq_eq_one_cases hk (hV b hb).1 with h' | h' | ⟨j, hj⟩
    · exact absurd h' hb1
    · exact absurd (h.trans h'.symm) hab
    · exact ⟨j, by rw [← hj]; exact hb⟩
  · exact ⟨i, by rw [← hi]; exact ha⟩

theorem refl_mem_four (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)} (hV : IsEA V) {i j : ZMod k}
    (hi : sr i ∈ V) (hj : sr j ∈ V) : j = i ∨ j = i + ((k / 2 : ℕ) : ZMod k) := by
  have hprod : sr i * sr j ∈ V := V.mul_mem hi hj
  rw [sr_mul_sr] at hprod
  have hsq := (hV _ hprod).1
  rw [r_mul_r] at hsq
  have h' : r ((j - i) + (j - i)) = r 0 := by rw [r_zero]; exact hsq
  have hd := DihedralGroup.r.inj h'
  rcases zmod_double_eq_zero hk hd with h0 | h0
  · left; exact sub_eq_zero.1 h0
  · right; rw [← h0]; ring

theorem sr_add_half_mem_four (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)} (hV : IsEA V)
    (hc : Nat.card V = 4) {i : ZMod k} (hi : sr i ∈ V) : sr (i + ((k / 2 : ℕ) : ZMod k)) ∈ V := by
  have hz := z₀_mem_four hk hV hc
  have := V.mul_mem hi hz
  rwa [z₀, sr_mul_r] at this

theorem four_eq_of_common_refl (hk : 2 ∣ k) (hk2 : 2 ≤ k) {V V' : Subgroup (DihedralGroup k)}
    (hV : IsEA V) (hc : Nat.card V = 4) (hV' : IsEA V') (hc' : Nat.card V' = 4) {i : ZMod k}
    (hi : sr i ∈ V) (hi' : sr i ∈ V') : V = V' := by
  have hne := half_ne_zero hk hk2
  set h : ZMod k := ((k / 2 : ℕ) : ZMod k) with hh
  let S : Set (DihedralGroup k) := {r 0, r h, sr i, sr (i + h)}
  have hS : S.ncard = 4 := by
    have d1 : r (0 : ZMod k) ≠ r h := fun h' => hne (DihedralGroup.r.inj h').symm
    have d2 : sr i ≠ sr (i + h) := fun h' => hne (by
      have := DihedralGroup.sr.inj h'
      exact (add_eq_left.1 this.symm))
    show ({r 0, r h, sr i, sr (i + h)} : Set (DihedralGroup k)).ncard = 4
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d2]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨?_, ?_⟩ <;> intro h' <;> cases h'
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨d1, ?_, ?_⟩ <;> intro h' <;> cases h'
  have key : ∀ W : Subgroup (DihedralGroup k), IsEA W → Nat.card W = 4 → sr i ∈ W →
      (W : Set (DihedralGroup k)) = S := by
    intro W hW hcW hiW
    have hz := z₀_mem_four hk hW hcW
    have hsub : S ⊆ (W : Set (DihedralGroup k)) := by
      intro g hg
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact W.one_mem
      · exact hz
      · exact hiW
      · exact sr_add_half_mem_four hk hW hcW hiW
    have hcard : ((W : Subgroup (DihedralGroup k)) : Set (DihedralGroup k)).ncard = 4 := by
      rw [← hcW]; exact (Nat.card_coe_set_eq _).symm
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hS, hcard]) (Set.toFinite _)).symm
  exact SetLike.coe_injective ((key V hV hc hi).trans (key V' hV' hc' hi').symm)

theorem le_four_of_normal_four (hk : 2 ∣ k) {V : Subgroup (DihedralGroup k)} (hV : IsEA V)
    (hc : Nat.card V = 4) (hn : V.Normal) : k ≤ 4 := by
  obtain ⟨i, hi⟩ := exists_refl_mem_four hk hV hc
  have hconj := hn.conj_mem _ hi (r 1)
  rw [inv_r, r_mul_sr, sr_mul_r] at hconj
  rcases refl_mem_four hk hV hi hconj with h | h
  ·
    have h2 : (2 : ZMod k) = 0 := by
      have : (i - 1 + -1) - i = 0 := sub_eq_zero.2 h
      have h5 : (i - 1 + -1) - i = -2 := by ring
      rw [h5] at this
      exact neg_eq_zero.1 this
    rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · have h3 : (2 : ZMod k) + ((k / 2 : ℕ) : ZMod k) = 0 := by
      have h4 : (i + ((k / 2 : ℕ) : ZMod k)) - (i - 1 + -1) = 0 := sub_eq_zero.2 h.symm
      have h5 : (i + ((k / 2 : ℕ) : ZMod k)) - (i - 1 + -1) = 2 + ((k / 2 : ℕ) : ZMod k) := by ring
      rw [h5] at h4
      exact h4
    have h2 : ((k / 2 + 2 : ℕ) : ZMod k) = 0 := by
      push_cast
      rw [add_comm]; exact h3
    have hd := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by omega) hd
    omega

theorem four_subgroups_pigeon (hk : k = 2 ∨ k = 4) {V₁ V₂ V₃ : Subgroup (DihedralGroup k)}
    (h₁ : IsEA V₁) (c₁ : Nat.card V₁ = 4) (h₂ : IsEA V₂) (c₂ : Nat.card V₂ = 4)
    (h₃ : IsEA V₃) (c₃ : Nat.card V₃ = 4) : V₁ = V₂ ∨ V₁ = V₃ ∨ V₂ = V₃ := by
  have hk2 : 2 ∣ k := by rcases hk with rfl | rfl <;> norm_num
  have hk2' : 2 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  rcases hk with rfl | rfl
  · have hY : Nat.card (DihedralGroup 2) = 4 := by rw [DihedralGroup.nat_card]
    have top : ∀ V : Subgroup (DihedralGroup 2), Nat.card V = 4 → V = ⊤ := fun V hc => by
      have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
      exact Subgroup.eq_top_of_card_eq V (by rw [hc, hY])
    left; rw [top _ c₁, top _ c₂]
  · have key : ∀ V : Subgroup (DihedralGroup 4), IsEA V → Nat.card V = 4 →
        sr 0 ∈ V ∨ sr 1 ∈ V := by
      intro V hV hc
      obtain ⟨i, hi⟩ := exists_refl_mem_four hk2 hV hc
      have hi2 := sr_add_half_mem_four hk2 hV hc hi
      have h4 : ∀ i : ZMod 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
      have e2 : ((2 : ZMod 4) + ((4 / 2 : ℕ) : ZMod 4)) = 0 := by decide
      have e3 : ((3 : ZMod 4) + ((4 / 2 : ℕ) : ZMod 4)) = 1 := by decide
      rcases h4 i with rfl | rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
      · left; rw [e2] at hi2; exact hi2
      · right; rw [e3] at hi2; exact hi2
    rcases key V₁ h₁ c₁ with a1 | a1 <;> rcases key V₂ h₂ c₂ with a2 | a2 <;>
      rcases key V₃ h₃ c₃ with a3 | a3
    all_goals first
      | exact Or.inl (four_eq_of_common_refl hk2 hk2' h₁ c₁ h₂ c₂ a1 a2)
      | exact Or.inr (Or.inl (four_eq_of_common_refl hk2 hk2' h₁ c₁ h₃ c₃ a1 a3))
      | exact Or.inr (Or.inr (four_eq_of_common_refl hk2 hk2' h₂ c₂ h₃ c₃ a2 a3))

section Transport2

variable {Y : Type*} [Group Y]

theorem four_subgroups_pigeon_of_equiv (e : Y ≃* DihedralGroup k) (hk : k = 2 ∨ k = 4)
    {V₁ V₂ V₃ : Subgroup Y} (h₁ : IsEA V₁) (c₁ : Nat.card V₁ = 4) (h₂ : IsEA V₂)
    (c₂ : Nat.card V₂ = 4) (h₃ : IsEA V₃) (c₃ : Nat.card V₃ = 4) :
    V₁ = V₂ ∨ V₁ = V₃ ∨ V₂ = V₃ := by
  have inj := Subgroup.map_injective (f := e.toMonoidHom) e.injective
  have cm : ∀ V : Subgroup Y, Nat.card V = 4 → Nat.card (V.map e.toMonoidHom) = 4 := fun V hc => by
    rw [Subgroup.card_map_of_injective e.injective]; exact hc
  rcases four_subgroups_pigeon hk (isEA_map h₁ e) (cm _ c₁) (isEA_map h₂ e) (cm _ c₂)
    (isEA_map h₃ e) (cm _ c₃) with h | h | h
  · exact Or.inl (inj h)
  · exact Or.inr (Or.inl (inj h))
  · exact Or.inr (Or.inr (inj h))

theorem le_four_of_normal_four_of_equiv (e : Y ≃* DihedralGroup k) (hk : 2 ∣ k) {V : Subgroup Y}
    (hV : IsEA V) (hc : Nat.card V = 4) (hn : V.Normal) : k ≤ 4 := by
  have hn' : (V.map e.toMonoidHom).Normal := Subgroup.Normal.map hn e.toMonoidHom e.surjective
  refine le_four_of_normal_four hk (isEA_map hV e) ?_ hn'
  rw [Subgroup.card_map_of_injective e.injective]; exact hc

theorem exists_conj_of_index_two_of_equiv (e : Y ≃* DihedralGroup k) (hk : 4 ∣ k)
    {Y' : Subgroup Y} (hi : Y'.index = 2) (hnc : ¬ IsCyclic Y') {σ τ : Y} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hσY : σ ∉ Y') (hτY : τ ∉ Y') : ∃ p ∈ Y', p * σ * p⁻¹ = τ := by
  have hi' : (Y'.map e.toMonoidHom).index = 2 := by
    rw [show e.toMonoidHom = (e : Y →* DihedralGroup k) from rfl, Subgroup.index_map_equiv]; exact hi
  have hnc' : ¬ IsCyclic (Y'.map e.toMonoidHom) := fun h => hnc ((e.subgroupMap Y').isCyclic.2 h)
  have hmem : ∀ g : Y, g ∈ Y' ↔ e g ∈ Y'.map e.toMonoidHom := fun g => by
    constructor
    · intro hg; exact ⟨g, hg, rfl⟩
    · rintro ⟨g', hg', hgg⟩
      have : g' = g := e.injective hgg
      rw [← this]; exact hg'
  obtain ⟨p, hp, hpσ⟩ := exists_conj_of_index_two hk hi' hnc' (σ := e σ) (τ := e τ)
    (by rw [← map_mul, hσ, map_one]) (by rw [← map_mul, hτ, map_one])
    (fun h => hσY ((hmem σ).2 h)) (fun h => hτY ((hmem τ).2 h))
  obtain ⟨p', hp', rfl⟩ := hp
  refine ⟨p', hp', e.injective ?_⟩
  simpa using hpσ

theorem isDihedral2_of_equiv {A : Type*} [Group A] {D : Subgroup A}
    (e : D ≃* DihedralGroup k) :
    ∃ ρ s : A, ρ ∈ D ∧ s ∈ D ∧ s * s = 1 ∧ s * ρ * s⁻¹ = ρ⁻¹ ∧
      ∀ d ∈ D, ∃ i : ℤ, d = ρ ^ i ∨ d = s * ρ ^ i := by
  refine ⟨(e.symm (r 1) : A), (e.symm (sr 0) : A), (e.symm (r 1)).2, (e.symm (sr 0)).2, ?_, ?_, ?_⟩
  · have : e.symm (sr 0) * e.symm (sr 0) = 1 := by rw [← map_mul, sr_mul_self, map_one]
    simpa using congrArg Subtype.val this
  · have : e.symm (sr 0) * e.symm (r 1) * (e.symm (sr 0))⁻¹ = (e.symm (r 1))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, sr_mul_r, inv_sr, sr_mul_sr, inv_r]
      congr 2
      simp
    simpa using congrArg Subtype.val this
  · intro d hd
    have hex : ∀ j : ZMod k, e.symm (r j) = (e.symm (r 1)) ^ ((j.val : ℕ) : ℤ) := by
      intro j
      rw [← map_zpow, r_one_zpow]
      congr 2
      simp
    rcases hx : e ⟨d, hd⟩ with j | j
    · refine ⟨(j.val : ℕ), Or.inl ?_⟩
      have : (⟨d, hd⟩ : D) = e.symm (r j) := by rw [← hx]; simp
      have h2 := congrArg Subtype.val this
      rw [hex j] at h2
      simpa using h2
    · refine ⟨(j.val : ℕ), Or.inr ?_⟩
      have : (⟨d, hd⟩ : D) = e.symm (sr 0) * e.symm (r j) := by
        rw [← map_mul, sr_mul_r, zero_add, ← hx]; simp
      have h2 := congrArg Subtype.val this
      rw [hex j] at h2
      simpa using h2

omit [NeZero k] in
theorem central_sq_of_equiv [NeZero k] (e : Y ≃* DihedralGroup k) (hk : 2 ∣ k) {z : Y}
    (hzc : ∀ y, z * y = y * z) : z * z = 1 := by
  by_cases hk2 : k = 2
  · subst hk2
    have : ∀ g : DihedralGroup 2, g * g = 1 := by decide
    apply e.injective
    rw [map_mul, this, map_one]
  · have hc : ∀ y : DihedralGroup k, e z * y = y * e z := fun y => by
      have := congrArg e (hzc (e.symm y))
      simpa using this
    apply e.injective
    rw [map_mul, map_one]
    generalize e z = w at hc
    cases w with
    | r i =>
      have h1 := hc (sr 0)
      rw [r_mul_sr, sr_mul_r] at h1
      have h2 : (0 - i) = 0 + i := DihedralGroup.sr.inj h1
      rw [r_mul_r, ← r_zero]
      congr 1
      have : i + i = 0 := by
        have h3 : (0 - i) - (0 + i) = 0 := sub_eq_zero.2 h2
        have h4 : (0 - i) - (0 + i) = -(i + i) := by ring
        rw [h4] at h3
        exact neg_eq_zero.1 h3
      exact this
    | sr j =>
      exfalso
      have h1 := hc (r 1)
      rw [sr_mul_r, r_mul_sr] at h1
      have h2 : j + 1 = j - 1 := DihedralGroup.sr.inj h1
      have h3 : (2 : ZMod k) = 0 := by
        have h4 : (j + 1) - (j - 1) = 0 := sub_eq_zero.2 h2
        have h5 : (j + 1) - (j - 1) = 2 := by ring
        rw [h5] at h4
        exact h4
      rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff] at h3
      exact hk2 (Nat.dvd_antisymm h3 hk)

end Transport2

end CFSG.GH74.GLS.Stage1.Thm6.Glue.Dihedral
