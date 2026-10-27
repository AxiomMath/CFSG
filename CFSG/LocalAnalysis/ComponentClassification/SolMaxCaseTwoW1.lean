module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36D

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace CaseTwoW

variable {m : ℕ}

@[expose] def emb13 (hm : 13 ≤ m) : Fin 13 ≃ {i : Fin m // (i : ℕ) < 13} where
  toFun i := ⟨Fin.castLE hm i, i.2⟩
  invFun j := ⟨(j : Fin m), j.2⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Subtype.ext (Fin.ext rfl)

@[expose] def ι (hm : 13 ≤ m) : Perm (Fin 13) →* Perm (Fin m) :=
  Perm.extendDomainHom (emb13 hm)

theorem ι_apply_castLE (hm : 13 ≤ m) (v : Perm (Fin 13)) (i : Fin 13) :
    ι hm v (Fin.castLE hm i) = Fin.castLE hm (v i) :=
  Perm.extendDomain_apply_image v (emb13 hm) i

theorem ι_apply_lt (hm : 13 ≤ m) (v : Perm (Fin 13)) {i : Fin m} (hi : (i : ℕ) < 13) :
    ι hm v i = Fin.castLE hm (v ⟨i, hi⟩) :=
  ι_apply_castLE hm v ⟨i, hi⟩

theorem ι_apply_ge (hm : 13 ≤ m) (v : Perm (Fin 13)) {i : Fin m} (hi : 13 ≤ (i : ℕ)) :
    ι hm v i = i :=
  Perm.extendDomain_apply_not_subtype v (emb13 hm) (by omega)

theorem card_support_ι (hm : 13 ≤ m) (v : Perm (Fin 13)) :
    (ι hm v).support.card = v.support.card :=
  Perm.card_support_extend_domain (emb13 hm)

theorem sign_ι (hm : 13 ≤ m) (v : Perm (Fin 13)) : Perm.sign (ι hm v) = Perm.sign v :=
  Perm.sign_extendDomain v (emb13 hm)

theorem ι_mem_alternatingGroup (hm : 13 ≤ m) {v : Perm (Fin 13)} (hv : Perm.sign v = 1) :
    ι hm v ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, sign_ι, hv]

theorem ι_mul_self (hm : 13 ≤ m) {v : Perm (Fin 13)} (hv : v * v = 1) :
    ι hm v * ι hm v = 1 := by
  rw [← map_mul, hv, map_one]

theorem ι_commute (hm : 13 ≤ m) {u v : Perm (Fin 13)} (h : u * v = v * u) :
    ι hm u * ι hm v = ι hm v * ι hm u := by
  rw [← map_mul, h, map_mul]

@[expose] def s8₀ : Perm (Fin 13) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def b1₀ : Perm (Fin 13) := swap 0 1 * swap 2 3

@[expose] def b2₀ : Perm (Fin 13) := swap 0 1 * swap 4 5

@[expose] def c12₀ : Perm (Fin 13) := swap 2 4 * swap 3 5

@[expose] def p1₀ : Perm (Fin 13) := swap 8 9 * swap 10 11

@[expose] def σ8 (hm : 13 ≤ m) : Perm (Fin m) := ι hm s8₀

@[expose] def b1 (hm : 13 ≤ m) : Perm (Fin m) := ι hm b1₀

@[expose] def b2 (hm : 13 ≤ m) : Perm (Fin m) := ι hm b2₀

@[expose] def c12 (hm : 13 ≤ m) : Perm (Fin m) := ι hm c12₀

@[expose] def p1 (hm : 13 ≤ m) : Perm (Fin m) := ι hm p1₀

section Concrete

variable (hm : 13 ≤ m)

theorem σ8_mul_self : σ8 hm * σ8 hm = 1 := ι_mul_self hm (by decide)
theorem b1_mul_self : b1 hm * b1 hm = 1 := ι_mul_self hm (by decide)
theorem b2_mul_self : b2 hm * b2 hm = 1 := ι_mul_self hm (by decide)
theorem p1_mul_self : p1 hm * p1 hm = 1 := ι_mul_self hm (by decide)

theorem σ8_mem : σ8 hm ∈ alternatingGroup (Fin m) := ι_mem_alternatingGroup hm (by decide)
theorem b1_mem : b1 hm ∈ alternatingGroup (Fin m) := ι_mem_alternatingGroup hm (by decide)
theorem b2_mem : b2 hm ∈ alternatingGroup (Fin m) := ι_mem_alternatingGroup hm (by decide)
theorem c12_mem : c12 hm ∈ alternatingGroup (Fin m) := ι_mem_alternatingGroup hm (by decide)
theorem p1_mem : p1 hm ∈ alternatingGroup (Fin m) := ι_mem_alternatingGroup hm (by decide)

theorem card_support_σ8 : (σ8 hm).support.card = 8 := by
  rw [σ8, card_support_ι]; decide
theorem card_support_b1 : (b1 hm).support.card = 4 := by
  rw [b1, card_support_ι]; decide
theorem card_support_b2 : (b2 hm).support.card = 4 := by
  rw [b2, card_support_ι]; decide
theorem card_support_b1b2 : (b1 hm * b2 hm).support.card = 4 := by
  rw [b1, b2, ← map_mul, card_support_ι]; decide
theorem card_support_p1 : (p1 hm).support.card = 4 := by
  rw [p1, card_support_ι]; decide

theorem σ8_b1 : σ8 hm * b1 hm = b1 hm * σ8 hm := ι_commute hm (by decide)
theorem σ8_b2 : σ8 hm * b2 hm = b2 hm * σ8 hm := ι_commute hm (by decide)
theorem b1_b2 : b1 hm * b2 hm = b2 hm * b1 hm := ι_commute hm (by decide)
theorem σ8_c12 : σ8 hm * c12 hm = c12 hm * σ8 hm := ι_commute hm (by decide)
theorem σ8_p1 : σ8 hm * p1 hm = p1 hm * σ8 hm := ι_commute hm (by decide)
theorem b1_p1 : b1 hm * p1 hm = p1 hm * b1 hm := ι_commute hm (by decide)
theorem b2_p1 : b2 hm * p1 hm = p1 hm * b2 hm := ι_commute hm (by decide)

theorem c12_conj_b1 : c12 hm * b1 hm * (c12 hm)⁻¹ = b2 hm := by
  rw [c12, b1, b2, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (ι hm) (by decide)

theorem p1_apply_of_lt {i : Fin m} (hi : (i : ℕ) < 8) : p1 hm i = i := by
  rw [p1, ι_apply_lt hm _ (by omega)]
  have h : ∀ j : Fin 13, (j : ℕ) < 8 → p1₀ j = j := by decide
  exact Fin.ext (by simpa using congrArg Fin.val (h ⟨i, by omega⟩ hi))

theorem σ8_apply_of_ge {i : Fin m} (hi : 8 ≤ (i : ℕ)) : σ8 hm i = i := by
  rcases lt_or_ge (i : ℕ) 13 with h13 | h13
  · rw [σ8, ι_apply_lt hm _ h13]
    have h : ∀ j : Fin 13, 8 ≤ (j : ℕ) → s8₀ j = j := by decide
    exact Fin.ext (by simpa using congrArg Fin.val (h ⟨i, h13⟩ hi))
  · exact ι_apply_ge hm _ h13

theorem σ8_apply_of_lt {i : Fin m} (hi : (i : ℕ) < 8) :
    σ8 hm i ≠ i ∧ ((σ8 hm i : Fin m) : ℕ) < 8 := by
  rw [σ8, ι_apply_lt hm _ (by omega)]
  have h : ∀ j : Fin 13, (j : ℕ) < 8 → s8₀ j ≠ j ∧ ((s8₀ j : Fin 13) : ℕ) < 8 := by decide
  obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ hi
  refine ⟨fun he => h1 (Fin.ext ?_), by simpa using h2⟩
  have := congrArg Fin.val he
  simpa using this

end Concrete

@[expose] def IsBase (hm : 13 ≤ m) (v : Perm (Fin m)) : Prop :=
  ∀ i, v i = i ∨ v i = σ8 hm i

variable {hm : 13 ≤ m}

theorem isBase_one : IsBase hm 1 := fun _ => Or.inl rfl

theorem isBase_ι {v : Perm (Fin 13)} (hv : ∀ j, v j = j ∨ v j = s8₀ j) : IsBase hm (ι hm v) := by
  intro i
  rcases lt_or_ge (i : ℕ) 13 with h13 | h13
  · rw [σ8, ι_apply_lt hm _ h13, ι_apply_lt hm _ h13]
    rcases hv ⟨i, h13⟩ with h | h
    · left; rw [h]; exact Fin.ext rfl
    · right; rw [h]
  · left; exact ι_apply_ge hm _ h13

theorem isBase_σ8 : IsBase hm (σ8 hm) := isBase_ι (by decide)
theorem isBase_b1 : IsBase hm (b1 hm) := isBase_ι (by decide)
theorem isBase_b2 : IsBase hm (b2 hm) := isBase_ι (by decide)

theorem IsBase.apply_of_ge {v : Perm (Fin m)} (hv : IsBase hm v) {i : Fin m}
    (hi : 8 ≤ (i : ℕ)) : v i = i := by
  rcases hv i with h | h
  · exact h
  · rw [h, σ8_apply_of_ge hm hi]

theorem σ8_σ8 (hm : 13 ≤ m) (i : Fin m) : σ8 hm (σ8 hm i) = i := by
  rw [← Perm.mul_apply, σ8_mul_self, Perm.one_apply]

theorem IsBase.mul_self {v : Perm (Fin m)} (hv : IsBase hm v) : v * v = 1 := by
  refine Equiv.ext fun i => ?_
  simp only [Perm.mul_apply, Perm.one_apply]
  rcases hv i with h | h
  · rw [h, h]
  · rcases hv (σ8 hm i) with h' | h'
    · have e : σ8 hm i = i := v.injective (h'.trans h.symm)
      calc v (v i) = v (σ8 hm i) := by rw [h]
        _ = σ8 hm i := h'
        _ = i := e
    · rw [h, h', σ8_σ8]

theorem IsBase.mul {u v : Perm (Fin m)} (hu : IsBase hm u) (hv : IsBase hm v) :
    IsBase hm (u * v) := by
  intro i
  simp only [Perm.mul_apply]
  rcases hv i with h | h
  · rw [h]; exact hu i
  · rw [h]
    rcases hu (σ8 hm i) with h' | h'
    · right; exact h'
    · left; rw [h', σ8_σ8]

theorem IsBase.inv {v : Perm (Fin m)} (hv : IsBase hm v) : IsBase hm v⁻¹ := by
  have h : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv.mul_self
  rw [h]
  exact hv

theorem isBase_conj {π v : Perm (Fin m)} (hπ : π * σ8 hm = σ8 hm * π) (hv : IsBase hm v) :
    IsBase hm (π * v * π⁻¹) := by
  have hπ' : ∀ i, π (σ8 hm i) = σ8 hm (π i) := fun i => by
    rw [← Perm.mul_apply, hπ, Perm.mul_apply]
  intro i
  simp only [Perm.mul_apply]
  rcases hv (π⁻¹ i) with h | h
  · left; rw [h]; simp
  · right; rw [h, hπ']; simp

theorem IsBase.support_subset {v : Perm (Fin m)} (hv : IsBase hm v) :
    v.support ⊆ (σ8 hm).support := by
  intro i hi
  rw [Perm.mem_support] at hi ⊢
  rcases hv i with h | h
  · exact absurd h hi
  · rw [← h]; exact hi

theorem card_support_eq_four_of_isBase {v : Perm (Fin m)} (hv : IsBase hm v)
    (hvA : v ∈ alternatingGroup (Fin m)) (hv1 : v ≠ 1) (hv8 : v ≠ σ8 hm) :
    v.support.card = 4 := by
  have hle : v.support.card ≤ 8 := (Finset.card_le_card hv.support_subset).trans
    (card_support_σ8 hm).le
  have hdvd := four_dvd_card_support_of_mem_alternating hv.mul_self hvA
  have h0 : v.support.card ≠ 0 := by
    intro h
    exact hv1 (Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp h))
  have h8 : v.support.card ≠ 8 := by
    intro h
    have hsub := Finset.eq_of_subset_of_card_le hv.support_subset
      (by rw [h, card_support_σ8])
    apply hv8
    ext i
    by_cases hi : i ∈ (σ8 hm).support
    · rw [← hsub, Perm.mem_support] at hi
      rcases hv i with h' | h'
      · exact absurd h' hi
      · rw [h']
    · rw [Perm.mem_support, not_not] at hi
      have hi' : i ∉ v.support := by rw [hsub, Perm.mem_support, not_not]; exact hi
      rw [Perm.mem_support, not_not] at hi'
      rw [hi', hi]
  omega

@[expose] def pt (hm : 13 ≤ m) (i : Fin 13) : Fin m := Fin.castLE hm i

theorem pt_injective (hm : 13 ≤ m) : Function.Injective (pt hm) := Fin.castLE_injective hm

theorem σ8_pt (j : Fin 13) : σ8 hm (pt hm j) = pt hm (s8₀ j) := ι_apply_castLE hm s8₀ j

theorem IsBase.apply_of_apply_σ8 {v : Perm (Fin m)} (hv : IsBase hm v) {i : Fin m}
    (h : v (σ8 hm i) = σ8 hm i) : v i = i := by
  rcases hv i with h' | h'
  · exact h'
  · have := v.injective (h'.trans h.symm)
    rw [h', ← this]

theorem IsBase.eq_one {v : Perm (Fin m)} (hv : IsBase hm v) (hvA : v ∈ alternatingGroup (Fin m))
    (h0 : v (pt hm 0) = pt hm 0) (h2 : v (pt hm 2) = pt hm 2) (h4 : v (pt hm 4) = pt hm 4) :
    v = 1 := by
  have h6 : ∀ i : Fin m, (i : ℕ) < 6 → v i = i := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin 13, i = pt hm j := ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    have hj : (j : ℕ) < 6 := by simpa [pt] using hi
    have hcase : ∀ j : Fin 13, (j : ℕ) < 6 →
        (j = 0 ∨ j = 2 ∨ j = 4) ∨ (s8₀ j = 0 ∨ s8₀ j = 2 ∨ s8₀ j = 4) := by decide
    rcases hcase j hj with h | h
    · rcases h with h | h | h <;> rw [h] <;> assumption
    · refine hv.apply_of_apply_σ8 ?_
      rw [σ8_pt]
      rcases h with h | h | h <;> rw [h] <;> assumption
  have hσ6 : σ8 hm (pt hm 6) = pt hm 7 := by rw [σ8_pt]; rfl
  have hσ7 : σ8 hm (pt hm 7) = pt hm 6 := by rw [σ8_pt]; rfl
  have h67 : pt hm 6 ≠ pt hm 7 := fun h => by
    have := congrArg Fin.val h
    simp [pt] at this
  have hother : ∀ i : Fin m, i ≠ pt hm 6 → i ≠ pt hm 7 → v i = i := by
    intro i hi6 hi7
    rcases lt_or_ge (i : ℕ) 6 with h | h
    · exact h6 i h
    rcases lt_or_ge (i : ℕ) 8 with h' | h'
    · exfalso
      have : (i : ℕ) = 6 ∨ (i : ℕ) = 7 := by omega
      rcases this with h'' | h''
      · exact hi6 (Fin.ext (by simp [pt, h'']))
      · exact hi7 (Fin.ext (by simp [pt, h'']))
    · exact hv.apply_of_ge h'
  rcases hv (pt hm 6) with h | h
  · refine Equiv.ext fun i => ?_
    simp only [Perm.one_apply]
    by_cases hi6 : i = pt hm 6
    · rw [hi6, h]
    by_cases hi7 : i = pt hm 7
    · rw [hi7]
      refine hv.apply_of_apply_σ8 ?_
      rw [hσ7, h]
    · rw [hother i hi6 hi7]
  · exfalso
    rw [hσ6] at h
    have h7 : v (pt hm 7) = pt hm 6 := by
      rcases hv (pt hm 7) with h' | h'
      · exact absurd (v.injective (h.trans h'.symm)) h67
      · rw [h', hσ7]
    have hswap : v = swap (pt hm 6) (pt hm 7) := by
      refine Equiv.ext fun i => ?_
      by_cases hi6 : i = pt hm 6
      · rw [hi6, h, swap_apply_left]
      by_cases hi7 : i = pt hm 7
      · rw [hi7, h7, swap_apply_right]
      · rw [hother i hi6 hi7, swap_apply_of_ne_of_ne hi6 hi7]
    rw [Perm.mem_alternatingGroup, hswap, Perm.sign_swap h67] at hvA
    exact absurd hvA (by decide)

theorem card_le_eight_of_isBase (S : Subgroup (Perm (Fin m)))
    (hS : ∀ v ∈ S, IsBase hm v ∧ v ∈ alternatingGroup (Fin m)) : Nat.card S ≤ 8 := by
  classical
  let f : S → Bool × Bool × Bool := fun v =>
    (decide ((v : Perm (Fin m)) (pt hm 0) = pt hm 0),
      decide ((v : Perm (Fin m)) (pt hm 2) = pt hm 2),
      decide ((v : Perm (Fin m)) (pt hm 4) = pt hm 4))
  have hpt : ∀ (u v : S) (j : Fin 13), (j : ℕ) < 8 →
      (decide ((u : Perm (Fin m)) (pt hm j) = pt hm j) =
        decide ((v : Perm (Fin m)) (pt hm j) = pt hm j)) →
      ((u : Perm (Fin m))⁻¹ * v) (pt hm j) = pt hm j := by
    intro u v j hj he
    have hne : σ8 hm (pt hm j) ≠ pt hm j := (σ8_apply_of_lt hm (by simpa [pt] using hj)).1
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
    rcases (hS u u.2).1 (pt hm j) with hu | hu <;> rcases (hS v v.2).1 (pt hm j) with hv | hv
    · rw [hu, hv]
    · exfalso
      rw [hu, hv] at he
      exact hne (of_decide_eq_true (he.symm.trans (decide_eq_true rfl)))
    · exfalso
      rw [hu, hv] at he
      exact hne (of_decide_eq_true (he.trans (decide_eq_true rfl)))
    · rw [hu, hv]
  have hinj : Function.Injective f := by
    intro u v huv
    simp only [f, Prod.mk.injEq] at huv
    obtain ⟨e0, e2, e4⟩ := huv
    have hw := hS _ (S.mul_mem (S.inv_mem u.2) v.2)
    have h1 := hw.1.eq_one hw.2 (hpt u v 0 (by decide) e0) (hpt u v 2 (by decide) e2)
      (hpt u v 4 (by decide) e4)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have := Nat.card_le_card_of_injective f hinj
  simpa using this

theorem apply_of_commute_base {π : Perm (Fin m)} (h8 : π * σ8 hm = σ8 hm * π)
    (h1 : π * b1 hm = b1 hm * π) (h2 : π * b2 hm = b2 hm * π) {i : Fin m} (hi : (i : ℕ) < 8) :
    π i = i ∨ π i = σ8 hm i := by
  have hfix : ∀ b : Perm (Fin m), π * b = b * π → ∀ x, (b (π x) = π x ↔ b x = x) := by
    intro b hb x
    rw [← Perm.mul_apply, ← hb, Perm.mul_apply, π.injective.eq_iff]
  obtain ⟨a, rfl⟩ : ∃ a : Fin 13, i = pt hm a := ⟨⟨i, by omega⟩, Fin.ext rfl⟩
  have ha : (a : ℕ) < 8 := by simpa [pt] using hi
  have hpt_iff : ∀ (u : Perm (Fin 13)) (x : Fin 13), (ι hm u (pt hm x) = pt hm x ↔ u x = x) :=
    fun u x => by rw [pt, ι_apply_castLE, (Fin.castLE_injective hm).eq_iff]
  rcases lt_or_ge ((π (pt hm a) : Fin m) : ℕ) 13 with hj13 | hj13
  · obtain ⟨c, hc⟩ : ∃ c : Fin 13, π (pt hm a) = pt hm c := ⟨⟨_, hj13⟩, Fin.ext rfl⟩
    have key : ∀ a c : Fin 13, (a : ℕ) < 8 →
        ((s8₀ c = c ↔ s8₀ a = a) → (b1₀ c = c ↔ b1₀ a = a) → (b2₀ c = c ↔ b2₀ a = a) →
          c = a ∨ c = s8₀ a) := by decide
    have hσ := hfix _ h8 (pt hm a)
    have hb1 := hfix _ h1 (pt hm a)
    have hb2 := hfix _ h2 (pt hm a)
    rw [hc, σ8, hpt_iff, hpt_iff] at hσ
    rw [hc, b1, hpt_iff, hpt_iff] at hb1
    rw [hc, b2, hpt_iff, hpt_iff] at hb2
    rcases key a c ha hσ hb1 hb2 with h | h
    · left; rw [hc, h]
    · right; rw [hc, h, σ8_pt]
  · exfalso
    have hσj : σ8 hm (π (pt hm a)) = π (pt hm a) := σ8_apply_of_ge hm (by omega)
    exact (σ8_apply_of_lt hm hi).1 ((hfix _ h8 (pt hm a)).mp hσj)

end CaseTwoW

theorem cycleType_eq_replicate_of_eight {m : ℕ} {σ : Perm (Fin m)} (hσ : σ * σ = 1)
    (h8 : σ.support.card = 8) : σ.cycleType = Multiset.replicate 4 2 := by
  have hne : σ ≠ 1 := by
    rintro rfl
    rw [Perm.support_one, Finset.card_empty] at h8
    omega
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) hne
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have hsum := Perm.sum_cycleType σ
  rw [hk, h8, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hk, show k + 1 = 4 by omega]

theorem mem_alternatingGroup_of_eight {m : ℕ} {σ : Perm (Fin m)} (hσ : σ * σ = 1)
    (h8 : σ.support.card = 8) : σ ∈ alternatingGroup (Fin m) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, cycleType_eq_replicate_of_eight hσ h8,
    Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  decide

theorem exists_alt_conj_of_eight {m : ℕ} (hm : 10 ≤ m) {σ σ' : Perm (Fin m)} (hσ : σ * σ = 1)
    (hσ' : σ' * σ' = 1) (h8 : σ.support.card = 8) (h8' : σ'.support.card = 8) :
    ∃ π : alternatingGroup (Fin m), (π : Perm (Fin m)) * σ * (π : Perm (Fin m))⁻¹ = σ' := by
  have hc : IsConj σ σ' := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_eq_replicate_of_eight hσ h8,
      cycleType_eq_replicate_of_eight hσ' h8']
  have hc' := alternatingGroup.isConj_of (σ := ⟨σ, mem_alternatingGroup_of_eight hσ h8⟩)
    (τ := ⟨σ', mem_alternatingGroup_of_eight hσ' h8'⟩) hc (by rw [h8, Fintype.card_fin]; omega)
  obtain ⟨π, hπ⟩ := isConj_iff.mp hc'
  exact ⟨π, congrArg Subtype.val hπ⟩

theorem odd_card_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
  have := h g
  rw [hg] at this
  exact absurd this (by decide)

variable {X : Type} [Group X]
variable {M : Subgroup X} {r : ℕ} {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)}

theorem IsPermAction.exists_lift_perm (hρ : IsPermAction θ ρ) [Finite X] (hr : 4 ≤ r) {a : X}
    (ha : a ∈ normalizer (M : Set X)) (ha2 : a * a = 1) {b : Perm (Fin r)}
    (hbA : b ∈ alternatingGroup (Fin r)) (hb : b * ρ ⟨a, ha⟩ = ρ ⟨a, ha⟩ * b) :
    ∃ (y : X) (hy : y ∈ M), y * a = a * y ∧ ρ ⟨y, le_normalizer hy⟩ = b := by
  obtain ⟨x, hxc, hx⟩ := hρ.exists_lift ha ha2 (b := ⟨b, hbA⟩) hb
  refine ⟨x, x.2, mem_centralizer_singleton_iff.mp hxc, ?_⟩
  rw [hρ.apply_of_mem hr x, hx]

theorem IsPermAction.exists_commute_lift (hρ : IsPermAction θ ρ) [Finite X] {H : Subgroup X}
    (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {A : Subgroup X} (hAH : A ≤ H) {x y₀ : X} (hx : x ∈ A) (hx2 : x * x = 1) (hy₀ : y₀ ∈ A)
    (hc : ρ ⟨y₀, hHN (hAH hy₀)⟩ * ρ ⟨x, hHN (hAH hx)⟩ =
      ρ ⟨x, hHN (hAH hx)⟩ * ρ ⟨y₀, hHN (hAH hy₀)⟩) :
    ∃ (y : X) (hy : y ∈ A), y * x = x * y ∧ ρ ⟨y, hHN (hAH hy)⟩ = ρ ⟨y₀, hHN (hAH hy₀)⟩ := by
  let f : ↥A →* Perm (Fin r) := ρ.comp (Subgroup.inclusion (hAH.trans hHN))
  have hf : ∀ z : ↥A, f z = ρ ⟨z, hHN (hAH z.2)⟩ := fun z => rfl
  let N := f.ker
  have hNodd : Odd (Nat.card N) := by
    refine odd_card_of_forall_odd_orderOf fun n => ?_
    have h1 : ρ ⟨((n : ↥A) : X), hHN (hAH (n : ↥A).2)⟩ = 1 := by rw [← hf]; exact n.2
    have h2 := hker _ (hAH (n : ↥A).2) (hρ.mem_coreActionKernel _ h1)
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h2
    exact h2
  let c : MulAut ↥A := MulAut.conj ⟨x, hx⟩
  have hcapp : ∀ z : ↥A, ((c z : ↥A) : X) = x * z * x⁻¹ := fun z => rfl
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hc2 : ∀ z, c (c z) = z := by
    intro z
    apply Subtype.ext
    rw [hcapp, hcapp, hxinv]
    calc x * (x * (z : X) * x) * x = (x * x) * z * (x * x) := by group
      _ = z := by rw [hx2]; group
  have hcN : ∀ n ∈ N, c n ∈ N := fun n hn => (MonoidHom.normal_ker f).conj_mem n hn _
  have hw : (⟨y₀, hy₀⟩ : ↥A)⁻¹ * c ⟨y₀, hy₀⟩ ∈ N := by
    change f ((⟨y₀, hy₀⟩ : ↥A)⁻¹ * c ⟨y₀, hy₀⟩) = 1
    rw [map_mul, map_inv, hf, hf]
    have hcy : (⟨((c ⟨y₀, hy₀⟩ : ↥A) : X), hHN (hAH (c ⟨y₀, hy₀⟩).2)⟩ :
        ↥(normalizer (M : Set X))) = ⟨x, hHN (hAH hx)⟩ * ⟨y₀, hHN (hAH hy₀)⟩ *
          (⟨x, hHN (hAH hx)⟩ : ↥(normalizer (M : Set X)))⁻¹ := Subtype.ext (hcapp _)
    rw [hcy, map_mul, map_mul, map_inv, ← hc]
    group
  obtain ⟨n, hn, hfix⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem c hc2 hcN hNodd hw
  refine ⟨((⟨y₀, hy₀⟩ * n : ↥A) : X), (⟨y₀, hy₀⟩ * n : ↥A).2, ?_, ?_⟩
  · have h := congrArg Subtype.val hfix
    rw [hcapp] at h
    calc ((⟨y₀, hy₀⟩ * n : ↥A) : X) * x = x * ((⟨y₀, hy₀⟩ * n : ↥A) : X) * x⁻¹ * x := by rw [h]
      _ = x * ((⟨y₀, hy₀⟩ * n : ↥A) : X) := by group
  · change f (⟨y₀, hy₀⟩ * n) = f ⟨y₀, hy₀⟩
    rw [map_mul, show f n = 1 from hn, mul_one]

theorem IsPermAction.exists_pow_involution (hρ : IsPermAction θ ρ) [Finite X] {H : Subgroup X}
    (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g))
    {y : X} (hy : y ∈ H) (hy2 : ρ ⟨y, hHN hy⟩ * ρ ⟨y, hHN hy⟩ = 1) :
    ∃ k : ℕ, Odd k ∧ y ^ k * y ^ k = 1 ∧ ρ ⟨y ^ k, hHN (pow_mem hy k)⟩ = ρ ⟨y, hHN hy⟩ := by
  obtain ⟨s, q, hq, hsq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hρq : ρ ⟨y ^ q, hHN (pow_mem hy q)⟩ = ρ ⟨y, hHN hy⟩ := by
    have h1 : (⟨y ^ q, hHN (pow_mem hy q)⟩ : ↥(normalizer (M : Set X))) =
        ⟨y, hHN hy⟩ ^ q := Subtype.ext (by simp)
    rw [h1, map_pow]
    obtain ⟨k, rfl⟩ := hq
    rw [pow_succ, pow_mul, sq, hy2, one_pow, one_mul]
  refine ⟨q, hq, ?_, hρq⟩
  have hmem : y ^ q * y ^ q ∈ H := mul_mem (pow_mem hy q) (pow_mem hy q)
  have hker1 : ρ ⟨y ^ q * y ^ q, hHN hmem⟩ = 1 := by
    have h1 : (⟨y ^ q * y ^ q, hHN hmem⟩ : ↥(normalizer (M : Set X))) =
        ⟨y ^ q, hHN (pow_mem hy q)⟩ * ⟨y ^ q, hHN (pow_mem hy q)⟩ := rfl
    rw [h1, map_mul, hρq, hy2]
  have hodd := hker _ hmem (hρ.mem_coreActionKernel _ hker1)
  have hdvd : orderOf (y ^ q * y ^ q) ∣ 2 ^ s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← sq, ← pow_mul, ← pow_mul, show q * (2 * 2 ^ s) = (2 ^ s * q) * 2 by ring, ← hsq,
      pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rwa [pow_zero, orderOf_eq_one_iff] at hj
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul, Nat.not_odd_iff_even])

end CFSG.ComponentClassification.SolMax
