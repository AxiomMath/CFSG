module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Equiv Equiv.Perm CFSG.ABGLocalTools

section Five

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_avoiding_five (h5 : Fintype.card Ω = 5) (x y z t : Ω) :
    ∃ ω : Ω, ω ≠ x ∧ ω ≠ y ∧ ω ≠ z ∧ ω ≠ t := by
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset Ω) ⊆ {x, y, z, t} := by
    intro ω _
    by_cases h1 : ω = x
    · simp [h1]
    by_cases h2 : ω = y
    · simp [h2]
    by_cases h3 : ω = z
    · simp [h3]
    simp [hcon ω h1 h2 h3]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, h5] at h1
  have h2 : ({x, y, z, t} : Finset Ω).card ≤ 4 := Finset.card_le_four
  omega

theorem forall_eq_five (h5 : Fintype.card Ω = 5) {x y z w ω : Ω} (hxy : x ≠ y) (hxz : x ≠ z)
    (hxw : x ≠ w) (hxω : x ≠ ω) (hyz : y ≠ z) (hyw : y ≠ w) (hyω : y ≠ ω) (hzw : z ≠ w)
    (hzω : z ≠ ω) (hwω : w ≠ ω) : ∀ p : Ω, p = x ∨ p = y ∨ p = z ∨ p = w ∨ p = ω := by
  have hS : ({x, y, z, w, ω} : Finset Ω).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxw, hxω]),
      Finset.card_insert_of_notMem (by simp [hyz, hyw, hyω]),
      Finset.card_insert_of_notMem (by simp [hzw, hzω]),
      Finset.card_insert_of_notMem (by simp [hwω]), Finset.card_singleton]
  have hU : ({x, y, z, w, ω} : Finset Ω) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hS, h5])
  intro p
  have : p ∈ ({x, y, z, w, ω} : Finset Ω) := by rw [hU]; exact Finset.mem_univ p
  simpa using this

theorem swaps_disjoint_of_card_eight (P : Subgroup (Perm Ω)) (hP : Nat.card P = 8) {a b c d : Ω}
    (hab : a ≠ b) (hcd : c ≠ d) (h1 : swap a b ∈ P) (h2 : swap c d ∈ P)
    (hne : swap a b ≠ swap c d) : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have key : ∀ p q r : Ω, p ≠ q → p ≠ r → q ≠ r → swap p q ∈ P → swap p r ∈ P → False := by
    intro p q r hpq hpr hqr hpq' hpr'
    have h3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same hpq hpr hqr
    have hmem : swap p q * swap p r ∈ P := P.mul_mem hpq' hpr'
    have hord : orderOf (⟨swap p q * swap p r, hmem⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
    rw [← Subgroup.orderOf_coe (⟨swap p q * swap p r, hmem⟩ : P)] at hord
    have h4 : orderOf (swap p q * swap p r) = 3 := h3.orderOf
    have h5 : orderOf ((⟨swap p q * swap p r, hmem⟩ : P) : Perm Ω) = 3 := h4
    rw [h5, hP] at hord
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl
    by_cases hbd : b = d
    · exact hne (by rw [hbd])
    · exact key a b d hab hcd hbd h1 h2
  · rintro rfl
    by_cases hbc : b = c
    · exact hne (by rw [hbc, swap_comm])
    · exact key a b c hab (Ne.symm hcd) hbc h1 (by rwa [swap_comm] at h2)
  · rintro rfl
    by_cases had : a = d
    · exact hne (by rw [had, swap_comm])
    · exact key b a d (Ne.symm hab) hcd had (by rwa [swap_comm] at h1) h2
  · rintro rfl
    by_cases hac : a = c
    · exact hne (by rw [hac])
    · exact key b a c (Ne.symm hab) (Ne.symm hcd) hac (by rwa [swap_comm] at h1)
        (by rwa [swap_comm] at h2)

omit [Fintype Ω] [DecidableEq Ω] in
theorem perm_ext_five {x y z w ω : Ω} (hall : ∀ p : Ω, p = x ∨ p = y ∨ p = z ∨ p = w ∨ p = ω)
    {σ τ : Perm Ω} (hx : σ x = τ x) (hy : σ y = τ y) (hz : σ z = τ z) (hw : σ w = τ w)
    (hω : σ ω = τ ω) : σ = τ := by
  ext p
  rcases hall p with rfl | rfl | rfl | rfl | rfl <;> assumption

omit [Fintype Ω] in
theorem mem_four_of_preserves {x y z w ω : Ω}
    (hall : ∀ p : Ω, p = x ∨ p = y ∨ p = z ∨ p = w ∨ p = ω)
    (_hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hxω : x ≠ ω) (hyω : y ≠ ω) (hzω : z ≠ ω) (hwω : w ≠ ω) (σ : Perm Ω) (hσω : σ ω = ω)
    (hpair : (σ x = x ∧ σ y = y) ∨ (σ x = y ∧ σ y = x)) :
    σ = 1 ∨ σ = swap x y ∨ σ = swap z w ∨ σ = swap x y * swap z w := by
  have hσz : σ z = z ∨ σ z = w := by
    rcases hall (σ z) with h | h | h | h | h
    · exfalso
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hxz (σ.injective (h.trans h1.symm)).symm
      · exact hyz (σ.injective (h.trans h2.symm)).symm
    · exfalso
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hyz (σ.injective (h.trans h2.symm)).symm
      · exact hxz (σ.injective (h.trans h1.symm)).symm
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      exact hzω (σ.injective (h.trans hσω.symm))
  have hσw : σ w = z ∨ σ w = w := by
    rcases hall (σ w) with h | h | h | h | h
    · exfalso
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hxw (σ.injective (h.trans h1.symm)).symm
      · exact hyw (σ.injective (h.trans h2.symm)).symm
    · exfalso
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hyw (σ.injective (h.trans h2.symm)).symm
      · exact hxw (σ.injective (h.trans h1.symm)).symm
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      exact hwω (σ.injective (h.trans hσω.symm))
  have hzw' : (σ z = z ∧ σ w = w) ∨ (σ z = w ∧ σ w = z) := by
    rcases hσz with h3 | h3
    · left
      refine ⟨h3, ?_⟩
      rcases hσw with h | h
      · exact absurd (σ.injective (h.trans h3.symm)) hzw.symm
      · exact h
    · right
      refine ⟨h3, ?_⟩
      rcases hσw with h | h
      · exact h
      · exact absurd (σ.injective (h.trans h3.symm)) hzw.symm
  have e2 := hxz.symm
  have e3 := hxw.symm
  have e4 := hyz.symm
  have e5 := hyw.symm
  have e7 := hxω.symm
  have e8 := hyω.symm
  have e9 := hzω.symm
  have e10 := hwω.symm
  rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hzw' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · left
    refine perm_ext_five hall ?_ ?_ ?_ ?_ ?_ <;> simp [h1, h2, h3, h4, hσω]
  · right; right; left
    refine perm_ext_five hall ?_ ?_ ?_ ?_ ?_ <;>
      simp [h1, h2, h3, h4, hσω, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left,
        Equiv.swap_apply_right, hxz, hxw, hyz, hyw, e9, e10]
  · right; left
    refine perm_ext_five hall ?_ ?_ ?_ ?_ ?_ <;>
      simp [h1, h2, h3, h4, hσω, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left,
        Equiv.swap_apply_right, e2, e3, e4, e5, e7, e8]
  · right; right; right
    refine perm_ext_five hall ?_ ?_ ?_ ?_ ?_ <;>
      simp [h1, h2, h3, h4, hσω, Equiv.swap_apply_of_ne_of_ne, Equiv.swap_apply_left,
        Equiv.swap_apply_right, hxz, hxw, hyz, hyw, e2, e3, e4, e5, e7, e8, e9, e10]

theorem mem_four_of_pairs (h5 : Fintype.card Ω = 5) {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (σ : Perm Ω)
    (h1 : (σ a = a ∧ σ b = b) ∨ (σ a = b ∧ σ b = a))
    (h2 : (σ c = c ∧ σ d = d) ∨ (σ c = d ∧ σ d = c)) :
    σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d := by
  obtain ⟨ω, hωa, hωb, hωc, hωd⟩ := exists_avoiding_five h5 a b c d
  have hall := forall_eq_five h5 hab hac had hωa.symm hbc hbd hωb.symm hcd hωc.symm hωd.symm
  have hσω : σ ω = ω := by
    rcases hall (σ ω) with h | h | h | h | h
    · exfalso
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hωa (σ.injective (h.trans e1.symm))
      · exact hωb (σ.injective (h.trans e2.symm))
    · exfalso
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hωb (σ.injective (h.trans e2.symm))
      · exact hωa (σ.injective (h.trans e1.symm))
    · exfalso
      rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hωc (σ.injective (h.trans e1.symm))
      · exact hωd (σ.injective (h.trans e2.symm))
    · exfalso
      rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hωd (σ.injective (h.trans e2.symm))
      · exact hωc (σ.injective (h.trans e1.symm))
    · exact h
  exact mem_four_of_preserves hall hab hac had hbc hbd hcd hωa.symm hωb.symm hωc.symm hωd.symm σ
    hσω h1

omit [Fintype Ω] in
theorem swap_eq_swap_mem {a b x y : Ω} (hab : a ≠ b) (h : swap x y = swap a b) :
    (a = x ∨ a = y) ∧ (b = x ∨ b = y) := by
  have key : ∀ p q : Ω, p ≠ q → swap x y = swap p q → (p = x ∨ p = y) := by
    intro p q hpq hs
    by_contra hc
    push Not at hc
    have h1 : swap x y p = q := by rw [hs, swap_apply_left]
    rw [swap_apply_of_ne_of_ne hc.1 hc.2] at h1
    exact hpq h1
  exact ⟨key a b hab h, key b a hab.symm (by rw [h, swap_comm])⟩

theorem sylow_two_swaps (h5 : Fintype.card Ω = 5) (P : Subgroup (Perm Ω)) (hP : Nat.card P = 8)
    {x y : Ω} (hxy : x ≠ y) (hsw : swap x y ∈ P) :
    ∃ z w ω : Ω, z ≠ w ∧ z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧ ω ≠ x ∧ ω ≠ y ∧ ω ≠ z ∧ ω ≠ w ∧
      (∀ σ ∈ P, σ ω = ω) ∧ swap z w ∈ P ∧ (∃ q ∈ P, q * swap x y * q⁻¹ = swap z w) ∧
      ∀ u v : Ω, u ≠ v → swap u v ∈ P → swap u v = swap x y ∨ swap u v = swap z w := by
  classical
  have hPg : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, ∀ σ ∈ P, σ ω = ω := by
    have hmod := hPg.card_modEq_card_fixedPoints Ω
    rw [Nat.card_eq_fintype_card, h5] at hmod
    by_contra hno
    push Not at hno
    have h0 : Nat.card (MulAction.fixedPoints P Ω) = 0 := by
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun ⟨a, ha⟩ => ?_⟩
      obtain ⟨σ, hσ, hne⟩ := hno a
      exact hne (ha ⟨σ, hσ⟩)
    rw [h0] at hmod
    exact absurd hmod (by decide)
  have hswω := hω _ hsw
  have hxω : x ≠ ω := by
    intro h
    rw [← h, swap_apply_left] at hswω
    exact hxy hswω.symm
  have hyω : y ≠ ω := by
    intro h
    rw [← h, swap_apply_right] at hswω
    exact hxy hswω
  obtain ⟨z, hzx, hzy, hzω, -⟩ := exists_avoiding_five h5 x y ω ω
  obtain ⟨w, hwx, hwy, hwz, hwω⟩ := exists_avoiding_five h5 x y z ω
  have hzw : z ≠ w := hwz.symm
  have hall := forall_eq_five h5 hxy hzx.symm hwx.symm hxω hzy.symm hwy.symm hyω hzw hzω hwω
  have hex : ∃ q ∈ P, ¬ ((q x = x ∨ q x = y) ∧ (q y = x ∨ q y = y)) := by
    by_contra hno
    push Not at hno
    have hsub : (P : Set (Perm Ω)) ⊆
        ↑({1, swap x y, swap z w, swap x y * swap z w} : Finset (Perm Ω)) := by
      intro σ hσ
      obtain ⟨hx1, hy1⟩ := hno σ hσ
      have hpair : (σ x = x ∧ σ y = y) ∨ (σ x = y ∧ σ y = x) := by
        rcases hx1 with h1 | h1 <;> rcases hy1 with h2 | h2
        · exact absurd (σ.injective (h1.trans h2.symm)) hxy
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact absurd (σ.injective (h1.trans h2.symm)) hxy
      rcases mem_four_of_preserves hall hxy hzx.symm hwx.symm hzy.symm hwy.symm hzw hxω hyω hzω
        hwω σ (hω σ hσ) hpair with h | h | h | h <;> simp [h]
    have h4 : Nat.card ↥P ≤ 4 := by
      calc Nat.card ↥P = (P : Set (Perm Ω)).ncard := Nat.card_coe_set_eq _
        _ ≤ (↑({1, swap x y, swap z w, swap x y * swap z w} : Finset (Perm Ω)) :
              Set (Perm Ω)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = ({1, swap x y, swap z w, swap x y * swap z w} : Finset (Perm Ω)).card :=
            Set.ncard_coe_finset _
        _ ≤ 4 := Finset.card_le_four
    omega
  obtain ⟨q, hqP, hq⟩ := hex
  have hqne : q x ≠ q y := fun h => hxy (q.injective h)
  have hconj : q * swap x y * q⁻¹ = swap (q x) (q y) := (swap_apply_apply q x y).symm
  have hqP' : swap (q x) (q y) ∈ P := by
    rw [← hconj]
    exact P.mul_mem (P.mul_mem hqP hsw) (P.inv_mem hqP)
  have hne : swap x y ≠ swap (q x) (q y) := fun h => hq (swap_eq_swap_mem hqne h)
  obtain ⟨d1, d2, d3, d4⟩ := swaps_disjoint_of_card_eight P hP hxy hqne hsw hqP' hne
  have hqxω : q x ≠ ω := fun h => hxω (q.injective (h.trans (hω q hqP).symm))
  have hqyω : q y ≠ ω := fun h => hyω (q.injective (h.trans (hω q hqP).symm))
  have hqx : q x = z ∨ q x = w := by
    rcases hall (q x) with h | h | h | h | h
    · exact absurd h.symm d1
    · exact absurd h.symm d3
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hqxω
  have hqy : q y = z ∨ q y = w := by
    rcases hall (q y) with h | h | h | h | h
    · exact absurd h.symm d2
    · exact absurd h.symm d4
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hqyω
  have hzwq : swap (q x) (q y) = swap z w := by
    rcases hqx with h1 | h1 <;> rcases hqy with h2 | h2
    · exact absurd (h1.trans h2.symm) hqne
    · rw [h1, h2]
    · rw [h1, h2, swap_comm]
    · exact absurd (h1.trans h2.symm) hqne
  have hzwP : swap z w ∈ P := hzwq ▸ hqP'
  refine ⟨z, w, ω, hzw, hzx, hzy, hwx, hwy, hxω.symm, hyω.symm, hzω.symm, hwω.symm, hω, hzwP,
    ⟨q, hqP, hconj.trans hzwq⟩, ?_⟩
  intro u v huv huvP
  by_contra hcon
  push Not at hcon
  obtain ⟨e1, e2, e3, e4⟩ := swaps_disjoint_of_card_eight P hP huv hxy huvP hsw hcon.1
  obtain ⟨f1, f2, f3, f4⟩ := swaps_disjoint_of_card_eight P hP huv hzw huvP hzwP hcon.2
  have hu : u = ω := by
    rcases hall u with h | h | h | h | h
    · exact absurd h e1
    · exact absurd h e2
    · exact absurd h f1
    · exact absurd h f2
    · exact h
  have hv : v = ω := by
    rcases hall v with h | h | h | h | h
    · exact absurd h e3
    · exact absurd h e4
    · exact absurd h f3
    · exact absurd h f4
    · exact h
  exact huv (hu.trans hv.symm)

theorem card_sylow_sym_five (h5 : Fintype.card Ω = 5) {P : Subgroup (Perm Ω)}
    (hP : IsSylowOf 2 P ⊤) : Nat.card P = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h120 : (120 : ℕ).factorization 2 = 3 := by
    have h : (120 : ℕ) = 2 ^ 3 * 15 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  have h120' : Nat.card (Perm Ω) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h5]
    rfl
  rw [hP.card_eq, Subgroup.card_top, h120', h120]
  norm_num

end Five

end CFSG.QuasithinUnique.Setup.Lift
