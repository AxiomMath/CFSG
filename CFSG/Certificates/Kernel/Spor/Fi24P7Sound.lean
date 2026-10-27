module

public import Certificates.Data.Kernel.Spor.Fi24P7
public import CFSG.Certificates.Kernel.Spor.Fi24G2eSound
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.Fi24P7S

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24P7 CFSG.KC.Fi24G2eS

theorem incStep_spec {FL : ℕ → ℕ} {n m j : ℕ} (h : incStep FL n m j = true) :
    FL j < n ∧ (j + 1 < m → FL j < FL (j + 1)) := by
  unfold incStep at h
  simp only [letB_eqE, andB_eqE, orB_eqE, Bool.and_eq_true, Bool.or_eq_true] at h
  refine ⟨by simpa using h.1, fun hj => ?_⟩
  rcases h.2 with h2 | h2
  · have := Nat.le_of_ble_eq_true h2
    omega
  · simpa using h2

theorem wStep_spec {TG : ℕ → ℕ → ℕ} {FL P : ℕ → ℕ} {w : List ℕ} {m j : ℕ}
    (h : wStep TG FL P w m j = true) : P j < m ∧ walk TG w (FL j) = FL (P j) := by
  unfold wStep at h
  simp only [letB_eqE, andB_eqE, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem tStep_spec {PA PB PAR DEP : ℕ → ℕ} {m j0 j : ℕ} (h : tStep PA PB PAR DEP m j0 j = true) :
    j = j0 ∨ (PAR j < m ∧ DEP (PAR j) < DEP j ∧ (PA (PAR j) = j ∨ PB (PAR j) = j)) := by
  unfold tStep at h
  simp only [letB_eqE, andB_eqE, orB_eqE, Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h with h | ⟨h1, h2, h3⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · refine Or.inr ⟨by simpa using h1, by simpa using h2, ?_⟩
    rcases h3 with h3 | h3
    · exact Or.inl (Nat.eq_of_beq_eq_true h3)
    · exact Or.inr (Nat.eq_of_beq_eq_true h3)

theorem qStep_spec {Q QA P : ℕ → ℕ} {m1 M k : ℕ} (h : qStep Q QA P m1 M k = true) :
    QA k < M ∧ Q (QA k) = m1 * P (Q k / m1) + P (Q k % m1) := by
  unfold qStep at h
  simp only [letB_eqE, andB_eqE, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem qIncStep_spec {Q : ℕ → ℕ} {m1 M k : ℕ} (h : qIncStep Q m1 M k = true) :
    Q k < m1 * m1 ∧ (k + 1 < M → Q k < Q (k + 1)) := by
  unfold qIncStep at h
  simp only [letB_eqE, andB_eqE, orB_eqE, Bool.and_eq_true, Bool.or_eq_true] at h
  refine ⟨by simpa using h.1, fun hk => ?_⟩
  rcases h.2 with h2 | h2
  · have := Nat.le_of_ble_eq_true h2
    omega
  · simpa using h2

theorem inj_of_inc {FL : ℕ → ℕ} {m : ℕ} (h : ∀ j < m, j + 1 < m → FL j < FL (j + 1)) :
    ∀ i < m, ∀ j < m, FL i = FL j → i = j := by
  have mono : ∀ i j, i < j → j < m → FL i < FL j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have h1 := h j (by omega) hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h2 | h2
      · exact (ih h2 (by omega)).trans h1
      · rw [h2]
        exact h1
  intro i hi j hj e
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd e (mono i j h1 hj).ne
  · exact h1
  · exact absurd e (mono j i h1 hi).ne'

section Orbit

variable {G X : Type*} [Group G] [MulAction G X]

def keepSub [Finite G] (S : Set X) : Subgroup G where
  carrier := {g | ∀ x ∈ S, g • x ∈ S}
  one_mem' := fun x hx => by rw [one_smul]; exact hx
  mul_mem' := fun {g h} hg hh x hx => by rw [mul_smul]; exact hg _ (hh x hx)
  inv_mem' := fun {g} hg => by
    have hpow : ∀ n : ℕ, ∀ x ∈ S, g ^ n • x ∈ S := by
      intro n
      induction n with
      | zero => intro x hx; rw [pow_zero, one_smul]; exact hx
      | succ n ih => intro x hx; rw [pow_succ, mul_smul]; exact ih _ (hg x hx)
    have hn : 0 < orderOf g := orderOf_pos g
    have e : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    intro x hx
    rw [e]
    exact hpow _ x hx

theorem dvd_card_closure_of_tree [Finite G] (a b : G) {m : ℕ} (e : ℕ → X)
    (he : ∀ i < m, ∀ j < m, e i = e j → i = j) {PA PB PAR DEP : ℕ → ℕ}
    (hA : ∀ j < m, PA j < m ∧ a⁻¹ • e j = e (PA j))
    (hB : ∀ j < m, PB j < m ∧ b⁻¹ • e j = e (PB j)) {j0 : ℕ} (hj0 : j0 < m)
    (ht : ∀ j < m, j = j0 ∨ (PAR j < m ∧ DEP (PAR j) < DEP j ∧ (PA (PAR j) = j ∨ PB (PAR j) = j))) :
    m ∣ Nat.card (Subgroup.closure ({a, b} : Set G)) := by
  classical
  set H := Subgroup.closure ({a, b} : Set G) with hH
  set S : Set X := ↑((Finset.range m).image e) with hS
  have memS : ∀ x, x ∈ S ↔ ∃ j < m, e j = x := by
    intro x
    rw [hS, Finset.mem_coe, Finset.mem_image]
    simp only [Finset.mem_range]
  have haS : a⁻¹ ∈ keepSub (G := G) S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (memS x).1 hx
    exact (memS _).2 ⟨PA j, (hA j hj).1, (hA j hj).2.symm⟩
  have hbS : b⁻¹ ∈ keepSub (G := G) S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (memS x).1 hx
    exact (memS _).2 ⟨PB j, (hB j hj).1, (hB j hj).2.symm⟩
  have hHS : H ≤ keepSub S := by
    rw [hH, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · have := (keepSub S).inv_mem haS
      rwa [inv_inv] at this
    · have := (keepSub S).inv_mem hbS
      rwa [inv_inv] at this
  have hsub : MulAction.orbit H (e j0) ⊆ S := by
    rintro _ ⟨h, rfl⟩
    exact hHS h.2 _ ((memS _).2 ⟨j0, hj0, rfl⟩)
  have hsup : ∀ d : ℕ, ∀ j < m, DEP j = d → e j ∈ MulAction.orbit H (e j0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hd
      rcases ht j hj with rfl | ⟨hq, hdq, hpq⟩
      · exact MulAction.mem_orbit_self _
      · obtain ⟨h, hh⟩ := ih _ (hd ▸ hdq) _ hq rfl
        have hh' : (h : G) • e j0 = e (PAR j) := hh
        rcases hpq with hp | hp
        · refine ⟨⟨a⁻¹, H.inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))⟩ * h, ?_⟩
          change (a⁻¹ * (h : G)) • e j0 = e j
          rw [mul_smul, hh', (hA _ hq).2, hp]
        · refine ⟨⟨b⁻¹, H.inv_mem (Subgroup.subset_closure
            (Set.mem_insert_of_mem _ rfl))⟩ * h, ?_⟩
          change (b⁻¹ * (h : G)) • e j0 = e j
          rw [mul_smul, hh', (hB _ hq).2, hp]
  have horb : MulAction.orbit H (e j0) = S := by
    refine Set.Subset.antisymm hsub ?_
    intro x hx
    obtain ⟨j, hj, rfl⟩ := (memS x).1 hx
    exact hsup _ j hj rfl
  have hcard : (MulAction.orbit H (e j0)).ncard = m := by
    rw [horb, hS, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact he i (by simpa using hi) j (by simpa using hj) h
  rw [← hcard, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

end Orbit

end CFSG.KC.Fi24P7S

end
