module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm

variable {Ω : Type} {p : ℕ}

section Cycle

variable [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem pow_apply_mem_of_moves {a : Perm Ω} {O : Finset Ω} (hmv : ∀ x, a x ≠ x ↔ x ∈ O)
    {x : Ω} (hx : x ∈ O) (k : ℕ) : (a ^ k) x ∈ O := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    have h1 := (hmv ((a ^ k) x)).2 ih
    exact (hmv _).1 (fun h => h1 (a.injective h))

omit [DecidableEq Ω] in
theorem pow_apply_injOn (hp : p.Prime) {a : Perm Ω} (ha : a ^ p = 1) {x : Ω} (hx : a x ≠ x) :
    Set.InjOn (fun k : ℕ => (a ^ k) x) (Set.Iio p) := by
  have hne : ∀ j k : ℕ, j < k → k < p → (a ^ j) x ≠ (a ^ k) x := by
    intro j k hjk hkp hEq
    have h1 : (a ^ (k - j)) x = x := by
      have : (a ^ j) ((a ^ (k - j)) x) = (a ^ j) x := by
        rw [← Perm.mul_apply, ← pow_add, show j + (k - j) = k by omega]
        exact hEq.symm
      exact (a ^ j).injective this
    have hm0 : 0 < k - j := by omega
    have hmp : k - j < p := by omega
    have hcop : Nat.Coprime (k - j) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hm0 hmp)).symm
    obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have h2 : (a ^ ((k - j) * r)) x = x := by
      rw [pow_mul]
      exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h1 r
    rw [pow_eq_pow_mod _ ha, hr, pow_one] at h2
    exact hx h2
  intro j hj k hk hjk
  simp only [Set.mem_Iio] at hj hk
  rcases lt_trichotomy j k with h | h | h
  · exact absurd hjk (hne j k h hk)
  · exact h
  · exact absurd hjk.symm (hne k j h hj)

theorem exists_pow_apply_eq_of_moves (hp : p.Prime) {a : Perm Ω} (ha : a ^ p = 1) {O : Finset Ω}
    (hO : O.card = p) (hmv : ∀ x, a x ≠ x ↔ x ∈ O) {x y : Ω} (hx : x ∈ O) (hy : y ∈ O) :
    ∃ k : ℕ, (a ^ k) x = y := by
  have hinj : Set.InjOn (fun k : ℕ => (a ^ k) x) (Finset.range p : Set ℕ) := by
    simpa using pow_apply_injOn hp ha ((hmv x).2 hx)
  have hcard : ((Finset.range p).image (fun k : ℕ => (a ^ k) x)).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : (Finset.range p).image (fun k : ℕ => (a ^ k) x) ⊆ O := by
    intro z hz
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
    exact pow_apply_mem_of_moves hmv hx k
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hO])
  rw [← heq] at hy
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hy
  exact ⟨k, hk⟩

theorem isCycle_of_moves (hp : p.Prime) {a : Perm Ω} (ha : a ^ p = 1) {O : Finset Ω}
    (hO : O.card = p) (hmv : ∀ x, a x ≠ x ↔ x ∈ O) : a.IsCycle := by
  obtain ⟨x, hx⟩ : O.Nonempty := Finset.card_pos.1 (by rw [hO]; exact hp.pos)
  refine ⟨x, (hmv x).2 hx, fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow_apply_eq_of_moves hp ha hO hmv hx ((hmv y).1 hy)
  exact ⟨k, by simpa using hk⟩

end Cycle

section Orbit

variable (U : Subgroup (Perm Ω))

theorem mem_orbit_iff_exists_mem {x y : Ω} : y ∈ MulAction.orbit U x ↔ ∃ u ∈ U, u x = y := by
  constructor
  · rintro ⟨⟨u, hu⟩, rfl⟩
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

theorem apply_mem_orbit_of_normalizer {g : Perm Ω}
    (hg : g ∈ Subgroup.normalizer (U : Set (Perm Ω))) {x y : Ω}
    (hy : y ∈ MulAction.orbit U x) : g y ∈ MulAction.orbit U (g x) := by
  obtain ⟨u, hu, rfl⟩ := (mem_orbit_iff_exists_mem U).1 hy
  refine (mem_orbit_iff_exists_mem U).2 ⟨g * u * g⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hg u).1 hu
  · simp [Perm.mul_apply]

theorem ncard_orbit_dvd_card (x : Ω) : (MulAction.orbit U x).ncard ∣ Nat.card U := by
  refine Dvd.intro (Nat.card (MulAction.stabilizer U x)) ?_
  rw [← MulAction.index_stabilizer, Subgroup.index_mul_card]

end Orbit

section NoTwo

variable [DecidableEq Ω] {U : Subgroup (Perm Ω)}

theorem subset_of_closed_of_moves (hp : p.Prime) {a : Perm Ω} (ha : a ^ p = 1) {A : Finset Ω}
    (hA : A.card = p) (hmA : ∀ x, a x ≠ x ↔ x ∈ A) {S : Set Ω} (hS : ∀ w ∈ S, a w ∈ S) {y : Ω}
    (hyS : y ∈ S) (hyA : y ∈ A) : ∀ z ∈ A, z ∈ S := by
  intro z hz
  obtain ⟨k, rfl⟩ := exists_pow_apply_eq_of_moves hp ha hA hmA hyA hz
  clear hz
  induction k with
  | zero => simpa using hyS
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact hS _ ih

theorem mem_or_mem_of_card [Fintype Ω] {A B : Finset Ω} (hA : A.card = p) (hB : B.card = p)
    (hAB : Disjoint A B) (hcard : Fintype.card Ω = 2 * p) (z : Ω) : z ∈ A ∨ z ∈ B := by
  have hunion : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hAB, hA, hB, hcard]
    ring
  exact Finset.mem_union.1 (by rw [hunion]; exact Finset.mem_univ z)

theorem apply_mem_of_normalized [Fintype Ω] (hp : p.Prime)
    (hcard : Fintype.card Ω = 2 * p) (hU : ¬ p ∣ Nat.card U) {a b : Perm Ω} {A B : Finset Ω}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hA : A.card = p) (hB : B.card = p) (hAB : Disjoint A B)
    (hmA : ∀ x, a x ≠ x ↔ x ∈ A) (hmB : ∀ x, b x ≠ x ↔ x ∈ B)
    (hna : a ∈ Subgroup.normalizer (U : Set (Perm Ω)))
    (hnb : b ∈ Subgroup.normalizer (U : Set (Perm Ω))) {x : Ω} (hx : x ∈ B) {u : Perm Ω}
    (hu : u ∈ U) : u x ∈ B := by
  by_contra hux
  have hcov := mem_or_mem_of_card hA hB hAB hcard
  have hyA : u x ∈ A := (hcov _).resolve_right hux
  have hax : a x = x := by
    by_contra h
    exact Finset.disjoint_left.1 hAB ((hmA x).1 h) hx
  have hby : b (u x) = u x := by
    by_contra h
    exact Finset.disjoint_left.1 hAB hyA ((hmB _).1 h)
  have hyorb : u x ∈ MulAction.orbit U x := (mem_orbit_iff_exists_mem U).2 ⟨u, hu, rfl⟩
  have h1 : ∀ z ∈ A, z ∈ MulAction.orbit U x := by
    refine subset_of_closed_of_moves hp ha hA hmA (fun w hw => ?_) hyorb hyA
    have := apply_mem_orbit_of_normalizer U hna hw
    rwa [hax] at this
  have horbeq : MulAction.orbit U (u x) = MulAction.orbit U x := MulAction.orbit_eq_iff.2 hyorb
  have h2 : ∀ z ∈ B, z ∈ MulAction.orbit U (u x) := by
    refine subset_of_closed_of_moves hp hb hB hmB (fun w hw => ?_) ?_ hx
    · have := apply_mem_orbit_of_normalizer U hnb hw
      rwa [hby] at this
    · rw [horbeq]
      exact MulAction.mem_orbit_self x
  have hall : ∀ z : Ω, z ∈ MulAction.orbit U x := by
    intro z
    rcases hcov z with hz | hz
    · exact h1 z hz
    · have := h2 z hz
      rwa [horbeq] at this
  have hcardorb : (MulAction.orbit U x).ncard = 2 * p := by
    rw [Set.eq_univ_of_forall hall, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  have hdvd := ncard_orbit_dvd_card U x
  rw [hcardorb] at hdvd
  exact hU ((Dvd.intro_left 2 rfl).trans hdvd)

theorem fixes_of_stable_of_moves [Fintype Ω] (hp : p.Prime) (hU : ¬ p ∣ Nat.card U) {a : Perm Ω}
    (ha : a ^ p = 1) {A : Finset Ω} (hA : A.card = p) (hmA : ∀ x, a x ≠ x ↔ x ∈ A)
    (hna : a ∈ Subgroup.normalizer (U : Set (Perm Ω))) (hst : ∀ u ∈ U, ∀ x ∈ A, u x ∈ A) :
    ∀ u ∈ U, ∀ x ∈ A, u x = x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ : A.Nonempty := Finset.card_pos.1 (by rw [hA]; exact hp.pos)
  have hZN : ∀ g ∈ Subgroup.zpowers a, g ∈ Subgroup.normalizer (U : Set (Perm Ω)) :=
    fun g hg => (Subgroup.zpowers_le.2 hna) hg
  let D : Subgroup (Perm Ω) :=
    { carrier := {g | g ∈ Subgroup.zpowers a ∧ g x₀ ∈ MulAction.orbit U x₀}
      mul_mem' := by
        rintro g h ⟨hgZ, hgx⟩ ⟨hhZ, hhx⟩
        refine ⟨Subgroup.mul_mem _ hgZ hhZ, ?_⟩
        have h1 := apply_mem_orbit_of_normalizer U (hZN g hgZ) hhx
        rw [MulAction.orbit_eq_iff.2 hgx] at h1
        simpa using h1
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro g ⟨hgZ, hgx⟩
        refine ⟨Subgroup.inv_mem _ hgZ, ?_⟩
        have h1 := apply_mem_orbit_of_normalizer U (hZN g⁻¹ (Subgroup.inv_mem _ hgZ)) hgx
        have h1' : x₀ ∈ MulAction.orbit U (g⁻¹ x₀) := by simpa using h1
        have h2 : MulAction.orbit U x₀ = MulAction.orbit U (g⁻¹ x₀) := MulAction.orbit_eq_iff.2 h1'

        rw [h2]
        exact MulAction.mem_orbit_self _ }
  have hne : a ≠ 1 := fun h => (hmA x₀).2 hx₀ (by rw [h]; rfl)
  have hZcard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha hne]
  have hDZ : D ≤ Subgroup.zpowers a := fun g hg => hg.1
  have hDdvd : Nat.card D ∣ p := hZcard ▸ Subgroup.card_dvd_of_le hDZ
  have hfix0 : ∀ u ∈ U, u x₀ = x₀ := by
    rcases (Nat.dvd_prime hp).1 hDdvd with h1 | h1
    · have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      intro u hu
      obtain ⟨k, hk⟩ := exists_pow_apply_eq_of_moves hp ha hA hmA hx₀ (hst u hu x₀ hx₀)
      have hmem : a ^ k ∈ D := ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k, by
        rw [hk]
        exact (mem_orbit_iff_exists_mem U).2 ⟨u, hu, rfl⟩⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      rw [← hk, hmem]
      rfl
    · exfalso
      have hD : D = Subgroup.zpowers a := Subgroup.eq_of_le_of_card_ge hDZ (by rw [hZcard, h1])
      have hall : (MulAction.orbit U x₀) = (A : Set Ω) := by
        refine Set.Subset.antisymm ?_ ?_
        · rintro _ ⟨⟨u, hu⟩, rfl⟩
          exact hst u hu x₀ hx₀
        · intro y hy
          obtain ⟨k, hk⟩ := exists_pow_apply_eq_of_moves hp ha hA hmA hx₀ (Finset.mem_coe.1 hy)
          have : a ^ k ∈ D := by rw [hD]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) k
          rw [← hk]
          exact this.2
      have := ncard_orbit_dvd_card U x₀
      rw [hall, Set.ncard_coe_finset, hA] at this
      exact hU this
  intro u hu x hx
  obtain ⟨k, rfl⟩ := exists_pow_apply_eq_of_moves hp ha hA hmA hx₀ hx
  have hnk : (a ^ k)⁻¹ ∈ Subgroup.normalizer (U : Set (Perm Ω)) :=
    inv_mem (Subgroup.pow_mem _ hna k)
  have h1 := (Subgroup.mem_normalizer_iff.1 hnk u).1 hu
  have h2 := hfix0 _ h1
  simp only [inv_inv, Perm.mul_apply] at h2
  have h3 : u ((a ^ k) x₀) = (a ^ k) x₀ := by
    apply (a ^ k).symm.injective
    simpa using h2
  exact h3

theorem eq_bot_of_normalized_by_cycles_coprime [Fintype Ω] (hp : p.Prime)
    (hcard : Fintype.card Ω = 2 * p) (hU : ¬ p ∣ Nat.card U) {a b : Perm Ω} {A B : Finset Ω}
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hA : A.card = p) (hB : B.card = p) (hAB : Disjoint A B)
    (hmA : ∀ x, a x ≠ x ↔ x ∈ A) (hmB : ∀ x, b x ≠ x ↔ x ∈ B)
    (hna : a ∈ Subgroup.normalizer (U : Set (Perm Ω)))
    (hnb : b ∈ Subgroup.normalizer (U : Set (Perm Ω))) : U = ⊥ := by
  have hstB : ∀ u ∈ U, ∀ x ∈ B, u x ∈ B := fun u hu x hx =>
    apply_mem_of_normalized hp hcard hU ha hb hA hB hAB hmA hmB hna hnb hx hu
  have hstA : ∀ u ∈ U, ∀ x ∈ A, u x ∈ A := fun u hu x hx =>
    apply_mem_of_normalized hp hcard hU hb ha hB hA hAB.symm hmB hmA hnb hna hx hu
  have hfA := fixes_of_stable_of_moves hp hU ha hA hmA hna hstA
  have hfB := fixes_of_stable_of_moves hp hU hb hB hmB hnb hstB
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  ext x
  rcases mem_or_mem_of_card hA hB hAB hcard x with hx | hx
  · exact hfA u hu x hx
  · exact hfB u hu x hx

end NoTwo

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
