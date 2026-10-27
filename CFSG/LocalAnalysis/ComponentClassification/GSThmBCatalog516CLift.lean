module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup
open scoped commutatorElement

section Fix

variable {Y : Type*} [Group Y]

theorem fix_of_perfect (α : MulAut Y) (P : Subgroup Y) (hP : ⁅P, P⁆ = P)
    (h : ∀ y ∈ P, y⁻¹ * α y ∈ center Y) : ∀ y ∈ P, α y = y := by
  have key : ⁅P, P⁆ ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id Y) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    change α ⁅x, y⁆ = ⁅x, y⁆
    obtain ⟨z₁, hz₁, e1⟩ : ∃ z ∈ center Y, α x = x * z := ⟨_, h x hx, by group⟩
    obtain ⟨z₂, hz₂, e2⟩ : ∃ z ∈ center Y, α y = y * z := ⟨_, h y hy, by group⟩
    have c1 : z₁ * y = y * z₁ := (mem_center_iff.mp hz₁ y).symm
    have c2 : z₂ * x⁻¹ = x⁻¹ * z₂ := (mem_center_iff.mp hz₂ x⁻¹).symm
    have c12 : z₁ * z₂ = z₂ * z₁ := (mem_center_iff.mp hz₁ z₂).symm
    rw [map_commutatorElement, e1, e2, commutatorElement_def, commutatorElement_def]
    calc x * z₁ * (y * z₂) * (x * z₁)⁻¹ * (y * z₂)⁻¹
        = x * (z₁ * y) * z₂ * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by group
      _ = x * y * (z₁ * z₂) * z₁⁻¹ * x⁻¹ * z₂⁻¹ * y⁻¹ := by rw [c1]; group
      _ = x * y * (z₂ * x⁻¹) * z₂⁻¹ * y⁻¹ := by rw [c12]; group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [c2]; group
  intro y hy
  exact (hP ▸ key) hy

end Fix

theorem eq_of_card_two {Y : Type*} [Group Y] {Z : Subgroup Y} (hZ : Nat.card Z = 2) {a b : Y}
    (ha : a ∈ Z) (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hne
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype Z := Fintype.ofFinite Z
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      exact hne (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm, fun h => hb1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_univ ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset Z)
  rw [← Nat.card_eq_fintype_card, hZ] at this
  omega

section Lift

variable {Y L : Type*} [Group Y] [Group L] (π : Y →* L)

@[expose] def liftN (M : Subgroup L) : Subgroup Y := ⁅M.comap π, M.comap π⁆

theorem liftN_le (M : Subgroup L) : liftN π M ≤ M.comap π := Subgroup.commutator_le_self _

variable {π}

theorem map_liftN {M : Subgroup L} (hM : ⁅M, M⁆ = M) (hMr : M ≤ π.range) :
    (liftN π M).map π = M := by
  rw [liftN, Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.mpr hMr, hM]

theorem liftN_perfect (hker : π.ker ≤ center Y) {M : Subgroup L} (hM : ⁅M, M⁆ = M)
    (hMr : M ≤ π.range) : ⁅liftN π M, liftN π M⁆ = liftN π M := by
  apply le_antisymm (Subgroup.commutator_le_self _)
  have hsplit : ∀ a ∈ M.comap π, ∃ n ∈ liftN π M, ∃ z ∈ center Y, a = n * z := by
    intro a ha
    have : π a ∈ (liftN π M).map π := by rw [map_liftN hM hMr]; exact ha
    obtain ⟨n, hn, hna⟩ := this
    refine ⟨n, hn, n⁻¹ * a, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hna, inv_mul_cancel]
  change ⁅M.comap π, M.comap π⁆ ≤ ⁅liftN π M, liftN π M⁆
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hsplit a ha
  obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hsplit b hb
  have c1 : z₁ * n₂ = n₂ * z₁ := (mem_center_iff.mp hz₁ n₂).symm
  have c2 : z₂ * n₁⁻¹ = n₁⁻¹ * z₂ := (mem_center_iff.mp hz₂ n₁⁻¹).symm
  have c12 : z₁ * z₂ = z₂ * z₁ := (mem_center_iff.mp hz₁ z₂).symm
  have : ⁅n₁ * z₁, n₂ * z₂⁆ = ⁅n₁, n₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc n₁ * z₁ * (n₂ * z₂) * (n₁ * z₁)⁻¹ * (n₂ * z₂)⁻¹
        = n₁ * (z₁ * n₂) * z₂ * z₁⁻¹ * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by group
      _ = n₁ * n₂ * (z₁ * z₂) * z₁⁻¹ * n₁⁻¹ * z₂⁻¹ * n₂⁻¹ := by rw [c1]; group
      _ = n₁ * n₂ * (z₂ * n₁⁻¹) * z₂⁻¹ * n₂⁻¹ := by rw [c12]; group
      _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by rw [c2]; group
  rw [this]
  exact Subgroup.commutator_mem_commutator hn₁ hn₂

theorem sq_eq_one_of_mem_center (hZ : Nat.card (center Y) = 2) {k : Y} (hk : k ∈ center Y) :
    k * k = 1 := by
  have : Finite (center Y) := Nat.finite_of_card_ne_zero (by omega)
  have h := pow_card_eq_one' (G := center Y) (x := ⟨k, hk⟩)
  rw [hZ, pow_two] at h
  exact congrArg Subtype.val h

theorem center_le_of_sq (hZ : Nat.card (center Y) = 2) {M : Subgroup L} (hM : ⁅M, M⁆ = M)
    (hMr : M ≤ π.range) (hker : π.ker ≤ center Y) {y : Y} (hy : π y ∈ M) (hy2 : y * y ≠ 1)
    (hyZ : y * y ∈ center Y) : center Y ≤ liftN π M := by
  have : π y ∈ (liftN π M).map π := by rw [map_liftN hM hMr]; exact hy
  obtain ⟨n, hn, hny⟩ := this
  have hk : y⁻¹ * n ∈ center Y := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hny, inv_mul_cancel])
  have hnn : n * n = y * y := by
    obtain ⟨k, hk', rfl⟩ : ∃ k ∈ center Y, n = y * k := ⟨_, hk, by group⟩
    have hkk := sq_eq_one_of_mem_center hZ hk'
    calc y * k * (y * k) = y * y * (k * k) := by
          rw [mul_assoc y k, ← mul_assoc k y k, (mem_center_iff.mp hk' y).symm]; group
      _ = y * y := by rw [hkk, mul_one]
  have hmem : n * n ∈ liftN π M := mul_mem hn hn
  rw [hnn] at hmem
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact one_mem _
  rw [eq_of_card_two hZ hz hyZ hz1 hy2]
  exact hmem

end Lift

section Bar

variable {Y : Type*} [Group Y]

abbrev piZ : Y →* Y ⧸ center Y := QuotientGroup.mk' (center Y)

theorem ker_piZ : (piZ (Y := Y)).ker ≤ center Y := by
  rw [QuotientGroup.ker_mk']

theorem range_piZ : (piZ (Y := Y)).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

theorem le_range_piZ (M : Subgroup (Y ⧸ center Y)) : M ≤ (piZ (Y := Y)).range := by
  rw [range_piZ]
  exact le_top

@[expose] def barAut (α : MulAut Y) : MulAut (Y ⧸ center Y) :=
  QuotientGroup.congr (center Y) (center Y) α (Subgroup.map_center_eq α)

theorem barAut_mk (α : MulAut Y) (y : Y) :
    barAut α (QuotientGroup.mk y) = QuotientGroup.mk (α y) :=
  QuotientGroup.congr_mk _ _ _ _ y

theorem barAut_one : barAut (1 : MulAut Y) = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [barAut_mk]
  rfl

theorem barAut_mul (α β : MulAut Y) : barAut (α * β) = barAut α * barAut β := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.mul_apply, barAut_mk, barAut_mk, barAut_mk]
  rfl

theorem barAut_sq {α : MulAut Y} (h : α ^ 2 = 1) : barAut α ^ 2 = 1 := by
  rw [pow_two, ← barAut_mul, ← pow_two, h, barAut_one]

theorem barAut_conj (t : Y) : barAut (MulAut.conj t) = MulAut.conj (QuotientGroup.mk t) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [barAut_mk, MulAut.conj_apply, MulAut.conj_apply]
  rfl

theorem not_inner_of_bar {α : MulAut Y} (h : ∀ x, barAut α ≠ MulAut.conj x) :
    ∀ t : Y, α ≠ MulAut.conj t := by
  rintro t rfl
  exact h _ (barAut_conj t)

theorem fixed_lift (α : MulAut Y) {M : Subgroup (Y ⧸ center Y)} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, barAut α x = x) : ∀ y ∈ liftN (piZ (Y := Y)) M, α y = y := by
  apply fix_of_perfect α _ (liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ M))
  intro y hy
  have h1 := hfix _ (liftN_le (piZ (Y := Y)) M hy)
  change barAut α (QuotientGroup.mk y) = QuotientGroup.mk y at h1
  rw [barAut_mk, QuotientGroup.eq] at h1
  have : (α y)⁻¹ * y ∈ center Y := h1
  have h2 := inv_mem this
  rwa [mul_inv_rev, inv_inv] at h2

theorem concl_center (hZ : Nat.card (center Y) = 2) (α : MulAut Y)
    {M : Subgroup (Y ⧸ center Y)} (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, barAut α x = x) {y : Y}
    (hy : (QuotientGroup.mk y : Y ⧸ center Y) ∈ M) (hy2 : y * y ≠ 1)
    (hyZ : y * y ∈ center Y) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧ center Y ≤ N :=
  ⟨liftN (piZ (Y := Y)) M, fixed_lift α hM hfix,
    liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ M),
    center_le_of_sq hZ hM (le_range_piZ M) (ker_piZ (Y := Y)) hy hy2 hyZ⟩

theorem concl_outer (α : MulAut Y) {M : Subgroup (Y ⧸ center Y)} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, barAut α x = x) (hout : ∀ x, barAut α ≠ MulAut.conj x)
    (h4 : 4 ∣ Nat.card M) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧ (∀ t : Y, α ≠ MulAut.conj t) ∧
      4 ∣ Nat.card N := by
  refine ⟨liftN (piZ (Y := Y)) M, fixed_lift α hM hfix,
    liftN_perfect (ker_piZ (Y := Y)) hM (le_range_piZ M), not_inner_of_bar hout, h4.trans ?_⟩
  have := Subgroup.card_map_dvd (H := liftN (piZ (Y := Y)) M) (piZ (Y := Y))
  rwa [map_liftN hM (le_range_piZ M)] at this

end Bar

end CFSG.ComponentClassification.GSThmB.Cent516
