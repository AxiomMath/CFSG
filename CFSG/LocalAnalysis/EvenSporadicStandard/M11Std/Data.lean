module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11

public section

namespace CFSG.EvenSporadicStandard.M11Std

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.OuterAutomorphisms

structure M11Facts (L : Type) [Group L] : Prop where
  exists_elts : ∃ a b g : L, a ^ 8 = 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a ^ 3 ∧ a ^ 4 ≠ 1 ∧
    (∀ j : ℕ, b ≠ a ^ j) ∧ g * a ^ 4 * g⁻¹ = b ∧ g * b * g⁻¹ = a ^ 4 * b
  card : Nat.card L = 7920
  card_inv : Nat.card {u : L // orderOf u = 2} = 165
  conj_inv : ∀ u v : L, orderOf u = 2 → orderOf v = 2 → IsConj u v

theorem M11Facts.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L') (h : M11Facts L) :
    M11Facts L' := by
  obtain ⟨a, b, g, h1, h2, h3, h4, h5, h6, h7⟩ := h.exists_elts
  refine ⟨⟨e a, e b, e g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa using congrArg e h1
  · simpa using congrArg e h2
  · simpa using congrArg e h3
  · intro h; apply h4; apply e.injective; simpa using h
  · intro j hj; apply h5 j; apply e.injective; simpa using hj
  · simpa using congrArg e h6
  · simpa using congrArg e h7
  · rw [← Nat.card_congr e.toEquiv]; exact h.card
  · rw [← h.card_inv]
    exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun u => by
      simp [MulEquiv.orderOf_eq]) |>.symm
  · intro u v hu hv
    have hu' : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (e.symm v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    obtain ⟨c, hc⟩ := isConj_iff.1 (h.conj_inv _ _ hu' hv')
    refine isConj_iff.2 ⟨e c, ?_⟩
    have := congrArg e hc
    simpa using this

abbrev m11aP : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 2] * List.formPerm [3, 5, 10, 8, 4, 9, 7, 6]

abbrev m11bP : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 2] * List.formPerm [5, 8] * List.formPerm [6, 9] * List.formPerm [7, 10]

abbrev m11gP : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 7, 3] * List.formPerm [2, 10, 4] * List.formPerm [5, 6, 9]

@[expose] def m11wordA : List ℤ :=
  [2, 2, 1, 2, -1, -2, -2, -1, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, -2]

@[expose] def m11wordB : List ℤ :=
  [-1, -2, -1, -1, 2, -1, -2, -1, -2, -1, 2, 1, -2, 1, 2, 1, 2]

@[expose] def m11wordG : List ℤ :=
  [-1, -2, -1, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -1, -2, -1, 2, -1]

theorem m11_gens_mem : ∀ g ∈ [m11gA, m11gB], g ∈ NativeSporadic.M11 := by
  intro g hg
  rcases List.mem_pair.1 hg with rfl | rfl
  · exact m11a.2
  · exact m11b.2

set_option maxRecDepth 100000 in
theorem m11aP_mem : m11aP ∈ NativeSporadic.M11 := by
  have h : evalCodes [m11gA, m11gB] m11wordA = m11aP := by decide
  rw [← h]; exact evalCodes_mem _ m11_gens_mem _

set_option maxRecDepth 100000 in
theorem m11bP_mem : m11bP ∈ NativeSporadic.M11 := by
  have h : evalCodes [m11gA, m11gB] m11wordB = m11bP := by decide
  rw [← h]; exact evalCodes_mem _ m11_gens_mem _

set_option maxRecDepth 100000 in
theorem m11gP_mem : m11gP ∈ NativeSporadic.M11 := by
  have h : evalCodes [m11gA, m11gB] m11wordG = m11gP := by decide
  rw [← h]; exact evalCodes_mem _ m11_gens_mem _

set_option maxRecDepth 100000 in
theorem m11_exists_elts : ∃ a b g : NativeSporadic.M11, a ^ 8 = 1 ∧ b * b = 1 ∧
    b * a * b⁻¹ = a ^ 3 ∧ a ^ 4 ≠ 1 ∧ (∀ j : ℕ, b ≠ a ^ j) ∧ g * a ^ 4 * g⁻¹ = b ∧
    g * b * g⁻¹ = a ^ 4 * b := by
  have hpow : ∀ j : ℕ, m11aP ^ j = m11aP ^ (j % 8) := fun j =>
    pow_eq_pow_mod j (by decide)
  refine ⟨⟨m11aP, m11aP_mem⟩, ⟨m11bP, m11bP_mem⟩, (⟨m11gP, m11gP_mem⟩ : NativeSporadic.M11)⁻¹,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; simp only [Subgroup.coe_pow, Subgroup.coe_one]; decide
  · apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_one]; decide
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
    decide
  · intro h
    have := congrArg Subtype.val h
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    revert this; decide
  · intro j hj
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow] at this
    rw [hpow j] at this
    have h8 : ∀ i : Fin 8, m11bP ≠ m11aP ^ (i : ℕ) := by decide
    exact h8 ⟨j % 8, Nat.mod_lt _ (by norm_num)⟩ this
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    decide
  · apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    decide

theorem m11_conj_inv :
    ∀ u v : NativeSporadic.M11, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  obtain ⟨hok, -, -⟩ := m11_oddcore_cover
  obtain ⟨hoa, -, -, -⟩ := m11_oddcore_aut
  obtain ⟨hr, hro, -, -, -⟩ := m11_rep_data
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  have h := exists_conj_of_repsOK hn m11Certificate hQ (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (m := 2) (by norm_num) m11InvReps
    (fun r hr' => by
      simp only [m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
        List.mem_singleton] at hr'
      subst hr'
      exact ⟨by simpa using hr, hro⟩) 400 hok
  have hcls : ∀ u : NativeSporadic.M11, orderOf u = 2 →
      ∃ c ∈ NativeSporadic.M11, (u : Equiv.Perm (Fin 11)) =
        c * evalCodes [m11gA, m11gB] [1] * c⁻¹ := by
    intro u hu
    obtain ⟨r, hrmem, c, hc, hu'⟩ := h.1 (u : Equiv.Perm (Fin 11))
      (by rw [inv_one, one_mul, m11Certificate_originalSubgroup]; exact u.2)
      (by rw [Subgroup.orderOf_coe]; exact hu)
    simp only [m11InvReps, m11InvRepWords, List.map_cons, List.map_nil,
      List.mem_singleton] at hrmem
    subst hrmem
    exact ⟨c, by rwa [m11Certificate_originalSubgroup] at hc, hu'⟩
  intro u v hu hv
  obtain ⟨c, hc, huc⟩ := hcls u hu
  obtain ⟨c', hc', hvc⟩ := hcls v hv
  refine isConj_iff.2 ⟨⟨c' * c⁻¹, NativeSporadic.M11.mul_mem hc' (NativeSporadic.M11.inv_mem hc)⟩,
    Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [huc, hvc]
  group

theorem m11Facts_native :
    M11Facts NativeSporadic.M11 :=
  ⟨m11_exists_elts, m11_card, at_m11_image_pair_count.2.2.2.2.1, m11_conj_inv⟩

end CFSG.EvenSporadicStandard.M11Std
