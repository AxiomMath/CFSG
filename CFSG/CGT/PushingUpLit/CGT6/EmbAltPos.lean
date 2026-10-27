module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUp Equiv

private theorem eq_top_of_index_lt_of_equiv {m : ℕ} (hm : 5 ≤ m) {K : Type*} [Group K]
    (e : K ≃* alternatingGroup (Fin m)) {B : Subgroup K} (hB : B.index < m) : B = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have : IsSimpleGroup K := e.isSimpleGroup
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B.normalCore with h | h
  · exfalso
    have h1 := B.index_normalCore_le_factorial_index
    rw [h, Subgroup.index_bot, Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at h1
    have h2 : (Nat.card (Fin m)).factorial / 2 ≤ B.index.factorial := h1
    have h3 : B.index.factorial ≤ (m - 1).factorial := Nat.factorial_le (by omega)
    have h4 : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
    have h5 : 5 * (m - 1).factorial ≤ m * (m - 1).factorial :=
      Nat.mul_le_mul_right _ hm
    have h6 : 0 < (m - 1).factorial := Nat.factorial_pos _
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h2
    omega
  · exact top_le_iff.mp (h ▸ B.normalCore_le)

private theorem pos_pair_eq_of_mem {Ω : Type*} [DecidableEq Ω] {ρ : Perm Ω}
    (hρ : ∀ y, ρ (ρ y) = y) {y z w : Ω} (hy : w ∈ ({y, ρ y} : Finset Ω))
    (hz : w ∈ ({z, ρ z} : Finset Ω)) : ({y, ρ y} : Finset Ω) = {z, ρ z} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz
  rcases hy with rfl | rfl <;> rcases hz with h | h
  · rw [h]
  · rw [h, hρ, Finset.pair_comm]
  · rw [← h, hρ, Finset.pair_comm]
  · rw [ρ.injective h]

open scoped Pointwise in
private theorem fix_of_comm_involution {m M : ℕ} (hm : 5 ≤ m) (hM : M < 2 * m) {K : Type*}
    [Group K] (e : K ≃* alternatingGroup (Fin m)) (π : K →* Perm (Fin M)) {ρ : Perm (Fin M)}
    (hρ : ρ * ρ = 1) (hc : ∀ k, ρ * π k = π k * ρ) {x : Fin M} (hx : ρ x ≠ x) (k : K) :
    π k x = x := by
  let _ : MulAction K (Fin M) := MulAction.compHom (Fin M) π
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hρρ : ∀ y, ρ (ρ y) = y := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hρ
  have hcomm : ∀ k y, π k (ρ y) = ρ (π k y) := fun k y => by
    simpa using (congrArg (fun f : Perm (Fin M) => f y) (hc k)).symm
  have hne : ∀ k, ρ (π k x) ≠ π k x := fun k h => hx (by
    rw [← hcomm] at h
    exact (π k).injective h)
  have hblock : ∀ k : K, k • ({x, ρ x} : Finset (Fin M)) = {π k x, ρ (π k x)} := fun k => by
    rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
    exact congrArg₂ _ rfl (congrArg _ (hcomm k x))
  set P₁ : Finset (Fin M) := {x, ρ x} with hP₁
  have hO : (MulAction.orbit K P₁).Finite := Set.toFinite _
  have hcard2 : ∀ P ∈ MulAction.orbit K P₁, P.card = 2 := by
    intro P hP
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hP
    rw [hblock]
    exact Finset.card_pair (hne k).symm
  have hdisj : ∀ P ∈ MulAction.orbit K P₁, ∀ Q ∈ MulAction.orbit K P₁, P ≠ Q → Disjoint P Q := by
    intro P hP Q hQ hPQ
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hP
    obtain ⟨k', rfl⟩ := MulAction.mem_orbit_iff.mp hQ
    rw [hblock, hblock] at hPQ ⊢
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact hPQ (pos_pair_eq_of_mem hρρ hw hw')
  have hcount : (MulAction.orbit K P₁).ncard * 2 ≤ M := by
    rw [Set.ncard_eq_toFinset_card _ hO]
    have h1 : (hO.toFinset.biUnion id).card = ∑ P ∈ hO.toFinset, P.card :=
      Finset.card_biUnion (fun P hP Q hQ hPQ =>
        hdisj P (hO.mem_toFinset.mp hP) Q (hO.mem_toFinset.mp hQ) hPQ)
    rw [Finset.sum_congr rfl (fun P hP => hcard2 P (hO.mem_toFinset.mp hP))] at h1
    simp only [Finset.sum_const, smul_eq_mul] at h1
    have h2 := Finset.card_le_univ (hO.toFinset.biUnion id)
    simp only [Fintype.card_fin] at h2
    omega
  have hB : (MulAction.stabilizer K P₁).index < m := by
    rw [MulAction.index_stabilizer]
    omega
  have hBtop := eq_top_of_index_lt_of_equiv hm e hB
  have hstab : ∀ k : K, k • P₁ = P₁ := fun k => by
    have : k ∈ MulAction.stabilizer K P₁ := by rw [hBtop]; exact Subgroup.mem_top k
    exact this
  have horb : MulAction.orbit K x ⊆ ↑P₁ := by
    rintro _ ⟨k, rfl⟩
    have : k • x ∈ k • P₁ := Finset.smul_mem_smul_finset (by simp [P₁])
    rw [hstab k] at this
    exact this
  have hx2 : (MulAction.orbit K x).ncard ≤ 2 :=
    calc (MulAction.orbit K x).ncard ≤ (↑P₁ : Set (Fin M)).ncard :=
          Set.ncard_le_ncard horb (Finset.finite_toSet _)
      _ = P₁.card := Set.ncard_coe_finset _
      _ ≤ 2 := Finset.card_le_two
  have hC : (MulAction.stabilizer K x).index < m := by
    rw [MulAction.index_stabilizer]
    omega
  have hCtop := eq_top_of_index_lt_of_equiv hm e hC
  have : k ∈ MulAction.stabilizer K x := by rw [hCtop]; exact Subgroup.mem_top k
  exact this

private theorem pos_card_four {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]

private theorem eq_swap_mul_swap_of_apply {M : ℕ} {π : Perm (Fin M)} {a b c d : Fin M}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : π.support ⊆ {a, b, c, d}) (h1 : π a = b) (h2 : π b = a) (h3 : π c = d)
    (h4 : π d = c) : π = swap a b * swap c d := by
  refine Equiv.ext fun y => ?_
  by_cases hy : y ∈ ({a, b, c, d} : Finset (Fin M))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h <;> subst h
    · simp [h1, Equiv.swap_apply_of_ne_of_ne, hac, had]
    · simp [h2, Equiv.swap_apply_of_ne_of_ne, hbc, hbd]
    · simp [h3, Equiv.swap_apply_of_ne_of_ne, had.symm, hbd.symm]
    · simp [h4, Equiv.swap_apply_of_ne_of_ne, hac.symm, hbc.symm]
  · have h : π y = y := Equiv.Perm.notMem_support.mp (fun h => hy (hs h))
    rw [h]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    simp [Equiv.swap_apply_of_ne_of_ne, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

private theorem klein_case_one {M : ℕ} {σ τ : Perm (Fin M)} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hστ : σ * τ = τ * σ) (hτ1 : τ ≠ 1) {T : Finset (Fin M)}
    (hT : σ.support ∪ τ.support ⊆ T) (hcard : T.card ≤ 4) {a : Fin M} (ha : σ a ≠ a)
    (hτa : τ a = a) :
    ∃ a b c d : Fin M, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ T = {a, b, c, d} ∧
      (σ = swap a b * swap c d ∨ τ = swap a b * swap c d ∨ σ * τ = swap a b * swap c d) := by
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hσ
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hτ
  have hcomm : ∀ y, σ (τ y) = τ (σ y) := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hστ
  obtain ⟨c, hc⟩ : ∃ c, τ c ≠ c := by
    by_contra h
    exact hτ1 (Equiv.ext fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  have hτb : τ (σ a) = σ a := by rw [← hcomm, hτa]
  have hσb : σ (σ a) = a := hσσ a
  have hab : a ≠ σ a := fun h => ha h.symm
  have hca : c ≠ a := fun h => hc (by rw [h, hτa])
  have hcb : c ≠ σ a := fun h => hc (by rw [h, hτb])
  have hda : τ c ≠ a := fun h => hca (by rw [← hττ c, h, hτa])
  have hdb : τ c ≠ σ a := fun h => hcb (by rw [← hττ c, h, hτb])
  have hcd : c ≠ τ c := fun h => hc h.symm
  have hTeq : T = {a, σ a, c, τ c} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact hT (Finset.mem_union_left _ (Equiv.Perm.mem_support.mpr ha))
      · exact hT (Finset.mem_union_left _ (Equiv.Perm.mem_support.mpr (by rw [hσb]; exact hab)))
      · exact hT (Finset.mem_union_right _ (Equiv.Perm.mem_support.mpr hc))
      · exact hT (Finset.mem_union_right _ (Equiv.Perm.mem_support.mpr (by rw [hττ]; exact hcd)))
    · rw [pos_card_four hab hca.symm hda.symm hcb.symm hdb.symm hcd]
      exact hcard
  have hσc : σ c = c ∨ σ c = τ c := by
    by_cases h : σ c = c
    · exact Or.inl h
    · right
      have hmem : σ c ∈ T := hT (Finset.mem_union_left _ (Equiv.Perm.mem_support.mpr
        (by rw [hσσ]; exact fun h' => h h'.symm)))
      rw [hTeq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h' | h' | h' | h'
      · exact absurd (by rw [← hσσ c, h']) hcb
      · exact absurd (σ.injective h') hca
      · exact absurd h' h
      · exact h'
  have hsupp : (σ * τ).support ⊆ {a, σ a, c, τ c} :=
    hTeq ▸ (Equiv.Perm.support_mul_le σ τ).trans hT
  refine ⟨a, σ a, c, τ c, hab, hca.symm, hda.symm, hcb.symm, hdb.symm, hcd, hTeq, ?_⟩
  rcases hσc with h | h
  · refine Or.inr (Or.inr (eq_swap_mul_swap_of_apply hab hca.symm hda.symm hcb.symm hdb.symm hcd
      hsupp ?_ ?_ ?_ ?_))
    · simp [hτa]
    · simp [hτb, hσb]
    · rw [Perm.mul_apply, hcomm, h]
    · rw [Perm.mul_apply, hττ, h]
  · refine Or.inl (eq_swap_mul_swap_of_apply hab hca.symm hda.symm hcb.symm hdb.symm hcd
      (hTeq ▸ (Finset.subset_union_left.trans hT)) rfl hσb h ?_)
    rw [← h, hσσ]

private theorem klein_four_support {M : ℕ} {σ τ : Perm (Fin M)} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hne : σ ≠ τ)
    {T : Finset (Fin M)} (hT : σ.support ∪ τ.support ⊆ T) (hcard : T.card ≤ 4) :
    ∃ a b c d : Fin M, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ T = {a, b, c, d} ∧
      (σ = swap a b * swap c d ∨ τ = swap a b * swap c d ∨ σ * τ = swap a b * swap c d) := by
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hσ
  have hττ : ∀ y, τ (τ y) = y := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hτ
  have hcomm : ∀ y, σ (τ y) = τ (σ y) := fun y => by
    simpa using congrArg (fun f : Perm (Fin M) => f y) hστ
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    exact hσ1 (Equiv.ext fun y => not_not.mp fun hy => h ⟨y, hy⟩)
  by_cases hτa : τ a = a
  · exact klein_case_one hσ hτ hστ hτ1 hT hcard ha hτa
  by_cases hτab : τ a = σ a
  · have hρρ : σ * τ * (σ * τ) = 1 := by
      calc σ * τ * (σ * τ) = σ * (τ * σ) * τ := by simp only [mul_assoc]
        _ = σ * (σ * τ) * τ := by rw [hστ]
        _ = (σ * σ) * (τ * τ) := by simp only [mul_assoc]
        _ = 1 := by rw [hσ, hτ, one_mul]
    have hρσ : σ * (σ * τ) = σ * τ * σ := by rw [mul_assoc, ← hστ]
    have hρ1 : σ * τ ≠ 1 := fun h => hne (by
      calc σ = σ * (τ * τ) := by rw [hτ, mul_one]
        _ = σ * τ * τ := (mul_assoc _ _ _).symm
        _ = τ := by rw [h, one_mul])
    have hρa : (σ * τ) a = a := by rw [Perm.mul_apply, hτab, hσσ]
    have hT' : σ.support ∪ (σ * τ).support ⊆ T :=
      Finset.union_subset (Finset.subset_union_left.trans hT)
        ((Equiv.Perm.support_mul_le σ τ).trans hT)
    obtain ⟨a', b, c, d, h1, h2, h3, h4, h5, h6, hTe, hdis⟩ :=
      klein_case_one hσ hρρ hρσ hρ1 hT' hcard ha hρa
    refine ⟨a', b, c, d, h1, h2, h3, h4, h5, h6, hTe, ?_⟩
    have hστρ : σ * (σ * τ) = τ := by rw [← mul_assoc, hσ, one_mul]
    rcases hdis with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (hστρ ▸ h))
  · have hab : a ≠ σ a := fun h => ha h.symm
    have hac : a ≠ τ a := fun h => hτa h.symm
    have hbc : σ a ≠ τ a := fun h => hτab h.symm
    have had : a ≠ σ (τ a) := fun h => hτab (by rw [← hσσ (τ a), ← h])
    have hbd : σ a ≠ σ (τ a) := fun h => hτa (σ.injective h).symm
    have hcd : τ a ≠ σ (τ a) := fun h => ha (τ.injective (by rw [← hcomm, ← h]))
    have hTeq : T = {a, σ a, τ a, σ (τ a)} := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · exact hT (Finset.mem_union_left _ (Equiv.Perm.mem_support.mpr ha))
        · exact hT (Finset.mem_union_left _
            (Equiv.Perm.mem_support.mpr (by rw [hσσ]; exact hab)))
        · exact hT (Finset.mem_union_right _
            (Equiv.Perm.mem_support.mpr (by rw [hττ]; exact hac)))
        · exact hT (Finset.mem_union_left _
            (Equiv.Perm.mem_support.mpr (by rw [hσσ]; exact hcd)))
      · rw [pos_card_four hab hac had hbc hbd hcd]
        exact hcard
    refine ⟨a, σ a, τ a, σ (τ a), hab, hac, had, hbc, hbd, hcd, hTeq, Or.inl ?_⟩
    exact eq_swap_mul_swap_of_apply hab hac had hbc hbd hcd
      (hTeq ▸ (Finset.subset_union_left.trans hT)) rfl (hσσ a) rfl (hσσ (τ a))

theorem exists_altStabilizer_of_commuting_involutions {m : ℕ} (hm : 5 ≤ m)
    {H : Subgroup (alternatingGroup (Fin (m + 4)))}
    (hH : Nonempty (↥H ≃* alternatingGroup (Fin m))) {σ τ : Perm (Fin (m + 4))}
    (hσ : σ * σ = 1) (hτ : τ * τ = 1) (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hne : σ ≠ τ) (hσH : ∀ h ∈ H, σ * (h : Perm (Fin (m + 4))) = (h : Perm (Fin (m + 4))) * σ)
    (hτH : ∀ h ∈ H, τ * (h : Perm (Fin (m + 4))) = (h : Perm (Fin (m + 4))) * τ) :
    ∃ a b c d : Fin (m + 4), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      H = altStabilizer (m + 4) {a, b, c, d} ∧
      (σ = swap a b * swap c d ∨ τ = swap a b * swap c d ∨ σ * τ = swap a b * swap c d) := by
  obtain ⟨e⟩ := hH
  let π : ↥H →* Perm (Fin (m + 4)) := (alternatingGroup (Fin (m + 4))).subtype.comp H.subtype
  have hM : m + 4 < 2 * m := by omega
  have hfixσ : ∀ k : ↥H, ∀ y ∈ σ.support, π k y = y := fun k y hy =>
    fix_of_comm_involution hm hM e π hσ (fun k => hσH k.1 k.2) (Equiv.Perm.mem_support.mp hy) k
  have hfixτ : ∀ k : ↥H, ∀ y ∈ τ.support, π k y = y := fun k y hy =>
    fix_of_comm_involution hm hM e π hτ (fun k => hτH k.1 k.2) (Equiv.Perm.mem_support.mp hy) k
  have hle : ∀ F : Finset (Fin (m + 4)), F ⊆ σ.support ∪ τ.support →
      H ≤ altStabilizer (m + 4) F := fun F hF h hh => by
    rw [mem_altStabilizer_iff]
    intro y hy
    rcases Finset.mem_union.mp (hF hy) with h' | h'
    · exact hfixσ ⟨h, hh⟩ y h'
    · exact hfixτ ⟨h, hh⟩ y h'
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcardH : Nat.card H = m.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp
  have hS4 : (σ.support ∪ τ.support).card ≤ 4 := by
    by_contra hlt
    obtain ⟨S', hS'S, hS'card⟩ := Finset.exists_subset_card_eq
      (show 5 ≤ (σ.support ∪ τ.support).card by omega)
    have h1 := Subgroup.card_le_of_le (hle S' hS'S)
    rw [hcardH, card_altStabilizer S' (by omega), hS'card,
      show m + 4 - 5 = m - 1 by omega] at h1
    have h4 : m * (m - 1).factorial = m.factorial := Nat.mul_factorial_pred (by omega)
    have h5 : 5 * (m - 1).factorial ≤ m * (m - 1).factorial := Nat.mul_le_mul_right _ hm
    have h6 : 0 < (m - 1).factorial := Nat.factorial_pos _
    omega
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hSe, hdis⟩ :=
    klein_four_support hσ hτ hστ hσ1 hτ1 hne (subset_refl _) hS4
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ?_, hdis⟩
  have h4 := pos_card_four hab hac had hbc hbd hcd
  refine Subgroup.eq_of_le_of_card_ge (hle _ hSe.symm.subset) ?_
  rw [hcardH, card_altStabilizer _ (by omega), h4]
  simp

end CFSG.CGT.PushingUpLit.CGT6
