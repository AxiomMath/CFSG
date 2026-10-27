module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLRoots

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Foote.Proving
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def ExcTLSimplyLaced (τ : Tag) : Prop := τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8

theorem excTL_iform_neg_left {τ : Tag} (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]
  ring

theorem excTL_iform_neg_right {τ : Tag} (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

theorem excTL_norm_two {τ : Tag} (hτ : ExcTLSimplyLaced τ) {v : Fin τ.rank → ℤ}
    (hv : IsRoot τ v) : iform v v = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hv
  rw [hj]
  have : τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]
  rw [this]
  norm_num

theorem excTL_norm_cases {τ : Tag} (hτ : τ ≠ .G2) {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    iform v v = 2 ∨ iform v v = 4 :=
  iform_self_cases (excTL_noG2 hτ) hv

theorem excTL_two_facts (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    (∀ x : K, x = 0 ∨ x = 1) ∧ (1 : K) + 1 = 0 ∧ (-1 : K) = 1 := by
  have hall : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    have : Fintype K := Fintype.ofFinite K
    have h2 : 2 < Fintype.card K := Fintype.two_lt_card_iff.2
      ⟨0, 1, x, zero_ne_one, Ne.symm hx.1, Ne.symm hx.2⟩
    rw [← Nat.card_eq_fintype_card, hK] at h2
    omega
  have h11 : (1 : K) + 1 = 0 := by
    rcases hall (1 + 1) with h | h
    · exact h
    · exact absurd (add_eq_right.1 h) one_ne_zero
  exact ⟨hall, h11, neg_eq_of_add_eq_zero_right h11⟩

theorem excTL_two_cast (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) {e : ℤ}
    (he : e = 1 ∨ e = -1) : (e : K) = 1 := by
  obtain ⟨-, -, hneg⟩ := excTL_two_facts K hK
  rcases he with rfl | rfl <;> simp [hneg]

section Norm

variable {τ : Tag}

theorem excTL_h_cases {h : ℤ} {v : Fin τ.rank → ℤ} (hτ : τ ≠ .G2) (hv : IsRoot τ v)
    (nv : iform v v = 2 * h) : h = 1 ∨ h = 2 := by
  rcases excTL_norm_cases hτ hv with h2 | h2 <;> omega

theorem excTL_a2_of_iform (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h)
    (hab : iform α β = -h) :
    IsRoot τ (α + β) ∧ ¬ IsRoot τ (α - β) ∧ ¬ IsRoot τ ((2 : ℤ) • α + β) ∧
      ¬ IsRoot τ (α + (2 : ℤ) • β) := by
  have hh := excTL_h_cases hτ hα nα
  have hβα : iform β α = -h := by rw [iform_comm]; exact hab
  have hne' : α ≠ -β := fun e => by
    rw [e, excTL_iform_neg_left, nβ] at hab
    omega
  refine ⟨isRoot_add_of_iform_neg hα hβ hne' (by omega), fun hr => ?_, fun hr => ?_,
    fun hr => ?_⟩
  · have := excTL_norm_cases hτ hr
    simp only [iform_sub_left, iform_sub_right, nα, nβ, hab, hβα] at this
    omega
  · have := excTL_norm_cases hτ hr
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, nα, nβ, hab,
      hβα] at this
    omega
  · have := excTL_norm_cases hτ hr
    simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, nα, nβ, hab,
      hβα] at this
    omega

theorem excTL_no_root_of_iform_pos (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ}
    (hα : IsRoot τ α) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h)
    (hab : iform α β = h) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsRoot τ (a • α + b • β) := by
  intro hr
  have h2 := excTL_norm_cases hτ hr
  have hh := excTL_h_cases hτ hα nα
  rw [iform_nsmul_add_nsmul, nα, nβ, hab] at h2
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hh1 : (1 : ℤ) ≤ h := by omega
  have e1 : (1 : ℤ) ≤ (a : ℤ) ^ 2 := by nlinarith
  have e2 : (1 : ℤ) ≤ (b : ℤ) ^ 2 := by nlinarith
  have e3 : (1 : ℤ) ≤ (a : ℤ) * b := by nlinarith
  rcases h2 with h2 | h2 <;> nlinarith [mul_le_mul_of_nonneg_left e1 (by omega : (0 : ℤ) ≤ h),
    mul_le_mul_of_nonneg_left e2 (by omega : (0 : ℤ) ≤ h),
    mul_le_mul_of_nonneg_left e3 (by omega : (0 : ℤ) ≤ h)]

theorem excTL_commute_pinnedX_pos (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h)
    (hab : iform α β = h) {K : Type} [Field K] (s t : K) :
    Commute (pinnedX τ K α s) (pinnedX τ K β t) := by
  have hh := excTL_h_cases hτ hα nα
  have hne : α ≠ β := fun e => by
    subst e
    omega
  have hne' : α ≠ -β := fun e => by
    rw [e, excTL_iform_neg_left, nβ] at hab
    omega
  exact commute_of_forall_not_isRoot hα hβ hne hne'
    (fun a b ha hb => excTL_no_root_of_iform_pos hτ hα nα nβ hab ha hb) K _
    (mem_rootSubgroup.2 ⟨s, rfl⟩) _ (mem_rootSubgroup.2 ⟨t, rfl⟩)

theorem excTL_two_comm_pinnedX (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {α β γ : Fin τ.rank → ℤ} {h : ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h)
    (hab : iform α β = -h) (hsum : α + β = γ) (s t : K) :
    ⁅pinnedX τ K α s, pinnedX τ K β t⁆ = pinnedX τ K γ (s * t) := by
  subst hsum
  obtain ⟨hsr, h1, h2, h3⟩ := excTL_a2_of_iform hτ hα hβ nα nβ hab
  obtain ⟨e, he, hcomm⟩ := excTL_a2_commutator hτ hα hβ hsr h1 h2 h3
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, hcomm K s t, excTL_two_cast K hK he]
  simp

theorem excTL_two_commute_orth (hτ : τ ≠ .G2) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {α β : Fin τ.rank → ℤ} {h : ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h) (hab : iform α β = 0) (s t : K) :
    Commute (pinnedX τ K α s) (pinnedX τ K β t) := by
  have hh := excTL_h_cases hτ hα nα
  have hne : α ≠ β := fun e => by
    subst e
    omega
  have hne' : α ≠ -β := fun e => by
    rw [e, excTL_iform_neg_left, nβ] at hab
    omega
  have hno : ∀ a b : ℕ, 0 < a → 0 < b → ¬ (a = 1 ∧ b = 1) → ¬ IsRoot τ (a • α + b • β) := by
    intro a b ha hb hab11 hr
    have h2 := excTL_norm_cases hτ hr
    rw [iform_nsmul_add_nsmul, nα, nβ, hab] at h2
    have h5 : (5 : ℤ) ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
      by_cases ha2 : 2 ≤ a
      · have : (4 : ℤ) ≤ (a : ℤ) ^ 2 := by
          have : (2 : ℤ) ≤ a := by exact_mod_cast ha2
          nlinarith
        have : (1 : ℤ) ≤ (b : ℤ) ^ 2 := by
          have : (1 : ℤ) ≤ b := by exact_mod_cast hb
          nlinarith
        omega
      · have ha1 : a = 1 := by omega
        have hb2 : 2 ≤ b := by
          by_contra hb2
          exact hab11 ⟨ha1, by omega⟩
        have : (4 : ℤ) ≤ (b : ℤ) ^ 2 := by
          have : (2 : ℤ) ≤ b := by exact_mod_cast hb2
          nlinarith
        subst ha1
        simp only [Nat.cast_one]
        omega
    have hh1 : (1 : ℤ) ≤ h := by omega
    rcases h2 with h2 | h2 <;> nlinarith
  by_cases hsr : IsRoot τ (α + β)
  swap
  · refine Commute.symm ?_ |>.symm
    exact commute_of_forall_not_isRoot hα hβ hne hne'
      (fun a b ha hb hr => by
        by_cases hab11 : a = 1 ∧ b = 1
        · obtain ⟨rfl, rfl⟩ := hab11
          exact hsr (by simpa using hr)
        · exact hno a b ha hb hab11 hr) K _ (mem_rootSubgroup.2 ⟨s, rfl⟩) _
      (mem_rootSubgroup.2 ⟨t, rfl⟩)
  · have hn : iform (α + β) (α + β) = 4 * h := by
      simp only [iform_add_left, iform_add_right, nα, nβ, hab, iform_comm β α]
      ring
    cases τ
    · exact absurd rfl hτ
    ·
      have hr' : IsRoot Tag.F4 (β - α) := by
        have hc : corootPair α (α + β) = 2 := by
          have h1 := corootPair_mul hα (α + β)
          rw [iform_add_right, nα, hab] at h1
          have h0 : (2 * h : ℤ) ≠ 0 := by omega
          exact mul_right_cancel₀ h0 (by linarith)
        have := IsRoot.smul hsr (rootReflection α)
        rw [rootReflection_smul hα, hc] at this
        have e : α + β - (2 : ℤ) • α = β - α := by rw [two_smul]; abel
        rwa [e] at this
      have hno' : ∀ p ∈ commCandidates, p ≠ (1, 1) → ¬ IsRoot Tag.F4 (p.1 • α + p.2 • β) := by
        intro p hp hp1 hr
        obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := mem_commCandidates.1 hp
        exact hno p.1 p.2 (by omega) (by omega) (fun hh => hp1 (Prod.ext hh.1 hh.2)) hr
      have hlist := commPairs_eq_single_of_string_one hsr hno'
      obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hα hβ hne hne'
      have h11 : ((1, 1) : ℕ × ℕ) ∈ commPairs Tag.F4 α β := by rw [hlist]; simp
      have hC11 := hC (1, 1) h11
      simp only [hr', and_self, ite_true] at hC11
      have h2K : (2 : K) = 0 := by
        rw [← one_add_one_eq_two]
        exact (excTL_two_facts K hK).2.1
      have hCK : ((C (1, 1) : ℤ) : K) = 0 := by
        rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.1 hC11 with h2 | h2 <;> rw [h2] <;>
          simp [h2K]
      have h4 := hF K s t
      rw [hlist] at h4
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
        pow_one, hCK, zero_mul, pinnedX_zero] at h4
      have h5 : ⁅pinnedX Tag.F4 K α s, pinnedX Tag.F4 K β t⁆ = 1 := by
        rw [commutatorElement_def, pinnedX_neg, pinnedX_neg]
        exact h4
      exact commutatorElement_eq_one_iff_mul_comm.1 h5
    all_goals
      exfalso
      have := excTL_norm_two (by unfold ExcTLSimplyLaced; decide) hsr
      omega

theorem excTL_iform_bound {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    iform α β ^ 2 < iform α α * iform β β ∧ iform α α ∣ 2 * iform α β ∧
      iform β β ∣ 2 * iform α β :=
  ⟨iform_sq_lt hα hβ hne hne', iform_dvd_of_isRoot hα β, by
    rw [iform_comm α β]
    exact iform_dvd_of_isRoot hβ α⟩

theorem excTL_iform_same (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (nα : iform α α = 2 * h) (nβ : iform β β = 2 * h) (hne : α ≠ β)
    (hne' : α ≠ -β) : iform α β = -h ∨ iform α β = 0 ∨ iform α β = h := by
  obtain ⟨hsq, hd, -⟩ := excTL_iform_bound hα hβ hne hne'
  rw [nα, nβ] at hsq
  rw [nα] at hd
  rcases excTL_h_cases hτ hα nα with rfl | rfl
  · have h1 : -2 < iform α β ∧ iform α β < 2 := by constructor <;> nlinarith
    omega
  · have h1 : -4 < iform α β ∧ iform α β < 4 := by constructor <;> nlinarith
    omega

theorem excTL_iform_mixed (hτ : τ ≠ .G2) {α β : Fin τ.rank → ℤ} {h : ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (nα : iform α α = 2 * h) (hk : iform β β ≠ 2 * h) (hne : α ≠ β)
    (hne' : α ≠ -β) : iform α β = -2 ∨ iform α β = 0 ∨ iform α β = 2 := by
  obtain ⟨hsq, hd, hd'⟩ := excTL_iform_bound hα hβ hne hne'
  rw [nα] at hsq hd
  have hh := excTL_h_cases hτ hα nα
  have hk2 := excTL_norm_cases hτ hβ
  have hs : -3 < iform α β ∧ iform α β < 3 := by
    rcases hh with rfl | rfl <;> rcases hk2 with h2 | h2 <;> rw [h2] at hsq hd' <;>
      first | omega | (constructor <;> nlinarith)
  rcases hh with rfl | rfl <;> rcases hk2 with h2 | h2 <;> rw [h2] at hd' hk <;> omega

@[expose] def excTLHex (γ δ : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {γ, δ, γ + δ, -γ, -δ, -(γ + δ)}

theorem excTLHex_neg {γ δ x : Fin τ.rank → ℤ} (hx : x ∈ excTLHex γ δ) : -x ∈ excTLHex γ δ := by
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem excTLHex_norm {γ δ : Fin τ.rank → ℤ} {h : ℤ} (nγ : iform γ γ = 2 * h)
    (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) {x : Fin τ.rank → ℤ}
    (hx : x ∈ excTLHex γ δ) : iform x x = 2 * h := by
  have hδγ : iform δ γ = -h := by rw [iform_comm]; exact hγδ
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with e | e | e | e | e | e <;> rw [e]
  · exact nγ
  · exact nδ
  · simp only [iform_add_left, iform_add_right, nγ, nδ, hγδ, hδγ]; omega
  · simp only [excTL_iform_neg_left, excTL_iform_neg_right, nγ]; omega
  · simp only [excTL_iform_neg_left, excTL_iform_neg_right, nδ]; omega
  · simp only [excTL_iform_neg_left, excTL_iform_neg_right, iform_add_left, iform_add_right, nγ,
      nδ, hγδ, hδγ]; omega

theorem excTLHex_nbrs {γ δ : Fin τ.rank → ℤ} {h : ℤ} (nγ : iform γ γ = 2 * h)
    (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) {α : Fin τ.rank → ℤ}
    (hα : α ∈ excTLHex γ δ) :
    ∃ α₁ ∈ excTLHex γ δ, ∃ α₂ ∈ excTLHex γ δ, iform α α₁ = -h ∧ iform α α₂ = -h ∧
      α₁ + α₂ = -α := by
  have hδγ : iform δ γ = -h := by rw [iform_comm]; exact hγδ
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with e | e | e | e | e | e <;> rw [e]
  · exact ⟨δ, by simp [excTLHex], -(γ + δ), by simp [excTLHex], hγδ,
      by simp only [excTL_iform_neg_right, iform_add_right, nγ, hγδ]; omega, by abel⟩
  · exact ⟨γ, by simp [excTLHex], -(γ + δ), by simp [excTLHex], hδγ,
      by simp only [excTL_iform_neg_right, iform_add_right, hδγ, nδ]; omega, by abel⟩
  · exact ⟨-γ, by simp [excTLHex], -δ, by simp [excTLHex],
      by simp only [excTL_iform_neg_right, iform_add_left, nγ, hδγ]; omega,
      by simp only [excTL_iform_neg_right, iform_add_left, hγδ, nδ]; omega, by abel⟩
  · exact ⟨-δ, by simp [excTLHex], γ + δ, by simp [excTLHex],
      by simp only [excTL_iform_neg_left, excTL_iform_neg_right, hγδ]; omega,
      by simp only [excTL_iform_neg_left, iform_add_right, nγ, hγδ]; omega, by abel⟩
  · exact ⟨-γ, by simp [excTLHex], γ + δ, by simp [excTLHex],
      by simp only [excTL_iform_neg_left, excTL_iform_neg_right, hδγ]; omega,
      by simp only [excTL_iform_neg_left, iform_add_right, hδγ, nδ]; omega, by abel⟩
  · exact ⟨γ, by simp [excTLHex], δ, by simp [excTLHex],
      by simp only [excTL_iform_neg_left, iform_add_left, nγ, hδγ]; omega,
      by simp only [excTL_iform_neg_left, iform_add_left, hγδ, nδ]; omega, by abel⟩

theorem excTLHex_iform_ne_zero {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hh : 0 < h)
    (nγ : iform γ γ = 2 * h) (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h)
    {x α : Fin τ.rank → ℤ} (hx : x ∈ excTLHex γ δ) (hα : α ∈ excTLHex γ δ) :
    iform x α ≠ 0 := by
  have hδγ : iform δ γ = -h := by rw [iform_comm]; exact hγδ
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hα
  rcases hx with e | e | e | e | e | e <;> rcases hα with e' | e' | e' | e' | e' | e' <;>
    rw [e, e'] <;>
    simp only [excTL_iform_neg_left, excTL_iform_neg_right, iform_add_left, iform_add_right, nγ,
      nδ, hγδ, hδγ] <;> omega

theorem excTL_iform_neg_neg (x y : Fin τ.rank → ℤ) : iform (-x) (-y) = iform x y := by
  rw [excTL_iform_neg_left, excTL_iform_neg_right, neg_neg]

theorem excTLHex_subset (hτ : τ ≠ .G2) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : γ ∈ Ψ) (hδ : δ ∈ Ψ) (nγ : iform γ γ = 2 * h)
    (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) : excTLHex γ δ ⊆ Ψ := by
  have hsumr := (excTL_a2_of_iform hτ (hΨ.isRoot γ hγ) (hΨ.isRoot δ hδ) nγ nδ hγδ).1
  have hsum : γ + δ ∈ Ψ := hΨ.add_mem γ hγ δ hδ hsumr
  intro x hx
  simp only [excTLHex, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with e | e | e | e | e | e <;> rw [e]
  exacts [hγ, hδ, hsum, hΨ.neg_mem _ hγ, hΨ.neg_mem _ hδ, hΨ.neg_mem _ hsum]

theorem excTL_chain_same (hτ : τ ≠ .G2) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : γ ∈ Ψ) (hδ : δ ∈ Ψ) (nγ : iform γ γ = 2 * h)
    (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) {α β : Fin τ.rank → ℤ}
    (hαH : α ∈ excTLHex γ δ) (hβΨ : β ∈ Ψ) (hβH : β ∉ excTLHex γ δ)
    (nβ : iform β β = 2 * h) (hne0 : iform α β ≠ 0) :
    ∃ a₁ ∈ Ψ, ∃ a₂ ∈ Ψ, ∃ a₃ ∈ Ψ, iform a₁ a₁ = 2 * h ∧ iform a₂ a₂ = 2 * h ∧
      iform a₃ a₃ = 2 * h ∧ iform a₁ a₂ = -h ∧ iform a₂ a₃ = -h ∧ iform a₁ a₃ = 0 := by
  have hhpos : 0 < h := by
    rcases excTL_h_cases hτ (hΨ.isRoot γ hγ) nγ with e | e <;> omega
  have hHΨ := excTLHex_subset hτ hΨ hγ hδ nγ nδ hγδ
  have hαΨ : α ∈ Ψ := hHΨ hαH
  have hαr := hΨ.isRoot α hαΨ
  have hβr := hΨ.isRoot β hβΨ
  have nα := excTLHex_norm nγ nδ hγδ hαH
  have hne1 : α ≠ β := fun e => hβH (e ▸ hαH)
  have hne2 : α ≠ -β := fun e => hβH (by
    have := excTLHex_neg hαH
    rwa [e, neg_neg] at this)
  have hval := excTL_iform_same hτ hαr hβr nα nβ hne1 hne2
  obtain ⟨β', hβ'Ψ, hβ'H, hαβ', nβ'⟩ : ∃ β' ∈ Ψ, β' ∉ excTLHex γ δ ∧ iform α β' = -h ∧
      iform β' β' = 2 * h := by
    have : iform α β = -h ∨ iform α β = h := by omega
    rcases this with h1 | h1
    · exact ⟨β, hβΨ, hβH, h1, nβ⟩
    · refine ⟨-β, hΨ.neg_mem _ hβΨ, fun hneg => hβH ?_, by rw [excTL_iform_neg_right, h1],
        by rw [excTL_iform_neg_neg, nβ]⟩
      have := excTLHex_neg hneg
      rwa [neg_neg] at this
  obtain ⟨α₁, hα₁H, α₂, hα₂H, h1, h2, hsum12⟩ := excTLHex_nbrs nγ nδ hγδ hαH
  have hβ'r := hΨ.isRoot β' hβ'Ψ
  have bound : ∀ x ∈ excTLHex γ δ, -h ≤ iform x β' ∧ iform x β' ≤ h := fun x hx => by
    have := excTL_iform_same hτ (hΨ.isRoot x (hHΨ hx)) hβ'r (excTLHex_norm nγ nδ hγδ hx) nβ'
      (fun e => hβ'H (e ▸ hx)) (fun e => hβ'H (by
        have := excTLHex_neg hx
        rwa [e, neg_neg] at this))
    omega
  obtain ⟨b1, b1'⟩ := bound α₁ hα₁H
  obtain ⟨b2, b2'⟩ := bound α₂ hα₂H
  have hsumform : iform α₁ β' + iform α₂ β' = h := by
    rw [← iform_add_left, hsum12, excTL_iform_neg_left, hαβ']
    ring
  have hval1 := excTL_iform_same hτ (hΨ.isRoot α₁ (hHΨ hα₁H)) hβ'r (excTLHex_norm nγ nδ hγδ hα₁H)
    nβ' (fun e => hβ'H (e ▸ hα₁H)) (fun e => hβ'H (by
      have := excTLHex_neg hα₁H
      rwa [e, neg_neg] at this))
  have hval2 := excTL_iform_same hτ (hΨ.isRoot α₂ (hHΨ hα₂H)) hβ'r (excTLHex_norm nγ nδ hγδ hα₂H)
    nβ' (fun e => hβ'H (e ▸ hα₂H)) (fun e => hβ'H (by
      have := excTLHex_neg hα₂H
      rwa [e, neg_neg] at this))
  have hcases : iform α₁ β' = 0 ∨ iform α₂ β' = 0 := by omega
  rcases hcases with h0 | h0
  · exact ⟨α₁, hHΨ hα₁H, α, hαΨ, β', hβ'Ψ, excTLHex_norm nγ nδ hγδ hα₁H, nα, nβ',
      by rw [iform_comm]; exact h1, hαβ', h0⟩
  · exact ⟨α₂, hHΨ hα₂H, α, hαΨ, β', hβ'Ψ, excTLHex_norm nγ nδ hγδ hα₂H, nα, nβ',
      by rw [iform_comm]; exact h2, hαβ', h0⟩

theorem excTL_mixed_arith (h k s c s₁ : ℤ) (hh : h = 1 ∨ h = 2) (hk : k = 2 ∨ k = 4)
    (hne : k ≠ 2 * h) (hs : s = -2 ∨ s = 2) (hcm : c * k = 2 * s)
    (hs₁ : s₁ = -2 ∨ s₁ = 0 ∨ s₁ = 2) : 2 * h - c * s = 0 ∧ -h - c * s₁ ≠ 0 := by
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl <;> try omega
  all_goals
    rcases hs with rfl | rfl <;> rcases hs₁ with rfl | rfl | rfl <;> constructor <;> omega

theorem excTL_chain_mixed (hτ : τ ≠ .G2) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : γ ∈ Ψ) (hδ : δ ∈ Ψ) (nγ : iform γ γ = 2 * h)
    (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) {α β : Fin τ.rank → ℤ}
    (hαH : α ∈ excTLHex γ δ) (hβΨ : β ∈ Ψ) (hβH : β ∉ excTLHex γ δ)
    (hk : iform β β ≠ 2 * h) (hne0 : iform α β ≠ 0) :
    ∃ α' ∈ excTLHex γ δ, ∃ β' ∈ Ψ, β' ∉ excTLHex γ δ ∧ iform β' β' = 2 * h ∧
      iform α' β' ≠ 0 := by
  have hh := excTL_h_cases hτ (hΨ.isRoot γ hγ) nγ
  have hhpos : 0 < h := by omega
  have hHΨ := excTLHex_subset hτ hΨ hγ hδ nγ nδ hγδ
  have hαΨ : α ∈ Ψ := hHΨ hαH
  have hαr := hΨ.isRoot α hαΨ
  have hβr := hΨ.isRoot β hβΨ
  have nα := excTLHex_norm nγ nδ hγδ hαH
  have hne1 : α ≠ β := fun e => hβH (e ▸ hαH)
  have hne2 : α ≠ -β := fun e => hβH (by
    have := excTLHex_neg hαH
    rwa [e, neg_neg] at this)
  have hval := excTL_iform_mixed hτ hαr hβr nα hk hne1 hne2
  have hs : iform α β = -2 ∨ iform α β = 2 := by omega
  have hcm : corootPair β α * iform β β = 2 * iform α β := by
    rw [corootPair_mul hβr α, iform_comm β α]
  have hβ'eq : rootReflection β • α = α - corootPair β α • β := rootReflection_smul hβr α
  have hβ'Ψ : rootReflection β • α ∈ Ψ := hΨ.reflection_mem α hαΨ β hβΨ
  have nβ' : iform (rootReflection β • α) (rootReflection β • α) = 2 * h := by
    rw [iform_smul, nα]
  obtain ⟨α₁, hα₁H, -, -, h1, -, -⟩ := excTLHex_nbrs nγ nδ hγδ hαH
  have hα₁r := hΨ.isRoot α₁ (hHΨ hα₁H)
  have hval₁ := excTL_iform_mixed hτ hα₁r hβr (excTLHex_norm nγ nδ hγδ hα₁H) hk
    (fun e => hβH (e ▸ hα₁H)) (fun e => hβH (by
      have := excTLHex_neg hα₁H
      rwa [e, neg_neg] at this))
  obtain ⟨F1, F2⟩ := excTL_mixed_arith h (iform β β) (iform α β) (corootPair β α)
    (iform α₁ β) hh (excTL_norm_cases hτ hβr) hk hs hcm hval₁
  have hβ'α : iform (rootReflection β • α) α = 0 := by
    rw [hβ'eq, iform_sub_left, iform_smul_left, iform_comm β α, nα]
    exact F1
  have hβ'H : rootReflection β • α ∉ excTLHex γ δ := fun hmem =>
    excTLHex_iform_ne_zero hhpos nγ nδ hγδ hmem hαH hβ'α
  refine ⟨α₁, hα₁H, rootReflection β • α, hβ'Ψ, hβ'H, nβ', ?_⟩
  rw [hβ'eq, iform_sub_right, iform_smul_right, iform_comm α₁ α, h1]
  exact F2

theorem excTL_chain_or_subset (hτ : τ ≠ .G2) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {γ δ : Fin τ.rank → ℤ} {h : ℤ} (hγ : γ ∈ Ψ) (hδ : δ ∈ Ψ)
    (nγ : iform γ γ = 2 * h) (nδ : iform δ δ = 2 * h) (hγδ : iform γ δ = -h) :
    Ψ ⊆ excTLHex γ δ ∨ ∃ a₁ ∈ Ψ, ∃ a₂ ∈ Ψ, ∃ a₃ ∈ Ψ, iform a₁ a₁ = 2 * h ∧
      iform a₂ a₂ = 2 * h ∧ iform a₃ a₃ = 2 * h ∧ iform a₁ a₂ = -h ∧ iform a₂ a₃ = -h ∧
      iform a₁ a₃ = 0 := by
  classical
  have hHΨ := excTLHex_subset hτ hΨ hγ hδ nγ nδ hγδ
  by_cases hsub : Ψ ⊆ excTLHex γ δ
  · exact Or.inl hsub
  right
  obtain ⟨ε, hεΨ, hεH⟩ := Set.not_subset.1 hsub
  have key : ∃ α ∈ excTLHex γ δ, ∃ β ∈ Ψ, β ∉ excTLHex γ δ ∧ iform α β ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rcases hΨ.irreducible (excTLHex γ δ) hHΨ
      (fun α hα β hβ hβH => hcon α hα β hβ hβH) with h0 | h0
    · exact (Set.eq_empty_iff_forall_notMem.1 h0 γ) (by simp [excTLHex])
    · exact hεH (h0 ▸ hεΨ)
  obtain ⟨α, hαH, β, hβΨ, hβH, hαβ⟩ := key
  by_cases hk : iform β β = 2 * h
  · exact excTL_chain_same hτ hΨ hγ hδ nγ nδ hγδ hαH hβΨ hβH hk hαβ
  · obtain ⟨α', hα'H, β', hβ'Ψ, hβ'H, nβ', hne⟩ :=
      excTL_chain_mixed hτ hΨ hγ hδ nγ nδ hγδ hαH hβΨ hβH hk hαβ
    exact excTL_chain_same hτ hΨ hγ hδ nγ nδ hγδ hα'H hβ'Ψ hβ'H nβ' hne

theorem excTL_a2_lengths (hτ : τ ≠ .G2) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hsum : IsRoot τ (γ + δ)) (h1 : ¬ IsRoot τ (γ - δ))
    (h2 : ¬ IsRoot τ ((2 : ℤ) • γ + δ)) (h3 : ¬ IsRoot τ (γ + (2 : ℤ) • δ)) :
    ∃ h : ℤ, iform γ γ = 2 * h ∧ iform δ δ = 2 * h ∧ iform γ δ = -h := by
  obtain ⟨hne, hne'⟩ := excTL_a2_ne hτ hγ hsum
  obtain ⟨hsq, hda, hdb⟩ := excTL_iform_bound hγ hδ hne hne'
  have hna := excTL_norm_cases hτ hγ
  have hnb := excTL_norm_cases hτ hδ
  have hnt := excTL_norm_cases hτ hsum
  have hδγ : iform δ γ = iform γ δ := iform_comm δ γ
  have ht : iform (γ + δ) (γ + δ) = iform γ γ + 2 * iform γ δ + iform δ δ := by
    simp only [iform_add_left, iform_add_right, hδγ]
    ring
  have c1 : corootPair δ (γ + δ) * iform δ δ = 2 * (iform γ δ + iform δ δ) := by
    rw [corootPair_mul hδ, iform_add_right, hδγ]
  have c2 : corootPair γ δ * iform γ γ = 2 * iform γ δ := corootPair_mul hγ δ
  have c3 : corootPair δ γ * iform δ δ = 2 * iform γ δ := by
    rw [corootPair_mul hδ, hδγ]
  have r1 : corootPair δ (γ + δ) = 2 → False := fun hc => by
    have := IsRoot.smul hsum (rootReflection δ)
    rw [rootReflection_smul hδ, hc] at this
    have e : γ + δ - (2 : ℤ) • δ = γ - δ := by rw [two_smul]; abel
    exact h1 (e ▸ this)
  have r2 : corootPair γ δ = -2 → False := fun hc => by
    have := IsRoot.smul hδ (rootReflection γ)
    rw [rootReflection_smul hγ, hc] at this
    have e : δ - (-2 : ℤ) • γ = (2 : ℤ) • γ + δ := by rw [neg_smul, sub_neg_eq_add]; abel
    exact h2 (e ▸ this)
  have r3 : corootPair δ γ = -2 → False := fun hc => by
    have := IsRoot.smul hγ (rootReflection δ)
    rw [rootReflection_smul hδ, hc] at this
    have e : γ - (-2 : ℤ) • δ = γ + (2 : ℤ) • δ := by rw [neg_smul, sub_neg_eq_add]
    exact h3 (e ▸ this)
  have hsq' : iform γ δ ^ 2 < iform γ γ * iform δ δ := hsq
  rcases hna with ha | ha <;> rcases hnb with hb | hb <;> rw [ha] at hda hsq' c2 ht <;>
    rw [hb] at hdb hsq' c1 c3 ht
  ·
    have hs : iform γ δ = -1 ∨ iform γ δ = 0 := by omega
    rcases hs with hs | hs
    · exact ⟨1, ha, hb, by omega⟩
    · exact absurd (by omega) r1
  ·
    exact absurd (by omega) r2
  ·
    exact absurd (by omega) r3
  ·
    exact ⟨2, ha, hb, by omega⟩

end Norm

end CFSG.HardMathSupport.Dickson.Sec6.I1431
