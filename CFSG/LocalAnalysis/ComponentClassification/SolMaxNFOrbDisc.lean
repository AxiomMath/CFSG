module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbCut

public section

namespace CFSG.ComponentClassification.SolMax.NFOrb

open Equiv
open scoped Pointwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {t : ι → ι → Perm Ω}

@[expose] def pairEq (t : ι → ι → Perm Ω) (ω : Ω) : Set ((ι × ι) × (ι × ι)) :=
  {q | t q.1.1 q.1.2 ω = t q.2.1 q.2.2 ω}

omit [Fintype ι] [DecidableEq ι] in
theorem pair_conj_apply {π : Perm Ω} {τ : Perm ι} (hπ : ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    (c d : ι) (ω : Ω) : t (τ c) (τ d) (π ω) = π (t c d ω) := by
  rw [← hπ c d, Perm.mul_apply, Perm.mul_apply, perm_inv_apply]

theorem pairEq_conj {π : Perm Ω} {τ : Perm ι} (hτ : τ ∈ alternatingGroup ι)
    (hπ : ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d)) (ω : Ω) :
    pairEq t (π ω) = (⟨τ, hτ⟩ : alternatingGroup ι) • pairEq t ω := by
  ext ⟨⟨p₁, p₂⟩, ⟨q₁, q₂⟩⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change t p₁ p₂ (π ω) = t q₁ q₂ (π ω) ↔
    t (τ⁻¹ p₁) (τ⁻¹ p₂) ω = t (τ⁻¹ q₁) (τ⁻¹ q₂) ω
  have h1 := pair_conj_apply hπ (τ⁻¹ p₁) (τ⁻¹ p₂) ω
  have h2 := pair_conj_apply hπ (τ⁻¹ q₁) (τ⁻¹ q₂) ω
  rw [perm_apply_inv, perm_apply_inv] at h1 h2
  rw [h1, h2]
  exact π.injective.eq_iff

omit [Fintype ι] [DecidableEq ι] in
theorem pairEq_apply (ht : ∀ c d e, t c d * t d e = t c e) (hs : ∀ c d, t c d = t d c)
    (a b : ι) (ω : Ω) : pairEq t (t a b ω) = pairEq t ω := by
  ext ⟨⟨p₁, p₂⟩, ⟨q₁, q₂⟩⟩
  change t p₁ p₂ (t a b ω) = t q₁ q₂ (t a b ω) ↔ t p₁ p₂ ω = t q₁ q₂ ω
  rw [← Perm.mul_apply, ← Perm.mul_apply, (pair_commute ht hs p₁ p₂ a b).eq,
    (pair_commute ht hs q₁ q₂ a b).eq, Perm.mul_apply, Perm.mul_apply]
  exact (t a b).injective.eq_iff

theorem exists_three (h4 : 4 ≤ Fintype.card ι) : ∃ a b c : ι, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x, y, hxy, hxa, -, hya, -⟩ := exists_two_notMem h4 a a
  exact ⟨a, x, y, Ne.symm hxa, Ne.symm hya, hxy⟩

theorem false_of_discrete [Fintype Ω] [DecidableEq Ω] (ht : ∀ c d e, t c d * t d e = t c e)
    (hs : ∀ c d, t c d = t d c) (h5 : 5 ≤ Fintype.card ι)
    (hΩ : Fintype.card Ω ≤ 2 * Fintype.card ι + 3)
    (hequiv : ∀ τ ∈ alternatingGroup ι, ∃ π : Perm Ω, ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    {ω : Ω} (hdisc : ∀ c d, c ≠ d → t c d ω ≠ ω) : False := by
  classical
  obtain ⟨a₀, b₀, c₀, hab₀, hac₀, hbc₀⟩ := exists_three (ι := ι) (by omega)
  by_cases hinv : ∀ g : alternatingGroup ι, g • pairEq t ω = pairEq t ω
  swap
  ·
    have hcard : Fintype.card ι ≤ Nat.card (MulAction.orbit (alternatingGroup ι) (pairEq t ω)) := by
      by_contra hlt
      exact hinv (smul_eq_of_card_orbit_lt h5 _ (by omega))
    have h3 := card_le_of_three_points (pairEq t) (MulAction.orbit (alternatingGroup ι)
      (pairEq t ω)) (fun y hy => by
        obtain ⟨g, hgy⟩ := hy
        have hgy' : g • pairEq t ω = y := hgy
        obtain ⟨π, hπ⟩ := hequiv (g : Perm ι) g.2
        have hg : pairEq t (π ω) = y := by rw [← hgy', pairEq_conj g.2 hπ]
        set τ := (g : Perm ι)
        refine ⟨π ω, t (τ a₀) (τ b₀) (π ω), t (τ a₀) (τ c₀) (π ω), hg, ?_, ?_, ?_, ?_, ?_⟩
        · rw [pairEq_apply ht hs, hg]
        · rw [pairEq_apply ht hs, hg]
        · exact fun h => hdisc a₀ b₀ hab₀ ((pair_fix_conj hπ a₀ b₀ ω).mp h.symm)
        · exact fun h => hdisc a₀ c₀ hac₀ ((pair_fix_conj hπ a₀ c₀ ω).mp h.symm)
        · intro h
          rw [pair_apply_eq_iff_fix ht hs] at h
          exact hdisc b₀ c₀ hbc₀ ((pair_fix_conj hπ b₀ c₀ ω).mp h))
    omega
  by_cases hrel : ∃ a b c d : ι, a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      t a b ω = t c d ω
  ·
    obtain ⟨a, b, c, d, hab, hcd, hac, had, hbc, hbd, habcd⟩ := hrel
    obtain ⟨e, hea, heb, hec, hed⟩ := exists_ne_four h5 a b c d
    set τ := swap d e * swap a b with hτ
    have hτA : τ ∈ alternatingGroup ι := swap_mul_swap_mem_alternatingGroup (Ne.symm hed) hab
    have hmem : ((b, a), (c, e)) ∈ (⟨τ, hτA⟩ : alternatingGroup ι) • pairEq t ω := by
      refine Set.mem_smul_set.mpr ⟨((a, b), (c, d)), habcd, ?_⟩
      change ((τ a, τ b), (τ c, τ d)) = ((b, a), (c, e))
      rw [hτ, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc),
        swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd), swap_apply_left,
        swap_apply_of_ne_of_ne hbd (Ne.symm heb), swap_apply_of_ne_of_ne had (Ne.symm hea),
        swap_apply_of_ne_of_ne hcd (Ne.symm hec)]
    rw [hinv] at hmem
    have h1 : t b a ω = t c e ω := hmem
    rw [← hs a b, habcd, pair_apply_eq_iff_fix ht hs] at h1
    exact hdisc d e (Ne.symm hed) h1
  push Not at hrel
  have hpair : ∀ a b c d : ι, a ≠ b → c ≠ d → t a b ω = t c d ω →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    intro a b c d hab hcd h
    by_cases hac : a = c
    · subst hac
      left
      refine ⟨rfl, ?_⟩
      by_contra hbd
      exact hdisc b d hbd ((pair_apply_eq_iff_fix ht hs a b d ω).mp h)
    by_cases had : a = d
    · subst had
      right
      refine ⟨rfl, ?_⟩
      by_contra hbc
      rw [hs c a] at h
      exact hdisc b c hbc ((pair_apply_eq_iff_fix ht hs a b c ω).mp h)
    by_cases hbc : b = c
    · subst hbc
      right
      refine ⟨?_, rfl⟩
      by_contra had'
      rw [hs a b] at h
      exact hdisc a d had' ((pair_apply_eq_iff_fix ht hs b a d ω).mp h)
    by_cases hbd : b = d
    · subst hbd
      left
      refine ⟨?_, rfl⟩
      by_contra hac'
      rw [hs a b, hs c b] at h
      exact hdisc a c hac' ((pair_apply_eq_iff_fix ht hs b a c ω).mp h)
    exact absurd h (hrel a b c d hab hcd hac had hbc hbd)
  set g : ι × ι → Ω := fun p => t p.1 p.2 ω with hg
  set I := (Finset.univ.offDiag : Finset (ι × ι)).image g with hI
  have hfib : ∀ y ∈ I,
      ((Finset.univ.offDiag : Finset (ι × ι)).filter fun p => g p = y).card = 2 := by
    intro y hy
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hy
    have hab' : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
    have : ((Finset.univ.offDiag : Finset (ι × ι)).filter fun p => g p = g (a, b)) =
        {(a, b), (b, a)} := by
      ext ⟨c, d⟩
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, hg]
      constructor
      · rintro ⟨hcd, h⟩
        rcases hpair c d a b hcd hab' h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨hab', rfl⟩
        · exact ⟨Ne.symm hab', by rw [hs]⟩
    rw [this, Finset.card_pair (by simp [Ne.symm hab'])]
  have hIcard : (Finset.univ.offDiag : Finset (ι × ι)).card = 2 * I.card := by
    rw [Finset.card_eq_sum_card_image g, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
      mul_comm]
  rw [Finset.offDiag_card, Finset.card_univ] at hIcard
  set O := MulAction.orbit (pairClosure t) ω with hO
  have hOfin : O.Finite := Set.toFinite O
  have hsub : insert ω I ⊆ hOfin.toFinset := by
    intro y hy
    rw [Set.Finite.mem_toFinset]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact MulAction.mem_orbit_self _
    · obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨⟨t a b, mem_pairClosure a b⟩, rfl⟩
  have hωI : ω ∉ I := by
    intro h
    obtain ⟨⟨a, b⟩, hab, hEq⟩ := Finset.mem_image.mp h
    exact hdisc a b (Finset.mem_offDiag.mp hab).2.2 hEq
  have hOcard : I.card + 1 ≤ Nat.card O := by
    rw [Nat.card_eq_card_finite_toFinset hOfin, ← Finset.card_insert_of_notMem hωI]
    exact Finset.card_le_card hsub
  have hOle : Nat.card O ≤ Fintype.card Ω := by
    rw [Nat.card_eq_card_finite_toFinset hOfin]
    exact Finset.card_le_univ _
  obtain ⟨k, hk⟩ := IsPGroup.card_orbit (isPGroup_pairClosure ht hs) ω
  rw [← hO] at hk
  set j := Fintype.card ι
  by_cases hk3 : k ≤ 3
  · have : 2 ^ k ≤ 8 := by
      calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
        _ = 8 := by norm_num
    have hjj : 5 * j ≤ j * j := Nat.mul_le_mul_right j h5
    omega
  · have : 16 ≤ 2 ^ k := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hj7 : 7 ≤ j := by omega
    have hjj : 7 * j ≤ j * j := Nat.mul_le_mul_right j hj7
    omega

end CFSG.ComponentClassification.SolMax.NFOrb
