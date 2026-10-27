module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNFOrbFamily

public section

namespace CFSG.ComponentClassification.SolMax.NFOrb

open Equiv
open scoped Pointwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {t : ι → ι → Perm Ω}

@[expose] def pairRel (t : ι → ι → Perm Ω) (ω : Ω) : Set (ι × ι) := {p | t p.1 p.2 ω = ω}

omit [Fintype ι] [DecidableEq ι] in
theorem mem_pairRel {ω : Ω} {p : ι × ι} : p ∈ pairRel t ω ↔ t p.1 p.2 ω = ω := Iff.rfl

omit [Fintype ι] [DecidableEq ι] in
theorem pairRel_apply (ht : ∀ c d e, t c d * t d e = t c e) (hs : ∀ c d, t c d = t d c)
    (a b : ι) (ω : Ω) : pairRel t (t a b ω) = pairRel t ω := by
  ext p
  exact pair_fix_apply ht hs a b p.1 p.2 ω

theorem pairRel_conj {π : Perm Ω} {τ : Perm ι} (hτ : τ ∈ alternatingGroup ι)
    (hπ : ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d)) (ω : Ω) :
    pairRel t (π ω) = (⟨τ, hτ⟩ : alternatingGroup ι) • pairRel t ω := by
  ext ⟨p, q⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, mem_pairRel, mem_pairRel]
  have h1 := pair_fix_conj hπ (τ⁻¹ p) (τ⁻¹ q) ω
  rw [perm_apply_inv, perm_apply_inv] at h1
  rw [h1]
  rfl

@[expose] def IsCenter (t : ι → ι → Perm Ω) (ω : Ω) (c : ι) : Prop :=
  (∀ d e, d ≠ c → e ≠ c → t d e ω = ω) ∧ ∀ d, d ≠ c → t c d ω ≠ ω

omit [Fintype ι] [DecidableEq ι] in
theorem IsCenter.conj {π : Perm Ω} {τ : Perm ι} (hπ : ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    {ω : Ω} {c : ι} (h : IsCenter t ω c) : IsCenter t (π ω) (τ c) := by
  refine ⟨fun d e hd he => ?_, fun d hd => ?_⟩
  · have h1 := pair_fix_conj hπ (τ⁻¹ d) (τ⁻¹ e) ω
    rw [perm_apply_inv, perm_apply_inv] at h1
    rw [h1]
    exact h.1 _ _ (fun h' => hd (by rw [← h', perm_apply_inv]))
      (fun h' => he (by rw [← h', perm_apply_inv]))
  · have h1 := pair_fix_conj hπ c (τ⁻¹ d) ω
    rw [perm_apply_inv] at h1
    rw [ne_eq, h1]
    exact h.2 _ (fun h' => hd (by rw [← h', perm_apply_inv]))

theorem IsCenter.eq (h3 : 3 ≤ Fintype.card ι) {ω : Ω} {c c' : ι} (h : IsCenter t ω c)
    (h' : IsCenter t ω c') : c = c' := by
  by_contra hcc
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({c, c'} : Finset ι))
    (t := Finset.univ)
    (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  exact h'.2 d hd.2 (h.1 c' d (Ne.symm hcc) hd.1)

open Classical in
theorem card_center_le_two [Fintype Ω] [DecidableEq Ω] (h5 : 5 ≤ Fintype.card ι)
    (hΩ : Fintype.card Ω ≤ 2 * Fintype.card ι + 3)
    (hequiv : ∀ τ ∈ alternatingGroup ι, ∃ π : Perm Ω, ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    (c : ι) : (Finset.univ.filter fun ω => IsCenter t ω c).card ≤ 2 := by
  classical
  set F : ι → Finset Ω := fun c => Finset.univ.filter fun ω => IsCenter t ω c with hFdef
  have hle : ∀ c c', (F c).card ≤ (F c').card := by
    intro c c'
    obtain ⟨τ, hτ, hτc⟩ := exists_mem_alternatingGroup_apply_eq (by omega) c c'
    obtain ⟨π, hπ⟩ := hequiv τ hτ
    refine Finset.card_le_card_of_injOn (fun ω => π ω) (fun ω hω => ?_) (fun ω _ ω' _ h => ?_)
    · simp only [hFdef, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hω ⊢
      rw [← hτc]
      exact hω.conj hπ
    · exact π.injective h
  have hdisj : (Set.univ : Set ι).PairwiseDisjoint F := by
    intro c _ c' _ hcc
    rw [Function.onFun, Finset.disjoint_left]
    intro ω hω hω'
    simp only [hFdef, Finset.mem_filter, Finset.mem_univ, true_and] at hω hω'
    exact hcc (hω.eq (by omega) hω')
  have hsum : ∑ c' : ι, (F c').card ≤ Fintype.card Ω := by
    rw [← Finset.card_biUnion (fun c' _ c'' _ h => hdisj (Set.mem_univ c') (Set.mem_univ c'') h)]
    exact Finset.card_le_univ _
  have hconst : ∑ c' : ι, (F c').card = Fintype.card ι * (F c).card := by
    rw [Finset.sum_congr rfl (fun c' _ => le_antisymm (hle c' c) (hle c c')), Finset.sum_const,
      smul_eq_mul, Finset.card_univ]
  change (F c).card ≤ 2
  by_contra h3
  have : Fintype.card ι * 3 ≤ Fintype.card ι * (F c).card := Nat.mul_le_mul_left _ (by omega)
  omega

theorem card_le_of_three_points [Fintype Ω] [DecidableEq Ω] {Y : Type*} (f : Ω → Y)
    (S : Set Y) [Finite S]
    (hS : ∀ y ∈ S, ∃ ω₁ ω₂ ω₃ : Ω, f ω₁ = y ∧ f ω₂ = y ∧ f ω₃ = y ∧ ω₁ ≠ ω₂ ∧ ω₁ ≠ ω₃ ∧
      ω₂ ≠ ω₃) :
    Nat.card S * 3 ≤ Fintype.card Ω := by
  classical
  have hfin : S.Finite := Set.toFinite S
  have h1 := card_mul_le_of_fibre f hfin.toFinset (k := 3) (fun y hy => by
    rw [Set.Finite.mem_toFinset] at hy
    obtain ⟨ω₁, ω₂, ω₃, h₁, h₂, h₃, h12, h13, h23⟩ := hS y hy
    rw [Nat.succ_le_iff, Finset.two_lt_card]
    exact ⟨ω₁, by simp [h₁], ω₂, by simp [h₂], ω₃, by simp [h₃], h12, h13, h23⟩)
  rw [Nat.card_eq_card_finite_toFinset hfin]
  exact h1

theorem false_of_three [Fintype Ω] [DecidableEq Ω] (ht : ∀ c d e, t c d * t d e = t c e)
    (hs : ∀ c d, t c d = t d c) (h5 : 5 ≤ Fintype.card ι)
    (hΩ : Fintype.card Ω ≤ 2 * Fintype.card ι + 3)
    (hequiv : ∀ τ ∈ alternatingGroup ι, ∃ π : Perm Ω, ∀ c d, π * t c d * π⁻¹ = t (τ c) (τ d))
    {ω : Ω} {a b c d e : ι} (hab : t a b ω ≠ ω) (hac : t a c ω ≠ ω) (hbc : t b c ω ≠ ω)
    (hde : d ≠ e) (hfix : t d e ω = ω) : False := by
  classical
  have hninv : ¬ ∀ g : alternatingGroup ι, g • pairRel t ω = pairRel t ω := by
    intro hinv
    have hab' : a ≠ b := fun h => hab (by rw [h, pair_self ht, Perm.one_apply])
    obtain ⟨τ, hτ, hτd, hτe⟩ := exists_mem_alternatingGroup_apply_eq_apply_eq (by omega) hde hab'
    apply hab
    have h1 : (a, b) ∈ (⟨τ, hτ⟩ : alternatingGroup ι) • pairRel t ω :=
      Set.mem_smul_set.mpr ⟨(d, e), hfix, by rw [Prod.smul_mk]; simp [hτd, hτe, Perm.smul_def]⟩
    rw [hinv] at h1
    exact h1
  have hcard : Fintype.card ι ≤ Nat.card (MulAction.orbit (alternatingGroup ι) (pairRel t ω)) := by
    by_contra hlt
    exact hninv (smul_eq_of_card_orbit_lt h5 _ (by omega))
  have h3 := card_le_of_three_points (pairRel t) (MulAction.orbit (alternatingGroup ι)
    (pairRel t ω)) (fun y hy => by
      obtain ⟨g, hgy⟩ := hy
      have hgy' : g • pairRel t ω = y := hgy
      obtain ⟨π, hπ⟩ := hequiv (g : Perm ι) g.2
      have hg : pairRel t (π ω) = y := by rw [← hgy', pairRel_conj g.2 hπ]
      set τ := (g : Perm ι)
      refine ⟨π ω, t (τ a) (τ b) (π ω), t (τ a) (τ c) (π ω), hg, ?_, ?_, ?_, ?_, ?_⟩
      · rw [pairRel_apply ht hs, hg]
      · rw [pairRel_apply ht hs, hg]
      · exact fun h => hab ((pair_fix_conj hπ a b ω).mp h.symm)
      · exact fun h => hac ((pair_fix_conj hπ a c ω).mp h.symm)
      · intro h
        rw [pair_apply_eq_iff_fix ht hs] at h
        exact hbc ((pair_fix_conj hπ b c ω).mp h))
  omega

end CFSG.ComponentClassification.SolMax.NFOrb
