module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallPerfect
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false



section Lists

theorem commPairs_eq_of_mem_iff {τ : Tag} (α β : Fin τ.rank → ℤ) {l : List (ℕ × ℕ)}
    (hl : l.Pairwise fun p q : ℕ × ℕ =>
      p.1 + p.2 < q.1 + q.2 ∨ (p.1 + p.2 = q.1 + q.2 ∧ p.1 < q.1))
    (hmem : ∀ p, p ∈ commPairs τ α β ↔ p ∈ l) : commPairs τ α β = l := by
  have hnd : l.Nodup := hl.imp fun {p q} h hpq => by subst hpq; omega
  have hperm : (commPairs τ α β).Perm l :=
    (List.perm_ext_iff_of_nodup (commPairs_nodup α β) hnd).2 hmem
  refine hperm.eq_of_pairwise ?_ (commPairs_pairwise α β) hl
  intro a _ b _ h1 h2
  omega

end Lists

section F4Local

variable {K : Type} [Field K]

theorem f4_commutator_single {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β) (hγ : IsRoot .F4 γ)
    (hne : β ≠ γ) (hne' : β ≠ -γ) (hlen : iform β β = iform γ γ) (hsum : IsRoot .F4 (β + γ)) :
    ∃ C : ℤ, (C = 1 ∨ C = -1 ∨ C = 2 ∨ C = -2) ∧
      (IsRoot .F4 (γ - β) ∨ C = 1 ∨ C = -1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        ⁅pinnedX .F4 R β c, pinnedX .F4 R γ d⁆ = pinnedX .F4 R (β + γ) ((C : R) * c * d) := by
  classical
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hβ hγ hne hne'
  have hlist : commPairs .F4 β γ = [(1, 1)] := by
    refine commPairs_eq_of_mem_iff β γ (by simp) fun p => ?_
    rw [mem_commPairs, List.mem_singleton]
    constructor
    · rintro ⟨hp, hr⟩
      obtain ⟨⟨h1, -⟩, h2, -⟩ := mem_commCandidates.1 hp
      rcases exponent_pair_cases noG2_F4 hβ hγ hne hne' h1 h2 hr with h | h | h
      · exact Prod.ext h.1 h.2
      · omega
      · omega
    · rintro rfl
      exact ⟨by decide, by simpa using hsum⟩
  have h11 : ((1, 1) : ℕ × ℕ) ∈ commPairs .F4 β γ := by rw [hlist]; simp
  have hC11 := hC (1, 1) h11
  refine ⟨C (1, 1), ?_, ?_, fun R _ c d => ?_⟩
  · by_cases hr : IsRoot .F4 (γ - β)
    · simp only [hr, and_self, ite_true] at hC11
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.1 hC11 with h | h <;> simp [h]
    · simp only [hr, and_false, ite_false] at hC11
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hC11 with h | h <;> simp [h]
  · by_cases hr : IsRoot .F4 (γ - β)
    · exact Or.inl hr
    · simp only [hr, and_false, ite_false] at hC11
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.1 hC11 with h | h <;> simp [h]
  · have := hF R c d
    rw [hlist] at this
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
      pow_one] at this
    rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, this]

theorem isRoot_two_smul_add_of_iform {s l : Fin Tag.F4.rank → ℤ} (hs : IsRoot .F4 s)
    (hl : IsRoot .F4 l) (hss : iform s s = 2) (hsl : iform s l = -2) :
    IsRoot .F4 (2 • s + l) := by
  have h := IsRoot.smul hl (rootReflection s)
  have hc : corootPair s l = -2 := by simp [corootPair, hss, hsl]
  rw [rootReflection_smul hs, hc] at h
  have e : l - (-2 : ℤ) • s = 2 • s + l := by
    rw [neg_smul, sub_neg_eq_add, two_smul, two_smul]; abel
  rwa [e] at h

theorem f4_commutator_mixed {s l : Fin Tag.F4.rank → ℤ} (hs : IsRoot .F4 s) (hl : IsRoot .F4 l)
    (hss : iform s s = 2) (hll : iform l l = 4) (hsl : iform s l = -2) :
    IsRoot .F4 (s + l) ∧ IsRoot .F4 (2 • s + l) ∧
    ∃ C₁ C₂ : ℤ, (C₁ = 1 ∨ C₁ = -1) ∧ (C₂ = 1 ∨ C₂ = -1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        ⁅pinnedX .F4 R s c, pinnedX .F4 R l d⁆ =
          pinnedX .F4 R (s + l) ((C₁ : R) * c * d) * pinnedX .F4 R (2 • s + l) ((C₂ : R) * c ^ 2 * d) := by
  classical
  have hne : s ≠ l := fun e => by rw [e] at hss; omega
  have hne' : s ≠ -l := fun e => by
    have := congrArg (fun x => iform x x) e
    simp only [iform_neg_left_eq, iform_neg_right_eq, neg_neg] at this
    omega
  have hr1 : IsRoot .F4 (s + l) := isRoot_add_of_iform_neg hs hl hne' (by omega)
  have hr2 := isRoot_two_smul_add_of_iform hs hl hss hsl
  obtain ⟨C, hC, hF⟩ := exists_pinnedX_commFormula_F4_exact hs hl hne hne'
  have hlist : commPairs .F4 s l = [(1, 1), (2, 1)] := by
    refine commPairs_eq_of_mem_iff s l (by simp) fun p => ?_
    rw [mem_commPairs]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨hp, hr⟩
      obtain ⟨⟨h1, -⟩, h2, -⟩ := mem_commCandidates.1 hp
      rcases exponent_pair_cases noG2_F4 hs hl hne hne' h1 h2 hr with h | h | h
      · exact Or.inl (Prod.ext h.1 h.2)
      · omega
      · exact Or.inr (Prod.ext h.1 h.2.1)
    · rintro (rfl | rfl)
      · exact ⟨by decide, by simpa using hr1⟩
      · exact ⟨by decide, by simpa using hr2⟩
  have h11 : ((1, 1) : ℕ × ℕ) ∈ commPairs .F4 s l := by rw [hlist]; simp
  have h21 : ((2, 1) : ℕ × ℕ) ∈ commPairs .F4 s l := by rw [hlist]; simp
  have hnr : ¬ IsRoot .F4 (l - s) := by
    intro hr
    have := iform_self_cases noG2_F4 hr
    simp only [iform_sub_left, iform_sub_right] at this
    rw [iform_comm l s] at this
    omega
  have e1 := hC (1, 1) h11
  have e2 := hC (2, 1) h21
  simp only [hnr, and_false, ite_false] at e1
  simp only [show ((2, 1) : ℕ × ℕ) ≠ (1, 1) by decide, false_and, ite_false] at e2
  refine ⟨hr1, hr2, C (1, 1), C (2, 1),
    (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 e1, (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).1 e2,
    fun R _ c d => ?_⟩
  have := hF R c d
  rw [hlist] at this
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_smul,
    pow_one] at this
  rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, this]

end F4Local

section F4Odd

variable {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}

theorem f4_mem_commutator_single (h2 : (2 : K) ≠ 0) (i : KernelComponent χ)
    {β γ : Fin Tag.F4.rank → ℤ} (hβΨ : β ∈ componentRoots χ i) (hγΨ : γ ∈ componentRoots χ i)
    (hne : β ≠ γ) (hne' : β ≠ -γ) (hlen : iform β β = iform γ γ) (hsum : IsRoot .F4 (β + γ))
    (t : K) :
    pinnedX .F4 K (β + γ) t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  obtain ⟨C, hCc, -, hform⟩ := f4_commutator_single (hΨ.isRoot β hβΨ) (hΨ.isRoot γ hγΨ) hne hne'
    hlen hsum
  have hCK : (C : K) ≠ 0 := by
    rcases hCc with h | h | h | h <;> simp [h, h2]
  exact pinnedX_mem_commutator_of_formula i hβΨ hγΨ hCK (fun c d => hform K c d) t

theorem pinnedX_mem_commutator_F4_of_two_ne_zero (h2 : (2 : K) ≠ 0) (i : KernelComponent χ)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α)
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i) (t : K) :
    pinnedX .F4 K α t ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hαr : IsRoot .F4 α := hΨ.isRoot α hα
  obtain ⟨δ, hδΨ, hne1, hne2, hneg⟩ := exists_neg_partner hΨ hbig hα
  have hδr : IsRoot .F4 δ := hΨ.isRoot δ hδΨ
  have hne2' : α ≠ -δ := fun e => hne2 (by rw [e, neg_neg])
  have hsq := iform_sq_lt hαr hδr hne1.symm hne2'
  have hdv1 := iform_dvd_of_isRoot hαr δ
  have hdv2 := iform_dvd_of_isRoot hδr α
  rw [iform_comm δ α] at hdv2
  have hsumr : IsRoot .F4 (α + δ) := isRoot_add_of_iform_neg hαr hδr hne2' hneg
  have hβΨ : α + δ ∈ componentRoots χ i := hΨ.add_mem α hα δ hδΨ hsumr
  have hγΨ : -δ ∈ componentRoots χ i := hΨ.neg_mem δ hδΨ
  have hγr : IsRoot .F4 (-δ) := IsRoot.neg hδr
  have hne' : α + δ ≠ -(-δ) := by
    intro e
    rw [neg_neg] at e
    exact hαr.ne_zero (by simpa using e)
  have hsum : α + δ + -δ = α := by abel
  have hneg_eq : iform (-δ) (-δ) = iform δ δ := by
    rw [iform_neg_left_eq, iform_neg_right_eq, neg_neg]
  have hb : iform (α + δ) (α + δ) = iform α α + 2 * iform α δ + iform δ δ := by
    simp only [iform_add_left, iform_add_right]
    rw [iform_comm δ α]; ring
  have hcases : (iform α α = 2 ∧ iform δ δ = 2 ∧ iform α δ = -1) ∨
      (iform α α = 4 ∧ iform δ δ = 4 ∧ iform α δ = -2) ∨
      (iform α α = 4 ∧ iform δ δ = 2 ∧ iform α δ = -2) ∨
      (iform α α = 2 ∧ iform δ δ = 4 ∧ iform α δ = -2) := by
    have h1 := iform_self_cases noG2_F4 hαr
    have h2' := iform_self_cases noG2_F4 hδr
    generalize iform α δ = e at hsq hdv1 hdv2 hneg ⊢
    rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2' <;> rw [h1] at hsq hdv1 <;>
      rw [h2'] at hsq hdv2 <;> (have hlow : -4 < e := by nlinarith) <;> interval_cases e <;> omega
  rcases hcases with ⟨ha, hd, he⟩ | ⟨ha, hd, he⟩ | ⟨ha, hd, he⟩ | ⟨ha, hd, he⟩
  · have hne : α + δ ≠ -δ := by
      intro e
      have e3 := congrArg (fun x => iform x δ) e
      simp only [iform_add_left, iform_neg_left_eq] at e3
      omega
    have := f4_mem_commutator_single h2 i hβΨ hγΨ hne hne' (by rw [hb, hneg_eq]; omega)
      (by rw [hsum]; exact hαr) t
    rwa [hsum] at this
  · have hne : α + δ ≠ -δ := by
      intro e
      have e3 := congrArg (fun x => iform x δ) e
      simp only [iform_add_left, iform_neg_left_eq] at e3
      omega
    have := f4_mem_commutator_single h2 i hβΨ hγΨ hne hne' (by rw [hb, hneg_eq]; omega)
      (by rw [hsum]; exact hαr) t
    rwa [hsum] at this
  · have hne : α + δ ≠ -δ := by
      intro e
      have e3 := congrArg (fun x => iform x δ) e
      simp only [iform_add_left, iform_neg_left_eq] at e3
      omega
    have := f4_mem_commutator_single h2 i hβΨ hγΨ hne hne' (by rw [hb, hneg_eq]; omega)
      (by rw [hsum]; exact hαr) t
    rwa [hsum] at this
  ·
    have hss : iform (α + δ) (α + δ) = 2 := by rw [hb]; omega
    have hll : iform (-δ) (-δ) = 4 := by rw [hneg_eq]; omega
    have hsl : iform (α + δ) (-δ) = -2 := by
      simp only [iform_add_left, iform_neg_right_eq]; omega
    obtain ⟨-, hr2, C₁, C₂, hC₁, hC₂, hform⟩ := f4_commutator_mixed hsumr hγr hss hll hsl
    have hlam : 2 • (α + δ) + -δ = α + (α + δ) := by rw [two_smul]; abel
    rw [hlam] at hr2
    have hlamΨ : α + (α + δ) ∈ componentRoots χ i := hΨ.add_mem α hα _ hβΨ hr2
    have hne3 : α ≠ α + δ := fun e => hδr.ne_zero (by simpa using e.symm)
    have hne4 : α ≠ -(α + δ) := by
      intro e
      have e3 := congrArg (fun x => iform α x) e
      simp only [iform_neg_right_eq, iform_add_right] at e3
      omega
    have hlammem : ∀ u : K, pinnedX .F4 K (α + (α + δ)) u ∈
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := fun u =>
      f4_mem_commutator_single h2 i hα hβΨ hne3 hne4 (by rw [hss, ha]) hr2 u
    have hC₁K : (C₁ : K) ≠ 0 := by rcases hC₁ with h | h <;> simp [h]
    set N := ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ with hN
    have e := hform K 1 (((C₁ : K))⁻¹ * t)
    rw [hsum, hlam] at e
    have hcomm : ⁅pinnedX .F4 K (α + δ) 1, pinnedX .F4 K (-δ) (((C₁ : K))⁻¹ * t)⁆ ∈ N :=
      Subgroup.commutator_mem_commutator (pinnedX_mem_rootSpan hβΨ _) (pinnedX_mem_rootSpan hγΨ _)
    rw [e] at hcomm
    have h1 := mul_mem hcomm (inv_mem (hlammem ((C₂ : K) * 1 ^ 2 * (((C₁ : K))⁻¹ * t))))
    rw [mul_inv_cancel_right] at h1
    rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ hC₁K, one_mul] at h1

theorem isPerfect_componentRootSpan_F4_of_two_ne_zero (h2 : (2 : K) ≠ 0) (i : KernelComponent χ)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α) :
    Group.IsPerfect (componentRootSpan K χ i) :=
  isPerfect_componentRootSpan_of_forall i fun α hα t =>
    pinnedX_mem_commutator_F4_of_two_ne_zero h2 i hbig hα t

end F4Odd

end CFSG.HardMathSupport.Timmesfeld.LangTorus
