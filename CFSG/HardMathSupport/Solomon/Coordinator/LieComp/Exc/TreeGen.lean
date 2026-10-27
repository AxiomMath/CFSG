module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LieType.Chevalley.CorootCoordinates
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false

@[expose] def rootsOfFam {τ : Tag} {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (s : Set ι) :
    Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ ∃ n : ι → ℕ, (∀ b, n b ≠ 0 → b ∈ s) ∧
    (γ = ∑ b, (n b : ℤ) • β b ∨ γ = -∑ b, (n b : ℤ) • β b)}

section Gen


variable {τ : Tag}

theorem iform_self_nonneg' (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases h : x = 0
  · rw [h]
    simp [iform]
  · exact (iform_self_pos h).le

theorem rootSubgroup_add_le (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    (G : Subgroup (ModGL τ K)) {δ ε : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hε : IsRoot τ ε)
    (hne : δ ≠ ε) (hne' : δ ≠ -ε) (hsum : IsRoot τ (δ + ε))
    (hδG : rootSubgroup τ K δ ≤ G) (hεG : rootSubgroup τ K ε ≤ G) :
    rootSubgroup τ K (δ + ε) ≤ G := by
  obtain ⟨hN, hF⟩ := (simply_laced_root_commutator_unit τ hτ hδ hε hne hne').1 hsum
  set N : ℤ := commConst τ δ ε (1, 1) with hNdef
  have hN2 : ((N : ℤ) : K) * (N : K) = 1 := by
    rcases hN with h | h <;> rw [h] <;> simp
  rw [rootSubgroup]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨t, rfl⟩
  have h1 : pinnedX τ K δ ((N : K) * t) ∈ G :=
    hδG (mem_rootSubgroup.2 ⟨_, rfl⟩)
  have h2 : pinnedX τ K ε 1 ∈ G := hεG (mem_rootSubgroup.2 ⟨_, rfl⟩)
  have h3 := G.commutator_mem_commutator h1 h2
  have h4 : ⁅pinnedX τ K δ ((N : K) * t), pinnedX τ K ε 1⁆ = pinnedX τ K (δ + ε) t := by
    rw [hF K ((N : K) * t) 1]
    congr 1
    calc (N : K) * ((N : K) * t) * 1 = ((N : K) * N) * t := by ring
      _ = t := by rw [hN2, one_mul]
  have h5 : ⁅pinnedX τ K δ ((N : K) * t), pinnedX τ K ε 1⁆ ∈ G := Subgroup.commutator_le_self G h3
  rwa [h4] at h5

theorem rootSpan_rootsOfFam_le (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hβ : ∀ b, IsRoot τ (β b)) (s : Set ι) :
    rootSpan τ K (rootsOfFam β s) ≤ ⨆ b ∈ s, (rootSL2 τ K (β b)).range := by
  classical
  set G : Subgroup (ModGL τ K) := ⨆ b ∈ s, (rootSL2 τ K (β b)).range with hG
  have hrootG : ∀ b ∈ s, rootSubgroup τ K (β b) ≤ G ∧ rootSubgroup τ K (-β b) ≤ G := by
    intro b hb
    have h : (rootSL2 τ K (β b)).range ≤ G := le_iSup₂ (f := fun b (_ : b ∈ s) =>
      (rootSL2 τ K (β b)).range) b hb
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (hβ b)] at h
    exact ⟨le_sup_left.trans h, le_sup_right.trans h⟩
  have hββ : ∀ b, iform (β b) (β b) = 2 := fun b =>
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hβ b)
  have key : ∀ N : ℕ, ∀ n : ι → ℕ, (∀ b, n b ≠ 0 → b ∈ s) → ∑ b, n b = N →
      IsRoot τ (∑ b, (n b : ℤ) • β b) →
        rootSubgroup τ K (∑ b, (n b : ℤ) • β b) ≤ G ∧
          rootSubgroup τ K (-∑ b, (n b : ℤ) • β b) ≤ G := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro n hn hN hroot
      set γ : Fin τ.rank → ℤ := ∑ b, (n b : ℤ) • β b with hγ
      have hγγ : iform γ γ = 2 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hroot
      have hex : ∃ b, n b ≠ 0 ∧ 1 ≤ iform γ (β b) := by
        by_contra hcon
        push Not at hcon
        have h3 : iform γ γ = ∑ b, (n b : ℤ) * iform γ (β b) := by
          have : iform γ γ = iform (∑ b, (n b : ℤ) • β b) γ := by rw [← hγ]
          rw [this, iform_finset_sum_left]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [iform_smul_left, iform_comm (β b) γ]
        have h4 : ∑ b, (n b : ℤ) * iform γ (β b) ≤ 0 := by
          refine Finset.sum_nonpos fun b _ => ?_
          by_cases hb : n b = 0
          · rw [hb]
            simp
          · have := hcon b hb
            have h5 : 0 ≤ (n b : ℤ) := by positivity
            nlinarith
        omega
      obtain ⟨b, hb1, hb2⟩ := hex
      have hbs : b ∈ s := hn b hb1
      have hnorm : iform (γ - β b) (γ - β b) = 4 - 2 * iform γ (β b) := by
        rw [iform_sub_left, iform_sub_right, iform_sub_right, hγγ, hββ b, iform_comm (β b) γ]
        ring
      have hnn : 0 ≤ iform (γ - β b) (γ - β b) := iform_self_nonneg' _
      have hle : iform γ (β b) ≤ 2 := by omega
      rcases (show iform γ (β b) = 2 ∨ iform γ (β b) = 1 by omega) with h2 | h1
      · have : γ - β b = 0 := by
          by_contra hx
          have := iform_self_pos hx
          rw [hnorm, h2] at this
          omega
        have hγb : γ = β b := sub_eq_zero.1 this
        rw [hγb]
        exact hrootG b hbs
      ·
        set δ : Fin τ.rank → ℤ := γ - β b with hδdef
        have hδroot : IsRoot τ δ := by
          have h := IsRoot.smul hroot (rootReflection (β b))
          rw [rootReflection_smul (hβ b)] at h
          have hcp : corootPair (β b) γ = 1 := by
            have := corootPair_mul (hβ b) γ
            rw [hββ b, iform_comm (β b) γ, h1] at this
            omega
          rw [hcp, one_smul] at h
          exact h
        set n' : ι → ℕ := fun c => if c = b then n c - 1 else n c with hn'
        have hn'b : n' b = n b - 1 := by simp [hn']
        have hn'le : ∀ c, n' c ≤ n c := fun c => by
          by_cases hc : c = b
          · subst hc
            simp [hn']
          · simp [hn', hc]
        have hsumn' : ∑ c, n' c + 1 = ∑ c, n c := by
          have : ∑ c, n c = ∑ c, (n' c + if c = b then 1 else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases hc : c = b
            · subst hc
              have := Nat.pos_of_ne_zero hb1
              simp [hn']
              omega
            · simp [hn', hc]
          rw [this, Finset.sum_add_distrib]
          simp
        have hδn' : δ = ∑ c, (n' c : ℤ) • β c := by
          have : ∑ c, (n c : ℤ) • β c = ∑ c, ((n' c : ℤ) • β c + if c = b then β b else 0) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            by_cases hc : c = b
            · subst hc
              have := Nat.pos_of_ne_zero hb1
              simp only [hn', ite_true]
              have e : ((n c : ℕ) : ℤ) = ((n c - 1 : ℕ) : ℤ) + 1 := by omega
              rw [e, add_smul, one_smul]
            · simp [hn', hc]
          rw [hδdef, hγ, this, Finset.sum_add_distrib]
          simp
        have hn'supp : ∀ c, n' c ≠ 0 → c ∈ s := fun c hc => hn c (by
          intro h0
          exact hc (Nat.le_zero.1 (h0 ▸ hn'le c)))
        have hNlt : ∑ c, n' c < N := by omega
        have hIH := ih (∑ c, n' c) hNlt n' hn'supp rfl (by rw [← hδn']; exact hδroot)
        rw [← hδn'] at hIH
        obtain ⟨hδG, hnδG⟩ := hIH
        have hγδ : γ = δ + β b := by rw [hδdef]; abel
        have hne : δ ≠ β b := fun h => by
          have : γ = (2 : ℤ) • β b := by rw [hγδ, h, two_smul]
          have h8 : iform γ γ = 8 := by
            rw [this, iform_smul_left, iform_smul_right, hββ b]
            norm_num
          omega
        have hne' : δ ≠ -β b := fun h => by
          have : γ = 0 := by rw [hγδ, h]; abel
          exact hroot.ne_zero this
        constructor
        · rw [hγδ]
          exact rootSubgroup_add_le hτ G hδroot (hβ b) hne hne' (by rw [← hγδ]; exact hroot)
            hδG (hrootG b hbs).1
        · have hnegsum : -γ = -δ + -β b := by rw [hγδ]; abel
          rw [hnegsum]
          exact rootSubgroup_add_le hτ G (IsRoot.neg hδroot) (IsRoot.neg (hβ b))
            (fun h => hne (neg_injective h)) (fun h => hne' (by rw [neg_neg] at h; exact neg_eq_iff_eq_neg.1 h))
            (by rw [← hnegsum]; exact IsRoot.neg hroot) hnδG (hrootG b hbs).2
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hroot, n, hn, hcase⟩ := hγ
  rcases hcase with rfl | rfl
  · exact (key _ n hn rfl hroot).1
  · exact (key _ n hn rfl (by simpa using IsRoot.neg hroot)).2

end Gen

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
