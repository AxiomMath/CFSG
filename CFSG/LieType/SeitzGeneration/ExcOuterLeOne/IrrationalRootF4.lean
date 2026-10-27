module

public import CFSG.LieType.Ree.Duality
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.RootTransport
public import CFSG.LieType.Steinberg.Adjoint.ExtraPairs

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section F4

abbrev f4i (n : Fin 4) : Fin Tag.F4.rank := n

variable {K : Type} [Field K]

theorem rootNorm_F4_eq {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    rootNorm Tag.F4 γ = 2 ∨ rootNorm Tag.F4 γ = 4 := by
  have h := CFSG.LieType.Ree.ReeTag.quadForm_eq (t := CFSG.LieType.Ree.ReeTag.F4) (α := γ) hγ
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (by decide))

theorem isRoot_and_rootNorm_of_mem_longRoots {γ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ CFSG.LieType.Ree.ReeTag.longRoots CFSG.LieType.Ree.ReeTag.F4) :
    IsRoot Tag.F4 γ ∧ rootNorm Tag.F4 γ = 4 := by
  obtain ⟨hr, hl⟩ := hγ
  refine ⟨hr, ?_⟩
  have h := (CFSG.LieType.Ree.ReeTag.lengthParam_eq_prime_iff (t := CFSG.LieType.Ree.ReeTag.F4)
    (α := γ)).1 hl
  exact h.trans (by decide)

theorem xPar_mem_iff_of_rootNorm_eq_F4 (H : Subgroup ↥(adjointGroup Tag.F4 K))
    (hw : ∀ i : Fin Tag.F4.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.F4)) i (1 : Kˣ) ∈ H)
    {γ δ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hδ : IsRoot Tag.F4 δ)
    (h : rootNorm Tag.F4 γ = rootNorm Tag.F4 δ) (u : K) :
    xPar (rootOperatorFamily Tag.F4) γ u ∈ H ↔ xPar (rootOperatorFamily Tag.F4) δ u ∈ H := by
  obtain ⟨j, hj, hjH⟩ := exists_simple_of_root H hw hγ
  obtain ⟨j', hj', hjH'⟩ := exists_simple_of_root H hw hδ
  have hjj : rootNorm Tag.F4 (Pi.single j 1) = rootNorm Tag.F4 (Pi.single j' 1) := by
    rw [← hj, ← hj', h]
  refine (hjH u).trans (Iff.trans ?_ (hjH' u).symm)
  fin_cases j <;> fin_cases j'
  all_goals first
    | exact Iff.rfl
    | exact xPar_mem_iff_of_neighbour H hw (by decide) (by decide) u
    | (exfalso; revert hjj; decide)

theorem F4_explicit_roots :
    IsRoot Tag.F4 (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) ∧
      rootNorm Tag.F4 (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) = 2 ∧
      IsRoot Tag.F4 (Pi.single (f4i 1) 1 + (2 : ℕ) • Pi.single (f4i 2) 1) ∧
      rootNorm Tag.F4 (Pi.single (f4i 1) 1 + (2 : ℕ) • Pi.single (f4i 2) 1) = 4 ∧
      IsRoot Tag.F4 (Pi.single (f4i 0) 1 + Pi.single (f4i 1) 1) ∧
      rootNorm Tag.F4 (Pi.single (f4i 0) 1 + Pi.single (f4i 1) 1) = 4 := by
  have h12 : IsRoot Tag.F4 (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) := by
    rw [add_comm]
    exact isRoot_single_add_single (i := f4i 1) (k := f4i 2) (by decide)
  have h122 : IsRoot Tag.F4 (Pi.single (f4i 1) 1 + (2 : ℕ) • Pi.single (f4i 2) 1) := by
    have h := IsRoot.reflect (f4i 2) (isRoot_single Tag.F4 (f4i 1))
    have e : reflect Tag.F4 (f4i 2) (Pi.single (f4i 1) 1) =
        Pi.single (f4i 1) 1 + (2 : ℕ) • Pi.single (f4i 2) 1 := by decide
    rwa [e] at h
  have h01 : IsRoot Tag.F4 (Pi.single (f4i 0) 1 + Pi.single (f4i 1) 1) :=
    isRoot_single_add_single (i := f4i 1) (k := f4i 0) (by decide)
  exact ⟨h12, by decide, h122, by decide, h01, by decide⟩

theorem commutator_xPar_F4_one_two :
    ∃ C C' : ℤ, (C = 1 ∨ C = -1) ∧ ∀ s c : K,
      ⁅xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 1) 1) s,
        xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 2) 1) c⁆ =
      xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) ((C : K) * s * c) *
        xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 1) 1 + (2 : ℕ) • Pi.single (f4i 2) 1)
          ((C' : K) * s * c ^ 2) := by
  have hα : IsRoot Tag.F4 (Pi.single (f4i 1) 1) := isRoot_single _ _
  have hβ : IsRoot Tag.F4 (Pi.single (f4i 2) 1) := isRoot_single _ _
  obtain ⟨hδ, -, -, -, -, -⟩ := F4_explicit_roots
  have hne : (Pi.single (f4i 1) 1 : Fin Tag.F4.rank → ℤ) ≠ Pi.single (f4i 2) 1 :=
    single_ne_single_of_ne (by decide)
  have hne' : (Pi.single (f4i 1) 1 : Fin Tag.F4.rank → ℤ) ≠ -Pi.single (f4i 2) 1 :=
    single_ne_neg_single_of _ _
  have h21 : ¬IsRoot Tag.F4 ((2 : ℕ) • (Pi.single (f4i 1) 1 : Fin Tag.F4.rank → ℤ) +
      Pi.single (f4i 2) 1) := by
    intro hr
    rcases rootNorm_F4_eq hr with h | h <;> revert h <;> decide
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily Tag.F4) f4Data_valid ⟨_, hα⟩ ⟨_, hβ⟩).natAbs
      = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily Tag.F4) f4Data_valid
        (single_ne_neg_single_of _ _) hδ]
    exact stringNorm_of_not_isRoot (not_isRoot_single_sub_single (by decide))
  refine ⟨RootOperatorFamily'.coeff11 (rootOperatorFamily Tag.F4) f4Data_valid ⟨_, hα⟩ ⟨_, hβ⟩,
    RootOperatorFamily'.coeff12 (rootOperatorFamily Tag.F4) f4Data_valid ⟨_, hα⟩ ⟨_, hβ⟩, ?_,
    fun s c => ?_⟩
  · rcases Int.natAbs_eq_iff.1 hN with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · rw [commutator_xPar (F := rootOperatorFamily Tag.F4) f4Data_valid noG2_F4 hα hβ hne hne' s c,
      xPar_of_not_isRoot h21, mul_one]

end F4

theorem eq_top_of_irrational_longRootElt {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : ∀ F : Subfield K, k ≤ F → F = k ∨ F = ⊤) (H : Subgroup ↥(adjointGroup .F4 K))
    (hrat : ∀ (γ : Fin Tag.F4.rank → ℤ), IsRoot .F4 γ → ∀ c ∈ k, xPar (rootOperatorFamily .F4) γ c ∈ H)
    (γ₀ : Fin Tag.F4.rank → ℤ) (hγ₀ : γ₀ ∈ CFSG.LieType.Ree.ReeTag.longRoots CFSG.LieType.Ree.ReeTag.F4)
    (t : K) (ht : t ∉ k) (hmem : xPar (rootOperatorFamily .F4) γ₀ t ∈ H) : H = ⊤ := by
  have hw := weylElement_one_mem_of_rat k H hrat
  obtain ⟨hγ₀r, hγ₀n⟩ := isRoot_and_rootNorm_of_mem_longRoots hγ₀
  have horb := fun {γ δ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hδ : IsRoot Tag.F4 δ)
    (h : rootNorm Tag.F4 γ = rootNorm Tag.F4 δ) (u : K) =>
    xPar_mem_iff_of_rootNorm_eq_F4 H hw hγ hδ h u
  obtain ⟨hr12, hn12, hr122, hn122, hr01, hn01⟩ := F4_explicit_roots
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_neighbour (K := K) f4Data_valid noG2_F4
    (i := f4i 1) (l := f4i 0) (by decide) (by decide)
  let S : Subring K :=
    { carrier := {u | ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → rootNorm Tag.F4 γ = 4 →
        xPar (rootOperatorFamily Tag.F4) γ u ∈ H}
      zero_mem' := fun γ _ _ => by simpa [xPar_zero] using H.one_mem
      one_mem' := fun γ hγ _ => hrat γ hγ 1 k.one_mem
      add_mem' := fun {a b} ha hb γ hγ hn => by
        rw [xPar_add]
        exact H.mul_mem (ha γ hγ hn) (hb γ hγ hn)
      neg_mem' := fun {a} ha γ hγ hn => by
        rw [← xPar_neg]
        exact H.inv_mem (ha γ hγ hn)
      mul_mem' := fun {a b} ha hb γ hγ hn => by
        have h1 := xPar_mul_mem_of_commutator H hε hcomm
          (ha _ (isRoot_single _ _) (by decide)) (hb _ (isRoot_single _ _) (by decide))
        exact (horb hr01 hγ (hn01.trans hn.symm) _).1 h1 }
  have hS : S = ⊤ := by
    refine eq_top_of_subring k hk S (fun c hc γ hγ _ => hrat γ hγ c hc) ht ?_
    intro γ hγ hn
    exact (horb hγ₀r hγ (hγ₀n.trans hn.symm) t).1 hmem
  have hlong : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → rootNorm Tag.F4 γ = 4 → ∀ c : K,
      xPar (rootOperatorFamily Tag.F4) γ c ∈ H := fun γ hγ hn c => by
    have : c ∈ S := by rw [hS]; trivial
    exact this γ hγ hn
  obtain ⟨C, C', hC, hcomm2⟩ := commutator_xPar_F4_one_two (K := K)
  have hshort1 : ∀ s : K, xPar (rootOperatorFamily Tag.F4)
      (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) ((C : K) * s) ∈ H := by
    intro s
    have hx1 := hlong (Pi.single (f4i 1) 1) (isRoot_single _ (f4i 1)) (by decide) s
    have hx2 : xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 2) 1) (1 : K) ∈ H :=
      hrat _ (isRoot_single _ _) 1 k.one_mem
    have h3 : ⁅xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 1) 1) s,
        xPar (rootOperatorFamily Tag.F4) (Pi.single (f4i 2) 1) (1 : K)⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hx1 hx2) (H.inv_mem hx1)) (H.inv_mem hx2)
    rw [hcomm2 s 1] at h3
    have h4 := hlong _ hr122 hn122 ((C' : K) * s * 1 ^ 2)
    have h5 := (Subgroup.mul_mem_cancel_right H h4).1 h3
    simpa using h5
  have hshort : ∀ s : K, xPar (rootOperatorFamily Tag.F4)
      (Pi.single (f4i 1) 1 + Pi.single (f4i 2) 1) s ∈ H := by
    intro s
    rcases hC with rfl | rfl
    · simpa using hshort1 s
    · have := hshort1 (-s)
      simpa using this
  refine eq_top_of_forall_xPar_mem H fun γ hγ c => ?_
  rcases rootNorm_F4_eq hγ with h | h
  · exact (horb hr12 hγ (hn12.trans h.symm) c).1 (hshort c)
  · exact hlong γ hγ h c

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
