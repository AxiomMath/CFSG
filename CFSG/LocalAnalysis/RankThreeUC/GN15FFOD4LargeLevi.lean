module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.LeviCopies
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4WeylRank

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
open scoped MatrixGroups

@[expose] def leviU : Fin 4 → Fin 4 → List (Fin 4) :=
  ![![[], [2, 3, 1, 2], [0, 2, 3, 1, 2], [2, 1, 0, 2, 3, 2, 1, 0, 2]],
    ![[], [2, 3, 0, 2], [1, 2, 3, 0, 2], [2, 1, 0, 2, 3, 2, 1, 0, 2]],
    ![[], [], [], []],
    ![[], [2, 1, 0, 2], [3, 2, 1, 0, 2], [2, 1, 0, 2, 3, 2, 1, 0, 2]]]

private def vCE' : Fin 4 → Fin Tag.D4.rank → ℤ := fun e => vCE e

private theorem leviU_hu0 : ∀ i : Fin 4,
    ((leviU 0 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 0 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) ∨
    ((leviU 0 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 0 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) := by
  decide +kernel

private theorem leviU_hu1 : ∀ i : Fin 4,
    ((leviU 1 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 1 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) ∨
    ((leviU 1 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 1 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) := by
  decide +kernel

private theorem leviU_hu3 : ∀ i : Fin 4,
    ((leviU 3 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 3 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) ∨
    ((leviU 3 i).foldr (reflectLG .D4)
        (List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∧
      (leviU 3 i).foldr (reflectLG .D4)
          (List.ofFn (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)) := by
  decide +kernel

private theorem leviU_vCE_distinct : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), ∀ i j : Fin 4, i ≠ j →
    (leviU e i).foldr (reflectLG .D4) (List.ofFn (vCE' e)) ≠
      (leviU e j).foldr (reflectLG .D4) (List.ofFn (vCE' e)) := by
  decide +kernel

private theorem not_isRoot_of_notMem_artifactRoots
    {v : Fin Tag.D4.rank → ℤ} (h : List.ofFn v ∉ Tag.artifactRoots .D4) : ¬ IsRoot .D4 v :=
  fun hv => h (isRoot_iff_mem_artifactRoots.1 hv)

private theorem wordProd_smul_D4
    (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    (coxeterSystem .D4).wordProd l • v = l.foldr (reflect .D4) v :=
  wordProd_smul' (τ := .D4) l v

private theorem ofFn_foldr_reflectG_D4 (l : List (Fin 4)) (v : Fin Tag.D4.rank → ℤ) :
    List.ofFn (l.foldr (reflect .D4) v) = l.foldr (reflectLG .D4) (List.ofFn v) :=
  ofFn_foldr_reflectG (τ := .D4) l v

section Chev


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
  {k V : Type} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup V] [Module k V]
  [Module.Finite k V] {ρ : Representation k (adjointGroup .D4 K) V} {y : V}
  {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)}

theorem levi_ends_finrank {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) {e : Fin 4} (he : e ∈ ({0, 1, 3} : Finset (Fin 4)))
    (hJ : J ⊆ ({2, e} : Finset (Fin 4))) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ (i : Fin 4) (z : Kˣ), χ (dC .D4 K i z) ^ (2 ^ g) = χ (dC .D4 K i z)) :
    4 * (2 ^ (n / g) * 2 ^ (n / g)) ≤ Module.finrank k V := by
  have he' : e = 0 ∨ e = 1 ∨ e = 3 := by simpa using he
  have toAction : ∀ (e i r s : Fin 4),
      (leviU e i).foldr (reflectLG .D4) (List.ofFn (Pi.single r 1 : Fin Tag.D4.rank → ℤ)) =
        List.ofFn (Pi.single s 1 : Fin Tag.D4.rank → ℤ) →
      (coxeterSystem .D4).wordProd (leviU e i) • (Pi.single r 1 : Fin Tag.D4.rank → ℤ) =
        (Pi.single s 1 : Fin Tag.D4.rank → ℤ) := by
    intro e i r s h
    apply List.ofFn_injective
    simp only [wordProd_smul_D4, ofFn_foldr_reflectG_D4]
    exact h
  rcases he' with rfl | rfl | rfl
  ·
    have hr : (1 : Fin 4) ∉ J := fun h =>
      (by decide : (1 : Fin 4) ∉ ({2, 0} : Finset (Fin 4))) (hJ h)
    have hr' : (3 : Fin 4) ∉ J := fun h =>
      (by decide : (3 : Fin 4) ∉ ({2, 0} : Finset (Fin 4))) (hJ h)
    have h0 : CFSG.LieType.Steinberg.Adjoint.iform (τ := .D4)
        (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)
        (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) = 0 := by
      decide +kernel
    have hp : ¬ IsRoot .D4
        (Pi.single (1 : Fin 4) (1 : ℤ) + Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hm : ¬ IsRoot .D4
        (Pi.single (1 : Fin 4) (1 : ℤ) - Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hcomm : ∀ a b : SL(2, K),
        rankOne .D4 K (1 : Fin 4) a * rankOne .D4 K (3 : Fin 4) b =
          rankOne .D4 K (3 : Fin 4) b * rankOne .D4 K (1 : Fin 4) a :=
      fun a b => rankOne_commute_of_orthogonal (τ := .D4) h0 hp hm a b
    let u : Fin 4 → WeylGroup .D4 := fun i => (coxeterSystem .D4).wordProd (leviU 0 i)
    refine levi_copies_two_pow (τ := .D4) (m := 4) hn hK hρ ht (r := (1 : Fin 4))
      (r' := (3 : Fin 4)) (by decide : (1 : Fin 4) ≠ (3 : Fin 4)) hr hr' hcomm hg hgn
      (hper (1 : Fin 4))
      (hper (3 : Fin 4)) u ?_ ?_
    · intro i
      rcases leviU_hu0 i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · simpa [u] using toAction 0 i 1 1 h1
        · simpa [u] using toAction 0 i 3 3 h2
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [u] using toAction 0 i 1 3 h1
        · simpa [u] using toAction 0 i 3 1 h2
    · refine linearIndependent_translates_of_isChevType_mem (τ := .D4) hρ ht
        (v₀ := vCE' 0) ?_ u ?_
      · intro j hj
        simpa [vCE'] using reflect_vCE 0 he j (hJ hj)
      · intro i j hij h
        have h1 : (leviU 0 i).foldr (reflect .D4) (vCE' 0) =
            (leviU 0 j).foldr (reflect .D4) (vCE' 0) := by
          simpa [u, wordProd_smul_D4] using h
        have h2 := congrArg List.ofFn h1
        rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
        exact leviU_vCE_distinct 0 he i j hij h2
  ·
    have hr : (0 : Fin 4) ∉ J := fun h =>
      (by decide : (0 : Fin 4) ∉ ({2, 1} : Finset (Fin 4))) (hJ h)
    have hr' : (3 : Fin 4) ∉ J := fun h =>
      (by decide : (3 : Fin 4) ∉ ({2, 1} : Finset (Fin 4))) (hJ h)
    have h0 : CFSG.LieType.Steinberg.Adjoint.iform (τ := .D4)
        (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)
        (Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) = 0 := by
      decide +kernel
    have hp : ¬ IsRoot .D4
        (Pi.single (0 : Fin 4) (1 : ℤ) + Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hm : ¬ IsRoot .D4
        (Pi.single (0 : Fin 4) (1 : ℤ) - Pi.single (3 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hcomm : ∀ a b : SL(2, K),
        rankOne .D4 K (0 : Fin 4) a * rankOne .D4 K (3 : Fin 4) b =
          rankOne .D4 K (3 : Fin 4) b * rankOne .D4 K (0 : Fin 4) a :=
      fun a b => rankOne_commute_of_orthogonal (τ := .D4) h0 hp hm a b
    let u : Fin 4 → WeylGroup .D4 := fun i => (coxeterSystem .D4).wordProd (leviU 1 i)
    refine levi_copies_two_pow (τ := .D4) (m := 4) hn hK hρ ht (r := (0 : Fin 4))
      (r' := (3 : Fin 4)) (by decide : (0 : Fin 4) ≠ (3 : Fin 4)) hr hr' hcomm hg hgn
      (hper (0 : Fin 4))
      (hper (3 : Fin 4)) u ?_ ?_
    · intro i
      rcases leviU_hu1 i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · simpa [u] using toAction 1 i 0 0 h1
        · simpa [u] using toAction 1 i 3 3 h2
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [u] using toAction 1 i 0 3 h1
        · simpa [u] using toAction 1 i 3 0 h2
    · refine linearIndependent_translates_of_isChevType_mem (τ := .D4) hρ ht
        (v₀ := vCE' 1) ?_ u ?_
      · intro j hj
        simpa [vCE'] using reflect_vCE 1 he j (hJ hj)
      · intro i j hij h
        have h1 : (leviU 1 i).foldr (reflect .D4) (vCE' 1) =
            (leviU 1 j).foldr (reflect .D4) (vCE' 1) := by
          simpa [u, wordProd_smul_D4] using h
        have h2 := congrArg List.ofFn h1
        rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
        exact leviU_vCE_distinct 1 he i j hij h2
  ·
    have hr : (0 : Fin 4) ∉ J := fun h =>
      (by decide : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))) (hJ h)
    have hr' : (1 : Fin 4) ∉ J := fun h =>
      (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))) (hJ h)
    have h0 : CFSG.LieType.Steinberg.Adjoint.iform (τ := .D4)
        (Pi.single (0 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ)
        (Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) = 0 := by
      decide +kernel
    have hp : ¬ IsRoot .D4
        (Pi.single (0 : Fin 4) (1 : ℤ) + Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hm : ¬ IsRoot .D4
        (Pi.single (0 : Fin 4) (1 : ℤ) - Pi.single (1 : Fin 4) (1 : ℤ) : Fin Tag.D4.rank → ℤ) := by
      exact not_isRoot_of_notMem_artifactRoots (by decide +kernel)
    have hcomm : ∀ a b : SL(2, K),
        rankOne .D4 K (0 : Fin 4) a * rankOne .D4 K (1 : Fin 4) b =
          rankOne .D4 K (1 : Fin 4) b * rankOne .D4 K (0 : Fin 4) a :=
      fun a b => rankOne_commute_of_orthogonal (τ := .D4) h0 hp hm a b
    let u : Fin 4 → WeylGroup .D4 := fun i => (coxeterSystem .D4).wordProd (leviU 3 i)
    refine levi_copies_two_pow (τ := .D4) (m := 4) hn hK hρ ht (r := (0 : Fin 4))
      (r' := (1 : Fin 4)) (by decide : (0 : Fin 4) ≠ (1 : Fin 4)) hr hr' hcomm hg hgn
      (hper (0 : Fin 4))
      (hper (1 : Fin 4)) u ?_ ?_
    · intro i
      rcases leviU_hu3 i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · simpa [u] using toAction 3 i 0 0 h1
        · simpa [u] using toAction 3 i 1 1 h2
      · refine Or.inr ⟨?_, ?_⟩
        · simpa [u] using toAction 3 i 0 1 h1
        · simpa [u] using toAction 3 i 1 0 h2
    · refine linearIndependent_translates_of_isChevType_mem (τ := .D4) hρ ht
        (v₀ := vCE' 3) ?_ u ?_
      · intro j hj
        simpa [vCE'] using reflect_vCE 3 he j (hJ hj)
      · intro i j hij h
        have h1 : (leviU 3 i).foldr (reflect .D4) (vCE' 3) =
            (leviU 3 j).foldr (reflect .D4) (vCE' 3) := by
          simpa [u, wordProd_smul_D4] using h
        have h2 := congrArg List.ofFn h1
        rw [ofFn_foldr_reflectG_D4, ofFn_foldr_reflectG_D4] at h2
        exact leviU_vCE_distinct 3 he i j hij h2

end Chev

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
