module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwoLow

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ComponentClassification.CatLeafProof CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four

@[expose] def d8Simple : Fin 8 → (Fin Tag.E8.rank → ℤ) :=
  ![![2, 2, 3, 4, 3, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]]

theorem d8Simple_isRoot : ∀ i, IsRoot .E8 (d8Simple i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  revert i
  decide +kernel

theorem d8Simple_eq_chain (j : Fin 8) :
    d8Simple j = if j = 0 then e8D8Root else Pi.single (e8D8Node j) 1 := by
  fin_cases j <;> decide +kernel

@[expose] def d8Start (i : Fin 8) (b : Bool) : Fin Tag.E8.rank → ℤ :=
  if b then d8Simple i else -d8Simple i

theorem d8Start_isRoot (i : Fin 8) (b : Bool) :
    IsRoot .E8 (d8Start i b) := by
  unfold d8Start
  split_ifs
  · exact d8Simple_isRoot i
  · exact IsRoot.neg (d8Simple_isRoot i)

@[expose] def d8Reach (l : List (Fin 8)) (δ : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  l.foldr (fun j u => u - iform (d8Simple j) u • d8Simple j) δ

@[expose] def d8Table : List (Fin 8 × Bool × List (Fin 8)) :=
  [    (0, false, [1, 2, 3, 4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, false, [2, 3, 4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, false, [3, 4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, false, [4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, false, [5, 7, 6, 5, 4, 3, 2, 1]),
    (0, false, [7, 6, 5, 4, 3, 2, 1]),
    (0, false, [7, 5, 4, 3, 2, 1]),
    (0, false, [6, 5, 4, 3, 2, 1]),
    (0, false, [5, 4, 3, 2, 1]),
    (0, false, [4, 3, 2, 1]),
    (0, false, [3, 2, 1]),
    (0, false, [2, 1]),
    (0, false, [1]),
    (0, false, []),
    (1, false, [2, 3, 4, 5, 7, 6, 5, 4, 3, 2]),
    (1, false, [3, 4, 5, 7, 6, 5, 4, 3, 2]),
    (2, false, [3, 4, 5, 7, 6, 5, 4, 3]),
    (1, false, [4, 5, 7, 6, 5, 4, 3, 2]),
    (2, false, [4, 5, 7, 6, 5, 4, 3]),
    (3, false, [4, 5, 7, 6, 5, 4]),
    (1, false, [5, 7, 6, 5, 4, 3, 2]),
    (2, false, [5, 7, 6, 5, 4, 3]),
    (3, false, [5, 7, 6, 5, 4]),
    (4, false, [5, 7, 6, 5]),
    (1, false, [7, 6, 5, 4, 3, 2]),
    (2, false, [7, 6, 5, 4, 3]),
    (3, false, [7, 6, 5, 4]),
    (4, false, [7, 6, 5]),
    (5, false, [7, 6]),
    (1, false, [7, 5, 4, 3, 2]),
    (2, false, [7, 5, 4, 3]),
    (3, false, [7, 5, 4]),
    (4, false, [7, 5]),
    (5, false, [7]),
    (7, false, []),
    (1, false, [6, 5, 4, 3, 2]),
    (2, false, [6, 5, 4, 3]),
    (3, false, [6, 5, 4]),
    (4, false, [6, 5]),
    (5, false, [6]),
    (6, false, []),
    (1, false, [5, 4, 3, 2]),
    (2, false, [5, 4, 3]),
    (3, false, [5, 4]),
    (4, false, [5]),
    (5, false, []),
    (1, false, [4, 3, 2]),
    (2, false, [4, 3]),
    (3, false, [4]),
    (4, false, []),
    (1, false, [3, 2]),
    (2, false, [3]),
    (3, false, []),
    (1, false, [2]),
    (2, false, []),
    (1, false, []),
    (1, true, []),
    (2, true, []),
    (1, true, [2]),
    (3, true, []),
    (2, true, [3]),
    (1, true, [3, 2]),
    (4, true, []),
    (3, true, [4]),
    (2, true, [4, 3]),
    (1, true, [4, 3, 2]),
    (5, true, []),
    (4, true, [5]),
    (3, true, [5, 4]),
    (2, true, [5, 4, 3]),
    (1, true, [5, 4, 3, 2]),
    (6, true, []),
    (5, true, [6]),
    (4, true, [6, 5]),
    (3, true, [6, 5, 4]),
    (2, true, [6, 5, 4, 3]),
    (1, true, [6, 5, 4, 3, 2]),
    (7, true, []),
    (5, true, [7]),
    (4, true, [7, 5]),
    (3, true, [7, 5, 4]),
    (2, true, [7, 5, 4, 3]),
    (1, true, [7, 5, 4, 3, 2]),
    (5, true, [7, 6]),
    (4, true, [7, 6, 5]),
    (3, true, [7, 6, 5, 4]),
    (2, true, [7, 6, 5, 4, 3]),
    (1, true, [7, 6, 5, 4, 3, 2]),
    (4, true, [5, 7, 6, 5]),
    (3, true, [5, 7, 6, 5, 4]),
    (2, true, [5, 7, 6, 5, 4, 3]),
    (1, true, [5, 7, 6, 5, 4, 3, 2]),
    (3, true, [4, 5, 7, 6, 5, 4]),
    (2, true, [4, 5, 7, 6, 5, 4, 3]),
    (1, true, [4, 5, 7, 6, 5, 4, 3, 2]),
    (2, true, [3, 4, 5, 7, 6, 5, 4, 3]),
    (1, true, [3, 4, 5, 7, 6, 5, 4, 3, 2]),
    (1, true, [2, 3, 4, 5, 7, 6, 5, 4, 3, 2]),
    (0, true, []),
    (0, true, [1]),
    (0, true, [2, 1]),
    (0, true, [3, 2, 1]),
    (0, true, [4, 3, 2, 1]),
    (0, true, [5, 4, 3, 2, 1]),
    (0, true, [6, 5, 4, 3, 2, 1]),
    (0, true, [7, 5, 4, 3, 2, 1]),
    (0, true, [7, 6, 5, 4, 3, 2, 1]),
    (0, true, [5, 7, 6, 5, 4, 3, 2, 1]),
    (0, true, [4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, true, [3, 4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, true, [2, 3, 4, 5, 7, 6, 5, 4, 3, 2, 1]),
    (0, true, [1, 2, 3, 4, 5, 7, 6, 5, 4, 3, 2, 1])]

theorem d8Table_spec :
    ∀ β ∈ rootFinset .E8, β 0 % 2 = 0 →
      ∃ e ∈ d8Table, d8Reach e.2.2 (d8Start e.1 e.2.1) = β := by
  decide +kernel

variable {K : Type} [Field K]

abbrev d8Target (K : Type) [Field K] : Subgroup (ModGL .E8 K) :=
  (⨆ k, e8D8Chain K k).map (adjointGroup .E8 K).subtype

theorem rootSubgroup_le_map_of_rootPair_le {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot .E8 γ) {M : Subgroup (adjointGroup .E8 K)} (h : rootPairE8 K γ ≤ M) :
    rootSubgroup Tag.E8 K γ ≤ M.map (adjointGroup .E8 K).subtype := by
  intro x hx
  have hxA : x ∈ adjointGroup Tag.E8 K := rootSubgroup_le_adjointGroup γ hx
  refine ⟨⟨x, hxA⟩, ?_, rfl⟩
  have hmem : (⟨x, hxA⟩ : adjointGroup Tag.E8 K) ∈
      (rootSubgroup Tag.E8 K γ).subgroupOf (adjointGroup Tag.E8 K) :=
    Subgroup.mem_subgroupOf.2 hx
  rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8) hγ] at hmem
  exact h (Subgroup.mem_sup_left hmem)

theorem rootPairE8_neg (γ : Fin Tag.E8.rank → ℤ) :
    rootPairE8 K (-γ) = rootPairE8 K γ := by
  rw [rootPairE8, rootPairE8, neg_neg, sup_comm]

theorem rootSubgroup_reflect_le_of_rootPair_le
    {M : Subgroup (ModGL .E8 K)} {γ δ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot .E8 γ)
    (hpair : rootSubgroup Tag.E8 K γ ⊔ rootSubgroup Tag.E8 K (-γ) ≤ M)
    (hδ : IsRoot .E8 δ) (h : rootSubgroup Tag.E8 K δ ≤ M) :
    rootSubgroup Tag.E8 K (δ - iform γ δ • γ) ≤ M := by
  set s := rootReflection γ with hs
  have hsδ : s • δ = δ - iform γ δ • γ :=
    rootReflection_smul_SL (τ := .E8) (fun β hβ => iform_self_of_isRoot_E8Fr hβ) hγ δ
  rw [← hsδ]
  obtain ⟨hnU, hnN, hnM⟩ := rootWeylOne_spec (K := K) hγ
  set n := rootWeylOne Tag.E8 K γ
  have hnD : n ∈ M := hpair hnU
  intro x hx
  have hconj := conj_mem_rootSpan_of_mapsRootLines (inv_mem hnN) hnM.inv
    (S := {s • δ}) (fun α hα => by rw [Set.mem_singleton_iff.1 hα]; exact IsRoot.smul hδ s)
    (rootSubgroup_le_rootSpan (Set.mem_singleton _) hx)
  rw [Set.image_singleton, inv_smul_smul, inv_inv] at hconj
  have hle : rootSpan Tag.E8 K {δ} ≤ M :=
    iSup₂_le fun β hβ => by rw [Set.mem_singleton_iff.1 hβ]; exact h
  have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [hx']
  exact mul_mem (mul_mem hnD (hle hconj)) (inv_mem hnD)

theorem rootSubgroup_d8Start_le (i : Fin 8) (b : Bool) :
    rootSubgroup Tag.E8 K (d8Start i b) ≤ d8Target K := by
  have hroot : IsRoot .E8 (d8Start i b) := d8Start_isRoot i b
  have hmem : rootPairE8 K (d8Simple i) ≤ ⨆ k, e8D8Chain K k := by
    by_cases hi : i = 0
    · subst hi
      have h0 : d8Simple 0 = e8D8Root := by rw [d8Simple_eq_chain 0, if_pos rfl]
      rw [h0]
      exact (le_of_eq (e8D8Chain_zero_eq (K := K)).symm).trans
        (le_iSup (fun k => e8D8Chain K k) 0)
    · have h0 : d8Simple i = Pi.single (e8D8Node i) 1 := by
        rw [d8Simple_eq_chain i, if_neg hi]
      rw [h0, ← e8D8Chain_ne_zero_eq (K := K) hi]
      exact le_iSup (fun k => e8D8Chain K k) i
  have hpair : rootPairE8 K (d8Start i b) ≤ ⨆ k, e8D8Chain K k := by
    unfold d8Start
    split_ifs
    · exact hmem
    · rwa [rootPairE8_neg]
  exact rootSubgroup_le_map_of_rootPair_le hroot hpair

theorem rootSubgroup_d8Simple_pair_le (j : Fin 8) :
    rootSubgroup Tag.E8 K (d8Simple j) ⊔ rootSubgroup Tag.E8 K (-(d8Simple j)) ≤
      d8Target K := by
  refine sup_le (rootSubgroup_d8Start_le (K := K) j true) ?_
  have h := rootSubgroup_d8Start_le (K := K) j false
  simpa [d8Start] using h

theorem rootSubgroup_d8Reach_le
    (l : List (Fin 8)) {δ : Fin Tag.E8.rank → ℤ} (hδ : IsRoot .E8 δ)
    (h : rootSubgroup Tag.E8 K δ ≤ d8Target K) :
    IsRoot .E8 (d8Reach l δ) ∧ rootSubgroup Tag.E8 K (d8Reach l δ) ≤ d8Target K := by
  induction l with
  | nil => exact ⟨hδ, h⟩
  | cons j l ih =>
    obtain ⟨hr, hle⟩ := ih
    have hstep : d8Reach (j :: l) δ =
        d8Reach l δ - iform (d8Simple j) (d8Reach l δ) • d8Simple j := rfl
    rw [hstep]
    refine ⟨?_, rootSubgroup_reflect_le_of_rootPair_le (d8Simple_isRoot j)
      (rootSubgroup_d8Simple_pair_le j) hr hle⟩
    rw [← rootReflection_smul_SL (τ := .E8) (fun β hβ => iform_self_of_isRoot_E8Fr hβ)
      (d8Simple_isRoot j)]
    exact IsRoot.smul hr _

theorem rootSpan_kernelRoots_d8Char_le_d8Chain :
    rootSpan Tag.E8 K (kernelRoots d8Char) ≤ d8Target K := by
  refine iSup₂_le fun β hβ => ?_
  have h0 : β 0 % 2 = 0 := (d8Char_eq_one_iff β).1 hβ.2
  obtain ⟨e, -, he2⟩ := d8Table_spec β (mem_rootFinset.2 hβ.1) h0
  have hstart : IsRoot .E8 (d8Start e.1 e.2.1) := d8Start_isRoot ..
  rw [← he2]
  exact (rootSubgroup_d8Reach_le e.2.2 hstart
    (rootSubgroup_d8Start_le e.1 e.2.1)).2

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Four
