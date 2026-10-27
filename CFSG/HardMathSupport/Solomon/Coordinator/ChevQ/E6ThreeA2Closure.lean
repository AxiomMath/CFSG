module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg.Adjoint CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (weylWordElt map_conj_weylWordElt_rootPair
  isRoot_wordReflect map_conj_weylElement_rootPair_adj map_subtype_rootGroup)

section Roots

@[expose] def e6A2Theta : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def e6A2ThetaNode : Fin Tag.E6.rank := ⟨5, by decide⟩

@[expose] def e6A2ThetaWord : List (Fin Tag.E6.rank) :=
  ([1, 3, 2, 0, 4, 3, 1, 2, 3, 4] : List (Fin 6))

@[expose] def e6A2ThetaReflect (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  CatLeafProof.wordReflect .E6 e6A2ThetaWord
    (reflect .E6 e6A2ThetaNode (CatLeafProof.wordReflect .E6 e6A2ThetaWord.reverse γ))

@[expose] def e6A2Pairing (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ j, Tag.cartan .E6 i j * γ j

@[expose] def e6A2Step (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  if γ e6KacNode = 2 ∨ γ e6KacNode = -2 then e6A2ThetaReflect γ
  else if 0 < e6A2Pairing (0 : Fin 6) γ * γ e6KacNode then reflect .E6 (0 : Fin 6) γ
  else if 0 < e6A2Pairing (1 : Fin 6) γ * γ e6KacNode then reflect .E6 (1 : Fin 6) γ
  else if 0 < e6A2Pairing (2 : Fin 6) γ * γ e6KacNode then reflect .E6 (2 : Fin 6) γ
  else if 0 < e6A2Pairing (4 : Fin 6) γ * γ e6KacNode then reflect .E6 (4 : Fin 6) γ
  else if 0 < e6A2Pairing (5 : Fin 6) γ * γ e6KacNode then reflect .E6 (5 : Fin 6) γ
  else γ

theorem wordReflect_e6A2ThetaWord :
    CatLeafProof.wordReflect .E6 e6A2ThetaWord (Pi.single e6A2ThetaNode 1) = e6A2Theta := by
  decide

theorem wordReflect_reverse_cancel {τ : Tag}
    (ω : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ) :
    CatLeafProof.wordReflect τ ω (CatLeafProof.wordReflect τ ω.reverse γ) = γ := by
  induction ω generalizing γ with
  | nil => rfl
  | cons i ω ih =>
    have h1 : CatLeafProof.wordReflect τ (i :: ω).reverse γ =
        CatLeafProof.wordReflect τ ω.reverse (reflect τ i γ) := by
      simp only [CatLeafProof.wordReflect, List.reverse_cons, List.foldr_append, List.foldr_cons,
        List.foldr_nil]
    rw [h1]
    change reflect τ i (CatLeafProof.wordReflect τ ω
      (CatLeafProof.wordReflect τ ω.reverse (reflect τ i γ))) = γ
    rw [ih, reflect_reflect]

theorem e6A2Step_cases (γ : Fin Tag.E6.rank → ℤ) :
    e6A2Step γ = γ ∨ e6A2Step γ = e6A2ThetaReflect γ ∨
      ∃ i, i ≠ e6KacNode ∧ e6A2Step γ = reflect .E6 i γ := by
  unfold e6A2Step
  split_ifs
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨⟨0, by decide⟩, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨1, by decide⟩, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨2, by decide⟩, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨4, by decide⟩, by decide, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨5, by decide⟩, by decide, rfl⟩)
  · exact Or.inl rfl

theorem isRoot_e6A2ThetaReflect {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    IsRoot .E6 (e6A2ThetaReflect γ) :=
  isRoot_wordReflect _ (IsRoot.reflect _ (isRoot_wordReflect _ hγ))

theorem isRoot_e6A2Step {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    IsRoot .E6 (e6A2Step γ) := by
  rcases e6A2Step_cases γ with e | e | ⟨i, -, e⟩ <;> rw [e]
  · exact hγ
  · exact isRoot_e6A2ThetaReflect hγ
  · exact IsRoot.reflect i hγ

theorem e6A2Step_iterate_root :
    ∀ k < (Tag.rootCertificate .E6).roots.length,
      ¬ (3 : ℤ) ∣ (Tag.rootCertificate .E6).root k e6KacNode →
        e6A2Step^[6] ((Tag.rootCertificate .E6).root k) = Pi.single e6KacNode 1 ∨
          e6A2Step^[6] ((Tag.rootCertificate .E6).root k) = -Pi.single e6KacNode 1 := by
  decide +kernel

theorem e6A2Step_iterate_eq {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (h3 : ¬ (3 : ℤ) ∣ β e6KacNode) :
    e6A2Step^[6] β = Pi.single e6KacNode 1 ∨ e6A2Step^[6] β = -Pi.single e6KacNode 1 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hβ
  exact e6A2Step_iterate_root k hk h3

theorem exists_mem_e6LineRoots_single :
    ∀ j : Fin Tag.E6.rank, j ≠ e6KacNode → ∃ i, Pi.single j 1 ∈ e6LineRoots i := by
  decide +kernel

theorem e6A2Theta_mem_e6LineRoots : e6A2Theta ∈ e6LineRoots 2 := by
  decide +kernel

end Roots

section Closing

noncomputable abbrev e6RootPair (K : Type) [Field K] (γ : Fin Tag.E6.rank → ℤ) :
    Subgroup (adjointGroup .E6 K) :=
  (adjDatum (rootOperatorFamily .E6) K).rootGroup γ ⊔
    (adjDatum (rootOperatorFamily .E6) K).rootGroup (-γ)

variable {K : Type} [Field K]

theorem e6RootPair_neg (γ : Fin Tag.E6.rank → ℤ) : e6RootPair K (-γ) = e6RootPair K γ := by
  rw [e6RootPair, e6RootPair, neg_neg, sup_comm]

theorem e6RootPair_wordReflect_le {M : Subgroup (adjointGroup .E6 K)}
    (ω : List (Fin Tag.E6.rank)) (hω : ∀ i ∈ ω, weylElement .E6 K i ∈ M)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h : e6RootPair K γ ≤ M) :
    e6RootPair K (CatLeafProof.wordReflect .E6 ω γ) ≤ M := by
  have hn : weylWordElt .E6 K ω ∈ M := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hω i hi
  change (adjDatum (rootOperatorFamily .E6) K).rootGroup (CatLeafProof.wordReflect .E6 ω γ) ⊔
    (adjDatum (rootOperatorFamily .E6) K).rootGroup (-CatLeafProof.wordReflect .E6 ω γ) ≤ M
  rw [← map_conj_weylWordElt_rootPair (K := K) ω hγ]
  rintro _ ⟨y, hy, rfl⟩
  exact M.mul_mem (M.mul_mem hn (h hy)) (M.inv_mem hn)

theorem e6RootPair_wordReflect_reflect_le {M : Subgroup (adjointGroup .E6 K)}
    (ω : List (Fin Tag.E6.rank)) (j : Fin Tag.E6.rank) {δ : Fin Tag.E6.rank → ℤ}
    (hδ : IsRoot .E6 δ)
    (hj : e6RootPair K (CatLeafProof.wordReflect .E6 ω (Pi.single j 1)) ≤ M)
    (h : e6RootPair K (CatLeafProof.wordReflect .E6 ω δ) ≤ M) :
    e6RootPair K (CatLeafProof.wordReflect .E6 ω (reflect .E6 j δ)) ≤ M := by
  set n := weylWordElt .E6 K ω
  set nj := weylElement .E6 K j
  have hw : nj ∈ (adjDatum (rootOperatorFamily .E6) K).rootGroup (Pi.single j 1) ⊔
      (adjDatum (rootOperatorFamily .E6) K).rootGroup (-Pi.single j 1) :=
    CFSG.LieType.Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .E6) j
  have hg : n * nj * n⁻¹ ∈ M := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hw
    rw [map_conj_weylWordElt_rootPair (K := K) ω (isRoot_single .E6 j)] at h1
    exact hj h1
  change (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (CatLeafProof.wordReflect .E6 ω (reflect .E6 j δ)) ⊔
    (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (-CatLeafProof.wordReflect .E6 ω (reflect .E6 j δ)) ≤ M
  rw [← map_conj_weylWordElt_rootPair (K := K) ω (IsRoot.reflect j hδ),
    ← map_conj_weylElement_rootPair_adj (K := K) j hδ, Subgroup.map_map]
  rintro _ ⟨z, hz, rfl⟩
  have hz' : n * z * n⁻¹ ∈ M := by
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hz
    rw [map_conj_weylWordElt_rootPair (K := K) ω hδ] at h1
    exact h h1
  have e : ((MulAut.conj n).toMonoidHom.comp (MulAut.conj nj).toMonoidHom) z =
      (n * nj * n⁻¹) * (n * z * n⁻¹) * (n * nj * n⁻¹)⁻¹ := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact M.mul_mem (M.mul_mem hg hz') (M.inv_mem hg)

theorem e6RootPair_thetaReflect_le {M : Subgroup (adjointGroup .E6 K)}
    (hθ : e6RootPair K e6A2Theta ≤ M) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ)
    (h : e6RootPair K γ ≤ M) : e6RootPair K (e6A2ThetaReflect γ) ≤ M := by
  refine e6RootPair_wordReflect_reflect_le e6A2ThetaWord e6A2ThetaNode
    (isRoot_wordReflect e6A2ThetaWord.reverse hγ) ?_ ?_
  · rw [wordReflect_e6A2ThetaWord]
    exact hθ
  · rw [wordReflect_reverse_cancel]
    exact h

theorem e6RootPair_e6A2Step_le {M : Subgroup (adjointGroup .E6 K)}
    (hL : ∀ i, i ≠ e6KacNode → weylElement .E6 K i ∈ M) (hθ : e6RootPair K e6A2Theta ≤ M)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h : e6RootPair K γ ≤ M) :
    e6RootPair K (e6A2Step γ) ≤ M := by
  rcases e6A2Step_cases γ with e | e | ⟨i, hi, e⟩ <;> rw [e]
  · exact h
  · exact e6RootPair_thetaReflect_le hθ hγ h
  · refine e6RootPair_wordReflect_le [i] (fun l hl => ?_) hγ h
    obtain rfl := List.mem_singleton.1 hl
    exact hL l hi

theorem e6RootPair_e6A2Step_iterate_le {M : Subgroup (adjointGroup .E6 K)}
    (hL : ∀ i, i ≠ e6KacNode → weylElement .E6 K i ∈ M) (hθ : e6RootPair K e6A2Theta ≤ M)
    (n : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (h : e6RootPair K γ ≤ M) :
    e6RootPair K (e6A2Step^[n] γ) ≤ M := by
  induction n generalizing γ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (isRoot_e6A2Step hγ) (e6RootPair_e6A2Step_le hL hθ hγ h)

theorem e6_eq_top_of_rankOne_le {M : Subgroup (adjointGroup .E6 K)}
    (h : ∀ i, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup i ≤ M) : M = ⊤ := by
  have hpair : ∀ γ, IsRoot .E6 γ → e6RootPair K γ ≤ M := by
    intro γ hγ
    induction hγ with
    | basis j => exact h j
    | @reflect i v hv ih =>
      refine e6RootPair_wordReflect_le [i] (fun l hl => ?_) hv ih
      obtain rfl := List.mem_singleton.1 hl
      exact h l (CFSG.LieType.Steinberg.Adjoint.weylElement_mem_rankOne
        (F := rootOperatorFamily .E6) l)
  rw [eq_top_iff, ← iSup_rootGroup_eq_top (rootOperatorFamily .E6) K]
  exact iSup₂_le fun γ hγ => le_sup_left.trans (hpair γ hγ)

theorem eq_top_of_e6RootPair_le (M : Subgroup (adjointGroup .E6 K))
    (hL : ∀ i, i ≠ e6KacNode → rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup i ≤ M)
    (hθ : e6RootPair K e6A2Theta ≤ M) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hβ3 : ¬ (3 : ℤ) ∣ β e6KacNode) (hβM : e6RootPair K β ≤ M) : M = ⊤ := by
  have hw : ∀ i, i ≠ e6KacNode → weylElement .E6 K i ∈ M := fun i hi =>
    hL i hi (CFSG.LieType.Steinberg.Adjoint.weylElement_mem_rankOne
      (F := rootOperatorFamily .E6) i)
  have h := e6RootPair_e6A2Step_iterate_le hw hθ 6 hβ hβM
  have h4 : rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup e6KacNode ≤ M := by
    rcases e6A2Step_iterate_eq hβ hβ3 with e | e
    · rw [e] at h
      exact h
    · rw [e, e6RootPair_neg] at h
      exact h
  refine e6_eq_top_of_rankOne_le fun i => ?_
  by_cases hi : i = e6KacNode
  · rw [hi]
    exact h4
  · exact hL i hi

theorem e6RootGroup_le_comap_iff {M : Subgroup (ModGL .E6 K)} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) :
    (adjDatum (rootOperatorFamily .E6) K).rootGroup γ ≤ M.comap (adjointGroup .E6 K).subtype ↔
      rootSubgroup .E6 K γ ≤ M := by
  rw [← Subgroup.map_le_iff_le_comap]
  exact iff_of_eq (congrArg (· ≤ M) (map_subtype_rootGroup (rootOperatorFamily .E6) hγ))

theorem map_conj_weylWordElt_rootSubgroup_sup (ω : List (Fin Tag.E6.rank))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    (rootSubgroup .E6 K γ ⊔ rootSubgroup .E6 K (-γ)).map
        (MulAut.conj (weylWordElt .E6 K ω : ModGL .E6 K)).toMonoidHom =
      rootSubgroup .E6 K (CatLeafProof.wordReflect .E6 ω γ) ⊔
        rootSubgroup .E6 K (-CatLeafProof.wordReflect .E6 ω γ) := by
  have hγ' := isRoot_wordReflect ω hγ
  have e : (MulAut.conj (weylWordElt .E6 K ω : ModGL .E6 K)).toMonoidHom.comp
        (adjointGroup .E6 K).subtype =
      (adjointGroup .E6 K).subtype.comp (MulAut.conj (weylWordElt .E6 K ω)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← map_subtype_rootGroup (rootOperatorFamily .E6) hγ,
    ← map_subtype_rootGroup (rootOperatorFamily .E6) (IsRoot.neg hγ), ← Subgroup.map_sup,
    Subgroup.map_map, e, ← Subgroup.map_map]
  rw [map_conj_weylWordElt_rootPair (K := K) ω hγ, Subgroup.map_sup,
    map_subtype_rootGroup (rootOperatorFamily .E6) hγ',
    map_subtype_rootGroup (rootOperatorFamily .E6) (IsRoot.neg hγ')]

theorem adjointGroup_le_of_e6A2_le (M : Subgroup (ModGL .E6 K))
    (hX : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤ M)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hβA : β ∉ ⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))
    (hβM : rootSubgroup .E6 K β ⊔ rootSubgroup .E6 K (-β) ≤ M) :
    adjointGroup .E6 K ≤ M := by
  set N := M.comap (adjointGroup .E6 K).subtype with hN
  have hΦ : ∀ {γ}, (∃ i, γ ∈ e6LineRoots i) →
      (adjDatum (rootOperatorFamily .E6) K).rootGroup γ ≤ N := by
    rintro γ ⟨i, hi⟩
    rw [hN, e6RootGroup_le_comap_iff (isRoot_of_mem_e6LineRoots hi)]
    exact (le_iSup₂_of_le γ (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 hi⟩) le_rfl).trans hX
  have hpair : ∀ {γ}, (∃ i, γ ∈ e6LineRoots i) → e6RootPair K γ ≤ N := by
    rintro γ ⟨i, hi⟩
    exact sup_le (hΦ ⟨i, hi⟩) (hΦ ⟨i, neg_mem_e6LineRoots hi⟩)
  have h3 : ¬ (3 : ℤ) ∣ β e6KacNode := by
    rw [three_dvd_iff_mem_e6LineRoots hβ]
    rintro ⟨i, hi⟩
    exact hβA (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 hi⟩)
  have hβN : e6RootPair K β ≤ N :=
    sup_le ((e6RootGroup_le_comap_iff hβ).2 (le_sup_left.trans hβM))
      ((e6RootGroup_le_comap_iff (IsRoot.neg hβ)).2 (le_sup_right.trans hβM))
  have htop : N = ⊤ :=
    eq_top_of_e6RootPair_le N (fun j hj => hpair (exists_mem_e6LineRoots_single j hj))
      (hpair ⟨2, e6A2Theta_mem_e6LineRoots⟩) hβ h3 hβN
  intro g hg
  have hgN : (⟨g, hg⟩ : adjointGroup .E6 K) ∈ N := by
    rw [htop]
    exact Subgroup.mem_top _
  exact hgN

theorem adjointGroup_le_of_e6A2_le_of_conj_le (M : Subgroup (ModGL .E6 K))
    (hX : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤ M)
    (ω : List (Fin Tag.E6.rank))
    (hω : ∃ i, ∃ γ ∈ e6LineRoots i, ∀ k, CatLeafProof.wordReflect .E6 ω γ ∉ e6LineRoots k)
    (hn : (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))).map
      (MulAut.conj (weylWordElt .E6 K ω : ModGL .E6 K)).toMonoidHom ≤ M) :
    adjointGroup .E6 K ≤ M := by
  obtain ⟨i, γ, hγi, hγ⟩ := hω
  have hγr := isRoot_of_mem_e6LineRoots hγi
  refine adjointGroup_le_of_e6A2_le M hX (isRoot_wordReflect ω hγr) ?_ ?_
  · intro hmem
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
    exact hγ k (Finset.mem_coe.1 hk)
  · rw [← map_conj_weylWordElt_rootSubgroup_sup ω hγr]
    refine (Subgroup.map_mono (sup_le ?_ ?_)).trans hn
    · exact le_iSup₂_of_le γ (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 hγi⟩) le_rfl
    · exact le_iSup₂_of_le (-γ)
        (Set.mem_iUnion.2 ⟨i, Finset.mem_coe.2 (neg_mem_e6LineRoots hγi)⟩) le_rfl

theorem eq_top_of_e6A2_le_of_conj_le (M : Subgroup (adjointGroup .E6 K))
    (hX : rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ))) ≤
      M.map (adjointGroup .E6 K).subtype)
    (ω : List (Fin Tag.E6.rank))
    (hω : ∃ i, ∃ γ ∈ e6LineRoots i, ∀ k, CatLeafProof.wordReflect .E6 ω γ ∉ e6LineRoots k)
    (hn : (rootSpan .E6 K (⋃ i, (e6LineRoots i : Set (Fin Tag.E6.rank → ℤ)))).map
      (MulAut.conj (weylWordElt .E6 K ω : ModGL .E6 K)).toMonoidHom ≤
        M.map (adjointGroup .E6 K).subtype) :
    M = ⊤ := by
  have h := adjointGroup_le_of_e6A2_le_of_conj_le _ hX ω hω hn
  refine eq_top_iff.2 fun g _ => ?_
  exact (Subgroup.mem_map_iff_mem (adjointGroup .E6 K).subtype_injective).1 (h g.2)

end Closing

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
