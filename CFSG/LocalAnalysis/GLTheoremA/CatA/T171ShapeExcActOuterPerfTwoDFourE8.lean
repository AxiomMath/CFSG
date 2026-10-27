module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourStableStab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourGraph
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignTori
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice

theorem linearIndependent_rat_of_real {ι : Type} [Fintype ι] {n : ℕ}
    {b : ι → (Fin n → ℤ)}
    (h : LinearIndependent ℝ (fun j => fun i => (b j i : ℝ))) :
    LinearIndependent ℚ (fun j => fun i => (b j i : ℚ)) := by
  have hQ : LinearIndependent ℚ (fun j => fun i => ((b j i : ℚ) : ℝ)) := by
    simpa using h.restrict_scalars' (R := ℚ)
  exact LinearIndependent.of_comp (Pi.algebraMap (Fin n) ℚ ℝ) hQ

section CertificatesThirtyFour


theorem rho_smul_map_rootReflection {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {ι : Type} (l : List ι) (v : ι → Fin τ.rank → ℤ)
    (hroot : ∀ k ∈ l, IsRoot τ (v k)) (x : Fin τ.rank → ℤ) :
    S.ρ ((l.map fun k => rootReflection (v k)).prod • x) =
      (l.map fun k => rootReflection (S.ρ (v k))).prod • S.ρ x := by
  induction l generalizing x with
  | nil => simp
  | cons k l ih =>
    have hβ : IsRoot τ (v k) := hroot k List.mem_cons_self
    have hρβ : IsRoot τ (S.ρ (v k)) := (S.frob.isRoot_iff (v k)).2 hβ
    calc S.ρ ((List.map (fun j => rootReflection (v j)) (k :: l)).prod • x)
        = S.ρ (rootReflection (v k) • ((l.map fun j => rootReflection (v j)).prod • x)) := by
          rw [List.map_cons, List.prod_cons, mul_smul]
      _ = rootReflection (S.ρ (v k)) •
            S.ρ ((l.map fun j => rootReflection (v j)).prod • x) :=
          map_rootReflection_smul (δ := S.rhoHom) S.frob.iform_eq hβ hρβ _
      _ = rootReflection (S.ρ (v k)) •
            ((l.map fun j => rootReflection (S.ρ (v j))).prod • S.ρ x) := by
          rw [ih (fun j hj => hroot j (List.mem_cons_of_mem _ hj))]
      _ = ((List.map (fun j => rootReflection (S.ρ (v j))) (k :: l)).prod) • S.ρ x := by
          rw [List.map_cons, List.prod_cons, mul_smul]

theorem linearIndependent_toRat_simpleRoots_rhoImage {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ)
    (horth : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform γ (S.ρ δ) = 0) :
    LinearIndependent ℚ (fun x : simpleRoots Ψ ⊕ simpleRoots Ψ =>
      fun k => ((Sum.elim (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ))
        (fun β : simpleRoots Ψ => S.ρ (β : Fin τ.rank → ℤ)) x) k : ℚ)) :=
  linearIndependent_rat_of_real (linearIndependent_toReal_simpleRoots_rhoImage S hΨ horth)

end CertificatesThirtyFour

section CertificatesTwo


theorem exists_simpleRoot_iform_ne_zero_E8 {γ : Fin Tag.E8.rank → ℤ} (hne : γ ≠ 0) :
    ∃ i : Fin Tag.E8.rank, iform γ (Pi.single i 1) ≠ 0 := by
  by_contra h
  push Not at h
  have hγsum : γ = ∑ i : Fin Tag.E8.rank, γ i • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  have hsum : iform (∑ i : Fin Tag.E8.rank,
      γ i • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) γ = 0 := by
    rw [iform_finset_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [iform_smul_left, iform_comm, h i, mul_zero]
  have h0 : iform γ γ = 0 := by
    simpa only [← hγsum] using hsum
  exact hne (eq_zero_of_iform_self_eq_zero h0)

theorem kernelComponent_subsingleton_of_kernelRoots_all_E8 {L : Type} [Field L]
    {χ : Multiplicative (Fin Tag.E8.rank → ℤ) →* Lˣ}
    (hker : kernelRoots χ = {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ}) :
    Subsingleton (KernelComponent χ) := by
  classical
  have hsingle : ∀ i : Fin Tag.E8.rank,
      (Pi.single i 1 : Fin Tag.E8.rank → ℤ) ∈ kernelRoots χ := by
    intro i
    rw [hker]
    exact IsRoot.basis i
  let cls : Fin Tag.E8.rank → KernelComponent χ := fun i => ⟦⟨Pi.single i 1, hsingle i⟩⟧
  have hedge : ∀ i j : Fin Tag.E8.rank, Tag.cartan .E8 i j ≠ 0 → cls i = cls j := by
    intro i j hij
    apply mk_eq_of_iform_ne_zero (α := ⟨Pi.single i 1, hsingle i⟩)
      (β := ⟨Pi.single j 1, hsingle j⟩)
    show iform (Pi.single i 1 : Fin Tag.E8.rank → ℤ) (Pi.single j 1) ≠ 0
    rwa [CFSG.SeitzReduction.E8Pilot.iform_single_single_E8]
  have h1 : cls 1 = cls 0 := (hedge 1 3 (by decide)).trans
    ((hedge 3 2 (by decide)).trans (hedge 2 0 (by decide)))
  have h2 : cls 2 = cls 0 := hedge 2 0 (by decide)
  have h3 : cls 3 = cls 0 := (hedge 3 2 (by decide)).trans (hedge 2 0 (by decide))
  have h4 : cls 4 = cls 0 := (hedge 4 3 (by decide)).trans h3
  have h5 : cls 5 = cls 0 := (hedge 5 4 (by decide)).trans h4
  have h6 : cls 6 = cls 0 := (hedge 6 5 (by decide)).trans h5
  have h7 : cls 7 = cls 0 := (hedge 7 6 (by decide)).trans h6
  have hchain : ∀ i, cls i = cls 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  have hclass : ∀ a : kernelRoots χ, (⟦a⟧ : KernelComponent χ) = cls 0 := by
    intro a
    obtain ⟨i, hi⟩ := exists_simpleRoot_iform_ne_zero_E8 (γ := (a : Fin Tag.E8.rank → ℤ))
      (fun h => a.2.1.ne_zero h)
    have e : (⟦a⟧ : KernelComponent χ) = ⟦⟨Pi.single i 1, hsingle i⟩⟧ :=
      mk_eq_of_iform_ne_zero (α := a) (β := ⟨Pi.single i 1, hsingle i⟩) (by
        show iform (a : Fin Tag.E8.rank → ℤ) (Pi.single i 1) ≠ 0
        exact hi)
    rw [e]
    exact hchain i
  refine ⟨fun i j => ?_⟩
  obtain ⟨a, rfl⟩ := Quotient.exists_rep i
  obtain ⟨b, rfl⟩ := Quotient.exists_rep j
  rw [hclass a, hclass b]

end CertificatesTwo

section CertificatesThirtyFive


theorem exists_cartanD_labelling_of_twistKind_twoD_rank_four {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    ∃ e : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin 4,
      ∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD 4 (e β) (e γ) := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨h4le, hcard⟩ := shape_of_twistKind_twoD hkind
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  have hiso := outer_isIsometry_rho S hs
  have hni := not_twistInner_of_twistKind_twoD_exc (Or.inl hkind)
  obtain ⟨r, hr, e, he⟩ := exists_cartanD_of_nonInner hΨ
    ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ])
    hiso.bijOn hiso.iform_eq hiso.neg hni h4le hcard
  have hcardΔ : (simpleRoots Ψ).card = r := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hr4 : r = 4 := by
    have hcomp := compRank_eq_card hΨ
    omega
  subst hr4
  exact ⟨e, he⟩

theorem exists_neg_mem_charStabilizer_of_image_ne {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i j : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4)
    (hj : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) j)
    (hji : j ≠ i) :
    ∃ w ∈ charStabilizer (rootCharHom a), ∀ γ : Fin τ.rank → ℤ, w • γ = -γ := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨e, he⟩ := exists_cartanD_labelling_of_twistKind_twoD_rank_four S hT i hkind h4
  let w1 : WeylGroup τ :=
    (twoDFourNegWord.map (fun k => rootReflection (e.symm k : Fin τ.rank → ℤ))).prod
  have hw1 : w1 ∈ componentWeylGroup Ψ ∧ ∀ γ ∈ Ψ, w1 • γ = -γ := twoDFourWord_spec hΨ e he
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ componentRoots (rootCharHom a) j := fun γ hγ => by
    rw [← hj]
    exact ⟨γ, hγ, rfl⟩
  let w2 : WeylGroup τ :=
    (twoDFourNegWord.map (fun k => rootReflection (S.ρ (e.symm k : Fin τ.rank → ℤ)))).prod
  have hw2mem : w2 ∈ componentWeylGroup (componentRoots (rootCharHom a) j) :=
    Subgroup.list_prod_mem _ <| List.forall_mem_map.2 fun k _ =>
      rootReflection_mem_componentWeylGroup_of_mem
        (isRootComponent_componentRoots (χ := rootCharHom a) j)
        (hρΨ _ (simpleRoots_subset (e.symm k).2))
  have hw1stab : w1 ∈ charStabilizer (rootCharHom a) :=
    Subgroup.list_prod_mem _ <| List.forall_mem_map.2 fun k _ =>
      rootReflection_mem_charStabilizer (simpleRoots_subset (e.symm k).2).1
  have hw2stab : w2 ∈ charStabilizer (rootCharHom a) :=
    Subgroup.list_prod_mem _ <| List.forall_mem_map.2 fun k _ =>
      rootReflection_mem_charStabilizer (hρΨ _ (simpleRoots_subset (e.symm k).2)).1
  have hw2neg : ∀ γ ∈ Ψ, w2 • S.ρ γ = -(S.ρ γ) := by
    intro γ hγ
    have hρeq : S.ρ (w1 • γ) = w2 • S.ρ γ :=
      rho_smul_map_rootReflection S twoDFourNegWord
        (fun k => (e.symm k : Fin τ.rank → ℤ))
        (fun k _ => simpleRoots_isRoot (e.symm k).2) γ
    rw [← hρeq, hw1.2 γ hγ, S.frob.neg_eq]
  have horth : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform γ (S.ρ δ) = 0 := by
    intro γ hγ δ hδ
    exact iform_eq_zero_of_mem_componentRoots (Ne.symm hji) hγ (hρΨ δ hδ)
  let b : simpleRoots Ψ ⊕ simpleRoots Ψ → Fin τ.rank → ℤ :=
    Sum.elim (fun β : simpleRoots Ψ => (β : Fin τ.rank → ℤ))
      (fun β : simpleRoots Ψ => S.ρ (β : Fin τ.rank → ℤ))
  have hbasis : LinearIndependent ℚ (fun x => fun k => (b x k : ℚ)) := by
    simpa only [b] using linearIndependent_toRat_simpleRoots_rhoImage S hΨ horth
  have hτ8 : τ.rank = 8 :=
    le_antisymm (rank_le_eight τ) (eight_le_rank_of_image_ne S hT i j hji hj h4)
  have hcard : Fintype.card (simpleRoots Ψ ⊕ simpleRoots Ψ) = τ.rank := by
    rw [Fintype.card_sum, Fintype.card_coe, ← compRank_eq_card hΨ, h4, hτ8]
  have hnegall : ∀ γ : Fin τ.rank → ℤ, (w2 * w1) • γ = -γ := by
    refine smul_eq_neg_of_basis' hcard b hbasis ?_
    rintro (β | β)
    · have hb : b (Sum.inl β) = (β : Fin τ.rank → ℤ) := rfl
      rw [hb, mul_smul, hw1.2 β (simpleRoots_subset β.2), smul_neg,
        smul_eq_of_mem_componentWeylGroup (Ne.symm hji) hw2mem (simpleRoots_subset β.2)]
    · have hb : b (Sum.inr β) = S.ρ (β : Fin τ.rank → ℤ) := rfl
      rw [hb, mul_smul,
        smul_eq_of_mem_componentWeylGroup hji hw1.1 (hρΨ β (simpleRoots_subset β.2))]
      exact hw2neg β (simpleRoots_subset β.2)
  exact ⟨w2 * w1, mul_mem hw2stab hw1stab, hnegall⟩

theorem rankFourTwoDE8Stable_holds : RankFourTwoDE8Stable := by
  intro L _ _ _ p S a hT i hkind h4
  classical
  obtain ⟨j, hj⟩ := outer_exists_image_component S hT i
  by_cases hji : j = i
  · rw [hj, hji]
  · exfalso
    obtain ⟨w, hwstab, hneg⟩ :=
      exists_neg_mem_charStabilizer_of_image_ne S hT i j hkind h4 hj hji
    have hker : kernelRoots (rootCharHom a) = {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ} := by
      ext γ
      exact ⟨fun h => h.1, fun hγ =>
        ⟨hγ, rootChar_eq_one_of_mem_charStabilizer_neg hwstab hneg γ⟩⟩
    haveI : Subsingleton (KernelComponent (rootCharHom a)) :=
      kernelComponent_subsingleton_of_kernelRoots_all_E8 hker
    exact hji (Subsingleton.elim j i)

end CertificatesThirtyFive

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
