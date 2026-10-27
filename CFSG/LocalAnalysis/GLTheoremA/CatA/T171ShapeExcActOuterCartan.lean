module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] [CharP K 2]

private theorem pow_four_eq_one_of_char_two {c : K} (h : c ^ 4 = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hone : (-1 : K) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two]
    exact h2
  have hsq : c ^ 2 = 1 := by
    have h' : (c ^ 2) ^ 2 = 1 := by rw [← pow_mul]; norm_num at h ⊢; exact h
    rcases sq_eq_one_iff.mp h' with h1 | h1
    · exact h1
    · rwa [hone] at h1
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · exact h1
  · rwa [hone] at h1

private theorem eq_one_of_cartan_eq_one {A : Matrix ι ι ℤ} (hdet : A.det = 4)
    {x : ι → Kˣ} (hx : ∀ j, ∏ i, x i ^ A i j = 1) : x = 1 := by
  classical
  have hmain : ∀ j, x j ^ A.det = 1 := by
    intro j
    have h1 : (∏ k, (∏ i, x i ^ A i k) ^ A.adjugate k j) = x j ^ A.det := by
      calc ∏ k, (∏ i, x i ^ A i k) ^ A.adjugate k j
          = ∏ k, ∏ i, x i ^ (A i k * A.adjugate k j) := by
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← Finset.prod_zpow]
            exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
        _ = ∏ i, ∏ k, x i ^ (A i k * A.adjugate k j) := Finset.prod_comm
        _ = ∏ i, x i ^ (∑ k, A i k * A.adjugate k j) := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Finset.prod_zpow_eq_zpow_sum]
        _ = ∏ i, x i ^ ((A * A.adjugate) i j) := by
            simp only [Matrix.mul_apply]
        _ = ∏ i, x i ^ (A.det * (1 : Matrix ι ι ℤ) i j) := by
            rw [Matrix.mul_adjugate]
            simp
        _ = x j ^ A.det := by
            rw [Finset.prod_eq_single j]
            · rw [Matrix.one_apply_eq, mul_one]
            · intro i _ hi
              rw [Matrix.one_apply_ne hi, mul_zero, zpow_zero]
            · intro hj
              exact absurd (Finset.mem_univ j) hj
    rw [← h1]
    exact Finset.prod_eq_one fun k _ => by rw [hx k, one_zpow]
  funext j
  apply Units.ext
  have h4 : ((x j : K)) ^ 4 = 1 := by
    have := hmain j
    rw [hdet] at this
    exact congrArg Units.val this
  exact pow_four_eq_one_of_char_two h4

section Center

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem center_eq_bot_of_cartan_det_eq_four (i : KernelComponent χ)
    (hdet : (Matrix.of fun β γ : simpleRoots (componentRoots χ i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4) :
    Subgroup.center (componentRootSpan L χ i) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨x, hx, hxz⟩ := CFSG.StandardType.LayerCycRoot.exists_mem_ker_of_mem_center
    (K := L) (χ := χ) (i := i) hz
  have hx1 : x = 1 := by
    apply eq_one_of_cartan_eq_one hdet
    intro j
    have h := congrFun hx j
    simpa [CFSG.StandardType.LayerCycRoot.cartanHom_apply, Pi.one_apply] using h
  rw [hx1] at hxz
  have h1 : ((CFSG.StandardType.LayerCycRoot.torusDiagHom L).comp
      (CFSG.StandardType.LayerCycRoot.simpleCorootHom (componentRoots χ i))) 1 = 1 := map_one _
  rw [h1] at hxz
  exact Subtype.ext hxz.symm

end Center

section TypeD

variable {τ : Tag}

theorem exists_cartanD_of_nonInner
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (σ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hbij : Set.BijOn σ Ψ Ψ)
    (hform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ)
    (hneg : ∀ γ ∈ Ψ, σ (-γ) = -σ γ)
    (hni : ¬ twistInner Ψ σ)
    (h4 : 4 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) :
    ∃ (r : ℕ) (_ : 4 ≤ r) (e : simpleRoots Ψ ≃ Fin r),
      ∀ β γ : simpleRoots Ψ,
        corootPair (β : Fin τ.rank → ℤ) γ =
          CFSG.LieType.Universal.Spin.cartanD r (e β) (e γ) := by
  classical
  have hf : IsIsometry Ψ σ := ⟨hbij, hform, hneg⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hf' : IsIsometry Ψ fun γ => σ (w • γ) := hf.comp_smul hΨ hw
  have hΨne : Ψ.Nonempty := by
    rcases Ψ.eq_empty_or_nonempty with rfl | hne
    · exfalso
      have : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by simp [compRank]
      rw [this] at h4
      omega
    · exact hne
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      t.cartanMatrix (e β) (e γ) := fun β γ => by
    simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  set π : simpleRoots Ψ → simpleRoots Ψ := fun β =>
    ⟨σ (w • (β : Fin τ.rank → ℤ)), hf'.apply_mem_simpleRoots hΨ hpos β.2⟩ with hπ
  have hπinj : Function.Injective π := by
    intro β γ h
    have h' : σ (w • (β : Fin τ.rank → ℤ)) = σ (w • (γ : Fin τ.rank → ℤ)) :=
      congrArg Subtype.val h
    exact Subtype.ext (hf'.bijOn.injOn (simpleRoots_subset β.2) (simpleRoots_subset γ.2) h')
  set πe : simpleRoots Ψ ≃ simpleRoots Ψ :=
    Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπinj) with hπe
  set σ' : Equiv.Perm (Fin t.rank) := (e.symm.trans πe).trans e with hσ'def
  have hσ' : ∀ j, σ (w • (e.symm j : Fin τ.rank → ℤ)) = e.symm (σ' j) := fun j => by
    rw [hσ'def]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hπe, Equiv.ofBijective_apply, hπ]
  have hσ'M : ∀ i j, t.cartanMatrix (σ' i) (σ' j) = t.cartanMatrix i j := by
    intro i j
    have h1 := he' (e.symm (σ' i)) (e.symm (σ' j))
    have h2 := he' (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, ← hσ', ← hσ']
    exact corootPair_isometry hf' (simpleRoots_subset (e.symm i).2)
      (simpleRoots_subset (e.symm j).2)
  have hσ'1 : σ' ≠ 1 := by
    intro h1
    apply hni
    have hfix : ∀ β ∈ simpleRoots Ψ, σ (w • β) = β := by
      intro β hβ
      have h : σ' (e ⟨β, hβ⟩) = e ⟨β, hβ⟩ := by
        have := congrArg (fun g : Equiv.Perm (Fin t.rank) => g (e ⟨β, hβ⟩)) h1
        simpa using this
      have h2 : e.symm (e ⟨β, hβ⟩) = ⟨β, hβ⟩ := Equiv.symm_apply_apply e _
      have h3 := hσ' (e ⟨β, hβ⟩)
      rw [h2] at h3
      have h4' : e.symm (σ' (e ⟨β, hβ⟩)) = ⟨β, hβ⟩ := by
        rw [h, Equiv.symm_apply_apply]
      rw [h4'] at h3
      exact h3
    obtain ⟨u, hu, hσu⟩ := exists_smul_eq_of_isIsometry hΨ hf hw hfix
    exact ⟨u, componentWeylGroup_le Ψ hu, hσu⟩
  rcases mem_rigidTypes_or_mem_countTypes ht hr8 with hmem | hmem
  · have hok : rigidOK t = true := List.all_eq_true.1 Certificates.certificate13659.1 t hmem
    exact absurd (eq_one_of_sepB hok hσ'M) hσ'1
  · have hok : countOK t = true := List.all_eq_true.1 Certificates.certificate13659.2 t hmem
    have hN : Ψ.ncard = t.numRoots := by
      rw [ncard_eq_ncard_orbit hΨ e he', ncard_orbit_of_orbitOK hok]
    rw [hN, hrank] at hcard
    rcases numRoots_of_mem_countTypes hmem with h | h | h
    · rw [h.2] at hcard
      have hr4 : 4 ≤ t.rank := hrank ▸ h4
      exfalso
      have hsub := Nat.sub_add_cancel (show 1 ≤ t.rank by omega)
      nlinarith
    · have hcard' : t.numRoots = 2 * t.rank * (t.rank - 1) := hcard
      have htD : t = .D (compRank Ψ) := by
        rcases t with n | n | n | n | _ | _ | _ | _ | _
        · simp only [TauCeti.DynkinType.rank_A, TauCeti.DynkinType.numRoots_A] at hcard' hrank
          exfalso
          have hn1 : 1 ≤ n := by omega
          nlinarith [Nat.sub_add_cancel hn1]
        · simp only [TauCeti.DynkinType.rank_B, TauCeti.DynkinType.numRoots_B] at hcard' hrank
          exfalso
          have hn1 : 1 ≤ n := by omega
          nlinarith [Nat.sub_add_cancel hn1]
        · simp only [TauCeti.DynkinType.rank_C, TauCeti.DynkinType.numRoots_C] at hcard' hrank
          exfalso
          have hn1 : 1 ≤ n := by omega
          nlinarith [Nat.sub_add_cancel hn1]
        · simp only [TauCeti.DynkinType.rank_D] at hrank
          rw [← hrank]
        · simp only [TauCeti.DynkinType.rank_E6, TauCeti.DynkinType.numRoots_E6] at hcard'
          norm_num at hcard'
        · simp only [TauCeti.DynkinType.rank_E7, TauCeti.DynkinType.numRoots_E7] at hcard'
          norm_num at hcard'
        · simp only [TauCeti.DynkinType.rank_E8, TauCeti.DynkinType.numRoots_E8] at hcard'
          norm_num at hcard'
        · simp only [TauCeti.DynkinType.rank_F4, TauCeti.DynkinType.numRoots_F4] at hcard'
          norm_num at hcard'
        · simp only [TauCeti.DynkinType.rank_G2, TauCeti.DynkinType.numRoots_G2] at hcard'
          norm_num at hcard'
      subst htD
      refine ⟨compRank Ψ, h4, e, fun β γ => ?_⟩
      rw [he', TauCeti.DynkinType.cartanMatrix_D, ← CFSG.LieType.Universal.Spin.cartanD_eq]
      rfl
    · have hrank6 : t.rank = 6 := h.1
      have hnum : t.numRoots = 72 := h.2
      rw [hnum, hrank6] at hcard
      norm_num at hcard

theorem det_cartan_eq_four_of_nonInner
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (σ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (hbij : Set.BijOn σ Ψ Ψ)
    (hform : ∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ)
    (hneg : ∀ γ ∈ Ψ, σ (-γ) = -σ γ)
    (hni : ¬ twistInner Ψ σ)
    (h4 : 4 ≤ compRank Ψ)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) :
    (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 := by
  obtain ⟨r, hr, e, he⟩ := exists_cartanD_of_nonInner hΨ σ hbij hform hneg hni h4 hcard
  have hmat : (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ) =
      (CFSG.LieType.Universal.Spin.cartanD r).submatrix e e := by
    ext β γ
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    exact he β γ
  rw [hmat, Matrix.det_submatrix_equiv_self]
  exact CFSG.StandardType.PsiDiag.SpinP.det_cartanD (by omega)

end TypeD

section TwistKind

variable {τ : Tag} {L : Type} [Field L]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
  {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {i : KernelComponent χ}

@[expose] def TwoDOrExcRankFour {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) : Prop :=
  twistKind S.ρ (rootCharHom a) i = .twoD ∨
    (twistKind S.ρ (rootCharHom a) i = .exc ∧
      compRank (componentRoots (rootCharHom a) i) = 4)

theorem not_twistInner_of_twistKind_twoD_exc
    (h : twistKind ρ χ i = .twoD ∨
      (twistKind ρ χ i = .exc ∧ compRank (componentRoots χ i) = 4)) :
    ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)]) := by
  intro hi
  rcases h with h | ⟨h, -⟩
  · unfold twistKind at h
    rw [if_pos hi] at h
    exact TwistKind.noConfusion h
  · unfold twistKind at h
    rw [if_pos hi] at h
    exact TwistKind.noConfusion h

theorem shape_of_twistKind_twoD
    (h : twistKind ρ χ i = .twoD) :
    4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1) := by
  unfold twistKind at h
  split_ifs at h with h1 h2 h3 h4
  exact h3

theorem ncard_of_twistKind_exc_rank_four
    (h : twistKind ρ χ i = .exc) (hr : compRank (componentRoots χ i) = 4) :
    (componentRoots χ i).ncard = 24 := by
  unfold twistKind at h
  split_ifs at h with h1 h2 h3 h4
  rcases h2 with ⟨h6, _⟩ | ⟨h4, h24, _⟩
  · omega
  · simpa [hr] using h24

end TwistKind

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
