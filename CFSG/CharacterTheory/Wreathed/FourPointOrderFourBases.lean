module

public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourSupport
public import CFSG.CharacterTheory.Wreathed.OddClassRestrictionBasis
public import CFSG.CharacterTheory.Wreathed.NormalComplementQuotientBlock

public noncomputable section

namespace CFSG.Wreathed.FourPointOrderFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FourPointCompleteModel

open scoped Classical Matrix

structure OddRestrictionComplexBasis {E : Type} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (B : Finset basis.index)
    (b : Fin 2 → OddElements E → ℂ) (gram : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  linearIndependent : LinearIndependent ℂ b
  span_eq : Submodule.span ℂ (Set.range b) =
    (Submodule.span ℂ ((fun χ => (basis.representation χ).character) '' (B : Set basis.index))).map
      (LinearMap.funLeft ℂ ℂ (Subtype.val : OddElements E → E))
  rows : ∃ D : Matrix B (Fin 2) ℤ, (∀ (χ : B) (α : Fin 2 → ℂ),
      (∀ g : OddElements E, (basis.representation χ).character g = ∑ j, α j * b j g) ↔
        ∀ j, α j = D χ j) ∧ Dᵀ * D = gram

theorem oddRestrictionComplexBasis_of_inflation {E K : Type} [Group E] [Fintype E] [Group K]
    [Fintype K] (f : E →* K) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (basisE : FiniteIrreducibleCharacterBasis E) (basisK : FiniteIrreducibleCharacterBasis K)
    (B : Finset basisE.index)
    (hB : ∀ χ, χ ∈ B ↔ ∃ θ : basisK.index,
      (basisE.representation χ).character = (basisK.representation θ).character ∘ f)
    (v : K) (hv : orderOf v = 3) (hconj : ∀ g : K, g ≠ 1 → Odd (orderOf g) → IsConj g v)
    (hK : Nat.card K = 96) (hc : Nat.card (Subgroup.centralizer {v}) = 12)
    (P : E → Prop) [DecidablePred P] (hP : ∀ g, P g ↔ f g = 1) :
    OddRestrictionComplexBasis basisE B
      ![fun _ => 1, fun g => 3 * (if P g then 1 else 0) - 1] !![16, 8; 8, 12] := by
  obtain ⟨hrestr, hindep, -, -, D, -, hDiff, -, hgram⟩ :=
    single_order_three_odd_class_integral_restriction_basis basisK v hv hconj
  set bE : Fin 2 → OddElements E → ℂ :=
    ![fun _ => 1, fun g => 3 * (if P g then 1 else 0) - 1] with hbEdef
  set bK := oddClassRestrictionBasis K with hbKdef
  have hι : Function.Surjective (oddElementsMap f) := oddElementsMap_surjective f hf hker
  have hbE : ∀ j g, bE j g = bK j (oddElementsMap f g) := by
    intro j g
    fin_cases j
    · rfl
    · simp only [hbEdef, hbKdef, oddClassRestrictionBasis, oddElementsMap, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      by_cases h : P g
      · rw [ite_eq_left h, ite_eq_left ((hP g).mp h)]
        norm_num
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hP g).mpr h'))]
        norm_num
  set Pull : (OddElements K → ℂ) →ₗ[ℂ] (OddElements E → ℂ) :=
    LinearMap.funLeft ℂ ℂ (oddElementsMap f) with hPull
  have hPull_inj : Function.Injective Pull :=
    LinearMap.funLeft_injective_of_surjective _ _ _ hι
  have hbE_eq : bE = Pull ∘ bK := by
    funext j g
    exact hbE j g
  have hlab : ∀ χ : B, ∃ θ : basisK.index,
      (basisE.representation χ).character = (basisK.representation θ).character ∘ f :=
    fun χ => (hB χ).mp χ.2
  choose θ hθ using hlab
  have hθinj : Function.Injective θ := by
    intro χ χ' h
    apply Subtype.ext
    apply basisE.distinct
    change (basisE.representation χ).character = (basisE.representation χ').character
    rw [hθ, hθ, h]
  have hθsurj : Function.Surjective θ := by
    intro θ'
    obtain ⟨χ, hχ⟩ := exists_label_comp_surjective basisK basisE f hf θ'
    have hχB : χ ∈ B := (hB χ).mpr ⟨θ', hχ⟩
    refine ⟨⟨χ, hχB⟩, basisK.distinct ?_⟩
    apply hf.injective_comp_right
    change (basisK.representation (θ ⟨χ, hχB⟩)).character ∘ f =
      (basisK.representation θ').character ∘ f
    rw [← hθ, hχ]
  set eB : B ≃ basisK.index := Equiv.ofBijective θ ⟨hθinj, hθsurj⟩ with heB
  have hrow : ∀ (χ : B) (α : Fin 2 → ℂ),
      (∀ g : OddElements E, (basisE.representation χ).character g = ∑ j, α j * bE j g) ↔
        ∀ j, α j = D (θ χ) j := by
    intro χ α
    rw [← hDiff (θ χ) α]
    constructor
    · intro h k
      obtain ⟨g, rfl⟩ := hι k
      have hg := h g
      rw [hθ χ] at hg
      simp only [Function.comp_apply, hbE] at hg
      exact hg
    · intro h g
      rw [hθ χ]
      simp only [Function.comp_apply, hbE]
      exact h (oddElementsMap f g)
  refine ⟨?_, ?_, ⟨D.submatrix eB id, hrow, ?_⟩⟩
  · rw [hbE_eq]
    exact hindep.map' Pull (LinearMap.ker_eq_bot.mpr hPull_inj)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      obtain ⟨fj, hclass, hfj⟩ := hrestr j
      set c : basisK.index → ℂ := fun θ' =>
        characterPairing fj (basisK.representation θ').character with hc
      refine ⟨∑ θ', c θ' • (basisE.representation (eB.symm θ' : basisE.index)).character, ?_, ?_⟩
      · refine Submodule.sum_mem _ fun θ' _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact ⟨(eB.symm θ' : basisE.index), (eB.symm θ').2, rfl⟩
      · funext g
        have hsymm : ∀ θ', (basisE.representation (eB.symm θ' : basisE.index)).character =
            (basisK.representation θ').character ∘ f := by
          intro θ'
          have h := hθ (eB.symm θ')
          have h2 : θ (eB.symm θ') = θ' := eB.apply_symm_apply θ'
          rw [h2] at h
          exact h
        simp only [LinearMap.funLeft_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hsymm,
          Function.comp_apply]
        rw [hbE, ← hfj, finiteIrreducibleCharacterBasis_reconstruction basisK fj hclass]
        rfl
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨χ, hχ, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have hexp := (hrow ⟨χ, hχ⟩ fun j => (D (θ ⟨χ, hχ⟩) j : ℂ)).mpr fun j => rfl
      have hfun : LinearMap.funLeft ℂ ℂ (Subtype.val : OddElements E → E)
          (basisE.representation χ).character =
            ∑ j, (D (θ ⟨χ, hχ⟩) j : ℂ) • bE j := by
        funext g
        simp only [LinearMap.funLeft_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact hexp g
      rw [hfun]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    exact hgram hK hc

theorem orderFour_principal_block {G : Type} [Group G] [Fintype G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) [Fintype (centralizerOddCoreQuotient n S e)]
    (Q : Subgroup (centralizerOddCoreQuotient n S e)) [Q.Normal] (hQ : IsPGroup 2 Q)
    (hcent : Subgroup.centralizer (Q : Set (centralizerOddCoreQuotient n S e)) ≤ Q)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (basisC : FiniteIrreducibleCharacterBasis (orderFourCentralizer n S e))
    (principalC : basisC.index)
    (hprincipalC : (basisC.representation principalC).character = 1) :
    (∀ χ, χ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC ↔
      ∃ θ : basisH.index, (basisC.representation χ).character =
        (basisH.representation θ).character ∘ orderFourMap n S e) ∧
    ∀ θ : basisH.index, ∃ χ ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal)
      principalC, (basisC.representation χ).character =
        (basisH.representation θ).character ∘ orderFourMap n S e := by
  obtain ⟨η, hη⟩ := exists_orderFour_quotient_equiv n hn S e
  obtain ⟨basisQ⟩ := finiteIrreducibleCharacterBasis_exists
    (G := orderFourCentralizer n S e ⧸ CFSG.oddCore (orderFourCentralizer n S e))
  obtain ⟨labelQ, -⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisQ
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  have hone := coefficientBlock_eq_univ_of_equiv η Q hQ hcent ideal basisQ labelQ
  have hR : ¬ 2 ∣ Nat.card (CFSG.oddCore (orderFourCentralizer n S e)) :=
    (CFSG.ComponentClassification.OddCore.odd_card _).not_two_dvd_nat
  obtain ⟨-, hiff, hsurj, -⟩ := normal_prime_complement_unique_quotient_principal_block basisC
    ideal 2 principalC hprincipalC (CFSG.oddCore (orderFourCentralizer n S e)) hR basisQ labelQ
    hone
  have hQH := exists_label_comp_surjective basisQ basisH η.symm.toMonoidHom η.symm.surjective
  have hHQ := exists_label_comp_surjective basisH basisQ η.toMonoidHom η.surjective
  refine ⟨fun χ => ⟨fun hχ => ?_, fun ⟨θ, hθ⟩ => ?_⟩, fun θ => ?_⟩
  · obtain ⟨θ', hθ'⟩ := (hiff χ).mp hχ
    obtain ⟨θ, hθ⟩ := hQH θ'
    refine ⟨θ, ?_⟩
    rw [hθ', hθ]
    funext c
    change (basisQ.representation θ').character (c : orderFourCentralizer n S e ⧸
      CFSG.oddCore (orderFourCentralizer n S e)) =
        (basisQ.representation θ').character (η.symm (orderFourMap n S e c))
    rw [← hη c, MulEquiv.symm_apply_apply]
  · obtain ⟨θ', hθ'⟩ := hHQ θ
    refine (hiff χ).mpr ⟨θ', ?_⟩
    rw [hθ, hθ']
    funext c
    change (basisH.representation θ).character (orderFourMap n S e c) =
      (basisH.representation θ).character (η (c : orderFourCentralizer n S e ⧸
        CFSG.oddCore (orderFourCentralizer n S e)))
    rw [hη c]
  · obtain ⟨θ', hθ'⟩ := hHQ θ
    obtain ⟨χ, hχ, hχθ⟩ := hsurj θ'
    refine ⟨χ, hχ, ?_⟩
    rw [hχθ, hθ']
    funext c
    change (basisH.representation θ).character (η (c : orderFourCentralizer n S e ⧸
        CFSG.oddCore (orderFourCentralizer n S e))) =
      (basisH.representation θ).character (orderFourMap n S e c)
    rw [hη c]

end CFSG.Wreathed.FourPointOrderFour
