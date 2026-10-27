module

public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

section Definitions

variable {E H : Type} [Group E] [Fintype E] [Group H]

@[expose] noncomputable def twistFamilyLabels (basis : FiniteIrreducibleCharacterBasis E)
    (fE : E →* H) {m d : ℕ} [NeZero d] (lam Ξ : Fin m → Fin d → H → ℂ) : Finset basis.index :=
  Finset.univ.filter fun l => ∃ r : Fin m,
    (basis.representation l).character = (fun y => lam r 0 (fE y)) ∨
      (basis.representation l).character = (fun y => Ξ r 0 (fE y))

@[expose] noncomputable def residualTorusLabels (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (fE : E →* H) {m d : ℕ} [NeZero d] (lam Ξ : Fin m → Fin d → H → ℂ) : Finset basis.index :=
  coefficientBlock basis (localizedComplexIntegerRing ideal) principal \
    twistFamilyLabels basis fE lam Ξ

structure ConditionalTwistResidualData (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (fE : E →* H) {m d : ℕ} [NeZero d] (lam Ξ : Fin m → Fin d → H → ℂ) (Φ : H → ℂ) (ε : ℤ)
    (q : ℕ) : Prop where
  regular_basis : PrincipalRegularIntegralBasisData basis ideal principal (fun y => Φ (fE y)) ε q
    ((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)])
  lam_irreducible : ∀ r v, (fun y => lam r v (fE y)) ∈ BlocksIrr E ∧ lam r v (fE 1) = 1
  xi_irreducible : ∀ r v, (fun y => Ξ r v (fE y)) ∈ BlocksIrr E ∧ Ξ r v (fE 1) = q
  lam_principal : ∀ r v,
    (∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation l).character = fun y => lam r v (fE y)) ↔ v = 0
  xi_principal : ∀ r v,
    (∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation l).character = fun y => Ξ r v (fE y)) ↔ v = 0
  family_injective : Function.Injective (Sum.elim (fun r : Fin m => fun y => lam r 0 (fE y))
    (fun r : Fin m => fun y => Ξ r 0 (fE y)))
  family_card : (twistFamilyLabels basis fE lam Ξ).card = 2 * m
  family_subset : twistFamilyLabels basis fE lam Ξ ⊆
    coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  lam_row : ∀ r, oddRestriction (fun y => lam r 0 (fE y)) =
    (1 : ℤ) • oddRestriction (1 : E → ℂ) +
      (0 : ℤ) • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))
  xi_row : ∀ r, oddRestriction (fun y => Ξ r 0 (fE y)) =
    (-ε) • oddRestriction (1 : E → ℂ) +
      ε • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))
  family_gram : ∀ D : Matrix (twistFamilyLabels basis fE lam Ξ) (Fin 2) ℤ,
    (∀ χ : twistFamilyLabels basis fE lam Ξ, oddRestriction (basis.representation χ).character =
      D χ 0 • oddRestriction (1 : E → ℂ) +
        D χ 1 • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))) →
    D.transpose * D = (m : ℤ) • !![2, -1; -1, 1]
  residual_rows : ∃ Q : Matrix (residualTorusLabels basis ideal principal fE lam Ξ) (Fin 2) ℤ,
    ∀ χ : residualTorusLabels basis ideal principal fE lam Ξ,
      oddRestriction (basis.representation χ).character =
        Q χ 0 • oddRestriction (1 : E → ℂ) +
          Q χ 1 • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))
  residual_gram : ∀ Q : Matrix (residualTorusLabels basis ideal principal fE lam Ξ) (Fin 2) ℤ,
    (∀ χ : residualTorusLabels basis ideal principal fE lam Ξ,
      oddRestriction (basis.representation χ).character =
        Q χ 0 • oddRestriction (1 : E → ℂ) +
          Q χ 1 • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y))) →
    Q.transpose * Q = (m : ℤ) • !![2, -1; -1, ((m / 2 : ℕ) : ℤ)]
  residual_degree : ∀ χ ∈ residualTorusLabels basis ideal principal fE lam Ξ,
    ∃ u : ℕ, 0 < u ∧ u ∣ d ∧
      ((basis.representation χ).character 1 = (u : ℂ) * ((q : ℂ) + 1) ∨
        (basis.representation χ).character 1 = (u : ℂ) * ((q : ℂ) - 1))

end Definitions

@[expose] def ResidualTorusCorrespondence {E E' H : Type} [Group E] [Fintype E] [Group E']
    [Fintype E'] [Group H] (σ : E' →* E) (basis : FiniteIrreducibleCharacterBasis E)
    (basis' : FiniteIrreducibleCharacterBasis E') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (principal' : basis'.index) (fE : E →* H)
    (fE' : E' →* H) {m d : ℕ} [NeZero d] (lam Ξ : Fin m → Fin d → H → ℂ) (Φ : H → ℂ)
    (ε : ℤ) : Prop :=
  ∃ τ : residualTorusLabels basis ideal principal fE lam Ξ ≃
      residualTorusLabels basis' ideal principal' fE' lam Ξ,
    (∀ θ, (basis'.representation (τ θ)).character = (basis.representation θ).character ∘ σ) ∧
    ∀ (θ : residualTorusLabels basis ideal principal fE lam Ξ) (r₀ r₁ : ℤ),
      oddRestriction (basis.representation θ).character =
          r₀ • oddRestriction (1 : E → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y)) ↔
        oddRestriction (basis'.representation (τ θ)).character =
          r₀ • oddRestriction (1 : E' → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE' y))

section Transport

theorem gram_twist_rows {ι : Type*} [Fintype ι] {m : ℕ} (e : Fin m ⊕ Fin m ≃ ι) {ε : ℤ}
    (hε : ε * ε = 1) (D : Matrix ι (Fin 2) ℤ)
    (hD₁ : ∀ r, D (e (Sum.inl r)) 0 = 1 ∧ D (e (Sum.inl r)) 1 = 0)
    (hD₂ : ∀ r, D (e (Sum.inr r)) 0 = -ε ∧ D (e (Sum.inr r)) 1 = ε) :
    D.transpose * D = (m : ℤ) • !![2, -1; -1, 1] := by
  ext i j
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [(hD₁ _).1, (hD₁ _).2, (hD₂ _).1, (hD₂ _).2, hε, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, mul_two]

variable {E H : Type} [Group E] [Fintype E] [Group H] [Fintype H]

theorem exists_coefficientBlock_comp_iff (basisE : FiniteIrreducibleCharacterBasis E)
    (basisH : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principalE : basisE.index) (principalH : basisH.index) (fE : E →* H)
    (hfE : Function.Surjective fE)
    (hblock : ∀ χ, χ ∈ coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisE.representation χ).character = (basisH.representation θ).character ∘ fE)
    (φ : H → ℂ) :
    (∃ l ∈ coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE,
        (basisE.representation l).character = fun y => φ (fE y)) ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation θ).character = φ := by
  constructor
  · rintro ⟨l, hl, hchar⟩
    obtain ⟨θ, hθ, hlθ⟩ := (hblock l).mp hl
    refine ⟨θ, hθ, funext fun h => ?_⟩
    obtain ⟨y, rfl⟩ := hfE h
    exact (congrFun (hchar.symm.trans hlθ) y).symm
  · rintro ⟨θ, hθ, hchar⟩
    obtain ⟨l, hl⟩ := CFSG.Semidihedral.Principal.exists_inflated_label fE hfE basisE basisH θ
    refine ⟨l, (hblock l).mpr ⟨θ, hθ, hl⟩, ?_⟩
    rw [hl, hchar]
    rfl

theorem conditionalTwistResidualData_of_inflation (basisE : FiniteIrreducibleCharacterBasis E)
    (basisH : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principalE : basisE.index) (principalH : basisH.index) (fE : E →* H)
    (hfE : Function.Surjective fE)
    (hblock : ∀ χ, χ ∈ coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE ↔
      ∃ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisE.representation χ).character = (basisH.representation θ).character ∘ fE)
    {m d : ℕ} [NeZero d] {lam Ξ : Fin m → Fin d → H → ℂ} {Φ : H → ℂ} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {q : ℕ}
    (hreg : PrincipalRegularIntegralBasisData basisE ideal principalE (fun y => Φ (fE y)) ε q
      ((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]))
    (hlam : ∀ r v, lam r v ∈ BlocksIrr H ∧ lam r v 1 = 1)
    (hxi : ∀ r v, Ξ r v ∈ BlocksIrr H ∧ Ξ r v 1 = q)
    (hlamP : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = lam r v) ↔ v = 0)
    (hxiP : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = Ξ r v) ↔ v = 0)
    (hlam_odd : ∀ r (y : H), Odd (orderOf y) → lam r 0 y = 1)
    (hxi_odd : ∀ r (y : H), Odd (orderOf y) → Ξ r 0 y = Φ y)
    (hinj : Function.Injective (Sum.elim (fun r : Fin m => lam r 0) (fun r : Fin m => Ξ r 0)))
    (hdeg : ∀ θ : basisH.index,
      (∃ r v, (basisH.representation θ).character = lam r v) ∨
      (∃ r v, (basisH.representation θ).character = Ξ r v) ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ d ∧
        ((basisH.representation θ).character 1 = (u : ℂ) * ((q : ℂ) + 1) ∨
          (basisH.representation θ).character 1 = (u : ℂ) * ((q : ℂ) - 1))) :
    ConditionalTwistResidualData basisE ideal principalE fE lam Ξ Φ ε q := by
  set B := coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE with hBdef
  set Fam := twistFamilyLabels basisE fE lam Ξ with hFamdef
  set T := residualTorusLabels basisE ideal principalE fE lam Ξ with hTdef
  set c₀ : OddElements E → ℂ := oddRestriction (1 : E → ℂ) with hc₀
  set c₁ : OddElements E → ℂ := oddRestriction (1 + (ε : ℂ) • fun y => Φ (fE y)) with hc₁
  have hεZ : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεC : (ε : ℂ) * ε = 1 := by exact_mod_cast hεZ
  have hfodd : ∀ y : E, Odd (orderOf y) → Odd (orderOf (fE y)) := fun y hy =>
    hy.of_dvd_nat (orderOf_map_dvd fE y)
  let fam : Fin m ⊕ Fin m → E → ℂ :=
    Sum.elim (fun r y => lam r 0 (fE y)) (fun r y => Ξ r 0 (fE y))
  have hfam_eq : ∀ x y,
      fam x y = Sum.elim (fun r : Fin m => lam r 0) (fun r => Ξ r 0) x (fE y) := by
    rintro (r | r) y <;> rfl
  have hfam_irr : ∀ x, fam x ∈ BlocksIrr E := by
    rintro (r | r)
    · exact Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hlam r 0).1
    · exact Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hxi r 0).1
  have hfam_inj : Function.Injective fam := by
    intro x x' h
    apply hinj
    funext z
    obtain ⟨y, rfl⟩ := hfE z
    rw [← hfam_eq, ← hfam_eq, h]
  have hmem := exists_coefficientBlock_comp_iff basisE basisH ideal principalE principalH fE hfE
    hblock
  have hlamP' : ∀ r v, (∃ l ∈ B, (basisE.representation l).character =
      fun y => lam r v (fE y)) ↔ v = 0 := fun r v => (hmem _).trans (hlamP r v)
  have hxiP' : ∀ r v, (∃ l ∈ B, (basisE.representation l).character =
      fun y => Ξ r v (fE y)) ↔ v = 0 := fun r v => (hmem _).trans (hxiP r v)
  have hlabel : ∀ x, ∃ l, (basisE.representation l).character = fam x := fun x =>
    CFSG.BlockBasics.exists_label_of_mem_irr basisE (hfam_irr x)
  choose ℓ hℓ using hlabel
  have hℓinj : Function.Injective ℓ := fun x x' h => hfam_inj (by rw [← hℓ, ← hℓ, h])
  have hFam_iff : ∀ l, l ∈ Fam ↔ ∃ x, ℓ x = l := by
    intro l
    rw [hFamdef, twistFamilyLabels, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, hr | hr⟩
      · exact ⟨Sum.inl r, basisE.distinct ((hℓ _).trans hr.symm)⟩
      · exact ⟨Sum.inr r, basisE.distinct ((hℓ _).trans hr.symm)⟩
    · rintro ⟨x, rfl⟩
      rcases x with r | r
      · exact ⟨r, Or.inl (hℓ _)⟩
      · exact ⟨r, Or.inr (hℓ _)⟩
  have hℓB : ∀ x, ℓ x ∈ B := by
    rintro (r | r)
    · obtain ⟨l, hl, hchar⟩ := (hlamP' r 0).mpr rfl
      rwa [basisE.distinct (hchar.trans (hℓ (Sum.inl r)).symm)] at hl
    · obtain ⟨l, hl, hchar⟩ := (hxiP' r 0).mpr rfl
      rwa [basisE.distinct (hchar.trans (hℓ (Sum.inr r)).symm)] at hl
  have hFamB : Fam ⊆ B := by
    intro l hl
    obtain ⟨x, rfl⟩ := (hFam_iff l).mp hl
    exact hℓB x
  let eF : Fin m ⊕ Fin m ≃ Fam := Equiv.ofBijective
    (fun x => ⟨ℓ x, (hFam_iff _).mpr ⟨x, rfl⟩⟩)
    ⟨fun x x' h => hℓinj (congrArg Subtype.val h), fun l => by
      obtain ⟨x, hx⟩ := (hFam_iff l.1).mp l.2
      exact ⟨x, Subtype.ext hx⟩⟩
  have hrow_lam : ∀ r, oddRestriction (fun y => lam r 0 (fE y)) = (1 : ℤ) • c₀ + (0 : ℤ) • c₁ := by
    intro r
    rw [hc₀, hc₁, oddRestriction_eq_zsmul_add_iff]
    intro y hy
    rw [hlam_odd r _ (hfodd y hy)]
    simp
  have hrow_xi : ∀ r, oddRestriction (fun y => Ξ r 0 (fE y)) = (-ε) • c₀ + ε • c₁ := by
    intro r
    rw [hc₀, hc₁, oddRestriction_eq_zsmul_add_iff]
    intro y hy
    rw [hxi_odd r _ (hfodd y hy)]
    simp only [Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg]
    linear_combination (-(Φ (fE y))) * hεC
  have hgramF : ∀ D : Matrix Fam (Fin 2) ℤ, (∀ χ : Fam,
      oddRestriction (basisE.representation χ).character = D χ 0 • c₀ + D χ 1 • c₁) →
      D.transpose * D = (m : ℤ) • !![2, -1; -1, 1] := by
    intro D hD
    refine gram_twist_rows eF hεZ D (fun r => ?_) (fun r => ?_)
    · have h := (hD (eF (Sum.inl r))).symm.trans
        ((congrArg oddRestriction (hℓ (Sum.inl r))).trans (hrow_lam r))
      exact hreg.linearIndependent.eq_of_pair h
    · have h := (hD (eF (Sum.inr r))).symm.trans
        ((congrArg oddRestriction (hℓ (Sum.inr r))).trans (hrow_xi r))
      exact hreg.linearIndependent.eq_of_pair h
  refine ⟨hreg, fun r v => ⟨Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hlam r v).1, ?_⟩,
    fun r v => ⟨Semidihedral.Principal.comp_mem_blocksIrr fE hfE (hxi r v).1, ?_⟩, hlamP', hxiP',
    ?_, ?_, hFamB, hrow_lam, hrow_xi, hgramF, ?_, ?_, ?_⟩
  · rw [map_one]
    exact (hlam r v).2
  · rw [map_one]
    exact (hxi r v).2
  · intro x x' h
    exact hfam_inj h
  · have h := Fintype.card_congr eF
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h
    rw [← h, two_mul]
  ·
    obtain ⟨D₀, hD₀⟩ := hreg.rows
    refine ⟨fun χ => D₀ ⟨χ.1, (Finset.mem_sdiff.mp χ.2).1⟩, fun χ => ?_⟩
    exact hD₀ ⟨χ.1, (Finset.mem_sdiff.mp χ.2).1⟩
  ·
    intro Q hQ
    obtain ⟨D₀, hD₀⟩ := hreg.rows
    let Dfull : basisE.index → Fin 2 → ℤ := fun l =>
      if h : l ∈ T then Q ⟨l, h⟩ else if h' : l ∈ B then D₀ ⟨l, h'⟩ else 0
    let D : Matrix B (Fin 2) ℤ := fun χ => Dfull χ.1
    have hD : ∀ χ : B, oddRestriction (basisE.representation χ).character =
        D χ 0 • c₀ + D χ 1 • c₁ := by
      intro χ
      by_cases h : χ.1 ∈ T
      · simp only [D, Dfull, dite_eq_left h]
        exact hQ ⟨χ.1, h⟩
      · simp only [D, Dfull, dite_eq_right h, dite_eq_left χ.2]
        exact hD₀ χ
    let DF : Matrix Fam (Fin 2) ℤ := fun χ => Dfull χ.1
    have hDF : ∀ χ : Fam, oddRestriction (basisE.representation χ).character =
        DF χ 0 • c₀ + DF χ 1 • c₁ := by
      intro χ
      have hχT : χ.1 ∉ T := fun h => (Finset.mem_sdiff.mp h).2 χ.2
      simp only [DF, Dfull, dite_eq_right hχT, dite_eq_left (hFamB χ.2)]
      exact hD₀ ⟨χ.1, hFamB χ.2⟩
    have hgram := hreg.gram D hD
    have hgramF' := hgramF DF hDF
    have hsplit : ∀ i j, (D.transpose * D) i j =
        (Q.transpose * Q) i j + (DF.transpose * DF) i j := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      have hT : ∀ χ : T, Q χ i * Q χ j = Dfull χ.1 i * Dfull χ.1 j := by
        intro χ
        simp only [Dfull, dite_eq_left χ.2]
        rfl
      rw [Finset.sum_congr rfl fun χ _ => hT χ]
      change ∑ χ : B, Dfull χ.1 i * Dfull χ.1 j =
        ∑ χ : T, Dfull χ.1 i * Dfull χ.1 j + ∑ χ : Fam, Dfull χ.1 i * Dfull χ.1 j
      rw [Finset.sum_coe_sort B (fun l => Dfull l i * Dfull l j),
        Finset.sum_coe_sort T (fun l => Dfull l i * Dfull l j),
        Finset.sum_coe_sort Fam (fun l => Dfull l i * Dfull l j)]
      exact (Finset.sum_sdiff hFamB).symm
    ext i j
    have h := hsplit i j
    rw [hgram, hgramF'] at h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith
  ·
    intro χ hχ
    obtain ⟨hχB, hχF⟩ := Finset.mem_sdiff.mp hχ
    obtain ⟨θ, hθ, hχθ⟩ := (hblock χ).mp hχB
    have h1 : (basisE.representation χ).character 1 = (basisH.representation θ).character 1 := by
      rw [hχθ, Function.comp_apply, map_one]
    rcases hdeg θ with ⟨r, v, hrv⟩ | ⟨r, v, hrv⟩ | ⟨u, hu, hud, hdegθ⟩
    · have hv : v = 0 := (hlamP r v).mp ⟨θ, hθ, hrv⟩
      subst hv
      have hc : (basisE.representation (ℓ (Sum.inl r))).character =
          (basisE.representation χ).character := by
        rw [hℓ, hχθ, hrv]
        rfl
      exact absurd ((hFam_iff χ).mpr ⟨Sum.inl r, basisE.distinct hc⟩) hχF
    · have hv : v = 0 := (hxiP r v).mp ⟨θ, hθ, hrv⟩
      subst hv
      have hc : (basisE.representation (ℓ (Sum.inr r))).character =
          (basisE.representation χ).character := by
        rw [hℓ, hχθ, hrv]
        rfl
      exact absurd ((hFam_iff χ).mpr ⟨Sum.inr r, basisE.distinct hc⟩) hχF
    · exact ⟨u, hu, hud, by rwa [h1]⟩

end Transport

section Correspondence

variable {E E' H : Type} [Group E] [Fintype E] [Group E'] [Fintype E'] [Group H]

theorem residualTorusCorrespondence_of_regularRow (σ : E' →* E)
    (basis : FiniteIrreducibleCharacterBasis E) (basis' : FiniteIrreducibleCharacterBasis E')
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index)
    (principal' : basis'.index) (fE : E →* H) (fE' : E' →* H) (hcomp : ∀ y, fE (σ y) = fE' y)
    (hfE' : Function.Surjective fE')
    (hinfl : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ φ : H → ℂ, (basis.representation χ).character = fun y => φ (fE y))
    {m d : ℕ} [NeZero d] (lam Ξ : Fin m → Fin d → H → ℂ) (Φ : H → ℂ) (ε : ℤ)
    (hcorr : RegularRowCorrespondence σ basis basis' ideal principal principal'
      (fun y => Φ (fE y)) (fun y => Φ (fE' y)) ε) :
    ResidualTorusCorrespondence σ basis basis' ideal principal principal' fE fE' lam Ξ Φ ε := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  set T := residualTorusLabels basis ideal principal fE lam Ξ with hTdef
  set T' := residualTorusLabels basis' ideal principal' fE' lam Ξ with hT'def
  obtain ⟨bij, hbij, -, hrow⟩ := hcorr
  have hlift : ∀ φ ψ : H → ℂ, ((fun y => φ (fE y)) = fun y => ψ (fE y)) ↔
      ((fun y => φ (fE y)) ∘ σ = fun y => ψ (fE' y)) := by
    intro φ ψ
    constructor
    · intro h
      funext y
      have := congrFun h (σ y)
      simp only [Function.comp_apply, ← hcomp]
      exact this
    · intro h
      have hφψ : φ = ψ := by
        funext z
        obtain ⟨y, rfl⟩ := hfE' z
        have := congrFun h y
        simp only [Function.comp_apply, hcomp] at this
        exact this
      rw [hφψ]
  have hF : ∀ θ : B, θ.1 ∈ twistFamilyLabels basis fE lam Ξ ↔
      (bij θ).1 ∈ twistFamilyLabels basis' fE' lam Ξ := by
    intro θ
    simp only [twistFamilyLabels, Finset.mem_filter, Finset.mem_univ, true_and, hbij]
    obtain ⟨φ, hφ⟩ := hinfl θ.1 θ.2
    rw [hφ]
    simp only [hlift]
  have hT : ∀ θ : B, θ.1 ∈ T ↔ (bij θ).1 ∈ T' := by
    intro θ
    rw [hTdef, hT'def, residualTorusLabels, residualTorusLabels, Finset.mem_sdiff,
      Finset.mem_sdiff, hF θ]
    exact ⟨fun h => ⟨(bij θ).2, h.2⟩, fun h => ⟨θ.2, h.2⟩⟩
  have hTB : ∀ {l}, l ∈ T → l ∈ B := fun h => (Finset.mem_sdiff.mp h).1
  have hTB' : ∀ {l}, l ∈ T' → l ∈ coefficientBlock basis' (localizedComplexIntegerRing ideal)
      principal' := fun h => (Finset.mem_sdiff.mp h).1
  let τ : T ≃ T' :=
    { toFun := fun θ => ⟨(bij ⟨θ.1, hTB θ.2⟩).1, (hT _).mp θ.2⟩
      invFun := fun θ' => ⟨(bij.symm ⟨θ'.1, hTB' θ'.2⟩).1, by
        have h := (hT (bij.symm ⟨θ'.1, hTB' θ'.2⟩)).mpr
        rw [Equiv.apply_symm_apply] at h
        exact h θ'.2⟩
      left_inv := fun θ => by
        apply Subtype.ext
        simp
      right_inv := fun θ' => by
        apply Subtype.ext
        simp }
  refine ⟨τ, fun θ => hbij ⟨θ.1, hTB θ.2⟩, fun θ r₀ r₁ => hrow ⟨θ.1, hTB θ.2⟩ r₀ r₁⟩

variable {E'' : Type} [Group E''] [Fintype E'']

theorem ResidualTorusCorrespondence.trans {σ : E' →* E} {σ' : E'' →* E'}
    {basis : FiniteIrreducibleCharacterBasis E} {basis' : FiniteIrreducibleCharacterBasis E'}
    {basis'' : FiniteIrreducibleCharacterBasis E''} {ideal : Ideal ComplexAlgebraicIntegers}
    [ideal.IsMaximal] {principal : basis.index} {principal' : basis'.index}
    {principal'' : basis''.index} {fE : E →* H} {fE' : E' →* H} {fE'' : E'' →* H} {m d : ℕ}
    [NeZero d] {lam Ξ : Fin m → Fin d → H → ℂ} {Φ : H → ℂ} {ε : ℤ}
    (h₁ : ResidualTorusCorrespondence σ basis basis' ideal principal principal' fE fE' lam Ξ Φ ε)
    (h₂ : ResidualTorusCorrespondence σ' basis' basis'' ideal principal' principal'' fE' fE'' lam
      Ξ Φ ε) :
    ResidualTorusCorrespondence (σ.comp σ') basis basis'' ideal principal principal'' fE fE''
      lam Ξ Φ ε := by
  obtain ⟨τ₁, hc₁, hr₁⟩ := h₁
  obtain ⟨τ₂, hc₂, hr₂⟩ := h₂
  refine ⟨τ₁.trans τ₂, fun θ => ?_, fun θ r₀ r₁ => (hr₁ θ r₀ r₁).trans (hr₂ (τ₁ θ) r₀ r₁)⟩
  rw [Equiv.trans_apply, hc₂, hc₁]
  rfl

end Correspondence

end CFSG.Wreathed
