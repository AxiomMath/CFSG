module

public import CFSG.CharacterTheory.Wreathed.OddAbelianLiftIntegrality
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegularGram
public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveLinearTwoRegularBasis
public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockOrderFormula

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u

section Transport

variable {H Γ : Type u} [Group H] [Fintype H] [Group Γ] [Fintype Γ]

theorem central_p_cover_principal_block_inflation (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (π : H →* Γ) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center H)
    (hZp : IsPGroup p π.ker) (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisΓ : FiniteIrreducibleCharacterBasis Γ) (principalΓ : basisΓ.index)
    (hprincipalΓ : (basisΓ.representation principalΓ).character = 1) :
    (∀ θ ψ, (basisH.representation ψ).character = (basisΓ.representation θ).character ∘ π →
      (ψ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ↔
        θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ)) ∧
    ∀ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
      ∃ ψ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation ψ).character = (basisΓ.representation θ).character ∘ π := by
  generalize hZdef : π.ker = Z at hZ hZp
  have : Z.Normal := hZdef ▸ π.normal_ker
  set ι : H ⧸ Z ≃* Γ := (QuotientGroup.quotientMulEquivOfEq hZdef.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  set basisQ := transportCharacterBasis ι basisΓ
  have hprincipalQ : (basisQ.representation principalΓ).character = 1 := by
    funext q
    rw [transportCharacterBasis_character, hprincipalΓ]
    rfl
  have hblock : coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalΓ =
      coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ :=
    transportCharacterBasis_coefficientBlock ι basisΓ (localizedComplexIntegerRing ideal) principalΓ
  obtain ⟨-, -, -, -, -, hchar, -, hprin, hinf⟩ := central_p_quotient_relative_block_correspondence
    Z ideal p hZ hZp basisH basisQ principalH hprincipalH principalΓ hprincipalQ
  have hcomp : ∀ θ, (basisQ.representation θ).character ∘ QuotientGroup.mk' Z =
      (basisΓ.representation θ).character ∘ π := fun θ => rfl
  refine ⟨fun θ ψ hψ => ?_, fun θ hθ => ?_⟩
  · have h := hchar principalH principalΓ hprin θ ψ (by rw [hcomp]; exact hψ)
    rwa [hblock] at h
  · rw [← hblock] at hθ
    obtain ⟨ψ, hψ, hψchar⟩ := hinf θ hθ
    exact ⟨ψ, hψ, hψchar.trans (hcomp θ)⟩

theorem mem_primeRegular_two_iff {E : Type u} [Group E] (x : E) :
    x ∈ primeRegular E 2 ↔ Odd (orderOf x) := by
  change ¬ 2 ∣ orderOf x ↔ _
  rw [Nat.two_dvd_ne_zero, Nat.odd_iff]

theorem regularRestriction_two_eq_sum_iff {E : Type u} [Group E] [Fintype E] {ℓ : ℕ}
    (f : E → ℂ) (g : Fin ℓ → E → ℂ) (a : Fin ℓ → ℂ) :
    regularRestriction 2 f = ∑ j, a j • regularRestriction 2 (g j) ↔
      oddRestriction f = ∑ j, a j • oddRestriction (g j) := by
  constructor
  · intro h
    funext x
    have := congrFun h ⟨x.1, (mem_primeRegular_two_iff x.1).mpr x.2⟩
    simpa only [regularRestriction_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      oddRestriction] using this
  · intro h
    funext x
    have := congrFun h ⟨x.1, (mem_primeRegular_two_iff x.1).mp x.2⟩
    simpa only [regularRestriction_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      oddRestriction] using this

theorem oddRestriction_comp_eq_sum {E E' : Type*} [Group E] [Group E'] (σ : E →* E') {ℓ : ℕ}
    {f : E' → ℂ} {g : Fin ℓ → E' → ℂ} {a : Fin ℓ → ℂ}
    (h : oddRestriction f = ∑ j, a j • oddRestriction (g j)) :
    oddRestriction (f ∘ σ) = ∑ j, a j • oddRestriction (g j ∘ σ) := by
  funext x
  have := congrFun h (oddElementsMap σ x)
  simpa only [oddRestriction, oddElementsMap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Function.comp_apply] using this

theorem comp_mem_coefficientCharacterSpace_transport {A A' : Type u} [Group A] [Fintype A]
    [Group A'] [Fintype A'] (e : A ≃* A') (basis : FiniteIrreducibleCharacterBasis A')
    (support : Finset basis.index) {f : A' → ℂ}
    (hf : f ∈ coefficientCharacterSpace basis support) :
    f ∘ e ∈ coefficientCharacterSpace (transportCharacterBasis e basis) support := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨θ, hθ, rfl⟩ := hg
    exact Submodule.subset_span ⟨θ, hθ, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

theorem central_two_cover_regular_rows_and_gram (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (π : H →* Γ) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center H)
    (hZ2 : IsPGroup 2 π.ker) (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisΓ : FiniteIrreducibleCharacterBasis Γ) (principalΓ : basisΓ.index)
    (hprincipalΓ : (basisΓ.representation principalΓ).character = 1) {ℓ : ℕ}
    (c : Fin ℓ → Γ → ℂ)
    (hc : ∀ j, c j ∈ coefficientCharacterSpace basisΓ
      (coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ))
    (hind : LinearIndependent ℂ fun j => oddRestriction (c j))
    (hspan : ∀ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
      ∃ d : Fin ℓ → ℂ, oddRestriction (basisΓ.representation θ).character =
        ∑ j, d j • oddRestriction (c j)) :
    (∀ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      ∃ a : Fin ℓ → ℂ, oddRestriction (basisH.representation χ).character =
        ∑ j, a j • oddRestriction (c j ∘ π)) ∧
    ∀ (d : basisΓ.index → Fin ℓ → ℂ) (a : basisH.index → Fin ℓ → ℂ),
      (∀ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
        oddRestriction (basisΓ.representation θ).character = ∑ j, d θ j • oddRestriction (c j)) →
      (∀ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        oddRestriction (basisH.representation χ).character =
          ∑ j, a χ j • oddRestriction (c j ∘ π)) →
      ∀ j k, ∑ χ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          starRingEnd ℂ (a χ j) * a χ k =
        (Nat.card π.ker : ℂ) * ∑ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal)
          principalΓ, starRingEnd ℂ (d θ j) * d θ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  generalize hZdef : π.ker = Z at hZ hZ2 ⊢
  have : Z.Normal := hZdef ▸ π.normal_ker
  set ι : H ⧸ Z ≃* Γ := (QuotientGroup.quotientMulEquivOfEq hZdef.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ) with hιdef
  set basisQ := transportCharacterBasis ι basisΓ
  have hprincipalQ : (basisQ.representation principalΓ).character = 1 := by
    funext q
    rw [transportCharacterBasis_character, hprincipalΓ]
    rfl
  have hblock : coefficientBlock basisQ (localizedComplexIntegerRing ideal) principalΓ =
      coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ :=
    transportCharacterBasis_coefficientBlock ι basisΓ (localizedComplexIntegerRing ideal) principalΓ
  have hcharQ : ∀ θ, (basisQ.representation θ).character =
      (basisΓ.representation θ).character ∘ ι := fun θ => rfl
  set vQ : Fin ℓ → (primeRegular (H ⧸ Z) 2 → ℂ) := fun j => regularRestriction 2 (c j ∘ ι)
    with hvQ
  have hexpQ : ∀ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
      ∀ d : Fin ℓ → ℂ, oddRestriction (basisΓ.representation θ).character =
        ∑ j, d j • oddRestriction (c j) →
      regularRestriction 2 (basisQ.representation θ).character = ∑ j, d j • vQ j := by
    intro θ _ d hd
    rw [hcharQ, regularRestriction_two_eq_sum_iff]
    exact oddRestriction_comp_eq_sum ι.toMonoidHom hd
  have hVQ : regularPrincipalSpace 2 basisQ ideal principalΓ = Submodule.span ℂ (Set.range vQ) := by
    apply le_antisymm
    · rw [regularPrincipalSpace, coefficientCharacterSpace, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
      rw [hblock] at hθ
      obtain ⟨d, hd⟩ := hspan θ hθ
      rw [SetLike.mem_coe, hexpQ θ hθ d hd]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨c j ∘ ι, ?_, rfl⟩
      have h := comp_mem_coefficientCharacterSpace_transport ι basisΓ _ (hc j)
      rwa [← hblock] at h
  set g : primeRegular (H ⧸ Z) 2 → OddElements Γ := fun x =>
    ⟨ι x, by rw [MulEquiv.orderOf_eq]; exact (mem_primeRegular_two_iff _).mp x.2⟩ with hg
  have hgsurj : Function.Surjective g := by
    intro y
    refine ⟨⟨ι.symm y, ?_⟩, ?_⟩
    · rw [mem_primeRegular_two_iff, MulEquiv.orderOf_eq]
      exact y.2
    · apply Subtype.ext
      simp [hg]
  have hli : LinearIndependent ℂ vQ := by
    have h := hind.map' (LinearMap.funLeft ℂ ℂ g)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective ℂ ℂ g hgsurj))
    convert h using 1
    funext j x
    rfl
  let bQ : Module.Basis (Fin ℓ) ℂ (regularPrincipalSpace 2 basisQ ideal principalΓ) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hVQ.symm)
  have hbQ : ∀ j, (bQ j : primeRegular (H ⧸ Z) 2 → ℂ) = vQ j := by
    intro j
    simp only [bQ, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  obtain ⟨-, -, -, hrowsH, hgram⟩ := central_p_quotient_principal_regular_space_and_Gram Z 2 ideal
    hZ hZ2 basisH basisQ principalH hprincipalH principalΓ hprincipalQ bQ
  have hpull : ∀ j, regularPullback Z 2 (bQ j) = regularRestriction 2 (c j ∘ π) := by
    intro j
    funext x
    rw [regularPullback_apply, hbQ]
    rfl
  refine ⟨fun χ hχ => ?_, fun d a hd ha j k => ?_⟩
  · obtain ⟨a, ha, -⟩ := hrowsH χ hχ
    refine ⟨a, ?_⟩
    rw [← regularRestriction_two_eq_sum_iff]
    simpa only [hpull] using ha
  · have h := hgram d a (fun θ hθ => by
        rw [hblock] at hθ
        simp only [hbQ]
        exact hexpQ θ hθ (d θ) (hd θ hθ))
      (fun χ hχ => by
        simp only [hpull]
        exact (regularRestriction_two_eq_sum_iff _ _ _).mpr (ha χ hχ)) j k
    rwa [hblock] at h

end Transport

section Core

variable {H Γ : Type u} [Group H] [Fintype H] [Group Γ] [Fintype Γ]

theorem oddRestriction_eq_zsmul_add_iff {E : Type*} [Group E] (f g₀ g₁ : E → ℂ) (m₀ m₁ : ℤ) :
    oddRestriction f = m₀ • oddRestriction g₀ + m₁ • oddRestriction g₁ ↔
      ∀ y : E, Odd (orderOf y) → f y = m₀ * g₀ y + m₁ * g₁ y := by
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa only [oddRestriction, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply] using this
  · intro h
    funext y
    simp only [oddRestriction, Pi.add_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
    exact h y.1 y.2

theorem oddRestriction_eq_sum_two_iff {E : Type*} [Group E] (f : E → ℂ) (g : Fin 2 → E → ℂ)
    (a : Fin 2 → ℂ) :
    oddRestriction f = ∑ j, a j • oddRestriction (g j) ↔
      ∀ y : E, Odd (orderOf y) → f y = a 0 * g 0 y + a 1 * g 1 y := by
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa only [oddRestriction, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      using this
  · intro h
    funext y
    simp only [oddRestriction, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h y.1 y.2

theorem central_two_cover_regular_integral_basis_of_quotient
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (π : H →* Γ) (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center H)
    (hZ2 : IsPGroup 2 π.ker) (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisΓ : FiniteIrreducibleCharacterBasis Γ) (principalΓ : basisΓ.index)
    (hprincipalΓ : (basisΓ.representation principalΓ).character = 1)
    (φ : Γ → ℂ) (lφ : basisΓ.index)
    (hlφB : lφ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ)
    (hlφ : (basisΓ.representation lφ).character = φ) (e : ℤ) (he : e = 1 ∨ e = -1)
    (U : Subgroup Γ) (hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUodd : Odd (Nat.card U))
    (hU : 1 < Nat.card U) (hφ1 : φ 1 = Nat.card U) (hφU : ∀ u ∈ U, u ≠ 1 → φ u = 0)
    (D : basisΓ.index → Fin 2 → ℤ)
    (hD : ∀ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
      oddRestriction (basisΓ.representation θ).character =
        D θ 0 • oddRestriction (1 : Γ → ℂ) + D θ 1 • oddRestriction (1 + (e : ℂ) • φ)) :
    let Φ : H → ℂ := fun h => φ (π h)
    let B := coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH
    (∃ lΦ ∈ B, (basisH.representation lΦ).character = Φ) ∧
    (∀ χ ∈ B, ∃ a b : ℤ, (∀ y : H, Odd (orderOf y) →
        (basisH.representation χ).character y = a + b * Φ y) ∧ 0 ≤ b ∧ 0 ≤ a + b ∧
      ∀ a' b' : ℤ, (∀ y : H, Odd (orderOf y) →
        (basisH.representation χ).character y = a' + b' * Φ y) → a' = a ∧ b' = b) ∧
    LinearIndependent ℤ ![oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)] ∧
    Submodule.span ℤ {oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)} =
      oddRestrictionLattice basisH B ∧
    (∃ A : basisH.index → Fin 2 → ℤ, ∀ χ ∈ B,
      oddRestriction (basisH.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) ∧
    ∀ A : basisH.index → Fin 2 → ℤ, (∀ χ ∈ B,
      oddRestriction (basisH.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) →
      ∀ i j, ∑ χ ∈ B, A χ i * A χ j = (Nat.card π.ker : ℤ) *
        ∑ θ ∈ coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ,
          D θ i * D θ j := by
  intro Φ B
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set BΓ := coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ with hBΓ
  have he2 : (e : ℂ) * e = 1 := by rcases he with rfl | rfl <;> norm_num
  have he0 : (e : ℂ) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hU0 : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra! h
    have hbot : U = ⊥ := (Subgroup.eq_bot_iff_forall U).mpr h
    rw [hbot, Subgroup.card_bot] at hU
    omega
  have hu2 : ¬ 2 ∣ orderOf u := fun h =>
    hUodd.not_two_dvd_nat (h.trans (Subgroup.orderOf_dvd_natCard U huU))
  obtain ⟨y₀, hy₀, hπy₀⟩ := exists_primeRegular_lift π hπ hu2
  have hy₀odd : Odd (orderOf y₀) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hy₀)
  have hΦy₀ : Φ y₀ = 0 := by
    change φ (π y₀) = 0
    rw [hπy₀]
    exact hφU u huU hu1
  have hΦ1 : Φ 1 = Nat.card U := by
    change φ (π 1) = _
    rw [map_one, hφ1]
  have huniq : ∀ a b a' b' : ℂ, (a + b * Φ 1 = a' + b' * Φ 1) → (a + b * Φ y₀ = a' + b' * Φ y₀) →
      a = a' ∧ b = b' := by
    intro a b a' b' h1 h2
    rw [hΦy₀, mul_zero, mul_zero, add_zero, add_zero] at h2
    subst h2
    refine ⟨rfl, ?_⟩
    rw [hΦ1, add_right_inj] at h1
    exact mul_right_cancel₀ hU0 h1
  obtain ⟨-, hinfl⟩ := central_p_cover_principal_block_inflation ideal 2 π hπ hZ hZ2 basisH
    principalH hprincipalH basisΓ principalΓ hprincipalΓ
  obtain ⟨lΦ, hlΦB, hlΦ⟩ := hinfl lφ hlφB
  have hlΦ' : (basisH.representation lΦ).character = Φ := by
    rw [hlΦ, hlφ]
    rfl
  set c : Fin 2 → Γ → ℂ := ![1, 1 + (e : ℂ) • φ] with hcdef
  have hprinΓmem : (1 : Γ → ℂ) ∈ coefficientCharacterSpace basisΓ BΓ := by
    rw [← hprincipalΓ]
    exact Submodule.subset_span ⟨principalΓ, coefficientBlock_self_mem _ _ _, rfl⟩
  have hc : ∀ j, c j ∈ coefficientCharacterSpace basisΓ BΓ := by
    intro j
    fin_cases j
    · exact hprinΓmem
    · refine Submodule.add_mem _ hprinΓmem (Submodule.smul_mem _ _ ?_)
      rw [← hlφ]
      exact Submodule.subset_span ⟨lφ, hlφB, rfl⟩
  have hind : LinearIndependent ℂ fun j => oddRestriction (c j) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 := congrFun hg ⟨1, by rw [orderOf_one]; exact odd_one⟩
    have h2 := congrFun hg ⟨u, Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hu2)⟩
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, oddRestriction,
      Pi.zero_apply, hcdef, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply,
      hφ1, hφU u huU hu1, mul_zero, add_zero, mul_one] at h1 h2
    have hg1 : g 1 = 0 := by
      have : g 1 * ((e : ℂ) * Nat.card U) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (mul_ne_zero he0 hU0)
    have hg0 : g 0 = 0 := by rw [hg1, add_zero] at h2; exact h2
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
  have hDc : ∀ θ ∈ BΓ, oddRestriction (basisΓ.representation θ).character =
      ∑ j, (D θ j : ℂ) • oddRestriction (c j) := by
    intro θ hθ
    rw [oddRestriction_eq_sum_two_iff]
    intro y hy
    have h := (oddRestriction_eq_zsmul_add_iff _ _ _ _ _).mp (hD θ hθ) y hy
    rw [h]
    simp [hcdef]
  obtain ⟨hrows, hgram⟩ := central_two_cover_regular_rows_and_gram ideal π hπ hZ hZ2 basisH
    principalH hprincipalH basisΓ principalΓ hprincipalΓ c hc hind
    (fun θ hθ => ⟨fun j => (D θ j : ℂ), hDc θ hθ⟩)
  have hcoeff : ∀ χ ∈ B, ∃ a b : ℤ, (∀ y : H, Odd (orderOf y) →
      (basisH.representation χ).character y = a + b * Φ y) ∧ 0 ≤ b ∧ 0 ≤ a + b := by
    intro χ hχ
    obtain ⟨a, ha⟩ := hrows χ hχ
    have hval : ∀ y : H, Odd (orderOf y) →
        (basisH.representation χ).character y = (a 0 + a 1) + ((e : ℂ) * a 1) * φ (π y) := by
      intro y hy
      rw [(oddRestriction_eq_sum_two_iff _ _ _).mp ha y hy]
      simp only [hcdef, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨⟨n₁, hn₁⟩, ⟨n₀, hn₀⟩⟩ := odd_abelian_lift_coefficients_natural π hπ hZ hZ2 U hUcomm
      hUodd hU φ hφ1 hφU (basisH.representation χ) _ _ hval
    refine ⟨(n₀ : ℤ) - n₁, n₁, fun y hy => ?_, Int.natCast_nonneg _, by omega⟩
    rw [hval y hy, hn₁]
    push_cast
    linear_combination hn₀ - hn₁
  have hcoeff_uniq : ∀ χ : basisH.index, ∀ a b a' b' : ℤ,
      (∀ y : H, Odd (orderOf y) → (basisH.representation χ).character y = a + b * Φ y) →
      (∀ y : H, Odd (orderOf y) → (basisH.representation χ).character y = a' + b' * Φ y) →
      a' = a ∧ b' = b := by
    intro χ a b a' b' h h'
    have h1 := (h 1 (by rw [orderOf_one]; exact odd_one)).symm.trans
      (h' 1 (by rw [orderOf_one]; exact odd_one))
    have h2 := (h y₀ hy₀odd).symm.trans (h' y₀ hy₀odd)
    obtain ⟨ha, hb⟩ := huniq _ _ _ _ h1 h2
    exact ⟨by exact_mod_cast ha.symm, by exact_mod_cast hb.symm⟩
  have hrowsZ : ∀ χ : basisH.index, ∀ a b : ℤ,
      (∀ y : H, Odd (orderOf y) → (basisH.representation χ).character y = a + b * Φ y) →
      oddRestriction (basisH.representation χ).character =
        (a - e * b) • oddRestriction (1 : H → ℂ) +
          (e * b) • oddRestriction (1 + (e : ℂ) • Φ) := by
    intro χ a b h
    rw [oddRestriction_eq_zsmul_add_iff]
    intro y hy
    rw [h y hy]
    simp only [Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (-(b : ℂ) * Φ y) * he2
  choose! aχ bχ haχ hbχ habχ using hcoeff
  set A : basisH.index → Fin 2 → ℤ := fun χ => ![aχ χ - e * bχ χ, e * bχ χ] with hAdef
  have hA : ∀ χ ∈ B, oddRestriction (basisH.representation χ).character =
      A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ) := by
    intro χ hχ
    simpa only [hAdef, Matrix.cons_val_zero, Matrix.cons_val_one] using
      hrowsZ χ _ _ (haχ χ hχ)
  refine ⟨⟨lΦ, hlΦB, hlΦ'⟩, fun χ hχ => ⟨aχ χ, bχ χ, haχ χ hχ, hbχ χ hχ, habχ χ hχ,
    fun a' b' h' => hcoeff_uniq χ _ _ _ _ (haχ χ hχ) h'⟩, ?_, ?_, ⟨A, hA⟩, ?_⟩
  ·
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrFun hst ⟨1, by rw [orderOf_one]; exact odd_one⟩
    have h2 := congrFun hst ⟨y₀, hy₀odd⟩
    simp only [oddRestriction, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply, Pi.one_apply, smul_eq_mul, Pi.zero_apply, mul_one, hΦy₀, mul_zero,
      add_zero] at h1 h2
    rw [hΦ1] at h1
    have ht : (t : ℂ) = 0 := by
      have : (t : ℂ) * ((e : ℂ) * Nat.card U) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (mul_ne_zero he0 hU0)
    have hs : (s : ℂ) = 0 := by rw [ht, add_zero] at h2; exact h2
    exact ⟨by exact_mod_cast hs, by exact_mod_cast ht⟩
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      have h0 : oddRestriction (1 : H → ℂ) ∈ oddRestrictionLattice basisH B := by
        rw [← hprincipalH]
        exact Submodule.subset_span ⟨principalH, coefficientBlock_self_mem _ _ _, rfl⟩
      have hΦmem : oddRestriction Φ ∈ oddRestrictionLattice basisH B := by
        rw [← hlΦ']
        exact Submodule.subset_span ⟨lΦ, hlΦB, rfl⟩
      have h1 : oddRestriction (1 + (e : ℂ) • Φ) =
          oddRestriction (1 : H → ℂ) + e • oddRestriction Φ := by
        funext y
        simp only [oddRestriction, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul,
          Pi.one_apply, Pi.mul_apply, Pi.intCast_apply]
      rintro _ (rfl | rfl)
      · exact h0
      · rw [SetLike.mem_coe, h1]
        exact Submodule.add_mem _ h0 (Submodule.smul_mem _ _ hΦmem)
    · rw [oddRestrictionLattice, Submodule.span_le]
      rintro _ ⟨χ, hχ, rfl⟩
      change oddRestriction (basisH.representation χ).character ∈ Submodule.span ℤ _
      rw [hA χ hχ]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))
  ·
    intro A' hA' i j
    have hc0 : c 0 ∘ π = 1 := rfl
    have hc1 : c 1 ∘ π = 1 + (e : ℂ) • Φ := rfl
    have h := hgram (fun θ j => (D θ j : ℂ)) (fun χ j => (A' χ j : ℂ)) hDc (fun χ hχ => by
        rw [oddRestriction_eq_sum_two_iff]
        intro y hy
        rw [(oddRestriction_eq_zsmul_add_iff _ _ _ _ _).mp (hA' χ hχ) y hy, hc0, hc1]) i j
    simp only [map_intCast] at h
    exact_mod_cast h

end Core

section Translations

variable (F : Type) [Field F]

@[expose] def translationHom (Γ : Subgroup (Equiv.Perm (Omega F)))
    (hGΓ : coordinateG F ≤ Γ) : Multiplicative F →* Γ where
  toFun b := ⟨translation F b.toAdd, hGΓ (Subgroup.subset_closure (Or.inl ⟨b.toAdd, rfl⟩))⟩
  map_one' := Subtype.ext (translation_zero (F := F))
  map_mul' a b := Subtype.ext (translation_add a.toAdd b.toAdd)

variable {F}

theorem translationHom_apply (Γ : Subgroup (Equiv.Perm (Omega F))) (hGΓ : coordinateG F ≤ Γ)
    (b : Multiplicative F) :
    ((translationHom F Γ hGΓ b : Γ) : Equiv.Perm (Omega F)) = translation F b.toAdd := rfl

theorem translationHom_injective (Γ : Subgroup (Equiv.Perm (Omega F)))
    (hGΓ : coordinateG F ≤ Γ) : Function.Injective (translationHom F Γ hGΓ) := by
  intro a b hab
  have h := congrArg (fun g : Γ => (g : Equiv.Perm (Omega F)) (some 0)) hab
  simp only [translationHom_apply, translation_some, zero_add, Option.some.injEq] at h
  exact h

theorem translation_subgroup_regular [Fintype F] (Γ : Subgroup (Equiv.Perm (Omega F)))
    (hGΓ : coordinateG F ≤ Γ) :
    let U := (translationHom F Γ hGΓ).range
    let φ : Γ → ℂ := fun g =>
      (Nat.card {x : Omega F // (g : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧ Nat.card U = Nat.card F ∧
      φ 1 = Nat.card U ∧ ∀ u ∈ U, u ≠ 1 → φ u = 0 := by
  intro U φ
  have hcard : Nat.card U = Nat.card F :=
    (Nat.card_congr (MonoidHom.ofInjective (translationHom_injective Γ hGΓ)).toEquiv).symm.trans
      (Nat.card_congr Multiplicative.toAdd)
  refine ⟨?_, hcard, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · have hfix : Nat.card {x : Omega F // ((1 : Γ) : Equiv.Perm (Omega F)) x = x} =
        Nat.card (Omega F) := Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)
    change (Nat.card {x : Omega F // ((1 : Γ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 = _
    rw [hfix, card_omega, hcard]
    push_cast
    ring
  · rintro _ ⟨b, rfl⟩ hb
    have hb0 : b.toAdd ≠ 0 := by
      intro h
      apply hb
      rw [show b = 1 from h, map_one]
    change (Nat.card {x : Omega F // ((translationHom F Γ hGΓ b : Γ) : Equiv.Perm (Omega F)) x =
      x} : ℂ) - 1 = 0
    rw [translationHom_apply, card_fixed_translation hb0]
    norm_num

end Translations

section Assembly

theorem principal_block_enumeration_injective {α : Type*} {h : ℕ} {a₀ a₁ a₂ a₃ : α}
    (ψ : Fin h → α) (hnodup : [a₀, a₁, a₂, a₃].Nodup) (hψ : Function.Injective ψ)
    (hne : ∀ i, ψ i ≠ a₀ ∧ ψ i ≠ a₁ ∧ ψ i ≠ a₂ ∧ ψ i ≠ a₃) :
    Function.Injective (Sum.elim ![a₀, a₁, a₂, a₃] ψ) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnodup
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := hnodup
  have hfin : Function.Injective ![a₀, a₁, a₂, a₃] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  rintro (i | i) (j | j) hij
  · exact congrArg Sum.inl (hfin hij)
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    obtain ⟨n0, n1, n2, n3⟩ := hne j
    fin_cases i <;> simp_all [eq_comm]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    obtain ⟨n0, n1, n2, n3⟩ := hne i
    fin_cases j <;> simp_all
  · exact congrArg Sum.inr (hψ hij)

theorem general_central_two_cover_principal_regular_integral_basis {p f : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hf : 1 ≤ f) (F : Type) [Field F] [Fintype F] (hcard : Nat.card F = p ^ f)
    (Γ : Subgroup (Equiv.Perm (Omega F))) (hDΓ : coordinateD F ≤ Γ) (hΓE : Γ ≤ coordinateE F)
    {k : ℕ} (hk : 2 ≤ k)
    (hS : ∃ S : Sylow 2 Γ, Nonempty ((S : Subgroup Γ) ≃* DihedralGroup (2 ^ (k - 1))))
    (hG : ∃ T : Sylow 2 (coordinateG F), ¬ IsCyclic (T : Subgroup (coordinateG F)))
    {H : Type} [Group H] [Fintype H] (π : H →* Γ) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center H) (hZ2 : IsPGroup 2 π.ker)
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let Φ : H → ℂ := fun h =>
      (Nat.card {x : Omega F // ((π h : Γ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1
    let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    3 ≤ k ∧
    (∃ lΦ ∈ B, (basis.representation lΦ).character = Φ) ∧
    (∀ χ ∈ B, ∃ a b : ℤ, (∀ y : H, Odd (orderOf y) →
        (basis.representation χ).character y = a + b * Φ y) ∧ 0 ≤ b ∧ 0 ≤ a + b ∧
      ∀ a' b' : ℤ, (∀ y : H, Odd (orderOf y) →
        (basis.representation χ).character y = a' + b' * Φ y) → a' = a ∧ b' = b) ∧
    LinearIndependent ℤ ![oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)] ∧
    Submodule.span ℤ {oddRestriction (1 : H → ℂ), oddRestriction (1 + (e : ℂ) • Φ)} =
      oddRestrictionLattice basis B ∧
    (∃ A : Matrix B (Fin 2) ℤ, ∀ χ : B,
      oddRestriction (basis.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) ∧
    ∀ A : Matrix B (Fin 2) ℤ, (∀ χ : B,
      oddRestriction (basis.representation χ).character =
        A χ 0 • oddRestriction (1 : H → ℂ) + A χ 1 • oddRestriction (1 + (e : ℂ) • Φ)) →
      A.transpose * A = (Nat.card π.ker : ℤ) • !![4, -2; -2, ((2 ^ (k - 2) + 1 : ℕ) : ℤ)] := by
  intro Φ e B
  obtain ⟨basisΓ⟩ := finiteIrreducibleCharacterBasis_exists (G := Γ)
  obtain ⟨principalΓ, hprincipalΓ, -⟩ := complete_character_basis_contains_irreducible basisΓ
    (principalFiniteComplexRepresentation Γ) (principalFiniteComplexRepresentation_isIrreducible Γ)
  rw [principalFiniteComplexRepresentation_character] at hprincipalΓ
  obtain ⟨hk3, lδ, lφ, lδφ, ψ, -, hlφ, -, hnodup, hψinj, hψne, hBΓ, -, -, -, -, -, -, -, -, -,
    hrowsΓ, hgramΓ⟩ := projective_linear_two_principal_regular_integral_basis hp hodd hf F hcard Γ
      hDΓ hΓE hk hS hG basisΓ ideal principalΓ hprincipalΓ
  set φ : Γ → ℂ := fun g =>
    (Nat.card {x : Omega F // (g : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 with hφdef
  set BΓ := coefficientBlock basisΓ (localizedComplexIntegerRing ideal) principalΓ with hBΓdef
  have he : e = 1 ∨ e = -1 := by
    by_cases hq : Nat.card F % 4 = 1
    · left
      exact ite_eq_left hq
    · right
      exact ite_eq_right hq
  set E : Fin 4 ⊕ Fin (2 ^ (k - 2) - 1) → basisΓ.index := Sum.elim ![principalΓ, lδ, lφ, lδφ] ψ
    with hEdef
  have hEinj : Function.Injective E := principal_block_enumeration_injective ψ hnodup hψinj hψne
  have hEmem : ∀ θ, θ ∈ BΓ ↔ ∃ i, E i = θ := by
    intro θ
    rw [hBΓ θ]
    constructor
    · rintro (rfl | rfl | rfl | rfl | ⟨i, rfl⟩)
      exacts [⟨Sum.inl 0, rfl⟩, ⟨Sum.inl 1, rfl⟩, ⟨Sum.inl 2, rfl⟩, ⟨Sum.inl 3, rfl⟩,
        ⟨Sum.inr i, rfl⟩]
    · rintro ⟨i | i, rfl⟩
      · fin_cases i
        exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
          Or.inr (Or.inr (Or.inr (Or.inl rfl)))]
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
  set R := dihedralRegularRows e (2 ^ (k - 2) - 1) with hRdef
  set D : basisΓ.index → Fin 2 → ℤ := fun θ j => ∑ i, if E i = θ then R i j else 0 with hDdef
  have hDE : ∀ i j, D (E i) j = R i j := by
    intro i j
    simp only [hDdef]
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left rfl]
    · intro i' _ hi'
      rw [ite_eq_right fun h => hi' (hEinj h)]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hD : ∀ θ ∈ BΓ, oddRestriction (basisΓ.representation θ).character =
      D θ 0 • oddRestriction (1 : Γ → ℂ) + D θ 1 • oddRestriction (1 + (e : ℂ) • φ) := by
    intro θ hθ
    obtain ⟨i, rfl⟩ := (hEmem θ).mp hθ
    rw [hDE, hDE]
    exact hrowsΓ i
  have hlφB : lφ ∈ BΓ := (hEmem lφ).mpr ⟨Sum.inl 2, rfl⟩
  have hGΓ : coordinateG F ≤ Γ := (coordinateG_le_D F).trans hDΓ
  obtain ⟨hUcomm, hUcard, hφ1, hφU⟩ := translation_subgroup_regular Γ hGΓ
  set U := (translationHom F Γ hGΓ).range with hUdef
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact hodd.pow
  have hq1 : 1 < Nat.card F := by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨hΦ, hcoeff, hind, hspan, ⟨A₀, hA₀⟩, hgram⟩ :=
    central_two_cover_regular_integral_basis_of_quotient ideal π hπ hZ hZ2 basis principal
      hprincipal basisΓ principalΓ hprincipalΓ φ lφ hlφB (funext hlφ) e he U hUcomm
      (hUcard ▸ hqodd) (hUcard ▸ hq1) hφ1 hφU D hD
  refine ⟨hk3, hΦ, hcoeff, hind, hspan, ⟨fun χ => A₀ χ, fun χ => hA₀ χ χ.2⟩, fun A hA => ?_⟩
  set A' : basis.index → Fin 2 → ℤ := fun χ j => if hχ : χ ∈ B then A ⟨χ, hχ⟩ j else 0
    with hA'def
  have hA' : ∀ χ ∈ B, oddRestriction (basis.representation χ).character =
      A' χ 0 • oddRestriction (1 : H → ℂ) + A' χ 1 • oddRestriction (1 + (e : ℂ) • Φ) := by
    intro χ hχ
    simp only [hA'def, dite_eq_left hχ]
    exact hA ⟨χ, hχ⟩
  have hsumΓ : ∀ i j, ∑ θ ∈ BΓ, D θ i * D θ j = (R.transpose * R) i j := by
    intro i j
    have himage : BΓ = Finset.univ.image E := by
      ext θ
      rw [hEmem θ, Finset.mem_image]
      simp only [Finset.mem_univ, true_and]
    rw [himage, Finset.sum_image fun x _ y _ hxy => hEinj hxy, Matrix.mul_apply]
    simp only [hDE, Matrix.transpose_apply]
  ext i j
  have hg := hgram A' hA' i j
  rw [hsumΓ, hgramΓ] at hg
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Matrix.transpose_apply]
  rw [← hg, ← Finset.sum_coe_sort B]
  refine Finset.sum_congr rfl fun χ _ => ?_
  simp only [hA'def, dite_eq_left χ.2]

end Assembly

end CFSG.Wreathed
