module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityAverageIndicator
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixed

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalGeneralBase
open CFSG.Wreathed.ConditionalFiveFixed CFSG.Wreathed.ConditionalFirstFourierRows
open CFSG.Semidihedral.Principal
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem actual_root_intrinsic_signed_core
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (A B D : BlocksIrr G) (σ τ₀ κ : ℤ),
      A ≠ B ∧ A ≠ D ∧ B ≠ D ∧
      (∀ χ ∈ ({A, B, D} : Finset (BlocksIrr G)),
        (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (χ : G → ℂ) ≠ 1) ∧
      (σ = 1 ∨ σ = -1) ∧ (τ₀ = 1 ∨ τ₀ = -1) ∧ (κ = 1 ∨ κ = -1) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) =
        1 + (σ : ℂ) • (A : G → ℂ) - (τ₀ : ℂ) • (B : G → ℂ) +
          (κ : ℂ) • (D : G → ℂ) ∧
      (1 + (σ : ℂ) • (A : G → ℂ) - (τ₀ : ℂ) • (B : G → ℂ) +
        (κ : ℂ) • (D : G → ℂ)) ∈ BlocksVChar G ∧
      (∀ g : G, (1 + (σ : ℂ) • (A : G → ℂ) - (τ₀ : ℂ) • (B : G → ℂ) +
        (κ : ℂ) • (D : G → ℂ)) g =
          if g ∈ squareRootSection (actualRoot S e) then 4 else 0) ∧
      (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        (A : G → ℂ) (actualRoot S e ^ h * v) = σ ∧
        (B : G → ℂ) (actualRoot S e ^ h * v) = -τ₀ ∧
        (D : G → ℂ) (actualRoot S e ^ h * v) = κ) ∧
      (1 : ℤ) + σ * irreducibleDegree A - τ₀ * irreducibleDegree B +
        κ * irreducibleDegree D = 0 := by
  let : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨F, hF, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hfinite
  have hFF := (conditional_five_fixed_and_disjoint_even_constituent_families hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  let m := 2 ^ n
  let a : G := wreathModelHom S e (Original.a m)
  let w : G := wreathModelHom S e (Original.z m)
  let U : Subgroup G := Subgroup.closure
    {wreathModelHom S e (Original.s m), wreathModelHom S e (Original.t m)}
  obtain ⟨σb, υb, g, hg⟩ := hFF.1
  let θ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 * m : ℕ) : ℂ))
  have hθ : IsPrimitiveRoot θ (2 * m) := Complex.isPrimitiveRoot_exp _ (by positivity)
  let ζ : ℂ := θ ^ 2
  have hζ : IsPrimitiveRoot ζ m := by
    simpa only [Nat.mul_div_cancel_left _ (by norm_num : 0 < (2 : ℕ))] using
      hθ.pow_of_dvd (by norm_num : (2 : ℕ) ≠ 0) ⟨m, rfl⟩
  obtain ⟨v, hv⟩ := (hFF.2 ζ hζ θ hθ rfl).1
  have hbase : IsAdaptedBase U a w σb υb g := hg
  let σU : U := ⟨σb, hbase.left_mem⟩
  let υU : U := ⟨υb, hbase.right_mem⟩
  have hbaseU : IsAdaptedBase U a w (σU : G) (υU : G) g := hbase
  obtain ⟨lam, hlam⟩ := ((hFF.2 ζ hζ θ hθ rfl).2 v hv σU υU g hbaseU).1
  have hFam := ((hFF.2 ζ hζ θ hθ rfl).2 v hv σU υU g hbaseU).2 lam hlam
  obtain ⟨α, β, η, σ, χ, δ, e₀, hP⟩ := hFam.1
  obtain ⟨ω, iB, iD, τ₀, κ, hcore, huniq, γ, εs, heven⟩ :=
    hFam.2 α β η σ χ δ e₀ hP
  have hPsave := hP
  obtain ⟨hinj, hα, hβ, hη, hσ, hχinj, hχ, hδ, hηe, hηi, hηuniq, hY0, hXj,
    hdegχ, hdeg0, hrel, hβe, hδrel⟩ := hP
  obtain ⟨hωB, hωp, hωα, hωχ, hBe, hDe, hBD, hτ₀, hκ, hYcore,
    hXcore, hCcore, hdegω, hdegpos⟩ := hcore
  obtain ⟨hγε, hγinj, hγdisj, hγav, hXeven, hYeven, hγdeg, hrows, hposcols,
    hωc0, hsection, hsub, hcard⟩ := heven
  have hAsection := (conditional_odd_constituent_complete_first_fourier_rows hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
    ζ hζ θ hθ rfl
  have hA := (hAsection.2 v hv).2 α β η σ χ δ e₀ hPsave
  let chI : basis.index → BlocksIrr G := fun ψ =>
    ⟨(basis.representation ψ).character, CFSG.BlockBasics.basis_character_mem_irr basis ψ⟩
  let A := chI (α e₀)
  let B := chI (α iB)
  let D := chI (α iD)
  have hblock (i : Fin 3) :
      (chI (α i) : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧
      (chI (α i) : G → ℂ) ≠ 1 := by
    refine ⟨?_, ?_⟩
    · change (basis.representation (α i)).character ∈ BlocksBlockOf ideal G (1 : G → ℂ)
      rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
      exact ⟨α i, (hα i).1, rfl⟩
    · intro h
      exact (hα i).2 (basis.distinct (h.trans hprincipal.symm))
  have hYcolumn : rootPrincipalAverageColumn n ideal (actualRoot S e) =
      1 + (σ : ℂ) • (A : G → ℂ) - (τ₀ : ℂ) • (B : G → ℂ) + (κ : ℂ) • (D : G → ℂ) := by
    rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal θ hθ]
    change (fun g => ∑ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (oddPowerCoefficient (basis.representation ψ) (actualRoot S e) θ (2 ^ n) : ℂ) *
        (basis.representation ψ).character g) = _
    have hcoef (ψ : basis.index) : oddPowerCoefficient (basis.representation ψ)
        (actualRoot S e) θ (2 ^ n) =
        (Module.finrank ℂ (Module.End.eigenspace ((basis.representation ψ).representation
          (actualRoot S e)) (θ ^ (2 * 0))) : ℤ) -
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation ψ).representation
          (actualRoot S e)) (θ ^ (2 * 0 + 2 ^ n))) := by
      unfold oddPowerCoefficient cyclicEigenmultiplicity
      rw [show (2 * 0 : ℕ) = 0 by rfl, Nat.zero_add]
    simp only [hcoef]
    exact hYcore
  refine ⟨A, B, D, σ, τ₀, κ, ?_, ?_, ?_, ?_, hσ, hτ₀, hκ, hYcolumn, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hBe (hinj (basis.distinct (congrArg Subtype.val h)).symm)
  · intro h
    exact hDe (hinj (basis.distinct (congrArg Subtype.val h)).symm)
  · intro h
    exact hBD (hinj (basis.distinct (congrArg Subtype.val h)))
  · intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact hblock e₀
    · exact hblock iB
    · exact hblock iD
  · rw [← hYcolumn]
    exact (actual_root_intrinsic_integral_column n hn S e ideal).1
  · intro x
    rw [← hYcolumn]
    exact actual_root_principal_average_indicator n hn S e ideal x
  · intro h v hh hv hc
    exact ⟨(hA.2.2.2.2.2 h hh v hc hv).2, (hsection h hh v hc hv).2.1,
      (hsection h hh v hc hv).2.2.1⟩
  · have hz := (actual_root_intrinsic_integral_column n hn S e ideal).2.2.1
    rw [hYcolumn] at hz
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hz
    rw [irreducibleDegree_cast A, irreducibleDegree_cast B, irreducibleDegree_cast D] at hz
    exact_mod_cast hz

omit [IsSimpleGroup G] in
theorem actual_root_principal_average_irreducible_pairing
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (χ : BlocksIrr G) (hχ : (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G) :
    BlocksInnerProduct (χ : G → ℂ) (rootPrincipalAverageColumn n ideal (actualRoot S e)) =
      rootCharacterAverage n (actualRoot S e) (χ : G → ℂ) := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨label, hlabel⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis χ.property
  have hlabelB : label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    change (χ : G → ℂ) ∈ BlocksBlockOf ideal G (1 : G → ℂ) at hχ
    rw [← hlabel, ← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
      at hχ
    obtain ⟨ψ, hψ, heq⟩ := hχ
    rwa [basis.distinct heq] at hψ
  let root : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 * 2 ^ n : ℕ) : ℂ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) := Complex.isPrimitiveRoot_exp _ (by positivity)
  rw [← hlabel, actual_root_principal_average_column_eq n hn S e basis ideal principal
    hprincipal root hroot]
  have hcolumn : oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) =
      ∑ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) •
          (basis.representation ψ).character := by
    ext g
    simp only [oddPowerPrincipalColumn, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.intCast_apply]
  have hpair (ψ : basis.index) :
      BlocksInnerProduct (basis.representation label).character (basis.representation ψ).character =
        if label = ψ then 1 else 0 := by
    rw [blocksInnerProduct_eq_characterPairing _
      (AddSubgroup.subset_closure (CFSG.BlockBasics.basis_character_mem_irr basis ψ))]
    simpa only [basis.distinct.eq_iff] using characterPairing_irreducible
      (basis.representation label) (basis.representation ψ) (basis.irreducible label)
      (basis.irreducible ψ)
  rw [hcolumn, innerProduct_finite_integral_column]
  simp only [hpair, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, hlabelB, ite_true]
  exact (actual_root_odd_power_average n hn S e (basis.representation label) root hroot).symm

omit [Fintype G] [IsSimpleGroup G] in
theorem root_character_average_of_constant_section
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (χ : G → ℂ) (δ : ℂ)
    (hχ : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        χ (actualRoot S e ^ h * v) = δ) :
    rootCharacterAverage n (actualRoot S e) χ = δ := by
  have hval (k : ℕ) : χ (actualRoot S e ^ (2 * k + 1)) = δ := by
    have hh : Odd ((2 * k + 1 : ℕ) : ℤ) := by exact_mod_cast (show Odd (2 * k + 1) from ⟨k, rfl⟩)
    simpa only [zpow_natCast, mul_one] using hχ ((2 * k + 1 : ℕ) : ℤ) 1 hh
      (by simp) (Subgroup.one_mem _)
  unfold rootCharacterAverage
  simp only [hval, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.two_pow_pos n).ne'), one_mul]

theorem actual_root_intrinsic_least_passing_character
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (d : ℕ) (β : BlocksIrr G), 0 < d ∧ irreducibleDegree β = d ∧
      (β : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (β : G → ℂ) ≠ 1 ∧
      (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
          (β : G → ℂ) (actualRoot S e ^ h * v) = -1) ∧
      (∀ ψ : BlocksIrr G, (ψ : G → ℂ) ∈ BlocksPrincipalBlock ideal G →
        (∃ c : ℤ, c < 0 ∧ rootCharacterAverage n (actualRoot S e) (ψ : G → ℂ) = c) →
          d ≤ irreducibleDegree ψ) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G, Module.finrank ℂ θ.vector ≤ d →
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        θ.character ∈ BlocksIrr G ∧ θ.character ∈ BlocksPrincipalBlock ideal G ∧
          θ.character ≠ 1 ∧ Module.finrank ℂ θ.vector = d := by
  obtain ⟨A, B, D, σ, τ₀, κ, hAB, hAD, hBD, hblock, hσ, hτ₀, hκ, hcolumn,
    hvirtual, hindicator, hsection, hdegree⟩ := actual_root_intrinsic_signed_core hnonab n hn S e
      hfour p f hp hpodd hf hmodel ideal
  obtain ⟨d, β, hd, hβblock, hβnontrivial, ⟨c, hc, havg⟩, hβdegree, hfloor, htest⟩ :=
    actual_root_intrinsic_minimal_degree n hn S e ideal
  have hβpair := actual_root_principal_average_irreducible_pairing n hn S e ideal β hβblock
  rw [hcolumn, havg] at hβpair
  have hβcases : β = A ∨ β = B ∨ β = D := by
    by_contra hnone
    have hβA : β ≠ A := fun h => hnone (Or.inl h)
    have hβB : β ≠ B := fun h => hnone (Or.inr (Or.inl h))
    have hβD : β ≠ D := fun h => hnone (Or.inr (Or.inr h))
    let P : BlocksIrr G := ⟨1, principal_mem_blocksIrr G⟩
    have hβP : β ≠ P := fun h => hβnontrivial (congrArg Subtype.val h)
    rw [Int.cast_smul_eq_zsmul ℂ σ, Int.cast_smul_eq_zsmul ℂ τ₀,
      Int.cast_smul_eq_zsmul ℂ κ] at hβpair
    simp only [innerProduct_add_right, innerProduct_sub_right,
      innerProduct_zsmul_right] at hβpair
    change BlocksInnerProduct (β : G → ℂ) (P : G → ℂ) +
      (σ : ℂ) * BlocksInnerProduct (β : G → ℂ) (A : G → ℂ) -
      (τ₀ : ℂ) * BlocksInnerProduct (β : G → ℂ) (B : G → ℂ) +
      (κ : ℂ) * BlocksInnerProduct (β : G → ℂ) (D : G → ℂ) = c at hβpair
    simp only [blocksInnerProduct_irreducible, hβP, hβA, hβB, hβD, ite_false,
      mul_zero, add_zero, sub_zero] at hβpair
    have hc0 : c = 0 := by exact_mod_cast hβpair.symm
    omega
  have hβsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        (β : G → ℂ) (actualRoot S e ^ h * v) = -1 := by
    rcases hβcases with hβA | hβB | hβD
    · have hAsec := fun h v hh hv hc => (hsection h v hh hv hc).1
      have hAavg := root_character_average_of_constant_section n S e (A : G → ℂ) σ hAsec
      rw [hβA, hAavg] at havg
      have hσc : σ = c := by exact_mod_cast havg
      have hσneg : σ = -1 := by rcases hσ with h | h <;> omega
      simpa only [hβA, hσneg, Int.cast_neg, Int.cast_one] using hAsec
    · have hBsec := fun h v hh hv hc => (hsection h v hh hv hc).2.1
      have hBavg := root_character_average_of_constant_section n S e (B : G → ℂ) (-τ₀) hBsec
      rw [hβB, hBavg] at havg
      have hτc : -τ₀ = c := by exact_mod_cast havg
      have hτpos : τ₀ = 1 := by rcases hτ₀ with h | h <;> omega
      simpa only [hβB, hτpos, Int.cast_one] using hBsec
    · have hDsec := fun h v hh hv hc => (hsection h v hh hv hc).2.2
      have hDavg := root_character_average_of_constant_section n S e (D : G → ℂ) κ hDsec
      rw [hβD, hDavg] at havg
      have hκc : κ = c := by exact_mod_cast havg
      have hκneg : κ = -1 := by rcases hκ with h | h <;> omega
      simpa only [hβD, hκneg, Int.cast_neg, Int.cast_one] using hDsec
  exact ⟨d, β, hd, hβdegree, hβblock, hβnontrivial, hβsection, hfloor,
    fun θ hdeg hsec => let h := htest θ hdeg hsec; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
