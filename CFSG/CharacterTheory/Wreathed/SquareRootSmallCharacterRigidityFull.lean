module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntrinsicDetection
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegrees
public import CFSG.CharacterTheory.Wreathed.ReciprocalDegreeExclusion

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ActualProjectiveLayer
open CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalGeneralBase
open CFSG.Wreathed.ConditionalFiveFixed CFSG.Wreathed.ConditionalFirstFourierRows
open CFSG.Semidihedral.Principal CFSG.Wreathed.ConditionalGlobalDegrees
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

private theorem square_root_degree_polynomial_nonnegative (q : ℕ) :
    0 ≤ (q : ℤ) ^ 2 + modFourSign q * q + 1 := by
  rcases modFourSign_cases q with h | h <;> rw [h] <;>
    nlinarith [sq_nonneg ((q : ℤ) - 1)]

theorem original_psl_two_parameter_ge_five {L : Type} [Group L]
    {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f) : 5 ≤ p ^ f := by
  have h3 := three_le_prime_pow hp hpodd hf
  have ho : p ^ f % 2 = 1 := Nat.odd_iff.mp ((hp.odd_of_ne_two hpodd).pow)
  have hn3 : p ^ f ≠ 3 := by
    intro h
    exact hmodel.1.2.2.2.2 (Prod.ext rfl h)
  omega

theorem actual_root_square_root_character_rigidity
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (Q : ℕ) (A B D : BlocksIrr G),
      (Q : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 2 + modFourSign (p ^ f) * (p ^ f) + 1 ∧
      A ≠ B ∧ A ≠ D ∧ B ≠ D ∧
      (∀ χ ∈ ({A, B, D} : Finset (BlocksIrr G)),
        (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (χ : G → ℂ) ≠ 1) ∧
      irreducibleDegree A = (p ^ f) ^ 3 ∧ irreducibleDegree B = Q ∧
      irreducibleDegree D = (p ^ f) * Q ∧
      signedTest (modFourSign (p ^ f)) A B D =
        rootPrincipalAverageColumn n ideal (actualRoot S e) ∧
      signedTest (modFourSign (p ^ f)) A B D ∈ BlocksVChar G ∧
      (∀ g : G, signedTest (modFourSign (p ^ f)) A B D g =
        if g ∈ squareRootSection (actualRoot S e) then 4 else 0) ∧
      (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        (A : G → ℂ) (actualRoot S e ^ h * v) = -(modFourSign (p ^ f) : ℂ) ∧
        (B : G → ℂ) (actualRoot S e ^ h * v) = -1 ∧
        (D : G → ℂ) (actualRoot S e ^ h * v) = modFourSign (p ^ f)) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G, Module.finrank ℂ θ.vector ≤ Q →
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        θ.character = (B : G → ℂ) ∧ Module.finrank ℂ θ.vector = Q := by
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
  have hcoresave := hcore
  have hevensave := heven
  obtain ⟨hinj, hα, hβ, hη, hσ, hχinj, hχ, hδ, hηe, hηi, hηuniq, hY0, hXj,
    hdegχ, hdeg0, hrel, hβe, hδrel⟩ := hP
  obtain ⟨hωB, hωp, hωα, hωχ, hBe, hDe, hBD, hτ₀, hκ, hYcore,
    hXcore, hCcore, hdegω, hdegpos⟩ := hcore
  obtain ⟨hγε, hγinj, hγdisj, hγav, hXeven, hYeven, hγdeg, hrows, hposcols,
    hωc0, hsection, hsub, hcard⟩ := heven
  have hGD := (conditional_global_principal_degrees_and_involution_values hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  have hGDcore := (((hGD.2 ζ hζ θ hθ rfl).2 v hv σU υU g hbaseU).2 lam hlam).2
    α β η σ χ δ e₀ hPsave
  obtain ⟨V, hV6, hVrep⟩ := exists_orbit_representatives (K := dualGroup (2 ^ n))
    (X := ZMod (2 ^ n) × ZMod (2 ^ n))
    (fun O => O.ncard = 6)
  have hGDcomplete := hGDcore.2 ω iB iD τ₀ κ γ εs hcoresave
    ⟨hγε, hγinj, hγdisj, hγav, hXeven, hYeven, hγdeg⟩ V hV6 hVrep
  obtain ⟨PE, QE, er, ψ, ρ₀, Δ, hW⟩ := hGDcomplete.1
  obtain ⟨⟨hσabs, hτabs, hκabs, hρabs⟩, hdegs, hmultiset, hvalues,
    hparity, hevenorbits, hotherorbits, hcentral⟩ :=
      hGDcomplete.2 PE QE er ψ ρ₀ Δ hW
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
  have hq : 5 ≤ p ^ f := original_psl_two_parameter_ge_five hp hpodd hf hmodel
  have hpoly := square_root_degree_polynomial_nonnegative (p ^ f)
  let Q := (((p ^ f : ℕ) : ℤ) ^ 2 + modFourSign (p ^ f) * (p ^ f) + 1).toNat
  have hQ : (Q : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 2 + modFourSign (p ^ f) * (p ^ f) + 1 :=
    Int.toNat_of_nonneg hpoly
  have hQF : (Q : ℤ) = (Nat.card F : ℤ) ^ 2 +
      (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) * Nat.card F + 1 := by
    rw [hdata.card]
    exact hQ
  have hsig : σ = -modFourSign (p ^ f) := by
    simpa only [hdata.card, modFourSign] using hσabs
  have htau : τ₀ = 1 := hτabs
  have hkap : κ = modFourSign (p ^ f) := by
    simpa only [hdata.card, modFourSign] using hκabs
  have hdegI (ψ : basis.index) :
      irreducibleDegree (chI ψ) = Module.finrank ℂ (basis.representation ψ).vector := by
    have h := irreducibleDegree_cast (chI ψ)
    change (basis.representation ψ).representation.character 1 = _ at h
    rw [Representation.char_one] at h
    exact_mod_cast h.symm
  have hdegA : irreducibleDegree A = (p ^ f) ^ 3 := by
    have h := hdegs.1
    rw [hdata.card] at h
    dsimp only at h
    change irreducibleDegree (chI (α e₀)) = _
    rw [hdegI]
    exact_mod_cast h
  have hdegB : irreducibleDegree B = Q := by
    have h := hdegs.2.1
    rw [← hQF] at h
    dsimp only at h
    change irreducibleDegree (chI (α iB)) = _
    rw [hdegI]
    exact_mod_cast h
  have hdegD : irreducibleDegree D = (p ^ f) * Q := by
    have h := hdegs.2.2.1
    rw [← hQF, hdata.card] at h
    dsimp only at h
    change irreducibleDegree (chI (α iD)) = _
    rw [hdegI]
    exact_mod_cast h
  have htestcolumn : signedTest (modFourSign (p ^ f)) A B D =
      rootPrincipalAverageColumn n ideal (actualRoot S e) := by
    rw [hYcolumn, hsig, htau, hkap]
    ext g
    simp only [signedTest, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply]
    push_cast
    ring
  have hsec : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
      (A : G → ℂ) (actualRoot S e ^ h * v) = -(modFourSign (p ^ f) : ℂ) ∧
      (B : G → ℂ) (actualRoot S e ^ h * v) = -1 ∧
      (D : G → ℂ) (actualRoot S e ^ h * v) = modFourSign (p ^ f) := by
    intro h v hh hv hc
    simpa only [hsig, htau, hkap, Int.cast_neg, Int.cast_one, A, B, D, chI, actualRoot,
      originalRoot] using
      And.intro ((hA.2.2.2.2.2 h hh v hc hv).2)
        (And.intro ((hsection h hh v hc hv).2.1) ((hsection h hh v hc hv).2.2.1))
  have hsupp : ∀ g ∉ squareRootSection (actualRoot S e),
      signedTest (modFourSign (p ^ f)) A B D g = 0 := by
    intro g hg
    rw [htestcolumn]
    exact (actual_root_intrinsic_integral_column n hn S e ideal).2.1 g hg
  refine ⟨Q, A, B, D, hQ, ?_, ?_, ?_, ?_, hdegA, hdegB, hdegD, htestcolumn,
    signedTest_mem_virtual _ A B D, ?_, hsec, ?_⟩
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
  · intro g
    rw [htestcolumn]
    exact actual_root_principal_average_indicator n hn S e ideal g
  · intro Θ hdegree hΘsection
    exact character_eq_of_square_root_sections (actualRoot S e) A B D (modFourSign (p ^ f))
      hq (modFourSign_cases (p ^ f)) hQ
      (by rw [irreducibleDegree_cast, hdegA])
      (by rw [irreducibleDegree_cast, hdegB])
      (by rw [irreducibleDegree_cast, hdegD])
      hsupp (fun h v hh hv hc => (hsec h v hh hv hc).2.1) Θ hdegree hΘsection

theorem actual_root_unique_small_character_and_minimum
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (Q : ℕ) (β : BlocksIrr G),
      (Q : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 2 + modFourSign (p ^ f) * (p ^ f) + 1 ∧
      (β : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (β : G → ℂ) ≠ 1 ∧
      irreducibleDegree β = Q ∧
      (∃ θβ : FiniteComplexRepresentation.{0, 0} G,
        θβ.character = (β : G → ℂ) ∧ Module.finrank ℂ θβ.vector = Q) ∧
      (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
          (β : G → ℂ) (actualRoot S e ^ h * v) = -1) ∧
      originalSectionLeastDegree (actualRoot S e) = Q ∧
      (∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        Q ≤ Module.finrank ℂ θ.vector ∧
          (Module.finrank ℂ θ.vector ≤ Q →
            θ.character = (β : G → ℂ) ∧ Module.finrank ℂ θ.vector = Q)) ∧
      ∃! ψ : G → ℂ,
        (∃ θ : FiniteComplexRepresentation.{0, 0} G,
          θ.character = ψ ∧ Module.finrank ℂ θ.vector ≤ Q) ∧
        ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            ψ (actualRoot S e ^ h * v) = -1 := by
  obtain ⟨Q, A, B, D, hQ, hAB, hAD, hBD, hblock, hAdegree, hBdegree, hDdegree,
    hcolumn, hvirtual, hindicator, hsection, hrigid⟩ :=
      actual_root_square_root_character_rigidity hnonab n hn S e hfour p f hp hpodd hf hmodel
        ideal
  have hBsection : B ∈ originalSectionPassingIrreducibles (actualRoot S e) :=
    fun h v hh hv hc => (hsection h v hh hv hc).2.1
  obtain ⟨θB, hθB, hθBdegree⟩ := irreducible_actual_finite_representation B
  rw [hBdegree] at hθBdegree
  have hminle : originalSectionLeastDegree (actualRoot S e) ≤ Q := by
    rw [← hBdegree]
    exact Nat.sInf_le ⟨B, hBsection, rfl⟩
  have hfloor (θ : FiniteComplexRepresentation.{0, 0} G)
      (hθ : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
          θ.character (actualRoot S e ^ h * v) = -1) :
      Q ≤ Module.finrank ℂ θ.vector := by
    by_contra h
    have hd := (hrigid θ (by omega) hθ).2
    omega
  have hdegree_nonempty :
      (irreducibleDegree '' originalSectionPassingIrreducibles (actualRoot S e)).Nonempty :=
    ⟨irreducibleDegree B, B, hBsection, rfl⟩
  obtain ⟨χ, hχ, hχdegree⟩ := Nat.sInf_mem hdegree_nonempty
  obtain ⟨θχ, hθχ, hθχdegree⟩ := irreducible_actual_finite_representation χ
  have hθχsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θχ.character (actualRoot S e ^ h * v) = -1 := by
    rw [hθχ]
    exact hχ
  have hmin : originalSectionLeastDegree (actualRoot S e) = Q := by
    apply Nat.le_antisymm hminle
    have h := hfloor θχ hθχsection
    rw [hθχdegree, hχdegree] at h
    exact h
  refine ⟨Q, B, hQ, (hblock B (by simp)).1, (hblock B (by simp)).2, hBdegree,
    ⟨θB, hθB, hθBdegree⟩, hBsection, hmin,
    fun θ hθ => ⟨hfloor θ hθ, fun hd => hrigid θ hd hθ⟩, ?_⟩
  refine ⟨(B : G → ℂ), ⟨⟨θB, hθB, by omega⟩, hBsection⟩, ?_⟩
  rintro ψ ⟨⟨θ, hθ, hd⟩, hψsection⟩
  have hθsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θ.character (actualRoot S e ^ h * v) = -1 := by
    rw [hθ]
    exact hψsection
  exact hθ.symm.trans (hrigid θ hd hθsection).1

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
