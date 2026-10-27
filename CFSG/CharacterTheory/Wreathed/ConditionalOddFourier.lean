module

public import CFSG.CharacterTheory.Wreathed.ConditionalOddFourierCore
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRoot

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalOddFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalSquareRoot

theorem conditional_odd_fourier_actual_equal_degree_constituent_family_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (hn3 : 3 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 * m) → ξ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (ξ ^ t))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      ∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
        (e₀ : Fin 3),
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ ∧
        (J.image χ).card = m / 2 ∧ ∀ j ∈ J, fc (χ j) j = 2 * σ := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m a y ΦH ΦN ε B₀ J ζ hζ ξ hξ hξζ ν c Y
  obtain ⟨-, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, -, -, -, hY1, hc0, -, hfourc, hrows, hall⟩ := hSR ζ hζ ξ hξ hξζ
  refine ⟨hrows, fun v hv => ?_⟩
  intro fc X
  obtain ⟨Fc, hFc, horth, hodd, -, -, hcard, -, -⟩ := hall v hv
  obtain ⟨v₀, -, -, huniq, -, -, -, -, hdeg, hprin, -, hsq, hgram⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata ζ hζ
  have hm8 : 8 ≤ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hP : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hJI : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => (Finset.mem_filter.mp hj).1
  have hJodd : ∀ j ∈ J, Odd j := fun j hj => (Finset.mem_filter.mp hj).2
  let cc : ℕ → basis.index → ℤ := fun j χ => Fc χ j 0
  have hcc : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀, (cc j χ : ℂ) = fc χ j :=
    fun j hj χ hχ => hFc χ hχ j hj 0
  have hccF : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀,
      (cc j χ : ℂ) = fourierTransform m ζ (fun k => v₀ χ k 0) j := by
    intro j hj χ hχ
    rw [hcc j hj χ hχ]
    refine fourierTransform_congr (fun k hk => ?_) j
    rw [huniq χ hχ k hk (v χ k) fun r hr hodd => hv χ hχ k hk r hr hodd]
  have hgramZ : ∀ j ∈ Finset.Ico 1 m, ∀ t ∈ Finset.Ico 1 m,
      ∑ χ ∈ B₀, cc j χ * cc t χ = if j = t then 8 else 4 := by
    intro j hj t ht
    have key : ((∑ χ ∈ B₀, cc j χ * cc t χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hccF j hj χ hχ, hccF t ht χ hχ]
    by_cases hjt : j = t
    · subst hjt
      rw [ite_eq_left rfl]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 = 8 := hsq j hj
      rw [show ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 =
        ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) j from
        Finset.sum_congr rfl fun _ _ => sq _, ← key] at h
      exact_mod_cast h
    · rw [ite_eq_right hjt]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t = 4 := hgram j hj t ht hjt
      rw [← key] at h
      exact_mod_cast h
  have hdegZ : ∀ j ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, basisDegree basis χ * cc j χ = 0 := by
    intro j hj
    have h : ∑ χ ∈ B₀, (basis.representation χ).character 1 *
        fourierTransform m ζ (fun k => v₀ χ k 0) j = 0 := hdeg j hj 0
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * cc j χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v₀ χ k 0) j := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [basisDegree_cast, hccF j hj χ hχ]
    rw [← key] at h
    exact_mod_cast h
  have hprinZ : ∀ j ∈ Finset.Ico 1 m, cc j principal = -1 := by
    intro j hj
    have h : fourierTransform m ζ (fun k => v₀ principal k 0) j = -1 := (hprin j hj).1
    rw [← hccF j hj principal hP] at h
    exact_mod_cast h
  have hparJ : ∀ j ∈ J, ∀ χ ∈ B₀, cc j χ ≡ c χ 0 [ZMOD 2] :=
    fun j hj χ hχ => hodd j (hJI j hj) (hJodd j hj) χ hχ
  have hcols : ParityColumns B₀ principal (basisDegree basis) J cc :=
    ⟨hP, fun χ _ => basisDegree_pos basis χ, basisDegree_principal basis hprincipal,
      fun j hj t ht => hgramZ j (hJI j hj) t (hJI t ht), fun j hj => hdegZ j (hJI j hj),
      fun j hj => hprinZ j (hJI j hj),
      fun j hj t ht χ hχ => ((hparJ t ht χ hχ).trans (hparJ j hj χ hχ).symm).dvd⟩
  have hM₀ : 0 < m / 2 := by omega
  have hJcard : J.card = m / 2 := hcard
  have hydeg : ∑ χ ∈ B₀, basisDegree basis χ * c χ 0 = 0 := by
    have h : Y 0 1 = 0 := hY1 0 hM₀
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * c χ 0 : ℤ) : ℂ) = Y 0 1 := by
      push_cast
      exact Finset.sum_congr rfl fun χ _ => by rw [basisDegree_cast, mul_comm]
    rw [← key] at h
    exact_mod_cast h
  obtain ⟨α, β, η, σ, χ, e₀, hinj, hα, hβ, hη, hσ, hχinj, hχ, hχdeg, hy, hcj, hηe, hηi, hYdeg,
      hσδ, hβe, hδ⟩ :=
    odd_class_constituents (y := fun χ => c χ 0) hcols (by omega) (hfourc 0 hM₀).2
      (hfourc 0 hM₀).1 hc0 hydeg
      (fun j hj => horth 0 hM₀ j (hJI j hj) 0) hparJ
      fun ψ hψB hψ => hloc.principal_degree ideal basis principal hprincipal ψ hψB hψ
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ, (δ : ℤ) = basisDegree basis (χ j₀) :=
    ⟨Module.finrank ℂ (basis.representation (χ j₀)).vector, rfl⟩
  have hdegχ : ∀ j ∈ J, (basis.representation (χ j)).character 1 = δ := by
    intro j hj
    rw [← basisDegree_cast, hχdeg j hj j₀ hj₀, ← hδdef]
    push_cast
    rfl
  have hαB : ∀ i, α i ∈ B₀ := fun i => (hα i).1
  have hX : ∀ j ∈ J, X j = basisCombination basis B₀ (cc j) := fun j hj =>
    Finset.sum_congr rfl fun χ hχ => by rw [← hcc j (hJI j hj) χ hχ]
  refine ⟨α, β, η, σ, χ, δ, e₀, hinj, hα, hβ, hη, hσ, hχinj, hχ, ?_, hηe, hηi, ?_, ?_, ?_, hdegχ,
    ?_, ?_, hβe, ?_, ?_, ?_⟩
  · have h := basisDegree_pos basis (χ j₀)
    rw [← hδdef] at h
    exact_mod_cast h
  · intro i hi
    by_contra hie
    have h := hηi i hie
    rw [hi] at h
    rcases hβ i with hb | hb <;> rw [hb] at h <;> norm_num at h
  · have hY : Y 0 = basisCombination basis B₀ (fun χ => c χ 0) :=
      (basisCombination_eq_fun B₀ _).symm
    rw [hY, basisCombination_congr B₀ (e' := unitVector principal + ∑ i, β i • unitVector (α i))
      fun ψ hψ => by
        rw [hy ψ hψ]
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul],
      basisCombination_principal_add_sum hprincipal hP hαB]
  · intro j hj
    rw [hX j hj, basisCombination_congr B₀ (e' := -unitVector principal +
      ∑ i, η i • unitVector (α i) + (2 * σ) • unitVector (χ j)) fun ψ hψ => by
        rw [hcj j hj ψ hψ]
        simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul],
      basisCombination_neg_principal_add_sum_add hprincipal hP hαB (hχ j hj).1]
    push_cast
    rfl
  · have h : ((1 + ∑ i, β i * basisDegree basis (α i) : ℤ) : ℂ) = 0 := by
      rw [hYdeg, Int.cast_zero]
    push_cast at h
    simpa only [basisDegree_cast] using h
  · have h : ((σ * basisDegree basis (χ j₀) : ℤ) : ℂ) =
        ((1 + β e₀ * basisDegree basis (α e₀) : ℤ) : ℂ) := by
      rw [hσδ j₀ hj₀]
    rw [← hδdef] at h
    push_cast at h
    simpa only [basisDegree_cast] using h
  · have h : ((basisDegree basis (χ j₀) : ℤ) : ℂ) = ((basisDegree basis (α e₀) + σ : ℤ) : ℂ) := by
      rw [hδ j₀ hj₀]
    rw [← hδdef] at h
    push_cast at h
    simpa only [basisDegree_cast] using h
  · rw [Finset.card_image_of_injOn hχinj, hJcard]
  · intro j hj
    rw [← hcc j (hJI j hj) (χ j) (hχ j hj).1, hcj j hj (χ j) (hχ j hj).1,
      unitVector_of_ne (hχ j hj).2.1, sum_mul_unitVector_of_forall_ne η (hχ j hj).2.2,
      unitVector_self]
    push_cast
    ring

theorem conditional_odd_fourier_actual_equal_degree_constituent_family
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (hn3 : 3 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ ξ : ℂ, IsPrimitiveRoot ξ (2 * m) → ξ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (ξ ^ t))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      ∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
        (e₀ : Fin 3),
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ ∧
        (J.image χ).card = m / 2 ∧ ∀ j ∈ J, fc (χ j) j = 2 * σ :=
  conditional_odd_fourier_actual_equal_degree_constituent_family_of_localHyp n hn hn3 S e p f hp
    hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalOddFourier
