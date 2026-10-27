module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderSix

public noncomputable section

open scoped Classical ComplexConjugate

namespace CFSG.Wreathed.SameFieldUnitary

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.ConditionalGlobalDegrees CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.BrauerWreathedOrder

variable {G : Type} [Group G] [Fintype G]

theorem unitary_principal_characters_of_localHyp
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f) {q : ℕ} (hq : p ^ f = q) (hq4 : q % 4 = 3)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ A B D χ ψ : basis.index,
      (basis.representation A).character 1 = (q : ℂ) ^ 3 ∧
      (basis.representation B).character 1 = (q : ℂ) ^ 2 - q + 1 ∧
      (basis.representation D).character 1 = (q : ℂ) * ((q : ℂ) ^ 2 - q + 1) ∧
      (basis.representation χ).character 1 = (q : ℂ) ^ 3 + 1 ∧
      (basis.representation ψ).character 1 = ((q : ℂ) - 1) * ((q : ℂ) ^ 2 - q + 1) ∧
      (basis.representation χ).character (wreathModelHom S e (Original.x (2 ^ n))) =
        -((q : ℂ) + 1) ∧
      (∀ φ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        let d : ℤ := (Module.finrank ℂ (basis.representation φ).vector : ℤ)
        d = 1 ∨ d = (q : ℤ) ^ 3 ∨ d = q * ((q : ℤ) - 1) ∨ d = (q : ℤ) ^ 2 - q + 1 ∨
          d = q * ((q : ℤ) ^ 2 - q + 1) ∨ d = (q : ℤ) ^ 3 + 1 ∨
          d = ((q : ℤ) - 1) * ((q : ℤ) ^ 2 - q + 1)) ∧
      ∀ g : G, Odd (orderOf g) →
        1 + (basis.representation A).character g =
            (basis.representation B).character g + (basis.representation D).character g ∧
          (basis.representation B).character g + (basis.representation D).character g =
            (basis.representation χ).character g ∧
          (basis.representation D).character g - (basis.representation B).character g =
            (basis.representation ψ).character g := by
  classical
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  have hm4 : 4 ≤ 2 ^ n := calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨θ, hθ⟩ : ∃ θ : ℂ, IsPrimitiveRoot θ (2 * 2 ^ n) :=
    ⟨_, Complex.isPrimitiveRoot_exp _ (by positivity)⟩
  have hζ : IsPrimitiveRoot (θ ^ 2) (2 ^ n) := hθ.pow (by positivity) rfl
  obtain ⟨-, H⟩ := conditional_global_principal_degrees_and_involution_values_of_localHyp n hn S
    e p f hp hpodd hf hloc ideal basis principal hprincipal
  obtain ⟨F, _, _, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hloc.modelData
  obtain ⟨⟨σ0, υ0, g0, hσ⟩, H2⟩ := H F Sigma b hSigma ρ Ψ hdata
  obtain ⟨⟨v, hv⟩, H4⟩ := H2 (θ ^ 2) hζ θ hθ rfl
  obtain ⟨⟨lam, hlam⟩, H6⟩ := H4 v hv ⟨σ0, hσ.left_mem⟩ ⟨υ0, hσ.right_mem⟩ g0 hσ
  obtain ⟨⟨α, β, η, σ', χ, δ, e₀, hcons⟩, H8⟩ := H6 lam hlam
  obtain ⟨⟨ω, iB, iD, τ₀, κ, γ, εs, hcore, heven⟩, H10⟩ := H8 α β η σ' χ δ e₀ hcons
  obtain ⟨V, hV1, hV2⟩ := exists_orbitRepresentatives (2 ^ n)
  obtain ⟨⟨P, Q, er, ψ, ρ₀, Δ, hwit⟩, H12⟩ := H10 ω iB iD τ₀ κ γ εs hcore heven V hV1 hV2
  obtain ⟨⟨hσ'', hτ₀, hκ, hρ₀⟩, ⟨hdA, hdB, hdD, -, hdχ, -, hdψ, -⟩, hmult,
      ⟨-, -, -, -, -, hxχ, -⟩, -, -, hVcard, -⟩ := H12 P Q er ψ ρ₀ Δ hwit
  obtain ⟨-, -, -, -, -, -, -, -, hY0, hXj, hC, -, -⟩ := hcore.2
  obtain ⟨-, hαB, -, -, -, -, hχB, -⟩ := hcons
  obtain ⟨-, -, -, -, -, -, -, -, -, hψV, -, -, -⟩ := hwit
  obtain ⟨hyord, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, hcr, -⟩ := hSR (θ ^ 2) hζ θ hθ rfl
  obtain ⟨vG, -, -, huniqG, -⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata (θ ^ 2) hζ
  obtain ⟨-, -, -, -, -, -, -, -, hGBζ⟩ :=
    (conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e
      p f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, hGBv⟩ := hGBζ (θ ^ 2) hζ θ hθ rfl
  obtain ⟨-, hGBlam⟩ := hGBv v hv ⟨σ0, hσ.left_mem⟩ ⟨υ0, hσ.right_mem⟩ g0 hσ
  obtain ⟨-, -, -, -, -, -, -, -, hodd, -⟩ := hGBlam lam hlam
  have hqF : Nat.card F = q := hdata.card.trans hq
  have hε : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by simp [hqF, hq4]
  have hε0 : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) ≠ 0 := by rw [hε]; norm_num
  have hprin : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem basis _ principal
  have h1J : 1 ∈ (Finset.Ico 1 (2 ^ n)).filter Odd :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_refl 1, by omega⟩, odd_one⟩
  have hVpos : 0 < (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card := by
    rw [hVcard]
    apply Nat.div_pos _ (by norm_num)
    calc 8 = 4 * 2 := by norm_num
      _ ≤ 2 ^ n * (2 ^ n - 2) := Nat.mul_le_mul hm4 (by omega)
  obtain ⟨I₀, hI₀⟩ := Finset.card_pos.mp hVpos
  have hI₀V : I₀ ∈ V := (Finset.mem_filter.mp hI₀).1
  obtain ⟨hψB, -, -, -, -, -, -, -, hψcf, -⟩ := hψV I₀ hI₀V
  have hrows : ∀ (j : ℕ) (ℓ : Fin 2) (z : G), Odd (orderOf z) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        fourierTransform (2 ^ n) (θ ^ 2) (fun k => v χ k ℓ) j *
          (basis.representation χ).character z = 0 := fun j ℓ z hz =>
    sum_fourierTransform_mul_eq_zero basis ideal principal _ _ _ _ _ hε0 v hv
      (fun k hk w hw => (huniqG principal hprin k hk w hw).trans
        (huniqG principal hprin k hk _ fun r hr hro => hv principal hprin k hk r hr hro).symm)
      (fun k hk r hr hro => not_odd_orderOf_pow_mul (orderOf_wreathModelHom_a n S e) hk hr hro)
      (θ ^ 2) j ℓ hz
  refine ⟨α e₀, α iB, α iD, χ 1, ψ I₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hε] at hσ'' hκ hρ₀ hdB hdD hdχ hdψ hxχ hmult
  · rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α e₀)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 3 from hdA, hqF]
    push_cast
    ring
  · rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α iB)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 2 + -1 * Nat.card F + 1 from hdB, hqF]
    push_cast
    ring
  · rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (α iD)).vector : ℤ)
      = Nat.card F * ((Nat.card F : ℤ) ^ 2 + -1 * Nat.card F + 1) from hdD, hqF]
    push_cast
    ring
  · rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (χ 1)).vector : ℤ)
      = (Nat.card F : ℤ) ^ 3 - -1 from hdχ 1 h1J, hqF]
    push_cast
    ring
  · rw [character_one_eq_finrank, show (Module.finrank ℂ (basis.representation (ψ I₀)).vector : ℤ)
      = (Nat.card F + -1) * ((Nat.card F : ℤ) ^ 2 + -1 * Nat.card F + 1) from hdψ I₀ hI₀V, hqF]
    push_cast
    ring
  · rw [show wreathModelHom S e (Original.x (2 ^ n)) =
        wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2) by
      rw [← map_pow]; rfl, hxχ 1 h1J, hqF]
    push_cast
    ring
  · intro φ hφ
    have hmem : (Module.finrank ℂ (basis.representation φ).vector : ℤ) ∈
        Multiset.map (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ))
          (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).val :=
      Multiset.mem_map_of_mem _ hφ
    rw [hmult] at hmem
    rw [hqF] at hmem
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton] at hmem
    dsimp only
    rcases hmem with ((((((h | h | h) | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩) | ⟨-, h⟩)) <;>
      [exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl (by rw [h]; ring)));
        exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; ring))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; ring)))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]; ring))))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h]; ring))))))]
  · intro g hg
    have eY := (congrFun hY0 g).symm.trans (sum_squareRootColumn_mul_eq_zero basis ideal
      principal hyord _ (θ ^ 2) 0 _ (fun χ hχ => hcr χ hχ 0 (by omega)) hg)
    have eX := apply_eq_zero_of_sum_smul_eq basis _ _ (hXj 1 h1J) (hrows 1 0 g hg)
    have eC := apply_eq_zero_of_sum_smul_eq basis _ _ hC (sum_mul_eq_zero_of_conj basis _ _
      (hodd ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n))) hg)
    have eψ := apply_eq_zero_of_sum_smul_eq basis _ _ hψcf (sum_mul_eq_zero_of_conj basis _ _
      (hodd I₀.1 I₀.2) hg)
    subst hσ'' hτ₀ hκ hρ₀
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul] at eY eX eC eψ
    push_cast at eY eX eC eψ
    refine ⟨by linear_combination eY, by linear_combination (-1 / 2 : ℂ) * eX + (-1 / 2 : ℂ) * eY,
      by linear_combination eC - eψ⟩

end CFSG.Wreathed.SameFieldUnitary
