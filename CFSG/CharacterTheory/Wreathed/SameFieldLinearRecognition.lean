module

public import CFSG.CharacterTheory.Wreathed.PrimewiseConfinedCentralCore
public import CFSG.CharacterTheory.Wreathed.SameFieldLinearGL
public import CFSG.CharacterTheory.BrauerLinearThree.QOne
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderPrincipal
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierLinear

public section

namespace CFSG.Wreathed.SameFieldLinearRecognition

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_odd_of_two_part (q n : ℕ) (hq : 2 ≤ q) (h : (q - 1).factorization 2 = n) :
    ∃ k, Odd k ∧ q - 1 = 2 ^ n * k := by
  have hq1 : q - 1 ≠ 0 := by omega
  refine ⟨(q - 1) / 2 ^ n, ?_, ?_⟩
  · have hcop := Nat.coprime_ordCompl Nat.prime_two hq1
    rw [h] at hcop
    exact Nat.coprime_two_left.mp hcop
  · have := Nat.ordProj_mul_ordCompl_eq_self (q - 1) 2
    rw [h] at this
    exact this.symm

theorem neg_one_ne_one_of_card {F : Type} [Field F] [Finite F] (p f : ℕ) (hp : p.Prime)
    (hpodd : p ≠ 2) (hF : Nat.card F = p ^ f) : (-1 : Fˣ) ≠ 1 := by
  intro h
  have h2 : (2 : F) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have hc2 : ringChar F = 2 := by
    have := (ringChar.spec F 2).mp h2
    have hprime : (ringChar F).Prime := by
      have : Fintype F := Fintype.ofFinite F
      exact CharP.char_is_prime F (ringChar F)
    exact (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp this
  have : Fintype F := Fintype.ofFinite F
  have heven := (FiniteField.even_card_iff_char_two (F := F)).mp hc2
  rw [← Nat.card_eq_fintype_card, hF] at heven
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hpodd).pow
  rw [Nat.odd_iff] at hodd
  omega

open CFSG.Wreathed CFSG.Wreathed.PrimewiseConfinedCentralCore in
theorem wreathed_linear_branch_of_original_primewise
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e),
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
            (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (hq1 : p ^ f % 4 = 1) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  obtain ⟨-, -, -, -, hRcyc, -, hRdvd, -, ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩, hall,
      -, -, -, JS, -, ⟨μ, -⟩, ⟨φ, -⟩⟩ :=
    original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
      hnonab n hn S e hfour p f hp hpodd hf hmodel hcov hconf
  have hSig : Nat.card Sigma = 1 := hall F Sigma b hSigma ρ Ψ hdata
  have : Subsingleton Sigma := (Nat.card_eq_one_iff_unique.mp hSig).1
  have : IsCyclic (centralizerOddCore n S e) := hRcyc
  let eW := CFSG.Semidihedral.SimpleLayerFrontier.semidirectProductTrivialRightEquiv
    (fieldAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma)
  let eH := φ.trans (Ψ.symm.trans eW.symm)
  let eN := μ.symm.trans (MulEquiv.prodCongr (MulEquiv.refl _) eH)
  set q := p ^ f with hqdef
  have hq3 : 3 ≤ q := by
    have h1 : p ≤ q := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    have := hp.two_le
    omega
  have htwo := NormalComponentLift.two_pow_eq_two_part (n := n) (hn := hn) (S := S) (e := e)
    hnonab hfour hp hpodd hf hmodel
  rw [ite_eq_left hq1] at htwo
  have hval : padicValInt 2 ((q : ℕ) - (1 : ℤ)) = n :=
    (Nat.pow_right_injective (le_refl 2) htwo).symm
  have hcast : ((q : ℕ) : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast, padicValInt.of_nat, ← Nat.factorization_def _ Nat.prime_two] at hval
  obtain ⟨k, hk, hqk⟩ := exists_odd_of_two_part q n (by omega) hval
  have hFcard : Nat.card F = q := hdata.card
  have hcardFx : Nat.card Fˣ = 2 ^ n * k := by
    rw [Nat.card_units, hFcard, hqk]
  have hRk : Nat.card (centralizerOddCore n S e) ∣ k := by
    rw [ite_eq_left hq1] at hRdvd
    have hk' : (((q : ℕ) : ℤ) - 1) / (2 ^ n : ℕ) = (k : ℤ) := by
      rw [hcast, hqk, Nat.cast_mul, Int.mul_ediv_cancel_left _ (by positivity)]
    rw [hk'] at hRdvd
    exact_mod_cast hRdvd
  have hneg := neg_one_ne_one_of_card (F := F) p f hp hpodd hFcard
  obtain ⟨Z, hZn, hZ, hZodd, ⟨eGL⟩⟩ :=
    SameFieldLinearGL.exists_GL_quotient_equiv_prod_centralExtension n k hn hk hcardFx b
      hdata.nonsquare hneg (centralizerOddCore n S e) hRk
  exact CFSG.BrauerLinearThree.brauer_linear_three_involution_centralizer_of_principal_block
    (fun {_G} _ _ => CFSG.Wreathed.BrauerWreathedOrder.brauer_wreathed_type_one_principal_block)
    p f hp hpodd hf hq1 G
    hnonab F hFcard Z hZ hZodd (wreathModelHom S e (Original.x (2 ^ n)))
    (CompatibleFamilies.orderOf_x S e hn) (eN.trans eGL.symm)

end CFSG.Wreathed.SameFieldLinearRecognition
