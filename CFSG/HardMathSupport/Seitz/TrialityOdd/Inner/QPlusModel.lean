module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.QPlusMain
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.Reduction

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.ClassicalInvolution.G2D4Models
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Model

variable {K : Type} [Field K]

def twistedEquivRoot (σ : K ≃+* K) [Finite K] (hK2 : ringChar K ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    twistedGroup σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  MulEquiv.ofBijective
    ((twistedIncl σ.toRingHom).codRestrict (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (fun z => twistedIncl_mem_root σ hK2 hq hK hσq z))
    ⟨fun a b h => by
      have h1 : twistedIncl σ.toRingHom a = twistedIncl σ.toRingHom b :=
        congrArg (Subtype.val : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
          ModGL TwistTag.D4.tag K) h
      exact CFSG.ClassicalInvolution.G2D4Models.twistedIncl_injective σ.toRingHom h1, by
      rintro ⟨g, hg⟩
      have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
        (σ := σ.toRingHom) hK2 hq hK hσq
      rw [← h] at hg
      obtain ⟨a, ha, rfl⟩ := hg
      exact ⟨⟨a, ha⟩, rfl⟩⟩

theorem closure_centralizers_graphFixed_D4_qplus_odd (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (X : Type) [Field X] [Finite X] [CharP X ℓ] (hX : Nat.card X = (ℓ ^ f) ^ 3)
    (σ : X ≃+* X) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ ℓ ^ f + 1)
    (E₁ : Subgroup (graphFixedRootGroup TwistTag.D4 X σ.toRingHom))
    [CFSG.IsElementaryAbelian p E₁] (hcard : Nat.card E₁ = p ^ 2) :
    Subgroup.closure {k' : graphFixedRootGroup TwistTag.D4 X σ.toRingHom |
      ∃ x ∈ E₁, x ≠ 1 ∧ k' * x = x * k'} = ⊤ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hX2 : ringChar X ≠ 2 := by rw [ringChar.eq X ℓ]; exact hℓ2
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (σ := σ.toRingHom) hX hσ
  let ε := (twistedEquivRoot σ hX2 hq2 hX hσ).symm
  have hshape : SylowShape p 2 ((ℓ ^ f + 1).factorization p)
      (twistedGroup σ.toRingHom) :=
    SylowShape.of_mulEquiv (twistedEquivRoot σ hX2 hq2 hX hσ)
      (CFSG.RankThree.PartOne.K128.sylowShape_D4_qplus hf X hX σ hσ (Fact.out) hp5 hpq)
  have hp : p.Prime := Fact.out
  have h := closure_cenGen_twistedGroup_qplus σ hσ3 hX2 hq2 hX hσ hodd hp5 hpq hshape
    (E₁.map ε.toMonoidHom) (by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : x ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
      rw [← map_pow, hx1, map_one]) (by
      rw [Subgroup.card_map_of_injective ε.injective, hcard])
  exact closure_cenGen_eq_top_of_map ε E₁ h

theorem trialityOddQPlus : TrialityOddQPlus := by
  intro q hq K _ _ _ hnab hiso p hp hp5 hpd hpq E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, σ, hX, hσ, hσ3, ⟨e⟩⟩ := exists_trialityD4_model_of_isoLie hiso
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hX' : Nat.card X = (q.p ^ q.exponent) ^ 3 := by rw [hX, hqc]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := by intro c; rw [hσ, hqc]
  have : CharP X q.p := charP_of_trialityD4_model X hX
  have hpq' : p ∣ q.p ^ q.exponent + 1 := by rw [← hqc]; exact hpq
  refine closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E hcard hinner
  intro E₁ hE₁ hcard₁
  have := hE₁
  exact closure_centralizers_graphFixed_D4_qplus_odd q.p q.exponent q.prime_p q.exponent_pos hq X
    hX' σ hσ' p hp5 hpq' E₁ hcard₁

theorem seitzExcAnisotropicTrialityOdd_of_phi36
    (h36 : TrialityOddPhi36) :
    SeitzExcAnisotropicTrialityOdd :=
  seitzExcAnisotropicTrialityOdd_of_residuals trialityOddQPlus h36

end Model

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
