module

public import CFSG.ClassicalInvolution.RouteD.MultiModelOrthGeom
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyOrth
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Transfer

variable {p : ℕ} [Fact p.Prime] {e : ℕ} {KY X : Type} [Group KY] [Finite KY] [Group X]
  {π : KY →* X} {𝓕 : Set (Subgroup KY)} {𝓕' : Set (Subgroup X)}

theorem star_of_map (hker : π.ker ≤ Subgroup.center KY) (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓕') (hsurj : ∀ L ∈ 𝓕', ∃ R ∈ 𝓕, R.map π = L)
    (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (h4 : 4 ≤ Nat.card (GaloisField p e))
    (hgeo : ∀ L ∈ 𝓕', ∀ L₁ ∈ 𝓕', ∀ L₂ ∈ 𝓕', Commutes L L₁ → Commutes L L₂ → Commutes L₁ L₂ →
      (∃ Lβ ∈ 𝓕', (∃ W, LinearBlockStandardPair (GaloisField p e) W L Lβ) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W L₁ Lβ) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W L₂ Lβ)) ∨
      ∃ L₃ ∈ 𝓕', Commutes L L₃ ∧ ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃) :
    ∀ R ∈ 𝓕, ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn 𝓕 R R₁ R₂ →
      ∃ R_β ∈ 𝓕, (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
  intro R hR R₁ hR₁ R₂ hR₂ h01 h02 h12 hnl
  have hci : ∀ {A B : Subgroup KY}, A ∈ 𝓕 → (Commutes (A.map π) (B.map π) ↔ Commutes A B) :=
    fun hA => Gaps.commutes_map_iff hker (hperf _ hA)
  have c01 : Commutes (R.map π) (R₁.map π) := (hci hR).mpr h01
  have c02 : Commutes (R.map π) (R₂.map π) := (hci hR).mpr h02
  have c12 : Commutes (R₁.map π) (R₂.map π) := (hci hR₁).mpr h12
  rcases hgeo _ (hmap R hR) _ (hmap R₁ hR₁) _ (hmap R₂ hR₂) c01 c02 c12 with
    ⟨Lβ, hLβ, a, b, c⟩ | ⟨L₃, hL₃, hc, hn1, hn2⟩
  · obtain ⟨Rβ, hRβ, rfl⟩ := hsurj Lβ hLβ
    exact ⟨Rβ, hRβ,
      Gaps.exists_lin_of_map h4 hC π hker (hperf R hR) (hperf Rβ hRβ) a,
      Gaps.exists_lin_of_map h4 hC π hker (hperf R₁ hR₁) (hperf Rβ hRβ) b,
      Gaps.exists_lin_of_map h4 hC π hker (hperf R₂ hR₂) (hperf Rβ hRβ) c⟩
  · exfalso
    obtain ⟨R₃, hR₃, rfl⟩ := hsurj L₃ hL₃
    apply hnl
    have c3 : Commutes R R₃ := (hci hR).mp hc
    have n1 : ¬ Commutes R₁ R₃ := fun hh => hn1 ((hci hR₁).mpr hh)
    have n2 : ¬ Commutes R₂ R₃ := fun hh => hn2 ((hci hR₂).mpr hh)
    exact (Relation.ReflTransGen.single ⟨hR₁, hR₃, h01.symm, c3.symm, n1⟩).tail
      ⟨hR₃, hR₂, c3.symm, h02.symm, fun hh => n2 hh.symm⟩

theorem fundSet_star {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    ∀ L ∈ Gaps.fundSet Q, ∀ L₁ ∈ Gaps.fundSet Q, ∀ L₂ ∈ Gaps.fundSet Q, Commutes L L₁ →
      Commutes L L₂ → Commutes L₁ L₂ →
      (∃ Lβ ∈ Gaps.fundSet Q, (∃ W, LinearBlockStandardPair K W L Lβ) ∧
        (∃ W, LinearBlockStandardPair K W L₁ Lβ) ∧ (∃ W, LinearBlockStandardPair K W L₂ Lβ)) ∨
      ∃ L₃ ∈ Gaps.fundSet Q, Commutes L L₃ ∧ ¬ Commutes L₁ L₃ ∧ ¬ Commutes L₂ L₃ := by
  rintro L ⟨i, hL⟩ L₁ ⟨i₁, hL₁⟩ L₂ ⟨i₂, hL₂⟩ h01 h02 h12
  rcases orth_star_dichotomy hodd h4 hL hL₁ hL₂ h01 h02 h12 with
    ⟨Lβ, ⟨j, hj⟩, a, b, c⟩ | ⟨L₃, ⟨j, hj⟩, a, b, c⟩
  · exact Or.inl ⟨Lβ, ⟨j, hj⟩, a, b, c⟩
  · exact Or.inr ⟨L₃, ⟨j, hj⟩, a, b, c⟩

end Transfer

section Models

variable {p : ℕ} [Fact p.Prime]

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic

theorem modelStar_pOmegaPlus {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hn : 4 ≤ n) :
    ∀ R ∈ ModelFund p .POmegaPlus n e, ∀ R₁ ∈ ModelFund p .POmegaPlus n e,
      ∀ R₂ ∈ ModelFund p .POmegaPlus n e, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund p .POmegaPlus n e) R R₁ R₂ →
      ∃ R_β ∈ ModelFund p .POmegaPlus n e,
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
  have h3 : 3 ≤ n := by omega
  have h : modelUniv .POmegaPlus n p e Fact.out =
      ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) h3⟩ :=
    RouteD.modelUniv_POmegaPlus_eq h3
  unfold ModelFund
  generalize modelUniv .POmegaPlus n p e Fact.out = L at h ⊢
  subst h
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n (GaloisField p e))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hCQ := Gaps.centralQuot_plus hp2 hn h3 hq
  exact star_of_map hCQ.ker_le hCQ.perf hCQ.map_mem hCQ.surj
    (Gaps.not_dvd_card_center_plus hp2 h3) h4 (fundSet_star hodd h4)

theorem modelStar_pOmegaOdd {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hn : 3 ≤ n) :
    ∀ R ∈ ModelFund p .POmegaOdd n e, ∀ R₁ ∈ ModelFund p .POmegaOdd n e,
      ∀ R₂ ∈ ModelFund p .POmegaOdd n e, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund p .POmegaOdd n e) R R₁ R₂ →
      ∃ R_β ∈ ModelFund p .POmegaOdd n e,
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have : Finite (spinGroup (quadOdd n (GaloisField p e))) :=
    ModelFacts.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hCQ := Gaps.centralQuot_odd hp2 hn hq
  exact star_of_map (KY := spinGroup (quadOdd n (GaloisField p e)))
    hCQ.ker_le hCQ.perf hCQ.map_mem hCQ.surj (Gaps.not_dvd_card_center_odd hp2 hn) h4
    (fundSet_star hodd h4)

theorem modelStar_pOmegaMinus {n e : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    ∀ R ∈ ModelFund p .POmegaMinus n e, ∀ R₁ ∈ ModelFund p .POmegaMinus n e,
      ∀ R₂ ∈ ModelFund p .POmegaMinus n e, Commutes R R₁ → Commutes R R₂ → Commutes R₁ R₂ →
      ¬ LinkedIn (ModelFund p .POmegaMinus n e) R R₁ R₂ →
      ∃ R_β ∈ ModelFund p .POmegaMinus n e,
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p e) W R₂ R_β) := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hn : 4 ≤ n := hadm.2.2
  have hCtx := ModelFacts.spinCtx_pOmegaMinus hadm hp2 hq
  have hY := RouteD.yData_minus (p := p) (f := e) hn hp2 hadm (by omega)
  have hF := Exotic.fundCorr_minus (p := p) (f := e) hp2 hq hadm
  have := hCtx.fin
  exact star_of_map
    (KY := spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (ker_spinAction_le_center _)
    (fun R hR => le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
      R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) (hY.perfR R hR))
    hF.1 hF.2 hCtx.hC h4 (fundSet_star hodd h4)

end Models

end CFSG.ClassicalInvolution.RouteD
