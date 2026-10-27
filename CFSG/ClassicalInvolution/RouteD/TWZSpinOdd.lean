module

public import CFSG.ClassicalInvolution.RouteD.TWZSpinMinus
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.TwinY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

section Statement

@[expose] def SqCountLeOn (t : StatedLieTag) (M : LieUniversal) (B : ℕ) : Prop :=
  ∀ (X : Type) [Group X] (θ : M.K →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center M.K →
    ∀ (R R' : Subgroup M.K), R ∈ GFund t M.D → R' ∈ GFund t M.D → R ≠ R' →
      ∀ (x x' : M.K), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) →
          α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
            Nat.card {S : Subgroup M.K // S ∈ GFund t M.D ∧
              ∀ r ∈ S, (α * α) (θ r) = θ r} ≤ B

end Statement

section Arith

theorem two_mul_framesOdd_zero {q : ℕ} (hq : 2 ≤ q) :
    2 * framesOdd q 0 = q ^ 2 * (q ^ 2 + 1) * framesPlus q 0 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold framesOdd framesPlus
  norm_num
  zify [h1, h2, h4]
  ring

theorem framesPlus_zero_pos {q : ℕ} (hq : 2 ≤ q) : 0 < framesPlus q 0 := by
  unfold framesPlus
  norm_num
  exact ⟨⟨by omega, by positivity⟩, by omega⟩

end Arith

section Transport

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem sqCountLeOn_of_spin (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : Module.finrank F (ι → F) = 7)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    (hlift : ∀ (H : Type) [Group H] (ψ : spinGroup Q →* H),
      ψ.ker ≤ Subgroup.center (spinGroup Q) → LiftSim Q ψ)
    {t : StatedLieTag} (D : UniversalRootDatum (spinGroup Q))
    (hcorr : ∀ R ∈ GFund t D, R.map (spinAction Q) ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ GFund t D, R.map (spinAction Q) = L)
    (hperf : ∀ R ∈ GFund t D, R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ GFund t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1) {B : ℕ}
    (hcount : ∀ X' : Submodule F (ι → F), PolarNondegOn Q X' →
      Module.finrank F X' + 2 = Module.finrank F (ι → F) → ∀ N : ℕ,
        N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
          2 * Nat.card (OFrame (Q.restrict X')) → N ≤ B) :
    SqCountLeOn t ⟨spinGroup Q, D⟩ B := by
  intro X _ θ hθs hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  have hinj : ∀ {S : Subgroup (spinGroup Q)}, S ∈ GFund t D →
      ∀ r ∈ S, spinAction Q r = 1 → r = 1 := fun {S} hS =>
    CFSG.ClassicalInvolution.Asc77.injOn_of_ker_le_center (ker_spinAction_le_center Q)
      fun r hr hcen => hnc S hS r hr (mem_center_of_commutators_central fun y => by
        have := hcen y
        exact this)
  rcases spin_sq_count hodd h5 hQ hrange hZ (by omega) (by omega) hproj hθs hθk (hlift X θ hθk)
    (hperf R hR) (hperf R' hR') (hcorr R hR) (hcorr R' hR') (hinj hR) (hinj hR') hne hx hx2 hx1
    hx' hx'2 hx'1 hxx' α hα4 hαR hαR' D hperf hcorr hsurj with h | h | ⟨X', hnd, hdim, hN⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hcount X' hnd hdim _ hN))

end Transport

section Odd

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.GroupTheory.WeirSylow (IsPlusType)

set_option linter.unusedSectionVars false

variable {p e : ℕ} [Fact p.Prime]


theorem sqCountLe_odd3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    SqCountLeOn .POmegaOdd
      (CFSG.ClassicalInvolution.Generic.modelUniv .POmegaOdd 3 p e Fact.out)
      ((p ^ e) ^ 2 * ((p ^ e) ^ 2 + 1)) := by
  have hn3 : 3 ≤ 3 := le_rfl
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField p e) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := 3) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := 3) trivial hadm
    (by simp)
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hq2 : 2 ≤ p ^ e := by omega
  show SqCountLeOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField p e)),
    oddDatum 3 (GaloisField p e)⟩ _
  refine sqCountLeOn_of_spin hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd 3 _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) hdim (fun F₁ F₂ h => ?_)
    (fun H _ ψ hψ => liftSim_quadOdd hp2 hn3 he ψ hψ) _ (fundCorr_odd hp2 hq hadm).1
    (fundCorr_odd hp2 hq hadm).2 hperf hnc ?_
  · have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  intro X' hnd hdimX N hN
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (detQ (K := GaloisField p e))) = framesPlus (p ^ e) 0 := by
    rw [NonClassical.card_o4, hcard]
    rfl
  rw [hO] at hN
  have hnd' := nondegenerate_polarBilin_restrict hnd
  have hX5 : Module.finrank (GaloisField p e) X' = 5 := by omega
  have hf := card_frame_regular_odd hodd hnd' (j := 0) (by omega)
  rw [hf, hcard] at hN
  have hid := two_mul_framesOdd_zero hq2
  have hpos := framesPlus_zero_pos hq2
  have : N * framesPlus (p ^ e) 0 = (p ^ e) ^ 2 * ((p ^ e) ^ 2 + 1) * framesPlus (p ^ e) 0 := by
    rw [hN, hid]
  exact (Nat.eq_of_mul_eq_mul_right hpos this).le

end Odd

end CFSG.ClassicalInvolution.RouteD.TWZ
