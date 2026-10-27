module

public import CFSG.ClassicalInvolution.SmallCases.NDBE1S
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGeom
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Standard
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LieType.Universal.SpinClause0
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
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

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.RouteD.Exotic

variable {p : ℕ} [Fact p.Prime]

theorem SpinTag.isFundTag {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) : IsFundTag t := by
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> trivial

theorem SpinTag.not_A1 {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) :
    ¬ (t = .PSL ∧ n = 2) := by
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem SpinTag.ne_G2 {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) : t ≠ .G2 := by
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem SpinTag.ne_D4 {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) : t ≠ .trialityD4 := by
  rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem not_isSquare_discr {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ¬ IsSquare ((-1 : F) ^ (4 - 1) * (4 * c - b ^ 2)) := by
  rintro ⟨d, hd⟩
  apply hirr ((d - b) / 2)
  field_simp
  norm_num at hd
  linear_combination (-1 : F) * hd

theorem center_eq_of_scalar {σ : Type} [Fintype σ] [DecidableEq σ] {F : Type} [Field F]
    {Q : QuadraticForm F (σ → F)} (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ : CenterScalar Q) (hneg : LinearEquiv.neg F ∉ elementaryGroup Q) {v₀ : σ → F}
    (hv₀ : Q v₀ ≠ 0)
    (hker : ∀ x : spinGroup Q, x ∈ (spinMatrix Q).ker →
      x = 1 ∨ (x : CliffordAlgebra Q) = -1) :
    ∀ y₁ ∈ Subgroup.center (spinGroup Q), ∀ y₂ ∈ Subgroup.center (spinGroup Q),
      y₁ ≠ 1 → y₂ ≠ 1 → y₁ = y₂ := by
  have hneg1 : ∀ y ∈ Subgroup.center (spinGroup Q), y ≠ 1 → (y : CliffordAlgebra Q) = -1 := by
    intro y hy hy1
    have hE : spinAction Q y ∈ elementaryGroup Q := hrange ▸ ⟨y, rfl⟩
    have hcen : (⟨spinAction Q y, hE⟩ : ↥(elementaryGroup Q)) ∈
        Subgroup.center ↥(elementaryGroup Q) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨g, hg⟩
      obtain ⟨s, rfl⟩ : g ∈ (spinAction Q).range := hrange ▸ hg
      apply Subtype.ext
      show spinAction Q s * spinAction Q y = spinAction Q y * spinAction Q s
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hy s)]
    obtain ⟨c, hc⟩ := mem_scalars.mp (hZ hcen)
    have hO := elementaryGroup_le_orthogonalGroup Q hE
    have hcc : c * c = 1 := by
      have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO v₀
      rw [show (spinAction Q y) v₀ = c • v₀ from hc v₀, QuadraticMap.map_smul, smul_eq_mul] at h1
      have h3 : (c * c - 1) * Q v₀ = 0 := by linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hv₀)
    rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
    · have h1 : spinAction Q y = 1 := LinearEquiv.ext fun v => by
        rw [show (spinAction Q y) v = (1 : F) • v from hc v, one_smul]
        rfl
      have hk : y ∈ (spinMatrix Q).ker := by
        rw [ker_spinMatrix]
        exact h1
      exact (hker y hk).resolve_left hy1
    · exfalso
      apply hneg
      have h1 : spinAction Q y = LinearEquiv.neg F := LinearEquiv.ext fun v => by
        rw [show (spinAction Q y) v = (-1 : F) • v from hc v, neg_one_smul]
        rfl
      rw [← h1]
      exact hE
  intro y₁ hy₁ y₂ hy₂ h₁ h₂
  exact Subtype.ext ((hneg1 y₁ hy₁ h₁).trans (hneg1 y₂ hy₂ h₂).symm)

theorem spin_center_eq (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ} (ht : SpinTag t n) :
    ∀ y₁ ∈ Subgroup.center (modelUniv t n p e Fact.out).K,
      ∀ y₂ ∈ Subgroup.center (modelUniv t n p e Fact.out).K, y₁ ≠ 1 → y₂ ≠ 1 → y₁ = y₂ := by
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact center_eq_of_scalar (range_spinAction_quadOdd h2 le_rfl)
      (centerScalar_quadOdd h2 le_rfl) (neg_not_mem_elementaryGroup_quadOdd h2 le_rfl)
      (v₀ := oddZ 3 (GaloisField p e)) (by rw [quadOdd_oddZ]; exact one_ne_zero)
      (fun x hx => (mem_ker_spinMatrix_quadOdd_iff h2 x).mp hx)
  · have hirr := minusCoeffs_irr p e
    exact center_eq_of_scalar (range_spinAction_quadMinus le_rfl hirr)
      (centerScalar_quadMinus le_rfl hirr)
      (fun h => not_isSquare_discr h2 hirr
        ((neg_mem_elementaryGroup_quadMinus_iff h2 hirr le_rfl).mp h))
      (v₀ := (Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).z)
      (by rw [OddFrame.map_z]; exact one_ne_zero)
      (fun x hx => (mem_ker_spinMatrix_quadMinus_iff hirr x).mp hx)

theorem spin_twins (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ}
    (ht : SpinTag t n) (hadm : StatedLieAdmissible t n p e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∃ R' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R ≠ R' ∧ Commutes R R' := by
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro R hR
    obtain ⟨R', hR', htw⟩ := oddTwinsExist hp2 hq hadm R hR
    exact ⟨R', hR', htw.1, htw.2.1⟩
  · intro R hR
    obtain ⟨R', hR', htw⟩ := minusTwinsExist_four hp2 hq hadm R hR
    exact ⟨R', hR', htw.1, htw.2.1⟩

theorem spin_perfect (hp2 : p ≠ 2) {e : ℕ} {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n) :
    Group.IsPerfect (modelUniv t n p e Fact.out).K := by
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact isPerfect_spinGroup_quadOdd h2 le_rfl
  · exact isPerfect_spinGroup_quadMinus le_rfl (minusCoeffs_irr p e)

theorem spin_fund_noncentral {e : ℕ} {t : StatedLieTag} {n : ℕ} (ht : SpinTag t n)
    (hadm : StatedLieAdmissible t n p e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∀ r ∈ R,
      r ∈ Subgroup.center (modelUniv t n p e Fact.out).K → r = 1 :=
  Asc77.fund_noncentral_modelUniv ht.isFundTag hadm ht.not_A1

end CFSG.ClassicalInvolution.NDB.ExoticModel
