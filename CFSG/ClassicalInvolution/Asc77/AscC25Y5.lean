module

public import CFSG.ClassicalInvolution.Asc77.AscC25Y2
public import CFSG.ClassicalInvolution.Asc77.AscC25Y3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25Y

section Exceptional

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem c25_8_one (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (hzY : z ∈ exactLayer Ω a) (hK : K ∈ tqMembers Ω a)
    (D : LieSystemData p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      (oddQuotientFamily (exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    {c : G} (hbC : c * z * c⁻¹ ∈ Subgroup.centralizer ({a} : Set G))
    {J : Subgroup (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))}
    (hJ : J ∈ oddQuotientFamily (exactPair Ω a))
    {y : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)}
    (hyJ : y ∈ J) (hy4 : y * y * y * y = 1) (hy2 : y * y ≠ 1)
    (hfix : layerAut (exactLayer Ω a)
      (conjSub_exactLayer hyp.std.setting.stand.hyp.conjInvariant hbC) y = y) :
    ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = c * z * c⁻¹ := by
  obtain ⟨M, hM, hMb⟩ := nc4_lift hyp ha2 hbC hJ hyJ hy4 hy2 hfix
  exact exists_centralizer_conj_of_member hyp ha2 hzY hK D hD1 hD4 hM hMb


theorem exists_exceptional (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      b = 1 ∨ b = a ∨ b = z ∨ b = a * z)
    (D : LieSystemData p f (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))
      (oddQuotientFamily (exactPair Ω a)))
    (hD1 : D.card = 1) (hD4 : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) :
    ∃ (w : G) (hwC : w * z * w⁻¹ ∈ Subgroup.centralizer ({a} : Set G)),
      (∀ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ ≠ w * z * w⁻¹) ∧
      ∀ J ∈ oddQuotientFamily (exactPair Ω a),
        ∀ y ∈ J, y * y * y * y = 1 → y * y ≠ 1 →
          layerAut (exactLayer Ω a)
            (conjSub_exactLayer hyp.std.setting.stand.hyp.conjInvariant hwC) y ≠ y := by
  classical
  have hcent := Subgroup.mem_centralizer_iff.mp haA.2
  have haR : ∀ x ∈ R, a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_left hx)).symm
  have haR' : ∀ x ∈ R', a * x = x * a := fun x hx => (hcent x (Subgroup.mem_sup_right hx)).symm
  obtain ⟨hzY, -, -, hK₂, -, -⟩ := C25X.layer_a_frame hyp ha2 ha1 haR haR'
  have hnGF := not_goodFusion hyp ha2 ha1 haz haA hconj hA0
  unfold GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  refine ⟨w, hwC, hw, ?_⟩
  intro J hJ y hyJ hy4 hy2 hfix
  obtain ⟨h, hhC, hh⟩ := c25_8_one hyp ha2 hzY hK₂ D hD1 hD4 hwC hJ hyJ hy4 hy2 hfix
  exact hw h hhC hh

end Exceptional

end C25Y

end CFSG.ClassicalInvolution.Asc77
