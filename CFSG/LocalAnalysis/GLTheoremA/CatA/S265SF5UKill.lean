module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint.Chevalley

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

theorem false_of_labelAll_torusLift_five (h : QSNL 5 S B T x D K)
    (hF : catalogIs (PSimple 5 K) (tyFUni 5)) {lab : GLALabel} (hlab : LabelOf S lab) {r : ℕ}
    (hr : 4 ≤ r) (hT : CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 5 r R) : False := by
  have hc := h.cfg
  haveI : Fact (Nat.Prime 5) := ⟨hc.prime⟩
  obtain ⟨hcomm, lab', -, hraw⟩ := hlab
  obtain ⟨-, -, -, -, -, -, -, hl⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hl
  obtain ⟨R, _, _, _, ⟨-, -, θ, -⟩, hlift⟩ := CFSG.StandardType.largeEvenRawDatum_exists
    (hT _ ((CFSG.StandardType.largeEvenRawDatum_legacy _ _).2
      (Y10GInnLin.largeEvenRawDatumLegacy_of_canonical_carrier hraw)))
  have hxc : x ∈ Subgroup.center Ω := Subgroup.mem_center_iff.2 hc.xcen
  have h1 := SF.pow_mul_card_le_of_torusLift hc.prime hcomm θ hlift
    (hc.elem.mono (Subgroup.zpowers_le.2 hc.xB))
    ((Subgroup.zpowers_le.2 hxc).trans (Subgroup.center_le_centralizer _))
  rw [Nat.card_zpowers, orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1] at h1
  have h2 := hc.rank
  rw [card_eq_of_qsnl h hF] at h2
  have h3 : 5 ^ r * 5 ≤ 5 ^ r * 1 := by
    rw [mul_one]
    exact (h1.trans h2).trans (Nat.pow_le_pow_right (by norm_num) hr)
  exact absurd (Nat.le_of_mul_le_mul_left h3 (by positivity)) (by norm_num)


omit [Finite Ω] in
theorem exists_adjoint_of_labelOf {lab : GLALabel} (hlab : LabelOf S lab) {τ : Tag}
    (hτ : lab.tag = .F4 ∧ τ = .F4 ∨ lab.tag = .E6 ∧ τ = .E6 ∨ lab.tag = .E7 ∧ τ = .E7 ∨
      lab.tag = .E8 ∧ τ = .E8) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ lab.n ∧
      Nonempty (↥S ⧸ Subgroup.center ↥S ≃* adjointGroup τ F) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hτ ⊢
  obtain ⟨-, lab', -, hraw⟩ := hlab
  obtain ⟨-, -, -, -, -, -, -, hl⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hl
  rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨F, _, _, hF, -, -, θ, -⟩ := hraw
    exact ⟨F, inferInstance, inferInstance, CFSG.StandardType.charP_two_of_card hF, hF,
      ⟨θ.trans (CFSG.StandardType.TableBF4.recipeEquiv F)⟩⟩
  · obtain ⟨F, _, _, hF, -, -, θ, -⟩ := hraw
    exact ⟨F, inferInstance, inferInstance, CFSG.StandardType.charP_two_of_card hF, hF,
      ⟨θ.trans (CFSG.StandardType.TableBExc.recipeEquiv .E6 F)⟩⟩
  · obtain ⟨F, _, _, hF, -, -, θ, -⟩ := hraw
    exact ⟨F, inferInstance, inferInstance, CFSG.StandardType.charP_two_of_card hF, hF,
      ⟨θ.trans (CFSG.StandardType.TableBExc.recipeEquiv .E7 F)⟩⟩
  · obtain ⟨F, _, _, hF, -, -, θ, -⟩ := hraw
    exact ⟨F, inferInstance, inferInstance, CFSG.StandardType.charP_two_of_card hF, hF,
      ⟨θ.trans (CFSG.StandardType.TableBExc.recipeEquiv .E8 F)⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
