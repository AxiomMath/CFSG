module

public import CFSG.Foundations.Basic
import CFSG.GH74.GLS.C3.Layer1.St1RigGen

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

theorem component_pair_action_of_subdirect {A B D : Subgroup Q}
    (hA : CFSG.IsComponent A) (hB : CFSG.IsComponent B) (hne : A ≠ B)
    (hD : D ≤ A ⊔ B)
    (hsurjA : ∀ a ∈ A, ∃ b ∈ B, a * b ∈ D)
    (hsurjB : ∀ b ∈ B, ∃ a ∈ A, b * a ∈ D)
    (alpha : MulAut Q) (halphaD : D.map alpha.toMonoidHom = D) :
    ((A.map alpha.toMonoidHom = A ∧ B.map alpha.toMonoidHom = B) ∨
        (A.map alpha.toMonoidHom = B ∧ B.map alpha.toMonoidHom = A)) ∧
      ((∀ d ∈ D, alpha d = d) → A.map alpha.toMonoidHom = A →
        (∀ a ∈ A, alpha a = a) ∧ (∀ b ∈ B, alpha b = b)) := by
  have hAcomp : CFSG.IsComponent (A.map alpha.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv alpha hA
  have hBcomp : CFSG.IsComponent (B.map alpha.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv alpha hB
  have hcommAB : ⁅A, B⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hA hB).resolve_left hne
  have hcommBA : ⁅B, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcommAB
  have hDle : D ≤ A.map alpha.toMonoidHom ⊔ B.map alpha.toMonoidHom := by
    calc D = D.map alpha.toMonoidHom := halphaD.symm
      _ ≤ (A ⊔ B).map alpha.toMonoidHom := Subgroup.map_mono hD
      _ = A.map alpha.toMonoidHom ⊔ B.map alpha.toMonoidHom :=
        Subgroup.map_sup A B alpha.toMonoidHom
  have hDleBA : D ≤ B.map alpha.toMonoidHom ⊔ A.map alpha.toMonoidHom := by
    simpa only [sup_comm] using hDle
  have hAor : A = A.map alpha.toMonoidHom ∨ A = B.map alpha.toMonoidHom :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.eq_of_diag_le_sup
      hA hAcomp hBcomp hcommAB hDle hsurjA
  have hBor : B = B.map alpha.toMonoidHom ∨ B = A.map alpha.toMonoidHom :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.eq_of_diag_le_sup
      hB hBcomp hAcomp hcommBA hDleBA hsurjB
  have hpair : (A.map alpha.toMonoidHom = A ∧ B.map alpha.toMonoidHom = B) ∨
      (A.map alpha.toMonoidHom = B ∧ B.map alpha.toMonoidHom = A) := by
    rcases hAor with hA1 | hA2
    · rcases hBor with hB1 | hB2
      · exact Or.inl ⟨hA1.symm, hB1.symm⟩
      · exact absurd (hA1.trans hB2.symm) hne
    · rcases hBor with hB1 | hB2
      · exact absurd (hA2.trans hB1.symm) hne
      · exact Or.inr ⟨hB2.symm, hA2.symm⟩
  refine ⟨hpair, ?_⟩
  intro hfixD hAeq
  have hBeq : B.map alpha.toMonoidHom = B := by
    rcases hpair with ⟨-, hBmap⟩ | ⟨hAmapB, -⟩
    · exact hBmap
    · exact absurd (hAeq.symm.trans hAmapB) hne
  have hBA : B ≤ Subgroup.centralizer (A : Set Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcommAB
  have hAlphaMemA : ∀ x : ↥A, alpha (x : Q) ∈ A := by
    intro x
    have hx : alpha (x : Q) ∈ A.map alpha.toMonoidHom :=
      Subgroup.mem_map_of_mem alpha.toMonoidHom x.2
    simpa only [hAeq] using hx
  let φA : ↥A →* ↥A :=
    (alpha.toMonoidHom.comp A.subtype).codRestrict A (fun x => hAlphaMemA x)
  have hφA_apply : ∀ x : ↥A, (φA x : Q) = alpha (x : Q) := by
    intro x
    simp [φA, MonoidHom.codRestrict_apply]
  have hcentral : ∀ x : ↥A, x⁻¹ * φA x ∈ Subgroup.center ↥A := by
    intro x
    obtain ⟨b, hb, hxb⟩ := hsurjA (x : Q) x.2
    have hdisp : (x : Q)⁻¹ * alpha (x : Q) ∈ A ⊓ B :=
      CFSG.ComponentClassification.FixedCommutingProduct.displacement_mem_inf
        A B alpha hAeq hBeq (x : Q) b x.2 hb (hfixD ((x : Q) * b) hxb)
    have hcentQ : (x : Q)⁻¹ * alpha (x : Q) ∈
        Subgroup.centralizer (A : Set Q) := hBA hdisp.2
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hcent := Subgroup.mem_centralizer_iff.mp hcentQ (y : Q) y.2
    simpa [hφA_apply x] using hcent
  have hφAid : φA = MonoidHom.id ↥A :=
    @CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      ↥A _ hA.1.1 φA hcentral
  have hfixA : ∀ a ∈ A, alpha a = a := by
    intro a ha
    have h := DFunLike.congr_fun hφAid (⟨a, ha⟩ : ↥A)
    have hcoe := congrArg Subtype.val h
    simpa [φA, MonoidHom.codRestrict_apply] using hcoe
  have hfixB : ∀ b ∈ B, alpha b = b := by
    intro b hb
    obtain ⟨a, ha, hba⟩ := hsurjB b hb
    have hmul : alpha b * alpha a = b * a := by
      simpa only [map_mul] using hfixD (b * a) hba
    rw [hfixA a ha] at hmul
    exact mul_right_cancel hmul
  exact ⟨hfixA, hfixB⟩

end CFSG.GH74.GLS.NT44
