module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNeg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem not_bcd_of_canon_twA {labJ : GLALabel} {r k : ℕ} (h : canonLabel labJ = ⟨.twA, r, k⟩) :
    labJ.tag ≠ .B ∧ labJ.tag ≠ .C ∧ labJ.tag ≠ .D := by
  obtain ⟨t, r', n⟩ := labJ
  cases t <;> simp [canonLabel] at h ⊢ <;> split_ifs at h <;> simp_all

theorem bcd_of_canon_A {labJ : GLALabel} {r k : ℕ} (h : canonLabel labJ = ⟨.A, r, k⟩)
    (hbcd : ¬ (labJ.tag ≠ .B ∧ labJ.tag ≠ .C ∧ labJ.tag ≠ .D)) :
    labJ.tag = .D ∧ labJ.rank = 3 ∧ r = 3 := by
  obtain ⟨t, r', n⟩ := labJ
  cases t <;> simp [canonLabel] at h hbcd ⊢ <;> split_ifs at h <;> simp_all

theorem not_twD5_of_canon {labJ : GLALabel} {t : LargeEvenLieTag} {r k : ℕ}
    (h : canonLabel labJ = ⟨t, r, k⟩) (ht : t ≠ .twD) : ¬ (labJ.tag = .twD ∧ labJ.rank = 5) := by
  obtain ⟨t', r', n⟩ := labJ
  rintro ⟨h1, h2⟩
  simp only at h1 h2
  subst h1 h2
  simp [canonLabel] at h
  exact ht h.1.symm

theorem uniLabel_cases (hRig : GGLabelRigidInput) {J : Type} [Group J] [Finite J]
    {labJ : GLALabel} {a m : ℕ} {E : Type} [Field E] [Finite E] (τ' : E ≃+* E)
    (hτ' : ∀ x, τ' (τ' x) = x) (ha : 2 ≤ a) (hτ'm : ∀ x, τ' x = x ^ (2 ^ m))
    (hE : Nat.card E = (2 ^ m) ^ 2) (hJ : HasLabel J (fun l : GLALabel => l = labJ))
    (hφ : Nonempty (J ⧸ Subgroup.center J ≃*
      heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) :
    canonLabel labJ = ⟨.twA, a - 1, m⟩ ∨ canonLabel labJ = ⟨.A, 1, m⟩ := by
  obtain ⟨φ⟩ := hφ
  obtain ⟨hlab, hs, hhas⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hJ
  haveI := hs
  have hm : 1 ≤ m := by
    by_contra hm0
    have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
    rw [hE, show m = 0 by omega] at h2
    norm_num at h2
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · obtain rfl : a = 2 := by omega
    obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ :=
      Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ' hτ' hτ'm hE
    right
    rw [Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig J labJ 2 m k le_rfl hk hJ
      ⟨φ.trans ψ⟩]
  · by_cases h31 : a = 3 ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h31
      exfalso
      haveI := Y10GInnUni.isSolvable_quot_heldSU_three_two τ' hτ' (fun x => by simpa using hτ'm x)
        (by simpa using hE)
      exact Y10GInnUni.not_isSolvable_quot_center
        (solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    · have ham : (a, 2 ^ m) ≠ (3, 2) := by
        intro h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
      obtain ⟨ψ⟩ := Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj Y10GInnUni.uniScalar_holds
        τ' hτ' hτ'm hE ha3 ham
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      have hiso : GGLabelIso labJ ⟨.twA, b, m⟩ :=
        hRig labJ ⟨.twA, b, m⟩ (J ⧸ Subgroup.center J) hlab
          (Y10GInnUni.largeEvenInLambda2_twA hm (by omega) fun hb => by omega) hhas
          (Y10GInnUni.ggHasLabel_twA hE (φ.trans ψ))
      left
      rw [Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso]
      rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10GNegBC
