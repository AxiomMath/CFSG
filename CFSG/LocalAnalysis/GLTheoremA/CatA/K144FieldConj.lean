module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPTransport
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)

section FieldConj


private lemma mulAut_pow_three_apply {G : Type} [Group G] (φ : MulAut G) (x : G) :
    (φ ^ 3) x = φ (φ (φ x)) := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, pow_succ, pow_one, MulAut.mul_apply,
    MulAut.mul_apply]

theorem primeField_of_fieldKind {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    {α : MulAut K} (hα : α ^ 3 = 1) {labK : GLALabel} (hnot : labK.tag ≠ .triD4)
    (h : FieldKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)) :
    GLAMarking K fun lab _ _ I F θ =>
      GLAPrimeField 3 lab I F (GLAInduces θ fun x y => α x = y) := by
  have hcen := center_centerQuot_eq_bot hq
  have hβ3 : centerQuotAut K α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  have h' := FP.canon_marking_and_labelAll_simple' (P' := FP.TransportFacts 3)
    (fun lab hlab => FP.canonTransportFacts Nat.prime_three (by norm_num) hlab) h
  obtain ⟨hK, lab, hlam, hraw⟩ := h'
  refine ⟨hq.1, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hP, hT⟩
  obtain ⟨hlabel, ⟨i, hi, f, hf, hind⟩, hout⟩ := hP
  subst hlabel
  have h3 : ¬ (lab.tag = .triD4 ∧ 3 = 3) := by
    rintro ⟨h, -⟩
    exact hnot h
  have hLS := (hT.2.2 h3).2
  have hpow : (i * f) ^ 3 = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := θ.surjective x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    have hb : (centerQuotAut K α) ((centerQuotAut K α) ((centerQuotAut K α) s)) = s := by
      have h := congrArg (fun φ : MulAut (K ⧸ Subgroup.center K) => φ s) hβ3
      rwa [mulAut_pow_three_apply, MulAut.one_apply] at h
    rw [mulAut_pow_three_apply, MulAut.one_apply]
    calc
      (i * f) ((i * f) ((i * f) (θ (QuotientGroup.mk s))))
          = (i * f) ((i * f) (θ (QuotientGroup.mk ((centerQuotAut K α) s)))) := by
            rw [hind s ((centerQuotAut K α) s) rfl]
      _ = (i * f) (θ (QuotientGroup.mk ((centerQuotAut K α) ((centerQuotAut K α) s)))) := by
            rw [hind ((centerQuotAut K α) s) ((centerQuotAut K α) ((centerQuotAut K α) s)) rfl]
      _ = θ (QuotientGroup.mk ((centerQuotAut K α) ((centerQuotAut K α)
            ((centerQuotAut K α) s)))) := by
            rw [hind ((centerQuotAut K α) ((centerQuotAut K α) s))
              ((centerQuotAut K α) ((centerQuotAut K α) ((centerQuotAut K α) s))) rfl]
      _ = θ (QuotientGroup.mk s) := by rw [hb]
  have hnotI : i * f ∉ I := fun hI => hout ⟨i * f, hI, hind⟩
  obtain ⟨f', hf', u', hu', hord, heq⟩ :=
    hLS i hi f (Subgroup.subset_closure hf) hnotI hpow
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).symm.trans θ, ?_⟩
  refine ⟨Or.inl hnot, f', hf', u', hu', hord, ?_⟩
  intro k k' hkk'
  subst hkk'
  rw [← heq]
  have h1 := hind (QuotientGroup.mk k) (QuotientGroup.mk (α k))
    (centerQuotAut_mk K α k).symm
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e1 : (CanonInn.quotCenterEquivOfBot hcen).symm (QuotientGroup.mk k) =
      QuotientGroup.mk (QuotientGroup.mk k) := by
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  have e2 : (CanonInn.quotCenterEquivOfBot hcen).symm (QuotientGroup.mk (α k)) =
      QuotientGroup.mk (QuotientGroup.mk (α k)) := by
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  rw [e1, e2]
  exact h1

end FieldConj

end CFSG.LocalAnalysis.GLTheoremA.K144
