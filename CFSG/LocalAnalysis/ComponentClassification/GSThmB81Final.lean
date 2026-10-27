module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Exit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

structure Lemma81Inputs : Prop where
  in81 : In81
  cfi : CFProp23IndexReduced
  ac : CFAutSmallCommutator
  aq : CFAutSmallQuotient
  st : SuzukiTausskyInput
  jo : CFSec8JOrder
  f2 : CFSp4F2
  l0 : CF81L0
  conf : CF81Conf
  noNilp : CF81NoNilp
  fieldOrd : CF81FieldOrd
  diag : CF81Diag
  step3 : GS81Step3Input
  step8 : GS81Step8Input
  step9 : GS81Step9Input
  exit6 : GS81Exit6Input
  exit10 : GS81Exit10Input
  exit11 : GS81Exit11Input
  gh74 : ClassicalInvolution.GH74SectionalModels
  ci : GSLit.ClassicalInvolutionInput
  rs : RestrictedStandardInput

open Hyp59 Hyp59.L81Hyp Hyp59.L81Hyp.Data in
theorem lemma81 (I : Lemma81Inputs) : Lemma81StatementK := by
  intro H _ _ h hKS hc hP8
  have J := I.in81
  have H₁ := L81Hyp.of_inputs J.b1 J.b6 J.cf23 J.cf24 J.cfc I.cfi hKS hc hP8
  obtain ⟨d⟩ := H₁.exists_data J.b1 J.b6 J.cf23 J.cf24 I.ac I.aq I.st J.cf1 J.cf2 I.jo I.f2
  have F := d.facts J.cf1 J.cf2 I.jo I.l0 I.conf
  obtain ⟨v, hvN, hva, hvz, hvv, hv2⟩ := d.exists_v J.b1 J.b6 J.cf23 J.cf24 J.cfc J.cf1 J.cf2 J.c F
  have hv : d.IsV v := ⟨hvN, hva, hvz, hvv, hv2⟩
  have h3b : ∀ c : H, c⁻¹ * d.b * c ≠ d.b * d.z := not_conj_b_bz (d := d) I.noNilp
    (fun hbz => I.step3 H h H₁ d F (fun c => not_conj_a_b hv J F c) hbz)
  have h3 := not_conj_asigma_sigma F h3b
  by_cases h6 : ∃ c : H, c⁻¹ * (h.a * d.sigma) * c = d.z * d.sigma
  ·
    obtain ⟨y, hyS, hya, hyz, hyσ⟩ := exists_y hv J F h3 h6
    have hdf := P_dihedral_fusion hv J F h3 hyS hya hyz hyσ I.fieldOrd I.diag
    have hst : d.Stage7 v :=
      { facts := F
        isV := hv
        not_b_bz := h3b
        conj_asigma := h6
        card_P := card_P_eq_card_D hv J F h3 I.fieldOrd
        P_le_F := P_le_F hv J F h3 I.fieldOrd
        dihedral := hdf.1
        fusion := hdf.2
        y := ⟨y, hyS, hya, hyz, hyσ, y_nontrivial_D J F I.diag hyS hyσ,
          y_nontrivial_P hv J F h3 hyS hya hyz hyσ I.fieldOrd I.diag⟩ }
    have hnA8 := not_A8 J I.step8 hst
    rcases hc with ⟨-, -, hA8⟩ | ⟨p, f, hp, hp2, hf, hJ, -, hK⟩
    · exact absurd hA8 hnA8
    ·
      obtain ⟨h9a, h9b⟩ := I.step9 H h H₁ d v hst p f hp hp2 hf hK
      by_cases hq : p ^ f = 3
      ·
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hq ▸ dvd_pow_self p (by omega : f ≠ 0))
        subst hp3
        have hf1 : f = 1 :=
          Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hq.trans (pow_one 3).symm)
        subst hf1
        exact I.exit11 I.in81 I.rs H h H₁ d v hst hJ hK h9a (h9b hq)
      ·
        have h3p : 3 ≤ p := by have := hp.two_le; omega
        have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
        exact I.exit10 I.ci H h H₁ d v hst p f hp hp2 hf hJ hK (by omega) h9a
  ·
    push Not at h6
    exact I.exit6 I.gh74 H h H₁ (exists_sylow_le_centralizer_B hv J F h3 h6)

end CFSG.ComponentClassification.GSThmB
