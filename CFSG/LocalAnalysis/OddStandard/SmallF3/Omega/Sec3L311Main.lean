module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L311Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem pocketCore2_le_conjugate [Finite G] (h33 : Asc82Lemma33F) (h34a : Asc82Lemma34a)
    (h36 : Asc82Lemma36) (hCS : Asc82OmegaPlusCStar) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {z g : G}
    (hz2 : orderOf z = 2) (hg : g⁻¹ * t * g = t * z) :
    pocketCore2 L z ≤ CFSG.conjugate L g := by
  refine iSup₂_le fun K hK => ?_
  have hD : Sec3PocketData t L z K :=
    sec3PocketData_of_sl23PocketIn hS.involution hS.component (Or.inl hS.inF)
      (conjugate_eq_self_of_lemma36 h36 hS) hz2 hK
  have hS' : Sec3SettingLB G (t * z) (CFSG.conjugate L g) := by
    rw [← hg]
    exact hS.conjugate g
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have htc : t ∈ centralizer ((L ⊔ zpowers t : Subgroup G) : Set G) := by
    have hle : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le hLt (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hu2 : orderOf (t * z) = 2 := by
    rw [← hg, orderOf_conjugate_eq]
    exact hS.involution
  rcases h34a G t L hS t L z K (t * z) (CFSG.conjugate L g) hD hu2 ⟨t, htc, rfl⟩
      hS'.component (Or.inl hS'.inF) with hcomm | hle
  · exfalso
    have hcyc := h33 G (t * z) (CFSG.conjugate L g) hS' (CFSG.conjugate L g)
      (hCS G (t * z) (CFSG.conjugate L g) hS' (lieModel_quotient_oddCore_conjugate g hΩ))
      hS'.inF
    obtain ⟨f, hf, -, hfK⟩ := exists_quaternion_of_isSL23Mod hK.2.2.2 hK.1 hz2
    have hKc : K ≤ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    let f' : QuaternionGroup 2 →* ↥(centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)) :=
      f.codRestrict _ fun q => hKc (hfK (MonoidHom.mem_range.mpr ⟨q, rfl⟩))
    refine not_injective_quaternion_of_cyclic_sylow hcyc f' fun a b hab => ?_
    exact hf (congrArg Subtype.val hab)
  · exact hle

theorem twoU43Comps_le_conjugate [Finite G] (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36)
    (h39 : Asc82Lemma39) (hInner : Asc82OmegaPlusInner) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hΩ : LieModel (↥L ⧸ oddCore ↥L) .POmegaPlus 4 3 1) {z g : G}
    (hg : g⁻¹ * t * g = t * z) {d : G} (hd2 : orderOf d = 2) (hdL : d ∈ L)
    (hdL' : d ∈ CFSG.conjugate L g) : twoU43Comps L d ≤ CFSG.conjugate L g := by
  refine iSup₂_le fun K hK => ?_
  obtain ⟨hKc, hdK, hK2⟩ := hK
  have hS' : Sec3SettingLB G (t * z) (CFSG.conjugate L g) := by
    rw [← hg]
    exact hS.conjugate g
  have hΩ' := lieModel_quotient_oddCore_conjugate g hΩ
  have hu2 : orderOf (t * z) = 2 := by
    rw [← hg, orderOf_conjugate_eq]
    exact hS.involution
  have h39K := h39 G t L hS d K hd2 hdL hdK hKc hK2
  have hdp : ¬ IsI4PlusIn (CFSG.conjugate L g) d := by
    rintro ⟨-, K', hK'⟩
    have hD := sec3PocketData_of_sl23PocketIn hu2 hS'.component (Or.inl hS'.inF)
      (conjugate_eq_self_of_lemma36 h36 hS') hd2 hK'
    exact h34c G (t * z) (CFSG.conjugate L g) hS' (t * z) (CFSG.conjugate L g) d K' hD K
      h39K.1 h39K.2.1
  obtain ⟨X, -, hXc, hdX, hX2, -⟩ := hInner G (CFSG.conjugate L g) ⟨hS'.inF, hΩ'⟩ d hd2 hdL' hdp
  obtain ⟨hXC, hXF, -⟩ := h39 G (t * z) (CFSG.conjugate L g) hS' d X hd2 hdL' hdX hXc hX2
  rw [← h39K.2.2 X hXC hXF]
  exact hXc.le.trans inf_le_left

theorem asc82Lemma311_of_inputs (h33 : Asc82Lemma33F) (h34a : Asc82Lemma34a)
    (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36) (h39 : Asc82Lemma39)
    (hInner : Asc82OmegaPlusInner) (hOuter : Asc82OmegaPlusOuter)
    (hPC : Asc82OmegaPlusPocketedConj) (hPL : Asc82OmegaPlusPocketLift)
    (hCl : Asc82OmegaPlusClosure) (hCS : Asc82OmegaPlusCStar) (hPE : Asc82PocketExists)
    (hGen : Asc82OmegaPlusGen) : Asc82Lemma311 := by
  intro G _ _ t L hS hΩ
  obtain ⟨z, hz⟩ := exists_isI4PlusIn_of_pocketExists hPE hS
  have hconj := isConj_of_omegaPlus h33 h34c h36 h39 hInner hOuter hPC hPL hCl hCS hS hΩ hz
  obtain ⟨g, hg0⟩ := isConj_iff.1 hconj
  have hg : g⁻¹ * t * g = t * z := by
    calc g⁻¹ * t * g = g⁻¹ * (g * (t * z) * g⁻¹) * g := by rw [hg0]
      _ = t * z := by group
  have hQ := pocketCore2_le_conjugate h33 h34a h36 hCS hS hΩ hz.1 hg
  have hLL' : L ≤ CFSG.conjugate L g := by
    refine (hGen G L ⟨hS.inF, hΩ⟩ z hz).trans (iSup₂_le fun d hd => ?_)
    exact twoU43Comps_le_conjugate h34c h36 h39 hInner hS hΩ hg hd.1
      (pocketCore2_le L z hd.2.1) (hQ hd.2.1)
  have hLtz : L ≤ centralizer ({t * z} : Set G) := by
    have h1 : CFSG.conjugate L g ≤ centralizer ({g⁻¹ * t * g} : Set G) :=
      (hS.conjugate g).component.le
    rw [hg] at h1
    exact hLL'.trans h1
  have hcommz : ∀ l ∈ L, l * z = z * l := by
    intro l hl
    have h1 : l * t = t * l := Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hl)
    have h2 : l * (t * z) = (t * z) * l := Subgroup.mem_centralizer_singleton_iff.mp (hLtz hl)
    have h3 : t * (l * z) = t * (z * l) := by
      calc t * (l * z) = (t * l) * z := by rw [mul_assoc]
        _ = (l * t) * z := by rw [h1]
        _ = l * (t * z) := by rw [mul_assoc]
        _ = (t * z) * l := h2
        _ = t * (z * l) := by rw [mul_assoc]
    exact mul_left_cancel h3
  exact not_forall_commute_of_pOmegaPlus hΩ hz.1 hz.mem hcommz

end CFSG.OddStandard.SmallF3.Omega
