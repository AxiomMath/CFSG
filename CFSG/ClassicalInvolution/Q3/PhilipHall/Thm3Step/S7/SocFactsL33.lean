module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.GH74.GLS.Prop27.LocBalL33
public import Certificates.Certificate517101

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows
  Certificates.S7SocQ8 Certificates.S7SocL33

namespace SocL33

theorem QSL_ok : ValidSchreier QSL :=
  Certificates.certificate517101.1.1

theorem card_QSL : Nat.card QSL.originalSubgroup = 32 := by
  rw [card_group QSL QSL_ok, Certificates.certificate517101.1.2.1]

theorem QSL_le_QA :
    QSL.originalSubgroup ≤ L33.QA.originalSubgroup :=
  leCheck_sound QSL L33.QA L33.QA_ok Certificates.certificate517101.1.2.2

theorem card_QA : Nat.card L33.QA.originalSubgroup = 11232 := by
  rw [card_group L33.QA L33.QA_ok, L33.QA_valid.2]

theorem index_QP :
    (L33.QP.originalSubgroup.subgroupOf L33.QA.originalSubgroup).index = 2 := by
  have h := Subgroup.card_mul_index (L33.QP.originalSubgroup.subgroupOf L33.QA.originalSubgroup)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe GH74.GLS.Prop27.l33_QP_le_QA).toEquiv,
    card_group L33.QP L33.QP_ok, L33.QP_valid.2, card_QA] at h
  omega

theorem index_QSL :
    ¬ 2 ∣ (QSL.originalSubgroup.subgroupOf L33.QA.originalSubgroup).index := by
  have h := Subgroup.card_mul_index (QSL.originalSubgroup.subgroupOf L33.QA.originalSubgroup)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSL_le_QA).toEquiv, card_QSL, card_QA] at h
  have h1 : (QSL.originalSubgroup.subgroupOf L33.QA.originalSubgroup).index = 351 := by omega
  rw [h1]
  decide

theorem check_parts :
    refCheck (elemsT QSL) l33Refs = true ∧ sigmaCheck sl4 l33Refs = true ∧
      inQP sl4 = false := by
  have h := Certificates.certificate517101.2
  simp only [l33SocCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem sl4_mem : sl4 ∈ QSL.originalSubgroup := by
  rw [QSL, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem sl4_not_mem :
    sl4 ∉ L33.QP.originalSubgroup := by
  rw [mem_iff_sift L33.QP L33.QP_ok]
  have h := check_parts.2.2
  rw [inQP] at h
  rw [h]
  decide

theorem l33_conj_ref
    {T : Subgroup (Equiv.Perm (Fin 26))} (hTA : T ≤ L33.QA.originalSubgroup)
    (e : ↥T ≃* QuaternionGroup 2) :
    ∃ c ∈ L33.QP.originalSubgroup, ∃ R ∈ l33Refs, ∀ t ∈ T, c⁻¹ * t * c ∈ R :=
  SocQ8.exists_conj_ref index_QP
    (IsPGroup.of_card (n := 5) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSL_le_QA).toEquiv, card_QSL]
      norm_num))
    index_QSL (QSL_le_QA sl4_mem) sl4_not_mem (fun x hx => (mem_elemsT QSL QSL_ok x).2 hx)
    check_parts.1 check_parts.2.1 hTA e

end SocL33

open SocL33 in
theorem l33Q8Class_proved :
    L33Q8Class := by
  intro G _ _ N hN hC hL T₁ T₂ h₁ h₂
  haveI := hN
  obtain ⟨e⟩ := L33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := L33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA]
    exact GH74.GLS.Prop27.l33_QP_le_QA
  set θ := GH74.GLS.Prop27.embedFromModel N M with hθdef
  have hθ : Function.Injective θ := GH74.GLS.Prop27.embedFromModel_injective N M hC
  have hθA : ∀ x, θ x ∈ L33.QA.originalSubgroup := fun x =>
    hMA ▸ GH74.GLS.Prop27.embedFromModel_mem N M x
  have hθP : ∀ p ∈ L33.QP.originalSubgroup, ∃ l ∈ N, θ l = p := by
    intro p hp
    rw [← hMP] at hp
    refine ⟨M.e.symm ⟨p, hp⟩, (M.e.symm ⟨p, hp⟩).2, ?_⟩
    rw [hθdef, GH74.GLS.Prop27.embedFromModel_of_mem N M hPA (M.e.symm ⟨p, hp⟩).2,
      Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hconj := fun (T : Subgroup (Equiv.Perm (Fin 26))) (hT : T ≤ L33.QA.originalSubgroup)
    (e : ↥T ≃* QuaternionGroup 2) => l33_conj_ref hT e
  obtain ⟨l₁, hl₁, R₁, hR₁, h₁'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₁
  obtain ⟨l₂, hl₂, R₂, hR₂, h₂'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₂
  simp only [l33Refs, List.mem_singleton] at hR₁ hR₂
  subst hR₁ hR₂
  exact SocQ8.mem_lOrbit_of_ref N θ hθ (by simp [q8Span]) (SocQ8.card_eq_eight h₁)
    (SocQ8.card_eq_eight h₂) hl₁ hl₂ h₁' h₂'

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
