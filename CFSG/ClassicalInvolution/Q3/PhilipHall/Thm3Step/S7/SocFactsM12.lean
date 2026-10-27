module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.GH74.Generic.S45.LEvSporM12Spec
public import Certificates.Certificate517103

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups
  CFSG.ComponentClassification.M12Cover Certificates.S5Rows Certificates.S7SocQ8
  Certificates.S7SocM12

namespace SocM12

theorem QSM_ok : ValidSchreier QSM :=
  Certificates.certificate517103.1.1

theorem card_QSM : Nat.card QSM.originalSubgroup = 128 := by
  rw [card_group QSM QSM_ok, Certificates.certificate517103.1.2]

theorem mem_D_iff (x : Equiv.Perm (Fin 24)) :
    x ∈ blockGroup ↔ inD x = true :=
  mem_iff_sift m12D m12D_check.1 x

theorem QSM_le :
    QSM.originalSubgroup ≤ autModel := by
  rw [QSM, certificate_originalSubgroup, Subgroup.closure_le]
  intro g hg
  have hgens : ([sm0, sm1, sm2, sm3, sm4, sm5, sm6].all fun g =>
      inD g || inD (m12Sigma * g)) = true := Certificates.certificate517103.2.1
  have h : (inD g || inD (m12Sigma * g)) = true := List.all_eq_true.1 hgens g hg
  rw [Bool.or_eq_true, ← mem_D_iff, ← mem_D_iff] at h
  exact mem_autModel.2 h

theorem check_parts :
    refCheck (elemsT QSM) m12Refs = true ∧ sigmaCheck sm6 m12Refs = true ∧ inD sm6 = false ∧
      (m12Refs.all fun R => R.all inD) = true := by
  have h := Certificates.certificate517103.2.2
  simp only [m12SocCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem refs_le
    {R : List (Equiv.Perm (Fin 24))} (hR : R ∈ m12Refs) : ∀ r ∈ R, r ∈ blockGroup := fun r hr =>
  (mem_D_iff r).2 (List.all_eq_true.1 (List.all_eq_true.1 check_parts.2.2.2 R hR) r hr)

theorem sm6_mem : sm6 ∈ QSM.originalSubgroup := by
  rw [QSM, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem sm6_not_mem :
    sm6 ∉ blockGroup := by
  rw [mem_D_iff, check_parts.2.2.1]
  decide

theorem index_QSM :
    ¬ 2 ∣ (QSM.originalSubgroup.subgroupOf autModel).index := by
  have h := Subgroup.card_mul_index (QSM.originalSubgroup.subgroupOf autModel)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSM_le).toEquiv, card_QSM, card_autModel] at h
  have h1 : (QSM.originalSubgroup.subgroupOf autModel).index = 1485 := by omega
  rw [h1]
  decide

theorem m12_conj_ref
    {T : Subgroup (Equiv.Perm (Fin 24))} (hTA : T ≤ autModel) (e : ↥T ≃* QuaternionGroup 2) :
    ∃ c ∈ blockGroup, ∃ R ∈ m12Refs, ∀ t ∈ T, c⁻¹ * t * c ∈ R :=
  SocQ8.exists_conj_ref index_blockGroup
    (IsPGroup.of_card (n := 7) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QSM_le).toEquiv, card_QSM]
      norm_num))
    index_QSM (QSM_le sm6_mem) sm6_not_mem (fun x hx => (mem_elemsT QSM QSM_ok x).2 hx)
    check_parts.1 check_parts.2.1 hTA e

end SocM12

open SocM12 in
theorem m12Q8Classes_proved :
    M12Q8Classes := by
  intro G _ _ N hN hC hS
  haveI := hN
  obtain ⟨eN⟩ := hS
  let θ' : ↥N ≃* ↥blockGroup := (show ↥N ≃* ↥CFSG.Blueprint.NativeSporadic.M12 from eN).trans
    m12EquivD
  set θ := GH74.Generic.S45.EvSpor.m12_smallAutModel.embed N θ'
  have hθ : Function.Injective θ :=
    GH74.Generic.S45.EvSpor.m12_smallAutModel.embed_injective N θ' hC
  have hθA : ∀ x, θ x ∈ autModel := GH74.Generic.S45.EvSpor.m12_smallAutModel.embed_mem N θ'
  have hθN : ∀ n (hn : n ∈ N), θ n = θ' ⟨n, hn⟩ := fun n hn =>
    GH74.Generic.S45.EvSpor.m12_smallAutModel.embed_coe N θ' ⟨n, hn⟩
  have hθP : ∀ p ∈ blockGroup, ∃ l ∈ N, θ l = p := by
    intro p hp
    refine ⟨θ'.symm ⟨p, hp⟩, (θ'.symm ⟨p, hp⟩).2, ?_⟩
    rw [hθN _ (θ'.symm ⟨p, hp⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hconj := fun (T : Subgroup (Equiv.Perm (Fin 24))) (hT : T ≤ autModel)
    (e : ↥T ≃* QuaternionGroup 2) => m12_conj_ref hT e
  refine ⟨fun T hT => ?_, fun T₁ T₂ h₁ h₂ hne T hT => ?_⟩
  · obtain ⟨l, hl, R, hR, h'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj hT
    intro t ht
    obtain ⟨n, hn, hθn⟩ := hθP _ (refs_le hR _ (h' t ht))
    have h1 : l⁻¹ * t * l ∈ N := hθ hθn ▸ hn
    have h2 := N.mul_mem (N.mul_mem hl h1) (N.inv_mem hl)
    rwa [show l * (l⁻¹ * t * l) * l⁻¹ = t by group] at h2
  · have hlen : ∀ R ∈ m12Refs, R.length ≤ 8 := by
      intro R hR
      simp only [m12Refs, List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl <;> simp [q8Span]
    have hpair : ∀ R ∈ m12Refs, R = q8Span m12Q0i m12Q0j ∨ R = q8Span m12Q1i m12Q1j := by
      intro R hR
      simpa [m12Refs] using hR
    obtain ⟨l₁, hl₁, R₁, hR₁, h₁'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₁
    obtain ⟨l₂, hl₂, R₂, hR₂, h₂'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₂
    obtain ⟨l, hl, R, hR, h'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj hT
    have hR12 : R₁ ≠ R₂ := by
      rintro rfl
      exact hne (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₁ hR₁) (SocQ8.card_eq_eight h₁)
        (SocQ8.card_eq_eight h₂) hl₁ hl₂ h₁' h₂')
    rcases SocQ8.eq_or_eq_of_pair (hpair R₁ hR₁) (hpair R₂ hR₂) (hpair R hR) hR12 with h | h
    · exact Or.inl (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₁ hR₁) (SocQ8.card_eq_eight h₁)
        (SocQ8.card_eq_eight hT) hl₁ hl h₁' (h ▸ h'))
    · exact Or.inr (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₂ hR₂) (SocQ8.card_eq_eight h₂)
        (SocQ8.card_eq_eight hT) hl₂ hl h₂' (h ▸ h'))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
