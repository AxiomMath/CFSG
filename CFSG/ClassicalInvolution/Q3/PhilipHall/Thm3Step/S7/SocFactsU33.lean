module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.SocFactsBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.TwoInputs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowU3Model
public import CFSG.GH74.GLS.Prop27.LocBal
public import Certificates.Certificate517102

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups Certificates.S5Rows
  Certificates.S7SocQ8 Certificates.S5RowsU33 Certificates.S7SocU33

namespace SocU33

theorem check_parts :
    refCheck (elemsT QSA) u33Refs = true ∧ sigmaCheck sa0 u33Refs = true ∧
      inQP sa0 = false ∧ (q8Span u33Q0i u33Q0j).all inQP = true ∧
      (q8Span u33Q1i u33Q1j).all inQP = false := by
  have h := Certificates.certificate517102
  simp only [u33SocCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem mem_QP_iff (x : Equiv.Perm (Fin 28)) :
    x ∈ U33.QP.originalSubgroup ↔ inQP x = true :=
  mem_iff_sift U33.QP U33.QP_ok x

theorem sa0_mem : sa0 ∈ QSA.originalSubgroup := by
  rw [QSA, certificate_originalSubgroup]
  exact Subgroup.subset_closure (by simp)

theorem sa0_not_mem :
    sa0 ∉ U33.QP.originalSubgroup := by
  rw [mem_QP_iff, check_parts.2.2.1]
  decide

theorem card_QSA : Nat.card QSA.originalSubgroup = 64 := by
  rw [card_group QSA S5.QSA_ok, S5.QSA_valid.2.1]

theorem index_QSA :
    ¬ 2 ∣ (QSA.originalSubgroup.subgroupOf U33.QA.originalSubgroup).index := by
  have h := Subgroup.card_mul_index (QSA.originalSubgroup.subgroupOf U33.QA.originalSubgroup)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S5.QSA_le_QA).toEquiv, card_QSA,
    S5.card_u33A] at h
  have h1 : (QSA.originalSubgroup.subgroupOf U33.QA.originalSubgroup).index = 189 := by omega
  rw [h1]
  decide

theorem u33_conj_ref
    {T : Subgroup (Equiv.Perm (Fin 28))}
    (hTA : T ≤ U33.QA.originalSubgroup) (e : ↥T ≃* QuaternionGroup 2) :
    ∃ c ∈ U33.QP.originalSubgroup, ∃ R ∈ u33Refs, ∀ t ∈ T, c⁻¹ * t * c ∈ R :=
  SocQ8.exists_conj_ref S5.index_u33P
    (IsPGroup.of_card (n := 6) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S5.QSA_le_QA).toEquiv, card_QSA]
      norm_num))
    index_QSA (S5.QSA_le_QA sa0_mem) sa0_not_mem
    (fun x hx => (mem_elemsT QSA S5.QSA_ok x).2 hx) check_parts.1 check_parts.2.1 hTA e

theorem exists_outer :
    ∃ r ∈ q8Span u33Q1i u33Q1j, r ∉ U33.QP.originalSubgroup := by
  by_contra hcon
  push Not at hcon
  have h1 : (q8Span u33Q1i u33Q1j).all inQP = true :=
    List.all_eq_true.2 fun r hr => (mem_QP_iff r).1 (hcon r hr)
  rw [check_parts.2.2.2.2] at h1
  exact Bool.false_ne_true h1

end SocU33

open SocU33 in
theorem u33Q8Classes_proved :
    U33Q8Classes := by
  intro G _ _ N hN hC hL T₁ T₂ h₁ h₂ hne
  haveI := hN
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA]
    exact S5.QP_le_QA
  set θ := GH74.GLS.Prop27.embedFromModel N M with hθdef
  have hθ : Function.Injective θ := GH74.GLS.Prop27.embedFromModel_injective N M hC
  have hθA : ∀ x, θ x ∈ U33.QA.originalSubgroup := fun x =>
    hMA ▸ GH74.GLS.Prop27.embedFromModel_mem N M x
  have hθN : ∀ n ∈ N, θ n ∈ U33.QP.originalSubgroup := by
    intro n hn
    rw [hθdef, GH74.GLS.Prop27.embedFromModel_of_mem N M hPA hn, ← hMP]
    exact (M.e ⟨n, hn⟩).2
  have hθP : ∀ p ∈ U33.QP.originalSubgroup, ∃ l ∈ N, θ l = p := by
    intro p hp
    rw [← hMP] at hp
    refine ⟨M.e.symm ⟨p, hp⟩, (M.e.symm ⟨p, hp⟩).2, ?_⟩
    rw [hθdef, GH74.GLS.Prop27.embedFromModel_of_mem N M hPA (M.e.symm ⟨p, hp⟩).2,
      Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hconj := fun (T : Subgroup (Equiv.Perm (Fin 28))) (hT : T ≤ U33.QA.originalSubgroup)
    (e : ↥T ≃* QuaternionGroup 2) => u33_conj_ref hT e
  have hlen : ∀ R ∈ u33Refs, R.length ≤ 8 := by
    intro R hR
    simp only [u33Refs, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl <;> simp [q8Span]
  have hpair : ∀ R ∈ u33Refs, R = q8Span u33Q0i u33Q0j ∨ R = q8Span u33Q1i u33Q1j := by
    intro R hR
    simpa [u33Refs] using hR
  obtain ⟨l₁, hl₁, R₁, hR₁, h₁'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₁
  obtain ⟨l₂, hl₂, R₂, hR₂, h₂'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj h₂
  have hR12 : R₁ ≠ R₂ := by
    rintro rfl
    exact hne (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₁ hR₁) (SocQ8.card_eq_eight h₁)
      (SocQ8.card_eq_eight h₂) hl₁ hl₂ h₁' h₂')
  refine ⟨?_, fun T hT => ?_⟩
  ·
    have hout : ∃ T : Subgroup G, ∃ l : G, Nat.card T = 8 ∧
        ∀ t ∈ T, θ (l⁻¹ * t * l) ∈ q8Span u33Q1i u33Q1j := by
      rcases SocQ8.eq_or_eq_of_pair (hpair R₁ hR₁) (hpair R₂ hR₂) (Or.inr rfl) hR12 with h | h
      · exact ⟨T₁, l₁, SocQ8.card_eq_eight h₁, h ▸ h₁'⟩
      · exact ⟨T₂, l₂, SocQ8.card_eq_eight h₂, h ▸ h₂'⟩
    obtain ⟨T, l, hT8, hTl⟩ := hout
    obtain ⟨r, hr, hrP⟩ := exists_outer
    obtain ⟨t, ht, htr⟩ := SocQ8.exists_mem_of_ref θ hθ (by simp [q8Span]) hT8 hTl hr
    have hNtop : N ≠ ⊤ := by
      intro htop
      apply hrP
      rw [← htr]
      exact hθN _ (htop ▸ Subgroup.mem_top _)
    have hcardN : Nat.card N = 6048 := by
      rw [Nat.card_congr e.toEquiv, card_group U33.QP U33.QP_ok, U33.QP_valid.2]
    have hcardG : Nat.card G ≤ 12096 := by
      rw [← S5.card_u33A]
      exact Nat.card_le_card_of_injective (θ.codRestrict _ hθA) fun a b hab =>
        hθ (congrArg Subtype.val hab)
    have h1 := Subgroup.index_mul_card N
    rw [hcardN] at h1
    have h2 : N.index ≠ 1 := fun h => hNtop (Subgroup.index_eq_one.1 h)
    have h3 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h4 : N.index ≤ 2 := by omega
    omega
  · obtain ⟨l, hl, R, hR, h'⟩ := SocQ8.exists_conj_ref_of_embed θ hθ hθA hθP hconj hT
    rcases SocQ8.eq_or_eq_of_pair (hpair R₁ hR₁) (hpair R₂ hR₂) (hpair R hR) hR12 with h | h
    · exact Or.inl (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₁ hR₁) (SocQ8.card_eq_eight h₁)
        (SocQ8.card_eq_eight hT) hl₁ hl h₁' (h ▸ h'))
    · exact Or.inr (SocQ8.mem_lOrbit_of_ref N θ hθ (hlen R₂ hR₂) (SocQ8.card_eq_eight h₂)
        (SocQ8.card_eq_eight hT) hl₂ hl h₂' (h ▸ h'))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident
