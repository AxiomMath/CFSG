module

public import CFSG.LargeExtraspecial.AS35YFHub
public import CFSG.LargeExtraspecial.S12InspFamDFi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace S14

@[expose] def Asc512FischerDataStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    ¬ InspNondeg _ S.EhatAsc →
      (∃ d₀ : S.LbarAsc ⧸ center S.LbarAsc, S.EhatAsc = {x | IsConj d₀ x}) ∧
      (∀ d ∈ S.EhatAsc, orderOf d = 2) ∧
      (∀ d ∈ S.EhatAsc, ∀ e ∈ S.EhatAsc, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∧
      closure S.EhatAsc = ⊤ ∧ center (S.LbarAsc ⧸ center S.LbarAsc) = ⊥ ∧
      IsSimpleGroup (commutator (S.LbarAsc ⧸ center S.LbarAsc))

theorem asc_false_of_fi24_gen {Xh : Type*} [Group Xh] {τ : Xh} {𝒜 : Set (MulAut Xh)}
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜 : ∀ α ∈ 𝒜, α τ = τ) {L : Subgroup Xh} (hCL : centralizer ({τ} : Set Xh) = zpowers τ ⊔ L)
    (hinf : zpowers τ ⊓ L = ⊥) (eL : L ≃* CFSG.Blueprint.NativeSporadic.Fi23) : False := by
  obtain ⟨hsimp, hns⟩ := s12_fi24_quotient_facts hCL hinf eL
  exact Setting.asc_false_of_centralizer_hom_simple_gen hub h𝒜 hns (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) fun k hk x => by
      rw [QuotientGroup.ker_mk'] at hk
      exact s12_zpowers_subgroupOf_central _ k hk x

theorem asc512InspFor_Fi_of (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt)
    (hdata : Asc512FischerDataStmt)
    (hcls : Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧
      (FischerSym X D ∨ FischerSp X D ∨ FischerO X D ∨ FischerPSU X D ∨ FischerF3 X D)) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerFi X D := by
  intro G _ _ S hS hst hfam
  obtain ⟨hND, -⟩ := hfam
  obtain ⟨hclass, hinv, hprod, hgen, hcenter, hsimple⟩ := hdata G S hS hst hND
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  obtain ⟨g, rfl⟩ := Setting.exists_conj_of_mem_DSet S ht
  have hgM := Setting.mem_M_of_mem_ESet S hS.sixFour ht.1
  have hd : (QuotientGroup.mk (Setting.ascTL ht hgM) : S.LbarAsc ⧸ center S.LbarAsc) ∈
      S.EhatAsc := ⟨Setting.ascTL ht hgM, S.ρ_mem_DbarAsc ht hgM, rfl⟩
  have hub := Setting.asc_hub hst h58 hS ht hgM
  have hfix := Setting.asc_hub_fix hst hP hS ht hgM
  have hcen : ∀ (C : Subgroup (S.LbarAsc ⧸ center S.LbarAsc)) (k : C),
      k ∈ (QuotientGroup.mk' (center C)).ker → ∀ x : C, k * x = x * k := fun C k hk x => by
    rw [QuotientGroup.ker_mk'] at hk
    exact (mem_center_iff.mp hk x).symm
  obtain ⟨-, -, -, h22, h23, h24⟩ :=
    CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition _ _
      hclass hinv hprod hgen hcenter hsimple _ hd
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned _ _
      hclass hinv hprod hgen hcenter hsimple with h1 | h2 | h3 | h4 | h5 | ⟨φ, -⟩ | ⟨φ, -⟩ |
      ⟨φ, -⟩
  · exact hcls G S hS hst ⟨hND, Or.inl h1⟩
  · exact hcls G S hS hst ⟨hND, Or.inr (Or.inl h2)⟩
  · exact hcls G S hS hst ⟨hND, Or.inr (Or.inr (Or.inl h3))⟩
  · exact hcls G S hS hst ⟨hND, Or.inr (Or.inr (Or.inr (Or.inl h4)))⟩
  · exact hcls G S hS hst ⟨hND, Or.inr (Or.inr (Or.inr (Or.inr h5)))⟩
  · exfalso
    obtain ⟨hperf, -, hZ2, hLie⟩ := h22 ⟨φ⟩
    have := CFSG.Fischer.Classification.Recognition.isSimpleGroup_of_lieModel_PSU_six hLie
    exact Setting.asc_false_of_centralizer_hom_simple_gen hub hfix
      (s12_not_isSolvable_quotient_center hperf hZ2) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (hcen _)
  · exfalso
    obtain ⟨hperf, -, hZ2, ⟨e⟩⟩ := h23 ⟨φ⟩
    have := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
    exact Setting.asc_false_of_centralizer_hom_simple_gen hub hfix
      (s12_not_isSolvable_quotient_center hperf hZ2) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (hcen _)
  · exfalso
    obtain ⟨L, ⟨eL⟩, hCL, hinf, -⟩ := h24 ⟨φ⟩
    exact asc_false_of_fi24_gen hub hfix hCL hinf eL

end S14

end CFSG.LargeExtraspecial
