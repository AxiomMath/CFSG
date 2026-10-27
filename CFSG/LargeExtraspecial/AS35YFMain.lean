module

public import CFSG.LargeExtraspecial.AS35YFFiData
public import CFSG.LargeExtraspecial.AS35YFSix
public import CFSG.LargeExtraspecial.AS35YFSp
public import CFSG.LargeExtraspecial.AS35YFO
public import CFSG.LargeExtraspecial.AS35YFF3
public import CFSG.LargeExtraspecial.S12TriH2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Equiv Equiv.Perm Matrix

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem asc_exists_tbar (hS : S.SixHyp) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.DSet ∧ g * S.z * g⁻¹ ∈ S.M := by
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  have hconj : ∃ h : G, h * S.z * h⁻¹ = t := Setting.exists_conj_of_mem_DSet S ht
  obtain ⟨g, rfl⟩ := hconj
  exact ⟨g, ht, Setting.mem_M_of_mem_ESet S hS.sixFour ht.1⟩

variable (hst : S.Asc512Standing)
include hst

theorem asc_false_of_perm (h58 : S14.Asc512FiveEightStmt) (hP : S14.Asc512PbarStmt)
    (hS : S.SixHyp) {g : G} (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {m : ℕ}
    (hm : m = 3 ∨ 5 ≤ m) (φ : S.LbarAsc ⧸ center S.LbarAsc ≃* Perm (Fin m))
    (hφ : ∀ x : S.LbarAsc ⧸ center S.LbarAsc, x ∈ S.EhatAsc ↔ (φ x).IsSwap) : False := by
  rcases hm with rfl | hm5
  · exact asc_false_of_perm_three hst hP hS htD htM φ hφ
  obtain rfl | rfl | hm7 : m = 5 ∨ m = 6 ∨ 7 ≤ m := by omega
  · exact asc_false_of_perm_five hst hP hS htD htM φ hφ
  · exact asc_false_of_perm_six hst hP hS htD htM φ hφ
  · have hτ : (φ (QuotientGroup.mk (ascTL htD htM))).IsSwap :=
      (hφ _).mp ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
    obtain ⟨a, b, hab, hτ'⟩ := hτ
    exact asc_false_of_perm_ge_seven_gen (asc_hub hst h58 hS htD htM)
      (asc_hub_fix hst hP hS htD htM) hm7 φ hab hτ'

theorem asc_false_of_sp_model (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) {m : ℕ} (hm : 2 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hmod : CFSG.Open.fischerLinearModel S.EhatAsc
      (CFSG.Open.fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (CFSG.Open.fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) : False := by
  have htE : (QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc) ∈ S.EhatAsc :=
    ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
  by_cases hm3 : 3 ≤ m
  · obtain ⟨φ, hφ⟩ := hmod
    obtain ⟨v, hv0, hT⟩ := (hφ _).1 htE
    exact asc_false_of_sp hst hP hS htD htM hm3 halt hnd φ hv0 hT
  · obtain rfl : m = 2 := by omega
    obtain ⟨φ, hφ⟩ := S12Insp5.exists_perm_six_of_sp_two
      ⟨_, htE, fun x => asc_mem_Ehat_iff hst htD htM x⟩ halt hnd hmod
    exact asc_false_of_perm_six hst hP hS htD htM φ hφ

end Setting

namespace S14

theorem asc512InspFor_sym (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerSym X D := by
  intro G _ _ S hS hst hfam
  exfalso
  obtain ⟨g, htD, htM⟩ := Setting.asc_exists_tbar hS
  obtain ⟨m, hm, φ, hφ⟩ := hfam.2
  exact Setting.asc_false_of_perm hst h58 hP hS htD htM hm φ hφ

theorem asc512InspFor_sp (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerSp X D := by
  intro G _ _ S hS hst hfam
  exfalso
  obtain ⟨g, htD, htM⟩ := Setting.asc_exists_tbar hS
  obtain ⟨m, hm, b, halt, hnd, hmod⟩ := hfam.2
  exact Setting.asc_false_of_sp_model hst hP hS htD htM hm halt hnd hmod

theorem asc512InspFor_orth (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerO X D := by
  intro G _ _ S hS hst hfam
  exfalso
  obtain ⟨g, htD, htM⟩ := Setting.asc_exists_tbar hS
  obtain ⟨m, hm, Q, hnd, hmin, hmod⟩ := hfam.2
  by_cases hm3 : 3 ≤ m
  · exact Setting.asc_false_of_orth hst h58 hP hS htD htM hm3 hnd hmod
  · obtain rfl : m = 2 := by omega
    exact Setting.asc_false_of_orth_two hst hP hS htD htM hnd (hmin rfl) hmod

theorem asc512InspFor_classical (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧
      (FischerSym X D ∨ FischerSp X D ∨ FischerO X D ∨ FischerPSU X D ∨ FischerF3 X D) := by
  intro G _ _ S hS hst hfam
  rcases hfam.2 with h | h | h | h | h
  · exact asc512InspFor_sym h58 hP G S hS hst ⟨hfam.1, h⟩
  · exact asc512InspFor_sp hP G S hS hst ⟨hfam.1, h⟩
  · exact asc512InspFor_orth h58 hP G S hS hst ⟨hfam.1, h⟩
  · exact asc512InspFor_psu hP G S hS hst ⟨hfam.1, h⟩
  · exact asc512InspFor_F3 h58 hP G S hS hst ⟨hfam.1, h⟩

section Fischer


theorem asc512InspFor_Fi (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerFi X D :=
  asc512InspFor_Fi_of h58 hP (asc512FischerData_of S12Tri.fischerTrialityInput hP h58)
    (asc512InspFor_classical h58 hP)

theorem asc512InspFor_degenerate (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧
      S12FischerConclusion X D := by
  intro G _ _ S hS hst hfam
  rcases (s12FischerConclusion_iff _ _).1 hfam.2 with h | h | h | h | h | h
  · exact asc512InspFor_classical h58 hP G S hS hst ⟨hfam.1, Or.inl h⟩
  · exact asc512InspFor_classical h58 hP G S hS hst ⟨hfam.1, Or.inr (Or.inl h)⟩
  · exact asc512InspFor_classical h58 hP G S hS hst ⟨hfam.1, Or.inr (Or.inr (Or.inl h))⟩
  · exact asc512InspFor_classical h58 hP G S hS hst
      ⟨hfam.1, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact asc512InspFor_classical h58 hP G S hS hst
      ⟨hfam.1, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩
  · exact asc512InspFor_Fi h58 hP G S hS hst ⟨hfam.1, h⟩

end Fischer

end S14

end CFSG.LargeExtraspecial
