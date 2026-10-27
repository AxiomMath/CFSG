module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovSpor

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.GSThmB.Fus23 CFSG.LocalAnalysis.ComponentInitial

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem ordA_one_ne_20160 (m : ℕ) : Open.ordA 1 m ≠ 20160 :=
  ordA_one_ne_of_lt (B := 35) (by norm_num) (by decide +kernel) m

theorem fixSub_conj {Y : Type*} [Group Y] (s : Y) :
    fixSub (MulAut.conj s) = centralizer ({s} : Set Y) := by
  ext x
  rw [mem_fixSub, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * s = (s * x * s⁻¹) * s := by rw [hx]
      _ = s * x := by group
  · intro hx
    rw [← hx, mul_inv_cancel_right]

include hKa in
theorem exists_fix_component_card (hZJ : center (OddBar h.J) = ⊥) :
    ∃ M : Subgroup (LK h),
      CFSG.Assembly.IsComponentOf M (fixSub ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h))) ∧
      Nat.card (↥M ⧸ center ↥M) = Nat.card (OddBar h.J) := by
  obtain ⟨M₀, hM₀, ⟨eM⟩⟩ := exists_fix_component center_LK (inn_le_GAut hKa)
    (phi hKa (abar h)) (Jhat_le_NL hKa) (Jhat_component hKa).1 (Jhat_component hKa).2
  obtain ⟨eJ⟩ := nonempty_Jhat_equiv hKa hZJ
  exact ⟨M₀, hM₀, Nat.card_congr ((CovHS.quotCenterEquiv eM).trans eJ).toEquiv⟩

theorem card_quotient_center_subgroupOf {Y : Type*} [Group Y] {M C : Subgroup Y} (hMC : M ≤ C) :
    Nat.card (↥(M.subgroupOf C) ⧸ center ↥(M.subgroupOf C)) = Nat.card (↥M ⧸ center ↥M) :=
  Nat.card_congr (CovHS.quotCenterEquiv (subgroupOfEquivOfLe hMC)).toEquiv

include hKa in
theorem false_of_suz
    (hSO : SolMax.SuzOuterComponentsInput)
    (hJ : Nonempty (OddBar h.J ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (OddBar h.J) .PSL 2 p f)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .Suz) : False := by
  have hZJ := center_eq_bot_of_small hJ
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  obtain ⟨eLS, -⟩ : ∃ f : LK h ≃* Blueprint.NativeSporadic.Suz, f = eZ.trans e := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ g : MulAut (LK h),
      g = ((phi hKa (abar h) : ↥(GAut hKa)) : MulAut (LK h)) := ⟨_, rfl⟩
  obtain ⟨M, hM, hMc⟩ := exists_fix_component_card hKa hZJ
  rw [← hφ] at hM
  have hφ2 : φ * φ = 1 := by
    have h0 := pow_orderOf_eq_one (phi hKa (abar h))
    rw [orderOf_phi_abar' hKa, sq] at h0
    rw [hφ, ← Subgroup.coe_mul, h0, Subgroup.coe_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    have h0 := orderOf_phi_abar' hKa
    have h2 : phi hKa (abar h) = 1 := Subtype.ext (by rw [← hφ, h1, Subgroup.coe_one])
    rw [h2, orderOf_one] at h0
    exact absurd h0 (by norm_num)
  have hcard : Nat.card (OddBar h.J) = 20160 ∨ Nat.card (OddBar h.J) = 95040 ∨
      Nat.card (OddBar h.J) = 604800 := by
    rw [← hMc]
    by_cases hin : φ ∈ OuterAutomorphisms.inner (LK h)
    · left
      obtain ⟨s, rfl⟩ := hin
      have hs2 : s * s = 1 := by
        have h1 : MulAut.conj (s * s) = 1 := by rw [map_mul, hφ2]
        exact OutInv.conj_injective (h := h) (h1.trans (map_one _).symm)
      have hs1 : s ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
      have hso : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
      rw [fixSub_conj] at hM
      have hB := (isComponentOf_iff_isComponent_subgroupOf hM.1).1 hM
      rw [← card_quotient_center_subgroupOf hM.1]
      exact CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order
        eLS s hso _ hB
    · right
      have hB := (isComponentOf_iff_isComponent_subgroupOf hM.1).1 hM
      rw [← card_quotient_center_subgroupOf hM.1]
      exact hSO (LK h) ⟨eLS⟩ φ hφ2 hin _ hB
  rcases hJ with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, hq, hmJ⟩
  · have h7 : Nat.card (OddBar h.J) = 2520 :=
      (Nat.card_congr e7.toEquiv).trans card_alternatingGroup_seven
    rw [h7] at hcard
    omega
  · have hJc : Nat.card (OddBar h.J) = Open.ordA 1 (p ^ f) :=
      (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
        (statedClassicalModel_of_lieModel_ne_zero (by norm_num) hmJ)).1 rfl
    rw [hJc] at hcard
    rcases hcard with hc | hc | hc
    · exact ordA_one_ne_20160 _ hc
    · exact CovM12.ordA_one_ne_95040 _ hc
    · exact CovJ2.ordA_one_ne_604800 _ hc

end CFSG.ComponentClassification.GSThmB.Cov
