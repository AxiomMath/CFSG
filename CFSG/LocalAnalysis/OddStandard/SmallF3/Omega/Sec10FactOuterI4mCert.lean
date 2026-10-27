module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactOuterI4m
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import Certificates.Certificate442016

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace Mo4m

open Certificates.OmegaOuter

theorem mem_b0Elems {g : P45} : g ∈ b0Elems () ↔ g ∈ B0 :=
  mem_B0_iff.symm

theorem check_sound
    {a : P45} (ha : a ∈ QA45.originalSubgroup) (hsq : a * a = 1)
    (haP : a ∉ QP45.originalSubgroup) (hB : ∀ b ∈ B0, a * b * a⁻¹ ∈ B0) :
    ∃ β ∈ B0, a * β = β * a ∧ Certificates.OmegaInv.fixCnt (a * β) = 15 := by
  have h := Certificates.certificate442016
  simp only [check, outerChk, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true,
    mem_elemsT QA45 QA45_ok, mem_elemsT QP45 QP45_ok, mem_b0Elems] at h
  rcases h a ha with ((h1 | h1) | h1) | ⟨β, hβ, h2, h3⟩
  · exact absurd hsq h1
  · exact absurd h1 haP
  · exfalso
    have h4 : (b0Elems.all fun x => decide (a * x * a⁻¹ ∈ b0Elems)) = true := by
      rw [List.all_eq_true]
      intro x hx
      rw [decide_eq_true_eq, mem_b0Elems]
      exact hB x (mem_b0Elems.1 hx)
    rw [h4] at h1
    exact Bool.noConfusion h1
  · exact ⟨β, hβ, h2, h3⟩

end Mo4m

theorem asc82FactOuterI4m_of_cert :
    Asc82FactOuterI4m := by
  intro G _ _ L hL P hP s0 hs0 hord hs0L
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hFP⟩ := F0.exists_frame_syl hP
  have hPL : P ≤ L := hP.1
  have hJ : JElem P = F.pre B0 := F.jElem_eq hFP hPL
  obtain ⟨hs0N, hs0J⟩ := Subgroup.mem_inf.1 hs0
  let y : ↥(normalizer (L : Set G)) := ⟨s0, hs0N⟩
  have hs0sq : s0 * s0 = 1 := by
    have h := pow_orderOf_eq_one s0
    rwa [hord, pow_two] at h
  have ha : F.φ y ∈ QA45.originalSubgroup := F.mem_A y
  have hsq : F.φ y * F.φ y = 1 := by
    rw [← map_mul, show y * y = 1 from Subtype.ext hs0sq, map_one]
  have haP : F.φ y ∉ QP45.originalSubgroup := by
    intro h
    apply hs0L
    have h1 : y ∈ (L ⊔ centralizer (L : Set G)).subgroupOf (normalizer (L : Set G)) := by
      rw [F.sup_subgroupOf_eq]
      exact h
    exact Subgroup.mem_subgroupOf.1 h1
  have hB : ∀ b ∈ B0, F.φ y * b * (F.φ y)⁻¹ ∈ B0 := fun b hb =>
    F.phi_conj_mem_B0 y (by rw [← hJ]; exact hs0J) hb
  obtain ⟨β, hβ, hcomm, hfix⟩ := Mo4m.check_sound ha hsq haP hB
  obtain ⟨b, hb⟩ := F.ψ_surj (B0_le_P hβ)
  have hbJ : (b : G) ∈ JElem P := by
    rw [hJ]
    exact PspFrame.mem_pre.2 ⟨b.2, by rw [hb]; exact hβ⟩
  have hbN : (b : G) ∈ normalizer (L : Set G) := Subgroup.le_normalizer b.2
  have hcomm' : s0 * (b : G) = (b : G) * s0 := by
    refine (F.comm_phi_psi_iff y b).1 ?_
    rw [hb]
    exact hcomm
  have hsbN : s0 * (b : G) ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem hs0N hbN
  have hφ : F.φ ⟨s0 * (b : G), hsbN⟩ = F.φ y * β := by
    have h1 : (⟨s0 * (b : G), hsbN⟩ : ↥(normalizer (L : Set G))) = y * ⟨(b : G), hbN⟩ := rfl
    rw [h1, map_mul, ← hb]
    rfl
  have hβA : β ∈ QA45.originalSubgroup := QP45_le_QA45 (B0_le_P hβ)
  have haβA : F.φ y * β ∈ QA45.originalSubgroup := QA45.originalSubgroup.mul_mem ha hβA
  have hβsq : β * β = 1 := B0_sq hβ
  have haβsq : (F.φ y * β) * (F.φ y * β) = 1 := by
    calc (F.φ y * β) * (F.φ y * β) = F.φ y * (β * F.φ y) * β := by group
      _ = F.φ y * (F.φ y * β) * β := by rw [hcomm]
      _ = (F.φ y * F.φ y) * (β * β) := by group
      _ = 1 := by rw [hsq, hβsq, mul_one]
  have haβne : F.φ y * β ≠ 1 := by
    intro h
    apply haP
    have h1 : F.φ y = β⁻¹ := mul_eq_one_iff_eq_inv.1 h
    rw [h1]
    exact QP45.originalSubgroup.inv_mem (B0_le_P hβ)
  have hInv : InvCent 1440 (F.φ ⟨s0 * (b : G), hsbN⟩) := by
    rw [hφ]
    exact MoInv.invCent_1440_of_fixCnt haβA haβsq haβne hfix
  obtain ⟨e⟩ := F.exists_equiv_perm_six hsbN hInv
  exact ⟨(b : G), hbJ, hcomm', LayerS6.isComponentIn_layerCent_of_equiv e,
    LayerS6.isL29_layerCent_of_equiv e⟩

end CFSG.OddStandard.SmallF3.Omega
