module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Abs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem normalizer_iff (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) (hne : K₁ ≠ K₂) {c : G}
    (hc : c ∈ centralizer ({z} : Set G)) :
    c ∈ normalizer (K₁ : Set G) ↔ c ∈ normalizer (K₂ : Set G) := by
  rcases hM.perm c hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => M.cj_eq_iff_normalizer.1 h2, fun _ => M.cj_eq_iff_normalizer.1 h1⟩
  · constructor
    · intro hn
      exact absurd (h1.symm.trans (M.cj_eq_iff_normalizer.2 hn)) (Ne.symm hne)
    · intro hn
      exact absurd (h2.symm.trans (M.cj_eq_iff_normalizer.2 hn)) hne

omit [Finite G] in
theorem S1_relIndex (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) :
    (S ⊓ normalizer (K₁ : Set G)).relIndex S ≤ 2 := by
  by_cases hall : S ≤ normalizer (K₁ : Set G)
  · rw [Subgroup.relIndex_eq_one.2 (le_inf le_rfl hall)]
    norm_num
  · obtain ⟨y, hyS, hyN⟩ : ∃ y ∈ S, y ∉ normalizer (K₁ : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hall hcon
    have hyC : y ∈ centralizer ({z} : Set G) := hM.S_syl.1 hyS
    have hy1 : M.cj K₁ y = K₂ := by
      rcases hM.perm y hyC with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (M.cj_eq_iff_normalizer.1 h1) hyN
      · exact h1
    refine B.relIndex_le_two_of_cover hyS (fun x hx => ?_)
    by_cases hxN : x ∈ normalizer (K₁ : Set G)
    · exact Or.inl ⟨hx, hxN⟩
    · right
      have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hx
      have hx1 : M.cj K₁ x = K₂ := by
        rcases hM.perm x hxC with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact absurd (M.cj_eq_iff_normalizer.1 h1) hxN
        · exact h1
      refine ⟨S.mul_mem hx (S.inv_mem hyS), M.cj_eq_iff_normalizer.1 ?_⟩
      rw [← M.cj_cj, hx1, ← hy1, M.cj_cj_inv]

theorem comm_Pof_Qof (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {p q : G} (hp : p ∈ Pof S K) (hq : q ∈ Qof S K) : p * q = q * p := by
  have hOK : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 p hp.2
  have hS : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem hp.1 hq.1) (S.inv_mem hp.1)) (S.inv_mem hq.1)
  have hbot : S ⊓ pPrimeCoreOf 2 K = ⊥ := M.inf_eq_bot_of_pgroup_odd hM.S_pgroup (hM.core K hK).odd
  have h1 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨hS, hOK⟩
  rw [hbot, Subgroup.mem_bot] at h1
  simp only [commutatorElement_def] at h1
  have e : p * q = q * p := by
    calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
      _ = q * p := by rw [h1]; group
  exact e

theorem Qof_inf_le_Qm (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) {x : G}
    (hx1 : x ∈ Qof S K₁) (hx2 : x ∈ Qof S K₂) : x ∈ M.Qm (pPrimeCoreOf 2) S K₁ K₂ := by
  have hxS : x ∈ S := hx1.1
  have hxC : x ∈ centralizer ({z} : Set G) := hM.S_syl.1 hxS
  refine ⟨hxS, M.mem_normalizer_of_both (fun y hy => hM.C_norm_K hxC hy)
    (fun y hy => hM.C_norm_K' hxC hy), M.mem_normalizer_of_both (fun y hy => hM.C_norm_OK hxC hy)
    (fun y hy => ?_), ?_⟩
  · have := hM.C_norm_OK ((centralizer ({z} : Set G)).inv_mem hxC) hy
    simpa using this
  · intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := hM.mem_sup hk
    have h1 : ⁅a, x⁆ ∈ pPrimeCoreOf 2 K₁ := hx1.2.2.2 a ha
    have h2 : ⁅b, x⁆ ∈ pPrimeCoreOf 2 K₂ := hx2.2.2.2 b hb
    have e : ⁅a * b, x⁆ = a * ⁅b, x⁆ * a⁻¹ * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1' := hM.O_le_OK (Or.inl rfl) h1
    have h2' := hM.O_le_OK (Or.inr rfl) h2
    exact mul_mem (hM.coreK.normal a (hM.comp_le (Or.inl rfl) ha) _ h2') h1'

theorem Pm_eq_sup (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) :
    M.Pm S K₁ K₂ = Pof S K₁ ⊔ Pof S K₂ := by
  have hinf : ∀ K, (K = K₁ ∨ K = K₂) → M.Pm S K₁ K₂ ⊓ K = Pof S K := by
    intro K hK
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (hM.comp_le hK)]
  have := hM.P_eq
  rwa [hinf K₁ (Or.inl rfl), hinf K₂ (Or.inr rfl)] at this

omit [Finite G] in
theorem Pof_Qof_le_S1 {K : Subgroup G} : Pof S K ⊔ Qof S K ≤ S ⊓ normalizer (K : Set G) := by
  refine sup_le (fun x hx => ⟨hx.1, ?_⟩) (fun x hx => ⟨hx.1, ?_⟩)
  · exact Subgroup.le_normalizer hx.2
  · exact hx.2.1

theorem Pz_le_X (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂) :
    M.Pm S K₁ K₂ ≤ Pof S K₁ ⊔ Qof S K₁ := by
  rw [Pm_eq_sup hM]
  exact sup_le_sup_left (Pof_le_Qof hM (Or.inr ⟨rfl, rfl⟩)) _

theorem Pm_relIndex_X (hM : M.M4 (pPrimeCoreOf 2) InducesFAut SDp z S K₁ K₂)
    (hidx : (Pof S K₂).relIndex (Qof S K₁) ≤ 2) :
    (M.Pm S K₁ K₂).relIndex (Pof S K₁ ⊔ Qof S K₁) ≤ 2 := by
  rw [Pm_eq_sup hM]
  exact B.relIndex_sup_le_two hidx (fun a ha c hc => comm_Pof_Qof hM (Or.inl rfl) ha hc)

theorem eq_two_of_mul_eq_four {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (h : a * b = 4) : a = 2 ∧ b = 2 := by
  interval_cases a <;> interval_cases b <;> omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R2
