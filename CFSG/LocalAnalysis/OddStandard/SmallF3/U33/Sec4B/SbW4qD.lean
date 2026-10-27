module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutHS29
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem mem_normalizer_of_normalIn {H K : Subgroup G} (hK : NormalIn H K) {g : G}
    (hg : g ∈ K) : g ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => hK.2 g hg x hx, fun hx => by
    have h1 := hK.2 g⁻¹ (K.inv_mem hg) (g * x * g⁻¹) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h1⟩

private theorem w4q_rho_lam_mem_M (hc : Ctx4C t L S x₁ x₂ lam rho tau) :
    rho ∈ ctxM t tau x₁ x₂ ∧ lam ∈ ctxM t tau x₁ x₂ := by
  constructor
  · rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · rw [hc.M_eq]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

private theorem w4q_x₁_ne_one (hc : Ctx4C t L S x₁ x₂ lam rho tau) : x₁ ≠ 1 := by
  intro h
  have h4 := hc.wreath.ord_x₁
  rw [h, orderOf_one] at h4
  exact absurd h4 (by norm_num)

private theorem w4q_x₂_ne_x₁ (hc : Ctx4C t L S x₁ x₂ lam rho tau) : x₂ ≠ x₁ := by
  intro h
  have hmem : x₁ ∈ (⊥ : Subgroup G) := by
    rw [← hc.wreath.inf_eq_bot]
    exact ⟨Subgroup.mem_zpowers x₁, by rw [← h]; exact Subgroup.mem_zpowers x₂⟩
  exact w4q_x₁_ne_one hc (by simpa using hmem)

private theorem w4q_x₂_eq_x₁_of_comm (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (h : lam * x₁ = x₁ * lam) : x₂ = x₁ := by
  have hconj := hc.wreath.conj_x₁
  rw [h] at hconj
  rw [mul_assoc, mul_inv_cancel, mul_one] at hconj
  exact hconj.symm

private theorem w4q_dichotomy_nonabelian (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 2 ^ 6)
    (hCQ : ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x = 1)
    (hcomm : ¬ ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a) :
    IsSylSL34 (ctxQ t tau x₁ x₂ rho) := by
  set Q : Subgroup G := ctxQ t tau x₁ x₂ rho with hQ
  have hNQ : NormalIn Q (ctxM t tau x₁ x₂) := by rw [hQ]; exact hc.normal_Q
  have hρ : rho ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_normalIn hNQ (w4q_rho_lam_mem_M hc).1
  have hlam : lam ∈ normalizer (Q : Set G) :=
    mem_normalizer_of_normalIn hNQ (w4q_rho_lam_mem_M hc).2
  have hx₁Q' : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₁Q : x₁ ∈ Q := by rw [hQ]; exact hx₁Q'
  have hx₁ne : x₁ ≠ 1 := w4q_x₁_ne_one hc
  have hfρ : ∃ h ∈ Q, rho * h ≠ h * rho := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    exact hx₁ne (hCQ x₁ hx₁Q hconj.symm)
  have hfx : ∃ h ∈ Q, lam * h ≠ h * lam := by
    refine ⟨x₁, hx₁Q, fun hconj => ?_⟩
    exact w4q_x₂_ne_x₁ hc (w4q_x₂_eq_x₁_of_comm hc hconj)
  have hs : Outside.Sigma3Rel (Outside.conjAut Q rho hρ) (Outside.conjAut Q lam hlam) :=
    Outside.sigma3Rel_conjAut Q hρ hlam hc.ord_rho hc.wreath.ord_lam hc.lam_rho hfρ hfx
  have hfpf : ∀ g : ↥Q, Outside.conjAut Q rho hρ g = g → g = 1 := by
    intro g hg
    have h1 : rho * (g : G) * rho⁻¹ = (g : G) := by
      have := congrArg (fun x : ↥Q => (x : G)) hg
      simpa [Outside.conjAut_coe] using this
    have h2 : rho * (g : G) = (g : G) * rho := (mul_inv_eq_iff_eq_mul).mp h1
    exact Subtype.ext (hCQ (g : G) g.2 h2.symm)
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := by
    have hcomm' := hcomm
    push Not at hcomm'
    obtain ⟨a, ha, b, hb, hab⟩ := hcomm'
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hcard64 : Nat.card ↥Q = 64 := by
    rw [hcard]
    norm_num
  exact (Outside.HS29 hcard64 hnab hs hfpf).1

theorem w4q_dichotomy
    (hc : Ctx4C t L S x₁ x₂ lam rho tau)
    (hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho) = 2 ^ 6)
    (hCQ : ∀ x ∈ ctxQ t tau x₁ x₂ rho, x * rho = rho * x → x = 1)
    (hsq : ∀ a ∈ ctxQ t tau x₁ x₂ rho, a ^ 2 ∈ fourGrp x₁ x₂) :
    IsZ4Z4E4 (ctxQ t tau x₁ x₂ rho) ∨ IsSylSL34 (ctxQ t tau x₁ x₂ rho) := by
  by_cases hcomm : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a
  · left
    have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (Subgroup.subset_closure (by simp))
    have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.base_le_Q (Subgroup.subset_closure (by simp))
    refine isZ4Z4E4_of_abelian hc.wreath hx₁Q hx₂Q hcomm ?_ hsq
    · rw [hcard]; norm_num
  · right
    exact w4q_dichotomy_nonabelian hc hcard hCQ hcomm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
