module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open scoped commutatorElement
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem M_le_LO : ctxM t tau x₁ x₂ ≤ ctxLO t tau x₁ x₂ := by
  intro g hg
  rw [ctxLO, Subgroup.mem_normalizer_iff]
  intro h
  exact ⟨fun hh => (O_normal_M t tau x₁ x₂).2 g hg h hh, fun hh => by
    have h' := (O_normal_M t tau x₁ x₂).2 g⁻¹ (inv_mem hg) (g * h * g⁻¹) hh
    have heq : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rwa [heq] at h'⟩

private theorem lam_conj_zpow (i : ℤ) : lam * rho ^ i * lam⁻¹ = (rho ^ i)⁻¹ := by
  calc lam * rho ^ i * lam⁻¹ = (lam * rho * lam⁻¹) ^ i :=
        (conj_zpow (i := i) (a := lam) (b := rho)).symm
    _ = (rho⁻¹) ^ i := by rw [hc.lam_rho]
    _ = (rho ^ i)⁻¹ := inv_zpow rho i

private theorem lam_normalizes_zpowers_rho :
    zpowers lam ≤ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩
  · intro hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hi, lam_conj_zpow hc hs i]
    exact inv_mem (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩)
  · intro hx
    have hx' : lam * (lam * x * lam⁻¹) * lam⁻¹ ∈ zpowers rho := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hi, lam_conj_zpow hc hs i]
      exact inv_mem (Subgroup.mem_zpowers_iff.mpr ⟨i, rfl⟩)
    have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (lam_mul_self hc)
    have heq : lam * (lam * x * lam⁻¹) * lam⁻¹ = x := by
      rw [hlinv]
      calc lam * (lam * x * lam) * lam = (lam * lam) * x * (lam * lam) := by group
        _ = x := by rw [lam_mul_self hc]; group
    rwa [heq] at hx'

theorem rho_conj_inv_lam_types {k : G}
    (hk : k = lam ∨ k = rho * lam ∨ k = rho⁻¹ * lam) :
    rho * k * rho⁻¹ * k⁻¹ = rho ^ 2 := by
  have hconj_inv : lam * rho⁻¹ * lam⁻¹ = rho := by
    calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
      _ = (rho⁻¹)⁻¹ := by rw [hc.lam_rho]
      _ = rho := by group
  rcases hk with hk | hk | hk
  · rw [hk]
    calc rho * lam * rho⁻¹ * lam⁻¹ = rho * (lam * rho⁻¹ * lam⁻¹) := by group
      _ = rho * rho := by rw [hconj_inv]
      _ = rho ^ 2 := by rw [pow_two]
  · rw [hk]
    calc rho * (rho * lam) * rho⁻¹ * (rho * lam)⁻¹
          = rho * rho * (lam * rho⁻¹ * lam⁻¹) * rho⁻¹ := by group
      _ = rho * rho * rho * rho⁻¹ := by rw [hconj_inv]
      _ = rho ^ 2 := by rw [show rho * rho * rho * rho⁻¹ = rho * rho by group, pow_two]
  · rw [hk]
    calc rho * (rho⁻¹ * lam) * rho⁻¹ * (rho⁻¹ * lam)⁻¹
          = (lam * rho⁻¹ * lam⁻¹) * rho := by group
      _ = rho * rho := by rw [hconj_inv]
      _ = rho ^ 2 := by rw [pow_two]

private theorem rho_zpow_eq (i : ℤ) : rho ^ i = 1 ∨ rho ^ i = rho ∨ rho ^ i = rho⁻¹ := by
  have h3 : rho ^ 3 = 1 := by
    have := pow_orderOf_eq_one rho
    rwa [hc.ord_rho] at this
  have h2nat : rho ^ 2 = rho⁻¹ := by
    have hh : rho ^ 2 * rho = 1 := by
      rw [← pow_succ]
      simpa using h3
    exact eq_inv_of_mul_eq_one_left hh
  have h2 : rho ^ (2 : ℤ) = rho⁻¹ := by simpa using h2nat
  have hz : rho ^ i = rho ^ (i % 3) := by
    rw [← zpow_mod_orderOf rho i, hc.ord_rho]
    simp
  rw [hz]
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by
    have hge : 0 ≤ i % 3 := Int.emod_nonneg i (by norm_num)
    have hlt : i % 3 < 3 := Int.emod_lt_of_pos i (by norm_num)
    omega
  rcases hcases with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right; rw [h]; exact h2

private theorem lam_zpow_eq (j : ℤ) : lam ^ j = 1 ∨ lam ^ j = lam := by
  have hz : lam ^ j = lam ^ (j % 2) := by
    rw [← zpow_mod_orderOf lam j, hc.wreath.ord_lam]
    simp
  rw [hz]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

private theorem rho_zpow_mul_lam_zpow_mem (i j : ℤ) :
    rho ^ i * lam ^ j ∈ ({1, rho, rho⁻¹, lam, rho * lam, rho⁻¹ * lam} : Set G) := by
  rcases rho_zpow_eq hc hs i with h | h | h <;> rcases lam_zpow_eq hc hs j with h' | h' <;>
    rw [h, h'] <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem decomp_M {m : G} (hm : m ∈ ctxM t tau x₁ x₂) :
    ∃ o ∈ ctxO t tau x₁ x₂, ∃ h ∈ ({1, rho, rho⁻¹, lam, rho * lam, rho⁻¹ * lam} : Set G),
      m = o * h := by
  have hle : closure ({rho, lam} : Set G) ≤
      Subgroup.normalizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact M_le_LO hc hs hc.rho_mem_M
    · exact M_le_LO hc hs hc.lam_mem_M
  have hmO : m ∈ ctxO t tau x₁ x₂ ⊔ closure ({rho, lam} : Set G) := by
    rw [← hc.M_eq]; exact hm
  have hmul : m ∈ ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) *
      ((closure ({rho, lam} : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hmO
  rw [Set.mem_mul] at hmul
  obtain ⟨o, ho, k, hk, hok⟩ := hmul
  have hEq : (zpowers rho ⊔ zpowers lam : Subgroup G) = closure ({rho, lam} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hk' : k ∈ zpowers rho ⊔ zpowers lam := by rw [hEq]; exact hk
  have hkmul : k ∈ ((zpowers rho : Subgroup G) : Set G) *
      ((zpowers lam : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (lam_normalizes_zpowers_rho hc hs)]
    exact hk'
  rw [Set.mem_mul] at hkmul
  obtain ⟨a, ha, b, hb, hab⟩ := hkmul
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
  refine ⟨o, ho, k, ?_, hok.symm⟩
  rw [← hab, ← hi, ← hj]
  exact rho_zpow_mul_lam_zpow_mem hc hs i j

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
