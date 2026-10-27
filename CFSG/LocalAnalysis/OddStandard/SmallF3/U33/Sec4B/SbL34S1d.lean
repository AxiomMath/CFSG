module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


variable (hc : Ctx4L t L S x₁ x₂ lam rho tau)
include hc

theorem coset_V {a : G} (ha : a ∈ fourGrp x₁ x₂) (hinv : (t * lam * a) * (t * lam * a) = 1) :
    a = 1 ∨ a = (x₁ * x₂) ^ 2 := by
  have hq : (t * lam) * (t * lam) = 1 := q_mul_self hc.toCtx4Q
  have hqinv : (t * lam)⁻¹ = t * lam := inv_eq_of_mul_eq_one_right hq
  have haa : a * a = 1 := by
    have h := (fourGrp_elemAbelian hc.toCtx4Q).2 a ha
    rwa [pow_two] at h
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hconj : (t * lam) * a * (t * lam)⁻¹ = a := by
    have h' : (t * lam) * a * (t * lam) = a⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa only [mul_assoc] using hinv)
    rw [hqinv, h', hainv]
  exact CV_q hc.toCtx4Q ha hconj

theorem coset_t_false {a : G} (ha : a ∈ fourGrp x₁ x₂)
    (hinv : (t * lam * (t * a)) * (t * lam * (t * a)) = 1)
    (hcl : ∃ g : G, g * t * g⁻¹ = t * lam * (t * a)) : False := by
  have htlt : t * lam * (t * a) = lam * a := by
    calc t * lam * (t * a) = t * (lam * t) * a := by group
      _ = t * (t * lam) * a := by rw [t_comm_lam hc.toCtx4Q]
      _ = (t * t) * (lam * a) := by group
      _ = lam * a := by rw [Ctx4Q.t_mul_self hc.toCtx4Q, one_mul]
  have hinv' : (lam * a) * (lam * a) = 1 := by
    rw [htlt] at hinv
    exact hinv
  obtain ⟨g, hg⟩ := hc.inv_l a ha hinv'
  obtain ⟨g', hg'⟩ := hcl
  have hzN : (x₁ * x₂) ^ 2 ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
  refine hc.tG_N (g⁻¹ * g') ((x₁ * x₂) ^ 2) hzN ?_
  calc (g⁻¹ * g') * t * (g⁻¹ * g')⁻¹
      = g⁻¹ * (g' * t * g'⁻¹) * g := by group
    _ = g⁻¹ * (lam * a) * g := by rw [hg', htlt]
    _ = g⁻¹ * (g * (x₁ * x₂) ^ 2 * g⁻¹) * g := by rw [← hg]
    _ = (x₁ * x₂) ^ 2 := by group

theorem coset_tau_false {a : G} (ha : a ∈ fourGrp x₁ x₂)
    (hinv : (t * lam * (tau * a)) * (t * lam * (tau * a)) = 1)
    (hcl : ∃ g : G, g * t * g⁻¹ = t * lam * (tau * a)) : False := by
  have h1 : t * lam * (tau * a) = t * lam * tau * a := by group
  have hinv' : (t * lam * tau * a) * (t * lam * tau * a) = 1 := by
    rw [h1] at hinv
    exact hinv
  obtain ⟨g, hg⟩ := hc.inv_tltau a ha hinv'
  obtain ⟨g', hg'⟩ := hcl
  have hmem : t * tau ∈ ctxN (t * tau) x₁ x₂ := Subgroup.subset_closure (by simp)
  have hk : (g'⁻¹ * g) * (t * tau) * (g'⁻¹ * g)⁻¹ = t := by
    calc (g'⁻¹ * g) * (t * tau) * (g'⁻¹ * g)⁻¹
        = g'⁻¹ * (g * (t * tau) * g⁻¹) * g' := by group
      _ = g'⁻¹ * (t * lam * tau * a) * g' := by rw [hg]
      _ = g'⁻¹ * (g' * t * g'⁻¹) * g' := by rw [← h1, ← hg']
      _ = t := by group
  have hk' : (g'⁻¹ * g)⁻¹ * t * ((g'⁻¹ * g)⁻¹)⁻¹ = t * tau := by
    calc (g'⁻¹ * g)⁻¹ * t * ((g'⁻¹ * g)⁻¹)⁻¹
        = (g'⁻¹ * g)⁻¹ * ((g'⁻¹ * g) * (t * tau) * (g'⁻¹ * g)⁻¹) * (g'⁻¹ * g) := by
          rw [hk]; group
      _ = t * tau := by group
  exact hc.tG_tN (g'⁻¹ * g)⁻¹ (t * tau) hmem hk'

theorem coset_ttau_false {a : G} (ha : a ∈ fourGrp x₁ x₂)
    (hinv : (t * lam * ((t * tau) * a)) * (t * lam * ((t * tau) * a)) = 1)
    (hcl : ∃ g : G, g * t * g⁻¹ = t * lam * ((t * tau) * a)) : False := by
  have htl : lam * t = t * lam := (t_comm_lam hc.toCtx4Q).symm
  have h1 : t * lam * ((t * tau) * a) = lam * tau * a := by
    calc t * lam * ((t * tau) * a) = t * (lam * t) * (tau * a) := by group
      _ = t * (t * lam) * (tau * a) := by rw [htl]
      _ = (t * t) * (lam * tau * a) := by group
      _ = lam * tau * a := by rw [Ctx4Q.t_mul_self hc.toCtx4Q, one_mul]
  have hinv' : (lam * tau * a) * (lam * tau * a) = 1 := by
    rw [h1] at hinv
    exact hinv
  obtain ⟨g, hg⟩ := hc.inv_ltau a ha hinv'
  obtain ⟨g', hg'⟩ := hcl
  have hmem : tau ∈ ctxN tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hk : (g'⁻¹ * g) * tau * (g'⁻¹ * g)⁻¹ = t := by
    calc (g'⁻¹ * g) * tau * (g'⁻¹ * g)⁻¹
        = g'⁻¹ * (g * tau * g⁻¹) * g' := by group
      _ = g'⁻¹ * (lam * tau * a) * g' := by rw [hg]
      _ = g'⁻¹ * (g' * t * g'⁻¹) * g' := by rw [← h1, ← hg']
      _ = t := by group
  have hk' : (g'⁻¹ * g)⁻¹ * t * ((g'⁻¹ * g)⁻¹)⁻¹ = tau := by
    calc (g'⁻¹ * g)⁻¹ * t * ((g'⁻¹ * g)⁻¹)⁻¹
        = (g'⁻¹ * g)⁻¹ * ((g'⁻¹ * g) * tau * (g'⁻¹ * g)⁻¹) * (g'⁻¹ * g) := by
          rw [hk]; group
      _ = tau := by group
  exact hc.tG_N (g'⁻¹ * g)⁻¹ tau hmem hk'

theorem x_one_or_z {x : G} (hx : x ∈ ctxX t tau x₁ x₂)
    (hinv : (t * lam * x) * (t * lam * x) = 1) (hcl : ∃ g : G, g * t * g⁻¹ = t * lam * x) :
    x = 1 ∨ x = (x₁ * x₂) ^ 2 := by
  rcases S4A.mem_ctxX_cases (hc.toCtx) hc.l44.1 hx with hV | ht | htau | httau
  · exact coset_V hc hV hinv
  · rw [Set.mem_smul_set] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    exact (coset_t_false hc ha hinv hcl).elim
  · rw [Set.mem_smul_set] at htau
    obtain ⟨a, ha, rfl⟩ := htau
    exact (coset_tau_false hc ha hinv hcl).elim
  · rw [Set.mem_smul_set] at httau
    obtain ⟨a, ha, rfl⟩ := httau
    exact (coset_ttau_false hc ha hinv hcl).elim

end CFSG.OddStandard.SmallF3.HarrisU33.L34
