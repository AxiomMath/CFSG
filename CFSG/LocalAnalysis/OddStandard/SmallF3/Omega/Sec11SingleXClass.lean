module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleXTheta

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Subgroup

namespace SL23Pair

private theorem s11s_sumCongr_inj {p p' q q' : Equiv.Perm (Fin 4)}
    (hpq : Equiv.Perm.sumCongr p q = Equiv.Perm.sumCongr p' q') : p = p' ∧ q = q' := by
  have h' : (p, q) = (p', q') := Equiv.Perm.sumCongrHom_injective hpq
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

include h

private theorem s11s_eq_conj_embA {α : MulAut K} {s : SL23}
    {p1 p2 : Equiv.Perm (Fin 4)}
    (hθ : h.theta α = Equiv.Perm.sumCongr p1 p2)
    (hθs : h.theta (MulAut.conj (h.embA s)) = Equiv.Perm.sumCongr p1 1) :
    ∀ y ∈ A, α y = h.embA s * y * (h.embA s)⁻¹ := by
  intro y hy
  have hβ : h.theta ((MulAut.conj (h.embA s))⁻¹ * α) = Equiv.Perm.sumCongr 1 p2 := by
    rw [map_mul, map_inv, hθs, hθ, Equiv.Perm.sumCongr_inv, Equiv.Perm.sumCongr_mul,
      inv_mul_cancel, inv_one, one_mul]
  have hfix : ((MulAut.conj (h.embA s))⁻¹ * α) y = y := by
    refine h.fix_A ?_ hy
    intro i
    have := congrArg (fun e : Equiv.Perm (Fin 4 ⊕ Fin 4) => e (Sum.inl i)) hβ
    simpa using this
  have h1 : α y = MulAut.conj (h.embA s) y := by
    have hfix' : (MulAut.conj (h.embA s))⁻¹ (α y) = y := hfix
    calc α y = MulAut.conj (h.embA s) ((MulAut.conj (h.embA s))⁻¹ (α y)) :=
          (MulAut.apply_inv_self K (MulAut.conj (h.embA s)) (α y)).symm
      _ = MulAut.conj (h.embA s) y := by rw [hfix']
  rwa [MulAut.conj_apply] at h1

private theorem s11s_eq_conj_embB {α : MulAut K} {s : SL23}
    {p1 p2 : Equiv.Perm (Fin 4)}
    (hθ : h.theta α = Equiv.Perm.sumCongr p1 p2)
    (hθs : h.theta (MulAut.conj (h.embB s)) = Equiv.Perm.sumCongr 1 p2) :
    ∀ y ∈ B, α y = h.embB s * y * (h.embB s)⁻¹ := by
  intro y hy
  have hβ : h.theta ((MulAut.conj (h.embB s))⁻¹ * α) = Equiv.Perm.sumCongr p1 1 := by
    rw [map_mul, map_inv, hθs, hθ, Equiv.Perm.sumCongr_inv, Equiv.Perm.sumCongr_mul,
      inv_mul_cancel, inv_one, one_mul]
  have hfix : ((MulAut.conj (h.embB s))⁻¹ * α) y = y := by
    refine h.fix_B ?_ hy
    intro i
    have := congrArg (fun e : Equiv.Perm (Fin 4 ⊕ Fin 4) => e (Sum.inr i)) hβ
    simpa using this
  have h1 : α y = MulAut.conj (h.embB s) y := by
    have hfix' : (MulAut.conj (h.embB s))⁻¹ (α y) = y := hfix
    calc α y = MulAut.conj (h.embB s) ((MulAut.conj (h.embB s))⁻¹ (α y)) :=
          (MulAut.apply_inv_self K (MulAut.conj (h.embB s)) (α y)).symm
      _ = MulAut.conj (h.embB s) y := by rw [hfix']
  rwa [MulAut.conj_apply] at h1

theorem s11s_sign_outer {α : MulAut K} (hA : ∀ a ∈ A, α a ∈ A) (hB : ∀ b ∈ B, α b ∈ B)
    (hoA : ¬ ∃ k ∈ A, ∀ y ∈ A, α y = k * y * k⁻¹)
    (hoB : ¬ ∃ k ∈ B, ∀ y ∈ B, α y = k * y * k⁻¹) :
    Equiv.Perm.sign (h.theta α) = 1 := by
  obtain ⟨p1, p2, hθ⟩ := h.s11s_theta_sumCongr hA
  have hp1 : Equiv.Perm.sign p1 = -1 := by
    by_contra hne
    rcases Int.units_eq_one_or (Equiv.Perm.sign p1) with h1 | h1
    · obtain ⟨s, hs⟩ := s11s_exists_of_even h1
      refine hoA ⟨h.embA s, h.embA_mem s, ?_⟩
      exact h.s11s_eq_conj_embA hθ (h.theta_conj_embA hs)
    · exact hne h1
  have hp2 : Equiv.Perm.sign p2 = -1 := by
    by_contra hne
    rcases Int.units_eq_one_or (Equiv.Perm.sign p2) with h1 | h1
    · obtain ⟨s, hs⟩ := s11s_exists_of_even h1
      refine hoB ⟨h.embB s, h.embB_mem s, ?_⟩
      exact h.s11s_eq_conj_embB hθ (h.s11s_theta_conj_embB hs)
    · exact hne h1
  rw [hθ, Equiv.Perm.sign_sumCongr, hp1, hp2]
  simp

theorem s11s_conj_comm {ψ : MulAut K} {g : K} (hc : ψ g * g⁻¹ ∈ A ⊓ B) :
    ψ * MulAut.conj g = MulAut.conj g * ψ := by
  let c : K := ψ g * g⁻¹
  have hcent : ∀ k : K, c * k = k * c := fun k => h.inf_central hc k
  have hψg : ψ g = c * g := by
    rw [show c = ψ g * g⁻¹ from rfl]
    group
  ext y
  show ψ (g * y * g⁻¹) = g * ψ y * g⁻¹
  calc ψ (g * y * g⁻¹) = ψ g * ψ y * (ψ g)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = (c * g) * ψ y * (c * g)⁻¹ := by rw [hψg]
    _ = c * (g * ψ y * g⁻¹) * c⁻¹ := by group
    _ = g * ψ y * g⁻¹ := by
          rw [hcent (g * ψ y * g⁻¹), mul_assoc, mul_inv_cancel, mul_one]

theorem s11s_psi_class {ψ : MulAut K} (h2 : ψ * ψ = 1) (hA : ∀ a ∈ A, ψ a ∈ A)
    (hB : ∀ b ∈ B, ψ b ∈ B)
    (htriv : ∀ q : SL23, q ^ 4 = 1 → ψ (h.embB q) * (h.embB q)⁻¹ ∈ A ⊓ B)
    (hnot : ¬ ∃ q : SL23, q ^ 4 = 1 ∧ ∀ y ∈ A, ψ y = h.embA q * y * (h.embA q)⁻¹) :
    Equiv.Perm.sign (h.theta ψ) = -1 ∧
      ∃ q : SL23, q ^ 4 = 1 ∧ ∀ y ∈ B, ψ y = h.embB q * y * (h.embB q)⁻¹ := by
  obtain ⟨p1, p2, hθ⟩ := h.s11s_theta_sumCongr hA
  have hp2klein : p2 ∈ klein := by
    apply s11s_mem_klein_of_comm
    intro v hv
    obtain ⟨q, hq4, hq⟩ := exists_pow_four_of_klein hv
    have hcomm := h.s11s_conj_comm (htriv q hq4)
    have heq : Equiv.Perm.sumCongr p1 p2 * Equiv.Perm.sumCongr 1 v =
        Equiv.Perm.sumCongr 1 v * Equiv.Perm.sumCongr p1 p2 := by
      have := congrArg h.theta hcomm
      rwa [map_mul, map_mul, hθ, h.s11s_theta_conj_embB hq] at this
    have heq' : Equiv.Perm.sumCongr (p1 * 1) (p2 * v) =
        Equiv.Perm.sumCongr (1 * p1) (v * p2) := by
      simpa only [Equiv.Perm.sumCongr_mul] using heq
    simpa using (s11s_sumCongr_inj heq').2
  obtain ⟨q, hq4, hq⟩ := exists_pow_four_of_klein hp2klein
  have hBconj : ∀ y ∈ B, ψ y = h.embB q * y * (h.embB q)⁻¹ :=
    h.s11s_eq_conj_embB hθ (h.s11s_theta_conj_embB hq)
  have hp1sq : p1 * p1 = 1 := by
    have hsq : Equiv.Perm.sumCongr (p1 * p1) (p2 * p2) = 1 := by
      rw [← Equiv.Perm.sumCongr_mul, ← hθ, ← map_mul, h2, map_one]
    have hsq' : Equiv.Perm.sumCongr (p1 * p1) (p2 * p2) = Equiv.Perm.sumCongr 1 1 := by
      rw [hsq, Equiv.Perm.sumCongr_one]
    exact (s11s_sumCongr_inj hsq').1
  have hp1not : p1 ∉ klein := by
    intro hk
    obtain ⟨q1, hq1, hq1'⟩ := exists_pow_four_of_klein hk
    exact hnot ⟨q1, hq1, h.s11s_eq_conj_embA hθ (h.theta_conj_embA hq1')⟩
  refine ⟨?_, q, hq4, hBconj⟩
  rw [hθ, Equiv.Perm.sign_sumCongr, s11s_sign_of_sq_not_klein hp1sq hp1not,
    sign_of_mem_klein hp2klein, mul_one]

theorem s11s_embB_neg_one {w : K} (hwB : w ∈ B) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    h.embB (-1) = w := by
  obtain ⟨s, rfl⟩ := h.exists_embB hwB
  have hs2 : s * s = 1 := by
    apply h.embB_injective
    rw [map_mul, map_one]
    exact hw2
  have hs1 : s ≠ 1 := by
    intro hs
    apply hw1
    rw [hs, map_one]
  rcases sl23_unique_involution s hs2 with hs | hs
  · exact absurd hs hs1
  · rw [hs]

theorem s11s_caseB_elem {q : SL23} (hq : q ^ 4 = 1) (h1 : q ≠ 1) (hm : q ≠ -1) :
    ((h.embB q * h.embB (k5g 0) * (h.embB q)⁻¹)⁻¹ * h.embB (k5g 0)) *
      ((h.embB q * h.embB (k5g 0) * (h.embB q)⁻¹)⁻¹ * h.embB (k5g 0)) = h.embB (-1) := by
  have hX : (q * k5g 0 * q⁻¹)⁻¹ * k5g 0 = q * (k5g 0)⁻¹ * q⁻¹ * k5g 0 := by group
  have hA : (h.embB q * h.embB (k5g 0) * (h.embB q)⁻¹)⁻¹ * h.embB (k5g 0) =
      h.embB (q * (k5g 0)⁻¹ * q⁻¹ * k5g 0) := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul, hX]
  rw [hA, ← map_mul, s11s_caseB_sq hq h1 hm]

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
