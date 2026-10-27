module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_R'_decomp (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) :
    (∃ q ∈ ctxQ t tau x₁ x₂ rho, a = q) ∨ (∃ q ∈ ctxQ t tau x₁ x₂ rho, a = q * tau) ∨
      (∃ q ∈ ctxQ t tau x₁ x₂ rho, a = q * t) ∨
      (∃ q ∈ ctxQ t tau x₁ x₂ rho, a = q * (t * tau)) := by
  have ht2 : t * t = 1 := S4A.t_mul_self hc.hyp
  have htau2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have htt : t * tau = tau * t :=
    (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)).symm
  have hK : ∀ k ∈ closure ({t, tau} : Set G), ∀ h ∈ ctxQ t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk h hh
    have hsub : ({t, tau} : Set G) ⊆ ctxM t tau x₁ x₂ := by
      intro y hy
      rcases hy with rfl | rfl
      · exact (c13_t_data hc.toCtx13A).1
      · exact (c13_tau_data hc.toCtx13A).1
    exact hc.normal_Q.2 k ((Subgroup.closure_le (K := ctxM t tau x₁ x₂)).mpr hsub hk) h hh
  obtain ⟨q, hq, k, hk, haqk⟩ := (mem_sup_iff_of_normalizes hK).mp ha
  rcases (mem_closure_pair_of_invol (a := t) (b := tau) ht2 htau2 htt).mp hk with
    hk1 | hkt | hktau | hkttau
  · exact Or.inl ⟨q, hq, by rw [haqk, hk1, mul_one]⟩
  · exact Or.inr (Or.inr (Or.inl ⟨q, hq, by rw [haqk, hkt]⟩))
  · exact Or.inr (Or.inl ⟨q, hq, by rw [haqk, hktau]⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨q, hq, by rw [haqk, hkttau]⟩))

theorem c13_card_le_four_inf (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {A : Subgroup G}
    (hA : A ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G)) :
    Nat.card A ≤ 4 * Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) := by
  set R' : Subgroup G := ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G) with hR'def
  have hAR' : A ≤ R' := by rw [hR'def]; exact hA
  have hQR' : ctxQ t tau x₁ x₂ rho ≤ R' := by rw [hR'def]; exact le_sup_left
  have hrelQ : (ctxQ t tau x₁ x₂ rho).relIndex R' = 4 := by
    have h := Subgroup.relIndex_mul_card (H := ctxQ t tau x₁ x₂ rho) (K := R')
    have hinf : ctxQ t tau x₁ x₂ rho ⊓ R' = ctxQ t tau x₁ x₂ rho :=
      inf_eq_left.mpr hQR'
    have hcardR' : Nat.card R' = 2 ^ 8 := by
      rw [hR'def, ← l12_R_eq hc.toCtx11, hc.card_R]
    rw [hinf, hcardR', l12_card_Q hc.toCtx11] at h
    omega
  have hne : (ctxQ t tau x₁ x₂ rho).relIndex R' ≠ 0 := by rw [hrelQ]; norm_num
  have hle_rel : (ctxQ t tau x₁ x₂ rho).relIndex A ≤ (ctxQ t tau x₁ x₂ rho).relIndex R' :=
    Subgroup.relIndex_le_of_le_right hAR' hne
  have h4 : (ctxQ t tau x₁ x₂ rho).relIndex A ≤ 4 := by rw [← hrelQ]; exact hle_rel
  have hmain := Subgroup.relIndex_mul_card (H := ctxQ t tau x₁ x₂ rho) (K := A)
  calc Nat.card A = (ctxQ t tau x₁ x₂ rho).relIndex A * Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ A) :=
        hmain.symm
    _ = (ctxQ t tau x₁ x₂ rho).relIndex A * Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) := by
        rw [inf_comm]
    _ ≤ 4 * Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) := Nat.mul_le_mul_right _ h4

theorem c13_inf_Q_le_V (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {A : Subgroup G}
    (hAR : A ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G))
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (ha : a ∉ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau) :
    A ⊓ ctxQ t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
  intro x hx
  have hxA : x ∈ A := hx.1
  have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := hx.2
  have hx2 : x ^ 2 = 1 := hA.2 x hxA
  have hxY : x ∈ ctxYq t tau x₁ x₂ rho :=
    (mem_ctxYq_iff hc.q_iso x).mpr ⟨hxQ, hx2⟩
  have hcommA : a * x = x * a := by
    haveI : IsMulCommutative ↥A := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : ↥A) (⟨x, hxA⟩ : ↥A))
  have hqx : ∀ q ∈ ctxQ t tau x₁ x₂ rho, q * x = x * q := fun q hq => hc.Q_comm q hq x hxQ
  have hfin : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      x ∈ centralizer ({t} : Set G) → x ∈ fourGrp x₁ x₂ := by
    intro q hq hxcent
    have hmem : x ∈ ctxYq t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := ⟨hxY, hxcent⟩
    rwa [hc.Y_cent.1] at hmem
  obtain hcase | hcase | hcase | hcase := c13_R'_decomp hc (hAR haA)
  · obtain ⟨q, hq, rfl⟩ := hcase
    exact absurd (Subgroup.mem_sup_left hq) ha
  · obtain ⟨q, hq, rfl⟩ := hcase
    refine absurd (Subgroup.mul_mem _ (Subgroup.mem_sup_left hq) ?_) ha
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  · obtain ⟨q, hq, rfl⟩ := hcase
    have h1 : q * (t * x) = q * (x * t) := by
      calc q * (t * x) = (q * t) * x := by group
        _ = x * (q * t) := hcommA
        _ = (x * q) * t := by group
        _ = (q * x) * t := by rw [← hqx q hq]
        _ = q * (x * t) := by group
    have htx : t * x = x * t := mul_left_cancel h1
    exact hfin q hq (Subgroup.mem_centralizer_singleton_iff.mpr htx.symm)
  · obtain ⟨q, hq, rfl⟩ := hcase
    have h2 : (t * tau) * x = x * (t * tau) := by
      have h1 : q * ((t * tau) * x) = q * (x * (t * tau)) := by
        calc q * ((t * tau) * x) = (q * (t * tau)) * x := by group
          _ = x * (q * (t * tau)) := hcommA
          _ = (x * q) * (t * tau) := by group
          _ = (q * x) * (t * tau) := by rw [← hqx q hq]
          _ = q * (x * (t * tau)) := by group
      exact mul_left_cancel h1
    have htx_tau : tau * x = x * tau := hc.tau_cent_Y x hxY
    have h3 : (t * x) * tau = (x * t) * tau := by
      calc (t * x) * tau = t * (x * tau) := by group
        _ = t * (tau * x) := by rw [← htx_tau]
        _ = (t * tau) * x := by group
        _ = x * (t * tau) := h2
        _ = (x * t) * tau := by group
    have htx : t * x = x * t := mul_right_cancel h3
    exact hfin q hq (Subgroup.mem_centralizer_singleton_iff.mpr htx.symm)

theorem c13_E32_le (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {A : Subgroup G}
    (hAR : A ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau} : Set G))
    (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : Nat.card A = 32) :
    A ≤ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau := by
  by_contra h
  obtain ⟨a, haA, ha⟩ := SetLike.not_le_iff_exists.mp h
  have hle : A ⊓ ctxQ t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ :=
    c13_inf_Q_le_V hc hAR hA haA ha
  have hcard_inf : Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) ≤ 4 := by
    have h := Subgroup.card_le_of_le hle
    rw [hc.wreath.fourGrp_eq_omega.2.2] at h
    exact h
  have hmain : Nat.card A ≤ 4 * Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) :=
    c13_card_le_four_inf hc hAR
  have h16 : Nat.card A ≤ 16 := by
    calc Nat.card A ≤ 4 * Nat.card ↥(A ⊓ ctxQ t tau x₁ x₂ rho) := hmain
      _ ≤ 4 * 4 := Nat.mul_le_mul_left 4 hcard_inf
      _ = 16 := by norm_num
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
