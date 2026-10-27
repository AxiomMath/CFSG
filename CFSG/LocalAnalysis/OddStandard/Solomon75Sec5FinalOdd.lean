module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalCtx
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalPerm

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

namespace Sec5Ctx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {N A : Subgroup X} {M : AhatModel X n A}

theorem conj_mem_oddCore (h : Sec5Ctx X n z N A M) {t₁ a₀ : X} (ht₁N : t₁ ∈ N) (ha₀ : a₀ ∈ A)
    (ht₁ : h.psi ⟨t₁, ht₁N⟩ = oddOne h.hn) (ha₀ψ : h.psi ⟨a₀, h.hAN ha₀⟩ = dblTwo h.hn) :
    (t₁⁻¹ * a₀ * t₁)⁻¹ * a₀ ∈ oddCoreOf A := by
  have hn := h.hn
  have hc' : t₁⁻¹ ∈ normalizer (A : Set X) := Subgroup.inv_mem _ (h.hNA ht₁N)
  have hperm : M.perm t₁⁻¹ hc' = oddOne hn := by
    have h1 : h.psi ⟨t₁⁻¹, inv_mem ht₁N⟩ = (h.psi ⟨t₁, ht₁N⟩)⁻¹ := by
      rw [← map_inv]; rfl
    rw [← h.psi_apply ⟨t₁⁻¹, inv_mem ht₁N⟩, h1, ht₁]
    exact inv_eq_of_mul_eq_one_right (oddOne_sq hn)
  have hind : M.C.Induces (M.autOf t₁⁻¹ hc') (oddOne hn) := by
    have := M.induces_perm hn t₁⁻¹ hc'
    rwa [hperm] at this
  have hρ : M.C.ρ (M.e (QuotientGroup.mk (⟨a₀, ha₀⟩ : ↥A))) =
      swap (pt hn 2) (pt hn 3) * swap (pt hn 4) (pt hn 5) := by
    rw [← h.psi_of_mem ha₀, ha₀ψ]; rfl
  have hfix := hind.apply_eq_of_dbl_fixed (pt_ne hn (by decide)) (pt_ne hn (by decide))
    (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide)) (pt_ne hn (by decide))
    (oddOne_apply_of_ne hn (by decide) (by decide)) (oddOne_apply_of_ne hn (by decide) (by decide))
    (oddOne_apply_of_ne hn (by decide) (by decide)) (oddOne_apply_of_ne hn (by decide) (by decide))
    hρ
  rw [M.autOf_mk] at hfix
  have h3 := QuotientGroup.eq.1 (M.e.injective hfix)
  have hmem : (t₁⁻¹ * a₀ * t₁)⁻¹ * a₀ ∈ A := by
    have e1 : t₁⁻¹ * a₀ * t₁ = ((conjAut hc' ⟨a₀, ha₀⟩ : ↥A) : X) := by
      rw [coe_conjAut]; simp
    rw [e1]
    exact mul_mem (inv_mem (conjAut hc' ⟨a₀, ha₀⟩).2) ha₀
  refine mem_oddCoreOf_iff.2 ⟨hmem, ?_⟩
  have e2 : (⟨(t₁⁻¹ * a₀ * t₁)⁻¹ * a₀, hmem⟩ : ↥A) = (conjAut hc' ⟨a₀, ha₀⟩)⁻¹ * ⟨a₀, ha₀⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjAut]
    simp
  rw [e2]
  exact h3

theorem sq_mem_zOdd (h : Sec5Ctx X n z N A M) {a₀ : X} (ha₀ : a₀ ∈ A)
    (ha₀ψ : h.psi ⟨a₀, h.hAN ha₀⟩ = dblTwo h.hn) : z⁻¹ * (a₀ * a₀) ∈ oddCoreOf A := by
  have hn := h.hn
  have hρ : M.C.ρ (M.e (QuotientGroup.mk (⟨a₀, ha₀⟩ : ↥A))) = dblTwo hn := by
    rw [← h.psi_of_mem ha₀, ha₀ψ]
  set ā₀ := M.e (QuotientGroup.mk (⟨a₀, ha₀⟩ : ↥A)) with hā₀
  have hc : ā₀ * ā₀ ∈ center M.K := by
    rw [← M.C.ρ_eq_one_iff, map_mul, hρ]
    exact dblTwo_sq hn
  have hne : ā₀ * ā₀ ≠ 1 :=
    M.C.dblI_sq_ne_one hn (by rw [hρ]; exact dblTwo_isDblI hn)
  have h1 := h.eq_zbar_of_mem_center hc hne
  unfold zbar at h1
  rw [hā₀, ← map_mul, ← QuotientGroup.mk_mul] at h1
  have h2 := QuotientGroup.eq.1 (M.e.injective h1)
  have hmem : z⁻¹ * (a₀ * a₀) ∈ A := mul_mem (inv_mem h.hzA) (mul_mem ha₀ ha₀)
  refine mem_oddCoreOf_iff.2 ⟨hmem, ?_⟩
  have h3 := inv_mem h2
  have e : (⟨z⁻¹ * (a₀ * a₀), hmem⟩ : ↥A) =
      ((⟨a₀, ha₀⟩ * ⟨a₀, ha₀⟩)⁻¹ * ⟨z, h.hzA⟩)⁻¹ := by
    apply Subtype.ext
    simp
  rw [e]
  exact h3

theorem sq_mem_or_sq_mem (h : Sec5Ctx X n z N A M) {t₁ a₀ : X} (ht₁N : t₁ ∈ N) (ha₀ : a₀ ∈ A)
    (ht₁ : h.psi ⟨t₁, ht₁N⟩ = oddOne h.hn) (ha₀ψ : h.psi ⟨a₀, h.hAN ha₀⟩ = dblTwo h.hn) :
    t₁ * t₁ ∈ oddCoreOf N ∨ (t₁ * a₀) * (t₁ * a₀) ∈ oddCoreOf N := by
  have hn := h.hn
  have hsq : h.psi ⟨t₁ * t₁, mul_mem ht₁N ht₁N⟩ = 1 := by
    have : (⟨t₁ * t₁, mul_mem ht₁N ht₁N⟩ : ↥N) = ⟨t₁, ht₁N⟩ * ⟨t₁, ht₁N⟩ := rfl
    rw [this, map_mul, ht₁]
    exact oddOne_sq hn
  obtain ⟨o, ho, m, hom⟩ := exists_of_mem_sup_zpowers
    (fun p hp => h.hNz p (oddCoreOf_le N hp)) (h.psi_eq_one_imp (mul_mem ht₁N ht₁N) hsq)
  have hv₀ := h.conj_mem_oddCore ht₁N ha₀ ht₁ ha₀ψ
  have ho₂ := h.sq_mem_zOdd ha₀ ha₀ψ
  set v₀ := (t₁⁻¹ * a₀ * t₁)⁻¹ * a₀ with hv₀def
  set o₂ := z⁻¹ * (a₀ * a₀) with ho₂def
  set u' := a₀⁻¹ * v₀⁻¹ * a₀ with hu'
  have hu'O : u' ∈ oddCoreOf A := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf A (inv_mem ha₀))) v₀⁻¹
    have := h1.1 (inv_mem hv₀)
    simpa [hu'] using this
  have hconj : a₀ * t₁ = t₁ * (a₀ * v₀⁻¹) := by
    have : a₀ * v₀⁻¹ = t₁⁻¹ * a₀ * t₁ := by rw [hv₀def]; group
    rw [this]; group
  have haa : a₀ * a₀ = z * o₂ := by rw [ho₂def]; group
  have e : (t₁ * a₀) * (t₁ * a₀) = (t₁ * t₁) * z * (o₂ * u') := by
    calc (t₁ * a₀) * (t₁ * a₀) = t₁ * (a₀ * t₁) * a₀ := by group
      _ = t₁ * (t₁ * (a₀ * v₀⁻¹)) * a₀ := by rw [hconj]
      _ = (t₁ * t₁) * ((a₀ * a₀) * (a₀⁻¹ * v₀⁻¹ * a₀)) := by group
      _ = (t₁ * t₁) * ((z * o₂) * u') := by rw [haa]
      _ = (t₁ * t₁) * z * (o₂ * u') := by group
  have hz2 := h.sq_z
  have hzm : z ^ m = 1 ∨ z ^ m = z :=
    zpowers_eq_of_orderOf_two h.hz (z ^ m) (zpow_mem (Subgroup.mem_zpowers z) m)
  have hoO₂ : o₂ ∈ oddCoreOf N := h.oddCoreOf_le_oddCoreOf ho₂
  have hu'N : u' ∈ oddCoreOf N := h.oddCoreOf_le_oddCoreOf hu'O
  rcases hzm with hz1 | hz1
  · left
    rw [hom, hz1, mul_one]
    exact ho
  · right
    rw [e, hom, hz1]
    have : (o * z) * z * (o₂ * u') = o * (o₂ * u') := by
      calc (o * z) * z * (o₂ * u') = o * (z * z) * (o₂ * u') := by group
        _ = o * (o₂ * u') := by rw [hz2, mul_one]
    rw [this]
    exact mul_mem ho (mul_mem hoO₂ hu'N)

omit [Finite X] in
theorem pow_odd_eq_self_of_mul_self_eq_one {G : Type} [Group G] {σ : G} (h : σ * σ = 1) {m : ℕ}
    (hm : Odd m) : σ ^ m = σ := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : σ ^ 2 = 1 := by rw [sq]; exact h
  rw [pow_succ, pow_mul, h2, one_pow, one_mul]

theorem exists_involution_of_sq_mem (h : Sec5Ctx X n z N A M) {t : X} (htN : t ∈ N)
    (hsq : t * t ∈ oddCoreOf N) {σ : Perm (Fin n)} (hσ : h.psi ⟨t, htN⟩ = σ) (hσ2 : σ * σ = 1) :
    ∃ (y : X) (hyN : y ∈ N), y * y = 1 ∧ h.psi ⟨y, hyN⟩ = σ := by
  have hodd := odd_card_oddCoreOf N
  refine ⟨t ^ Nat.card (oddCoreOf N), pow_mem htN _, pow_card_sq_eq_one hsq, ?_⟩
  have : (⟨t ^ Nat.card (oddCoreOf N), pow_mem htN _⟩ : ↥N) = (⟨t, htN⟩ : ↥N) ^ Nat.card
      (oddCoreOf N) := rfl
  rw [this, map_pow, hσ]
  exact pow_odd_eq_self_of_mul_self_eq_one hσ2 hodd

theorem exists_psi_eq_of_odd (h : Sec5Ctx X n z N A M) {t : X} (htN : t ∈ N)
    (hodd : sign (h.psi ⟨t, htN⟩) = -1) (σ : Perm (Fin n)) :
    ∃ (c : X) (hcN : c ∈ N), h.psi ⟨c, hcN⟩ = σ := by
  by_cases hσ : sign σ = 1
  · obtain ⟨a, ha, hψ⟩ := h.exists_mem_psi_eq hσ
    exact ⟨a, h.hAN ha, hψ⟩
  · have hσ' : sign σ = -1 := by
      rcases Int.units_eq_one_or (sign σ) with h1 | h1
      · exact absurd h1 hσ
      · exact h1
    have h1 : sign ((h.psi ⟨t, htN⟩)⁻¹ * σ) = 1 := by
      rw [Perm.sign_mul, Perm.sign_inv, hodd, hσ']
      decide
    obtain ⟨a, ha, hψ⟩ := h.exists_mem_psi_eq h1
    refine ⟨t * a, mul_mem htN (h.hAN ha), ?_⟩
    have : (⟨t * a, mul_mem htN (h.hAN ha)⟩ : ↥N) = ⟨t, htN⟩ * ⟨a, h.hAN ha⟩ := rfl
    rw [this, map_mul, hψ]
    group

theorem exists_involution_odd (h : Sec5Ctx X n z N A M) {t : X} (htN : t ∈ N)
    (hodd : sign (h.psi ⟨t, htN⟩) = -1) :
    ∃ (y : X) (hyN : y ∈ N), y * y = 1 ∧
      (h.psi ⟨y, hyN⟩ = oddOne h.hn ∨ h.psi ⟨y, hyN⟩ = oddOne h.hn * dblTwo h.hn) := by
  have hn := h.hn
  obtain ⟨t₁, ht₁N, ht₁⟩ := h.exists_psi_eq_of_odd htN hodd (oddOne hn)
  obtain ⟨a₀, ha₀, ha₀ψ⟩ := h.exists_mem_psi_eq (sign_dblTwo hn)
  rcases h.sq_mem_or_sq_mem ht₁N ha₀ ht₁ ha₀ψ with h1 | h1
  · obtain ⟨y, hyN, hy2, hyψ⟩ := h.exists_involution_of_sq_mem ht₁N h1 ht₁ (oddOne_sq hn)
    exact ⟨y, hyN, hy2, Or.inl hyψ⟩
  · have ht₃ : h.psi ⟨t₁ * a₀, mul_mem ht₁N (h.hAN ha₀)⟩ = oddOne hn * dblTwo hn := by
      have : (⟨t₁ * a₀, mul_mem ht₁N (h.hAN ha₀)⟩ : ↥N) =
          ⟨t₁, ht₁N⟩ * ⟨a₀, h.hAN ha₀⟩ := rfl
      rw [this, map_mul, ht₁, ha₀ψ]
    obtain ⟨y, hyN, hy2, hyψ⟩ := h.exists_involution_of_sq_mem (mul_mem ht₁N (h.hAN ha₀)) h1
      ht₃ (oddOne_mul_dblTwo_sq hn)
    exact ⟨y, hyN, hy2, Or.inr hyψ⟩

end Sec5Ctx

end CFSG.OddStandard.Solomon75
