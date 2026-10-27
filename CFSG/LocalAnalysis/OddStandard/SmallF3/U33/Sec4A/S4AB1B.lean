module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem pt_eq_one_or_sq_of_mem_zpowers {w x : G} (hw : orderOf w = 4) (hx : x ∈ zpowers w)
    (hxx : x * x = 1) : x = 1 ∨ x = w ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : w ^ (k + k) = 1 := by
    rw [zpow_add]
    exact hxx
  have h2 : (4 : ℤ) ∣ k + k := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := k + k)).mpr h1
    rwa [hw] at this
  obtain ⟨m, hm⟩ : ∃ m : ℤ, k = 2 * m := ⟨(k + k) / 4, by omega⟩
  have hs : (w ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    have := pow_orderOf_eq_one w
    rwa [hw] at this
  have hsm : (w ^ 2) ^ m = (w ^ 2) ^ (m % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 2]
    rw [zpow_add, zpow_mul]
    have h3 : (w ^ 2) ^ (2 : ℤ) = 1 := by
      rw [zpow_two, ← pow_two]
      exact hs
    rw [h3, one_zpow, mul_one]
  have hwk : w ^ k = (w ^ 2) ^ m := by
    rw [hm, zpow_mul]
    simp
  rw [hwk, hsm]
  rcases Int.emod_two_eq_zero_or_one m with h0 | h0
  · left
    rw [h0]
    simp
  · right
    rw [h0]
    simp

theorem pt_commutator_mul {p₁ p₂ u₁ u₂ : G} (h₁₁ : Commute p₁ u₁) (h₁₂ : Commute p₁ u₂)
    (h₂₁ : Commute p₂ u₁) (h₂₂ : Commute p₂ u₂) (h₁₂' : Commute p₁ p₂) :
    ⁅p₁ * u₁, p₂ * u₂⁆ = ⁅u₁, u₂⁆ := by
  have hc : Commute p₁ (p₂ * u₂) := h₁₂'.mul_right h₁₂
  have hcomm1 : Commute p₁ ⁅u₁, p₂ * u₂⁆ := by
    rw [commutatorElement_def]
    exact ((h₁₁.mul_right hc).mul_right h₁₁.inv_right).mul_right hc.inv_right
  rw [commutatorElement_mul_left_eq_conj_mul, hc.commutator_eq, mul_one, hcomm1.eq,
    mul_inv_cancel_right]
  have hcomm2 : Commute p₂ ⁅u₁, u₂⁆ := by
    rw [commutatorElement_def]
    exact ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  rw [commutatorElement_mul_right_eq_mul_conj, h₂₁.symm.commutator_eq, one_mul, hcomm2.eq,
    mul_inv_cancel_right]

theorem pt_center (h : Ctx0 t L S x₁ x₂ lam rho) :
    (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓
        centralizer ((twoCore t ⊔ wreathGrp x₁ x₂ lam : Subgroup G) : Set G) =
      twoCore t ⊔ zpowers (x₁ * x₂) := by
  haveI := h.hyp.isCyclic
  have hPP : ∀ a ∈ twoCore t, ∀ b ∈ twoCore t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) ⟨b, hb⟩)
  have hZT : wreathGrp x₁ x₂ lam ⊓ centralizer (wreathGrp x₁ x₂ lam : Set G) =
      zpowers (x₁ * x₂) := (h.wreath.center_eq).1
  apply le_antisymm
  · intro g hg
    obtain ⟨hgS, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨p, hp, u, hu, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hgS
    have hgC' := Subgroup.mem_centralizer_iff.mp hgC
    have huZ : u ∈ wreathGrp x₁ x₂ lam ⊓ centralizer (wreathGrp x₁ x₂ lam : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have h1 := hgC' b (Subgroup.mem_sup_right hb)
      have hpb : p * b = b * p := pt_comm_wreath h p hp b hb
      calc b * u = p⁻¹ * (p * b) * u := by group
        _ = p⁻¹ * (b * p) * u := by rw [hpb]
        _ = p⁻¹ * (b * (p * u)) := by group
        _ = p⁻¹ * (p * u * b) := by rw [h1]
        _ = u * b := by group
    rw [hZT] at huZ
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right huZ)
  · refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hg,
        Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      obtain ⟨p', hp', u, hu, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hs
      have hgu : g * u = u * g := pt_comm_wreath h g hg u hu
      have hgp : g * p' = p' * g := hPP g hg p' hp'
      calc p' * u * g = p' * (u * g) := by group
        _ = p' * (g * u) := by rw [hgu]
        _ = (p' * g) * u := by group
        _ = (g * p') * u := by rw [hgp]
        _ = g * (p' * u) := by group
    · have hgZ : g ∈ wreathGrp x₁ x₂ lam ⊓ centralizer (wreathGrp x₁ x₂ lam : Set G) := by
        rw [hZT]
        exact hg
      obtain ⟨hgT, hgCT⟩ := Subgroup.mem_inf.mp hgZ
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hgT,
        Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      obtain ⟨p', hp', u, hu, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hs
      have hgu : u * g = g * u := (Subgroup.mem_centralizer_iff.mp hgCT) u hu
      have hgp : p' * g = g * p' := pt_comm_wreath h p' hp' g hgT
      calc p' * u * g = p' * (u * g) := by group
        _ = p' * (g * u) := by rw [hgu]
        _ = (p' * g) * u := by group
        _ = (g * p') * u := by rw [hgp]
        _ = g * (p' * u) := by group

theorem pt_center_omega (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ g ∈ (twoCore t ⊔ wreathGrp x₁ x₂ lam) ⊓
        centralizer ((twoCore t ⊔ wreathGrp x₁ x₂ lam : Subgroup G) : Set G),
      g ^ 2 = 1 → g ∈ closure {t, (x₁ * x₂) ^ 2} := by
  intro g hg hg2
  rw [pt_center h] at hg
  have hx₁ : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hxT : x₁ * x₂ ∈ wreathGrp x₁ x₂ lam := Subgroup.mul_mem _ hx₁ hx₂
  have hcomm : ∀ a ∈ twoCore t, ∀ b ∈ zpowers (x₁ * x₂), a * b = b * a :=
    fun a ha b hb => pt_comm_wreath h a ha b (Subgroup.zpowers_le.mpr hxT hb)
  obtain ⟨p, hp, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hg
  have hpc : Commute p c := hcomm p hp c hc
  have hcT : c ∈ wreathGrp x₁ x₂ lam := Subgroup.zpowers_le.mpr hxT hc
  rw [pow_two] at hg2
  have hsq : p * p * (c * c) = 1 := by
    calc p * p * (c * c) = p * (p * c) * c := by group
      _ = p * (c * p) * c := by rw [hpc.eq]
      _ = (p * c) * (p * c) := by group
      _ = 1 := hg2
  have hppT : p * p ∈ wreathGrp x₁ x₂ lam := by
    have : p * p = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hcT hcT)
  have hpp1 : p * p = 1 := by
    have hmem : p * p ∈ twoCore t ⊓ wreathGrp x₁ x₂ lam := ⟨Subgroup.mul_mem _ hp hp, hppT⟩
    rw [pt_inf_wreath h, Subgroup.mem_bot] at hmem
    exact hmem
  have hcc1 : c * c = 1 := by
    rw [hpp1, one_mul] at hsq
    exact hsq
  have hord : orderOf (x₁ * x₂) = 4 := by
    rw [← Nat.card_zpowers]
    exact (h.wreath.center_eq).2
  have hp' : p = 1 ∨ p = t := h.hyp.eq_one_or_eq p hp (by rw [pow_two]; exact hpp1)
  have hc' : c = 1 ∨ c = (x₁ * x₂) ^ 2 := pt_eq_one_or_sq_of_mem_zpowers hord hc hcc1
  have ht : t ∈ closure ({t, (x₁ * x₂) ^ 2} : Set G) := Subgroup.subset_closure (by simp)
  have hz : (x₁ * x₂) ^ 2 ∈ closure ({t, (x₁ * x₂) ^ 2} : Set G) :=
    Subgroup.subset_closure (by simp)
  refine Subgroup.mul_mem _ ?_ ?_
  · rcases hp' with hp1 | hp1
    · rw [hp1]
      exact Subgroup.one_mem _
    · rw [hp1]
      exact ht
  · rcases hc' with hc1 | hc1
    · rw [hc1]
      exact Subgroup.one_mem _
    · rw [hc1]
      exact hz

theorem pt_deriv (h : Ctx0 t L S x₁ x₂ lam rho) :
    ⁅twoCore t ⊔ wreathGrp x₁ x₂ lam, twoCore t ⊔ wreathGrp x₁ x₂ lam⁆ =
      ⁅wreathGrp x₁ x₂ lam, wreathGrp x₁ x₂ lam⁆ := by
  haveI := h.hyp.isCyclic
  have hPP : ∀ a ∈ twoCore t, ∀ b ∈ twoCore t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) ⟨b, hb⟩)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨p₁, hp₁, u₁, hu₁, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hg₁
    obtain ⟨p₂, hp₂, u₂, hu₂, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hg₂
    rw [pt_commutator_mul (pt_comm_wreath h p₁ hp₁ u₁ hu₁) (pt_comm_wreath h p₁ hp₁ u₂ hu₂)
      (pt_comm_wreath h p₂ hp₂ u₁ hu₁) (pt_comm_wreath h p₂ hp₂ u₂ hu₂) (hPP p₁ hp₁ p₂ hp₂)]
    exact Subgroup.commutator_mem_commutator hu₁ hu₂
  · exact Subgroup.commutator_mono le_sup_right le_sup_right

theorem pt_omega_deriv (h : Ctx0 t L S x₁ x₂ lam rho) :
    (x₁ * x₂) ^ 2 ∈ ⁅twoCore t ⊔ wreathGrp x₁ x₂ lam, twoCore t ⊔ wreathGrp x₁ x₂ lam⁆ ∧
      ∀ g ∈ ⁅twoCore t ⊔ wreathGrp x₁ x₂ lam, twoCore t ⊔ wreathGrp x₁ x₂ lam⁆,
        g * g = 1 → g = 1 ∨ g = (x₁ * x₂) ^ 2 := by
  rw [pt_deriv h, (h.wreath.commutator_eq).1]
  have hord : orderOf (x₁⁻¹ * x₂) = 4 := by
    rw [← Nat.card_zpowers]
    exact (h.wreath.commutator_eq).2
  have hsq : (x₁⁻¹ * x₂) ^ 2 = (x₁ * x₂) ^ 2 := by
    have hc12 : Commute x₁ x₂ := h.wreath.comm
    have hc : Commute x₁⁻¹ x₂ := hc12.inv_left
    rw [hc.mul_pow, h.wreath.x₂_sq, inv_pow, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨?_, fun g hg hgg => ?_⟩
  · rw [← hsq]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  · rcases pt_eq_one_or_sq_of_mem_zpowers hord hg hgg with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (h1.trans hsq)

theorem pt_invol (h : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ f ∈ twoCore t ⊔ wreathGrp x₁ x₂ lam, f * f = 1 →
      f ∈ wreathGrp x₁ x₂ lam ∨ t * f ∈ wreathGrp x₁ x₂ lam := by
  intro f hf hff
  obtain ⟨p, hp, u, hu, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_wreath h)).mp hf
  have hpu : p * u = u * p := pt_comm_wreath h p hp u hu
  have hsq : p * p * (u * u) = 1 := by
    calc p * p * (u * u) = p * (p * u) * u := by group
      _ = p * (u * p) * u := by rw [hpu]
      _ = (p * u) * (p * u) := by group
      _ = 1 := hff
  have hppT : p * p ∈ wreathGrp x₁ x₂ lam := by
    have : p * p = (u * u)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hu hu)
  have hpp1 : p * p = 1 := by
    have hmem : p * p ∈ twoCore t ⊓ wreathGrp x₁ x₂ lam := ⟨Subgroup.mul_mem _ hp hp, hppT⟩
    rw [pt_inf_wreath h, Subgroup.mem_bot] at hmem
    exact hmem
  rcases h.hyp.eq_one_or_eq p hp (by rw [pow_two]; exact hpp1) with hp1 | hp1
  · left
    rw [hp1, one_mul]
    exact hu
  · right
    rw [hp1, ← mul_assoc, t_mul_self h.hyp, one_mul]
    exact hu

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
