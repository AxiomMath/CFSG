module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DegQ0
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cent
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section Lift2

variable {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}

omit [Finite X] in
theorem degLift_mem_oddCoreOf (M : AhatModel X n A) {c : X} (hc : c ∈ normalizer (A : Set X))
    {a : ↥A} (h : M.autOf c hc (M.e (QuotientGroup.mk a)) = M.e (QuotientGroup.mk a)) :
    (a : X)⁻¹ * (c * (a : X) * c⁻¹) ∈ oddCoreOf A := by
  rw [M.autOf_mk] at h
  have h3 := QuotientGroup.eq.1 (M.e.injective h).symm
  rw [mem_oddCoreOf_iff]
  refine ⟨?_, h3⟩
  refine mul_mem (inv_mem a.2) ?_
  have := (conjAut hc a).2
  rwa [coe_conjAut] at this

omit [Finite X] in
theorem degLift_e_mk_eq (M : AhatModel X n A) (a : ↥A) {b : X} (hb : b ∈ A)
    (h : (a : X)⁻¹ * b ∈ oddCoreOf A) :
    M.e (QuotientGroup.mk (⟨b, hb⟩ : ↥A)) = M.e (QuotientGroup.mk a) := by
  congr 1
  rw [QuotientGroup.eq]
  have h' : b⁻¹ * (a : X) ∈ oddCoreOf A := by
    have := inv_mem h
    rwa [mul_inv_rev, inv_inv] at this
  have : (⟨b, hb⟩ : ↥A)⁻¹ * a = ⟨b⁻¹ * (a : X), oddCoreOf_le A h'⟩ := by
    apply Subtype.ext
    simp
  rw [this]
  exact (mem_oddCoreOf_iff.1 h').2

theorem AhatModel.exists_lift_cent₂ (M : AhatModel X n A) {s x : X}
    (hs : s ∈ normalizer (A : Set X)) (hx : x ∈ normalizer (A : Set X)) (hs2 : s * s = 1)
    (hx4 : (x * x) * (x * x) = 1) (hsx : s * x = x * s) {y : M.K} (hys : M.autOf s hs y = y)
    (hyx : M.autOf x hx y = y) :
    ∃ (b : X) (hb : b ∈ A), s * b = b * s ∧ x * b = b * x ∧
      M.e (QuotientGroup.mk (⟨b, hb⟩ : ↥A)) = y := by
  obtain ⟨a₀, rfl⟩ := M.surj_mk y
  have hOodd : Odd (Nat.card (oddCoreOf A)) := odd_card_oddCoreOf A
  have hsO := mem_normalizer_oddCoreOf_of_mem_normalizer hs
  have hxO := mem_normalizer_oddCoreOf_of_mem_normalizer hx
  have h1 := degLift_mem_oddCoreOf M hx hyx
  have h2 := degLift_mem_oddCoreOf M hs hys
  have hx4' : x ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, sq, hx4]
  obtain ⟨p₁, hp₁, hfix₁⟩ := exists_fixed_mem_coset hOodd (k := 2) hx4' hxO h1
  set a₁ : X := (a₀ : X) * p₁ with ha₁
  have ha₁A : a₁ ∈ A := mul_mem a₀.2 (oddCoreOf_le A hp₁)
  have hxa₁ : Commute x a₁ := by
    change x * a₁ = a₁ * x
    calc x * a₁ = (x * a₁ * x⁻¹) * x := by group
      _ = a₁ * x := by rw [hfix₁]
  have hxs : Commute x s := hsx.symm
  have h2' : a₁⁻¹ * (s * a₁ * s⁻¹) ∈ oddCoreOf A := by
    have e : a₁⁻¹ * (s * a₁ * s⁻¹) =
        p₁⁻¹ * (((a₀ : X)⁻¹ * (s * (a₀ : X) * s⁻¹)) * (s * p₁ * s⁻¹)) := by
      rw [ha₁]; group
    rw [e]
    exact mul_mem (inv_mem hp₁) (mul_mem h2 ((mem_set_normalizer_iff.mp hsO _).mp hp₁))
  set O₁ : Subgroup X := oddCoreOf A ⊓ centralizer ({x} : Set X) with hO₁
  have hO₁odd : Odd (Nat.card O₁) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left)
  have hsC : s ∈ normalizer (centralizer ({x} : Set X) : Set X) :=
    Subgroup.le_normalizer (mem_centralizer_singleton_iff.2 hsx)
  have hsO₁ : s ∈ normalizer (O₁ : Set X) := mem_normalizer_inf hsO hsC
  have hw : a₁⁻¹ * (s * a₁ * s⁻¹) ∈ O₁ := by
    refine ⟨h2', mem_centralizer_singleton_iff.2 ?_⟩
    exact ((hxa₁.inv_right.mul_right ((hxs.mul_right hxa₁).mul_right hxs.inv_right))).symm.eq
  have hs2' : s ^ (2 ^ 1) = 1 := by rw [pow_one, sq, hs2]
  obtain ⟨p₂, hp₂, hfix₂⟩ := exists_fixed_mem_coset hO₁odd (k := 1) hs2' hsO₁ hw
  have hbA : a₁ * p₂ ∈ A := mul_mem ha₁A (oddCoreOf_le A hp₂.1)
  have hxp₂ : Commute x p₂ := (mem_centralizer_singleton_iff.1 hp₂.2).symm
  refine ⟨a₁ * p₂, hbA, ?_, (hxa₁.mul_right hxp₂).eq, ?_⟩
  · calc s * (a₁ * p₂) = (s * (a₁ * p₂) * s⁻¹) * s := by group
      _ = (a₁ * p₂) * s := by rw [hfix₂]
  · refine degLift_e_mk_eq M a₀ hbA ?_
    have e : (a₀ : X)⁻¹ * (a₁ * p₂) = p₁ * p₂ := by rw [ha₁]; group
    rw [e]
    exact mul_mem hp₁ hp₂.1

end Lift2

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.exists_odd_lift_comm [Finite K] {C : CoverSetup n K} {α : MulAut K}
    {k : ℕ} {hk : 2 * k ≤ n} (hα : C.Induces α (stdInv n k hk)) {i l : Fin k} {xb : K}
    (hxb : C.ρ xb = dblPair n k hk i l) {c : Perm (OtherPairs k i l)} (hc : c.IsThreeCycle) :
    ∃ y ∈ fixSub α, C.ρ y = otherHom n k hk i l c ∧ y * xb = xb * y := by
  have hodd3 : ∀ c' : Perm (OtherPairs k i l), c'.IsThreeCycle →
      Odd (orderOf (otherHom n k hk i l c')) := fun c' hc' =>
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one
      (otherHom_threeCycle_pow_three hc'))
  have hmem : otherHom n k hk i l c ∈ Q0 n k hk i l := by
    rw [Q0_eq_closure]
    exact Subgroup.subset_closure ⟨c, hc, rfl⟩
  obtain ⟨y₁, hy₁, hρy₁⟩ := hα.exists_mem_fixSub_of_odd_generated Q0_le_alternatingGroup
    Q0_comm_stdInv Q0_eq_closure.symm (by rintro _ ⟨c', hc', rfl⟩; exact hodd3 c' hc') _ hmem
  have hodd : Odd (orderOf (C.ρ y₁)) := by rw [hρy₁]; exact hodd3 c hc
  obtain ⟨v, hv, hvodd, hρv⟩ := exists_odd_pow_lift C.ρ y₁ hodd
  have hvfix : v ∈ fixSub α := (Subgroup.zpowers_le.2 hy₁) hv
  refine ⟨v, hvfix, hρv.trans hρy₁, ?_⟩
  set ζ : K := v * xb * v⁻¹ * xb⁻¹ with hζdef
  have hζ : ζ ∈ center K := by
    rw [← C.ρ_eq_one_iff, hζdef, map_mul, map_mul, map_mul, map_inv, map_inv, hρv, hρy₁, hxb,
      Q0_comm_dblPair _ hmem]
    group
  have hζ2 : ζ * ζ = 1 := C.sq_of_mem_center hζ
  have hζc : v * ζ = ζ * v := mem_center_iff.1 hζ v
  have h1 : v * xb = ζ * xb * v := by rw [hζdef]; group
  have h2 : v * v * xb = xb * (v * v) := by
    calc v * v * xb = v * (v * xb) := by group
      _ = v * (ζ * xb * v) := by rw [h1]
      _ = (v * ζ) * xb * v := by group
      _ = (ζ * v) * xb * v := by rw [hζc]
      _ = ζ * (v * xb) * v := by group
      _ = ζ * (ζ * xb * v) * v := by rw [h1]
      _ = (ζ * ζ) * xb * (v * v) := by group
      _ = xb * (v * v) := by rw [hζ2, one_mul]
  obtain ⟨m, hm⟩ := hvodd
  have hvpow : (v * v) ^ (m + 1) = v := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf v + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have h3 := ((show Commute (v * v) xb from h2).pow_left (m + 1)).eq
  rwa [hvpow] at h3

end AhatData

end CFSG.OddStandard.Solomon75
