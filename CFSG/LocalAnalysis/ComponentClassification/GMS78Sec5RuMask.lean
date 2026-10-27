module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuQCert
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuStein

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

theorem fin8_xor_cancel : ∀ a b c d : Fin 8, d = a ^^^ (b ^^^ c) → a = d ^^^ b ^^^ c := by
  decide

theorem fin8_eq_of_xor_eq_zero : ∀ a b : Fin 8, a ^^^ b = 0 → a = b := by
  decide

theorem nat_eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  have h1 := congrArg (· ^^^ b) h
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h1
  exact h1

end RuQCode

namespace Sec3.SzR

variable {G : Type} [Group G] [Finite G] {L T R R₂ : Subgroup G} {y d : G}

structure MaskCoords (L T R : Subgroup G) (μ : G → ℕ) (ν : G → Fin 8) : Prop where
  le : gmsA L T ≤ R
  central : ∀ x ∈ R, ∀ b ∈ gmsA L T, x * b = b * x
  sq_mem : ∀ x ∈ R, x ^ 2 ∈ gmsA L T
  comm_mem : ∀ x ∈ R, ∀ x' ∈ R, x * x' * x⁻¹ * x'⁻¹ ∈ gmsA L T
  normA : ∀ g ∈ normalizer (R : Set G), ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T
  lt : ∀ x ∈ R, μ x < 256
  mul : ∀ x ∈ R, ∀ x' ∈ R, μ (x * x') = μ x ^^^ μ x'
  ker : ∀ x ∈ R, μ x = 0 ↔ x ∈ gmsA L T
  surj : ∀ m < 256, ∃ x ∈ R, μ x = m
  ν_mul : ∀ b ∈ gmsA L T, ∀ b' ∈ gmsA L T, ν (b * b') = ν b ^^^ ν b'
  ν_inj : ∀ b ∈ gmsA L T, ν b = 0 → b = 1
  ν_surj : ∀ t, ∃ b ∈ gmsA L T, ν b = t
  sq : ∀ x ∈ R, ν (x ^ 2) = qC (μ x)
  act : ∀ g ∈ normalizer (R : Set G), ∃ r ∈ glList,
    (∀ b ∈ gmsA L T, ν (g * b * g⁻¹) = linApply r (ν b)) ∧
    ∀ x ∈ R, μ (g * x * g⁻¹) = maskApply (adMat r) (μ x)

theorem exists_maskCoords
    (hS : SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)
    (hNS : ¬ IsSylowOf 2 R (normalizer (R : Set G))) :
    ∃ (μ : G → ℕ) (ν : G → Fin 8), MaskCoords L T R μ ν := by
  classical
  have h0 := ruSim0_check
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨v, φ, c, e, Λ, hC⟩ := hS.exists_rCoords h34 hR₂
  obtain ⟨⟨⟨c₀, e₀, p₀, q₀⟩, X₀, Xi₀⟩, hdd, hΛ, hc', he', hact⟩ :=
    hS.exists_action h34 hR₂ h4 hNS hC
  have hAR : gmsA L T ≤ R := gmsA_le_T.trans hS.T_le
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one (1 : G)] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  set code := Function.surjInv RuCode.toGF_surjective with hcode
  have hcode1 : ∀ s, RuCode.toGF (code s) = s := Function.surjInv_eq RuCode.toGF_surjective
  have hcode2 : ∀ t, code (RuCode.toGF t) = t := fun t => RuCode.toGF_injective (hcode1 _)
  have hcode_add : ∀ s s', code (s + s') = code s ^^^ code s' := fun s s' =>
    RuCode.toGF_injective (by rw [hcode1, RuCode.toGF_xor, hcode1, hcode1])
  set code3 := Function.surjInv RuCode.toGF3_surjective with hcode3
  have hc3 : ∀ z, RuCode.toGF3 (code3 z) = z := Function.surjInv_eq RuCode.toGF3_surjective
  have hc3' : ∀ w, code3 (RuCode.toGF3 w) = w := fun w => RuCode.toGF3_injective (hc3 _)
  have hc3_add : ∀ z z', code3 (z + z') = addV (code3 z) (code3 z') := fun z z' =>
    RuCode.toGF3_injective (by rw [hc3, RuCode.toGF3_addV, hc3, hc3])
  have hW : ∀ x ∈ R, code3 (φ x) ∈ wList p₀ q₀ := by
    intro x hx
    rw [RuCode.mem_wList, ← hΛ]
    have h1 := hC.mem x hx
    rw [← hc3 (φ x)] at h1
    exact h1
  have hcanon := RuSimCode.canon_d h0 hdd
  have hXlt := RuSimCode.steinData_lt _ hdd
  have hxi : ∀ x ∈ R, xiApply Xi₀ (xApply X₀ p₀ q₀ (code3 (φ x))) = code3 (φ x) := fun x hx =>
    RuSimCode.xiApply_xApply h0 hdd (hW x hx)
  refine ⟨fun x => xApply X₀ p₀ q₀ (code3 (φ x)), fun b => code (v b),
    { le := hAR
      central := fun x hx b hb => hS.commute_gmsA hx hb
      sq_mem := fun x hx => hS.sq_mem_gmsA_of_mem_R h34 hX hx
      comm_mem := fun x hx x' hx' => hS.commutator_mem_gmsA h34 hx hx'
      normA := fun g hg b hb =>
        (mem_normalizer_iff.mp (hS.normalizer_le_normalizer_gmsA hR₂ hg) b).mp hb
      lt := fun x _ => RuSimCode.xApply_lt hXlt p₀ q₀ _
      mul := ?_
      ker := ?_
      surj := ?_
      ν_mul := ?_
      ν_inj := ?_
      ν_surj := ?_
      sq := ?_
      act := ?_ }⟩
  ·
    intro x hx x' hx'
    show xApply X₀ p₀ q₀ (code3 (φ (x * x'))) =
      xApply X₀ p₀ q₀ (code3 (φ x)) ^^^ xApply X₀ p₀ q₀ (code3 (φ x'))
    rw [hC.mul _ hx _ hx', hc3_add, RuSimCode.xApply_addV X₀ hcanon (RuCode.mem_wList.mp (hW _ hx))
      (RuCode.mem_wList.mp (hW _ hx'))]
  ·
    intro x hx
    show xApply X₀ p₀ q₀ (code3 (φ x)) = 0 ↔ x ∈ gmsA L T
    rw [← hC.ker _ hx]
    constructor
    · intro h1
      have h2 := hxi x hx
      rw [h1, RuSimCode.xiApply_zero] at h2
      rw [← hc3 (φ x), ← h2, RuSimCode.toGF3_zero']
    · intro h1
      have h2 : code3 (φ x) = (0, 0, 0) := by
        rw [h1]
        apply RuCode.toGF3_injective
        rw [hc3, RuSimCode.toGF3_zero']
      rw [h2, RuSimCode.xApply_zero X₀ hcanon]
  ·
    intro m hm
    have hw := RuSimCode.xiApply_mem h0 hdd hm
    obtain ⟨x, hx, hxφ⟩ := hC.surj (RuCode.toGF3 (xiApply Xi₀ m))
      ((hΛ _).mpr (RuCode.mem_wList.mp hw))
    refine ⟨x, hx, ?_⟩
    show xApply X₀ p₀ q₀ (code3 (φ x)) = m
    rw [hxφ, hc3', RuSimCode.xApply_xiApply h0 hdd hm]
  ·
    intro b hb b' hb'
    show code (v (b * b')) = code (v b) ^^^ code (v b')
    rw [hC.v_mul _ hb _ hb', hcode_add]
  ·
    intro b hb h
    have h1 : v b = 0 := by
      have h2 := congrArg RuCode.toGF h
      rw [hcode1, RuCode.toGF_zero] at h2
      exact h2
    exact hC.v_inj _ hb h1
  ·
    intro t
    obtain ⟨b, hb, hbt⟩ := hC.v_surj (RuCode.toGF t)
    exact ⟨b, hb, by show code (v b) = t; rw [hbt, hcode2]⟩
  ·
    intro x hx
    show code (v (x ^ 2)) = qC (xApply X₀ p₀ q₀ (code3 (φ x)))
    simp only at hc' he'
    have e1 : v (x ^ 2) = RuCode.toGF (sqN c₀ e₀ (code3 (φ x))) := by
      rw [hC.sq _ hx, ← RuCode.sqMap_toGF3, hc3, hc', he']
    have e2 := RuQCode.sqN_xiApply hdd (RuSimCode.xApply_lt hXlt p₀ q₀ (code3 (φ x)))
    simp only at e2
    rw [e1, hcode2, ← e2, hxi x hx]
  ·
    intro g hg
    obtain ⟨r, hrGL, hrA, hrR⟩ := hact g hg
    refine ⟨r, hrGL, fun b hb => ?_, fun x hx => ?_⟩
    · show code (v (g * b * g⁻¹)) = linApply r (code (v b))
      rw [hrA b hb (code (v b)) (hcode1 _).symm, hcode2]
    · show xApply X₀ p₀ q₀ (code3 (φ (g * x * g⁻¹))) =
        maskApply (adMat r) (xApply X₀ p₀ q₀ (code3 (φ x)))
      rw [hrR x hx (code3 (φ x)) (hc3 _).symm, hc3']
      exact RuSimCode.xApply_nMap h0 hdd r _

namespace MaskCoords

variable {μ : G → ℕ} {ν : G → Fin 8} (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem ν_one : ν 1 = 0 := by
  have h := hM.ν_mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one (1 : G)] at h
  have h1 : ν 1 ^^^ ν 1 = 0 := RuSimCode.fin8_xor_self _
  rw [← h] at h1
  exact h1

omit [Finite G] in
theorem eq_of_ν_eq {b b' : G} (hb : b ∈ gmsA L T) (hb' : b' ∈ gmsA L T) (h : ν b = ν b') :
    b = b' := by
  have h1 : ν (b * b'⁻¹) = 0 := by
    rw [hM.ν_mul _ hb _ (inv_mem hb'), h]
    have h2 := hM.ν_mul _ hb' _ (inv_mem hb')
    rw [mul_inv_cancel, hM.ν_one] at h2
    exact h2.symm
  exact mul_inv_eq_one.mp (hM.ν_inj _ (mul_mem hb (inv_mem hb')) h1)

omit [Finite G] in
theorem μ_inv {x : G} (hx : x ∈ R) : μ x⁻¹ = μ x := by
  have h := hM.mul _ (inv_mem hx) _ hx
  rw [inv_mul_cancel, (hM.ker _ (one_mem _)).mpr (one_mem _)] at h
  exact RuQCode.nat_eq_of_xor_eq_zero h.symm

omit [Finite G] in
theorem mul_inv_mem_of_μ_eq {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) (h : μ x = μ x') :
    x * x'⁻¹ ∈ gmsA L T := by
  rw [← hM.ker _ (mul_mem hx (inv_mem hx')), hM.mul _ hx _ (inv_mem hx'), hM.μ_inv hx', h]
  exact Nat.xor_self _

omit [Finite G] in
theorem sq_eq_one_iff {x : G} (hx : x ∈ R) : x ^ 2 = 1 ↔ qC (μ x) = 0 := by
  rw [← hM.sq _ hx]
  constructor
  · intro h
    rw [h, hM.ν_one]
  · intro h
    exact hM.ν_inj _ (hM.sq_mem _ hx) h

omit [Finite G] in
theorem comm {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) :
    ν (x * x' * x⁻¹ * x'⁻¹) = bC (μ x) (μ x') := by
  set c := x * x' * x⁻¹ * x'⁻¹ with hc
  have hcA : c ∈ gmsA L T := hM.comm_mem _ hx _ hx'
  have hcinv : c⁻¹ ∈ gmsA L T := inv_mem hcA
  have h1 : (x * x') ^ 2 = c⁻¹ * (x ^ 2 * x' ^ 2) := by
    have hcc : x' * x = c⁻¹ * (x * x') := by rw [hc]; group
    calc (x * x') ^ 2 = x * (x' * x) * x' := by rw [pow_two]; group
      _ = x * (c⁻¹ * (x * x')) * x' := by rw [hcc]
      _ = (x * c⁻¹) * (x * x') * x' := by group
      _ = (c⁻¹ * x) * (x * x') * x' := by rw [hM.central _ hx _ hcinv]
      _ = c⁻¹ * (x ^ 2 * x' ^ 2) := by rw [pow_two, pow_two]; group
  have h2 := hM.sq _ (mul_mem hx hx')
  rw [h1, hM.ν_mul _ hcinv _ (mul_mem (hM.sq_mem _ hx) (hM.sq_mem _ hx')),
    hM.ν_mul _ (hM.sq_mem _ hx) _ (hM.sq_mem _ hx'), hM.sq _ hx, hM.sq _ hx',
    hM.mul _ hx _ hx'] at h2
  have h3 : ν c⁻¹ = ν c := by
    have h4 := hM.ν_mul _ hcinv _ hcA
    rw [inv_mul_cancel, hM.ν_one] at h4
    exact RuQCode.fin8_eq_of_xor_eq_zero _ _ h4.symm
  rw [h3] at h2
  exact RuQCode.fin8_xor_cancel _ _ _ _ h2.symm

omit [Finite G] in
theorem commute_iff {x x' : G} (hx : x ∈ R) (hx' : x' ∈ R) :
    x * x' = x' * x ↔ bC (μ x) (μ x') = 0 := by
  rw [← hM.comm hx hx']
  constructor
  · intro h
    rw [show x * x' * x⁻¹ * x'⁻¹ = 1 by rw [h]; group, hM.ν_one]
  · intro h
    have h1 := hM.ν_inj _ (hM.comm_mem _ hx _ hx') h
    calc x * x' = (x * x' * x⁻¹ * x'⁻¹) * (x' * x) := by group
      _ = x' * x := by rw [h1, one_mul]

end MaskCoords

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
