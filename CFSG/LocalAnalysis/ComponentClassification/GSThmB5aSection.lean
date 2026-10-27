module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aKernel

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

namespace B5a

variable (h : Hyp52 H)

theorem conj_mem_P {s y : H} (hs : s ∈ h.S) (hy : y ∈ h.P) : s * y * s⁻¹ ∈ h.P := by
  obtain ⟨hyS, hyC⟩ := mem_inf.mp hy
  have hsJ : s⁻¹ ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le (inv_mem hs))).2
  have h1 := conj_mem_coreActionKernel hsJ hyC
  rw [inv_inv] at h1
  exact mem_inf.mpr ⟨mul_mem (mul_mem hs hyS) (inv_mem hs), h1⟩

theorem a_mem_S : h.a ∈ h.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := h.S_sylow
  have haC : h.a ∈ centralizer ({h.a} : Set H) := mem_centralizer_singleton_iff.mpr rfl
  have haN : h.a ∈ normalizer (h.J : Set H) := by
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← mem_centralizer_singleton_iff.mp (h.J_le hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have hc : Commute h.a (h.a * y * h.a⁻¹) :=
        (mem_centralizer_singleton_iff.mp (h.J_le hy)).symm
      have h2 : y = h.a * y * h.a⁻¹ := by
        calc y = h.a⁻¹ * (h.a * y * h.a⁻¹) * h.a := by group
          _ = (h.a * y * h.a⁻¹) * h.a⁻¹ * h.a := by rw [hc.inv_left.eq]
          _ = h.a * y * h.a⁻¹ := by group
      rw [h2]
      exact hy
  let a' : ↥(centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)) :=
    ⟨h.a, mem_inf.mpr ⟨haC, haN⟩⟩
  have hcen : zpowers a' ≤ center ↥(centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)) := by
    rw [zpowers_le, mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).1)
  have : (zpowers a').Normal := normal_of_le_center hcen
  have hp : IsPGroup 2 (zpowers a') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.orderOf_a, pow_one])
  have h1 : a' ∈ (R : Subgroup _) := hp.le_sylow_of_normal R (mem_zpowers a')
  rw [hR] at h1
  exact h1

theorem P_le_T_iff : h.P ≤ h.T ↔ h.P ≤ normalizer (h.B : Set H) := by
  constructor
  · intro hPT
    exact hPT.trans (inf_le_left.trans inf_le_right)
  · intro hPN
    exact le_inf (le_inf inf_le_left hPN) le_rfl

end B5a

namespace Hyp52

variable (h : Hyp52 H)

@[expose] def IsX0 (y : H) : Prop :=
  y ∈ h.P ∧ y ∉ h.T ∧ y ^ 2 ∈ h.T ∧ ∀ s ∈ h.S, ⁅y, s⁆ ∈ h.T

theorem exists_isX0 (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) : ∃ y, h.IsX0 y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 := B5a.isPGroup_S h
  have : Group.IsNilpotent h.S := hS2.isNilpotent
  set Y : ℕ → Subgroup H := fun i =>
    (Subgroup.upperCentralSeries h.S i).map h.S.subtype ⊓ h.P with hY
  have hYtop : ∃ n, ¬ Y n ≤ h.T := by
    refine ⟨Group.nilpotencyClass h.S, fun hle => hBP ((B5a.P_le_T_iff h).mp ?_)⟩
    intro y hy
    refine hle (mem_inf.mpr ⟨?_, hy⟩)
    rw [Subgroup.upperCentralSeries_nilpotencyClass]
    exact mem_map.mpr ⟨⟨y, (mem_inf.mp hy).1⟩, mem_top _, rfl⟩
  set i := Nat.find hYtop with hi
  have hiY : ¬ Y i ≤ h.T := Nat.find_spec hYtop
  have hi0 : i ≠ 0 := by
    intro h0
    apply hiY
    rw [h0]
    intro y hy
    obtain ⟨⟨z, hz, rfl⟩, -⟩ := mem_inf.mp hy
    rw [Subgroup.upperCentralSeries_zero, SetLike.mem_coe, mem_bot] at hz
    rw [hz]
    exact one_mem _
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hjY : Y j ≤ h.T := by
    have := Nat.find_min hYtop (show j < i by omega)
    push Not at this
    exact this
  obtain ⟨y, hyY, hyT⟩ := Set.not_subset.mp hiY
  obtain ⟨m, hm⟩ := (hS2.to_le (inf_le_left : h.P ≤ h.S) ⟨y, (mem_inf.mp hyY).2⟩)
  have hm' : y ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hex : ∃ k, y ^ 2 ^ (k + 1) ∈ h.T := ⟨m, by
    rw [pow_succ, pow_mul, hm', one_pow]
    exact one_mem _⟩
  set k := Nat.find hex with hk
  have hkT : y ^ 2 ^ (k + 1) ∈ h.T := Nat.find_spec hex
  have hkT' : y ^ 2 ^ k ∉ h.T := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero, pow_one]
      exact hyT
    · obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
      have := Nat.find_min hex (show l < k by omega)
      rw [hl]
      exact this
  have hzY : y ^ 2 ^ k ∈ Y i := pow_mem hyY _
  refine ⟨y ^ 2 ^ k, (mem_inf.mp hzY).2, hkT', ?_, fun s hs => ?_⟩
  · rw [← pow_mul, ← pow_succ]
    exact hkT
  · apply hjY
    obtain ⟨⟨z, hz, hzy⟩, hzP⟩ := mem_inf.mp hzY
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [hj] at hz
      have h1 := Subgroup.mem_upperCentralSeries_succ_iff.mp hz ⟨s, hs⟩
      refine mem_map.mpr ⟨_, h1, ?_⟩
      rw [← hzy]
      rfl
    · rw [commutatorElement_def, show y ^ 2 ^ k * s * (y ^ 2 ^ k)⁻¹ * s⁻¹ =
        y ^ 2 ^ k * (s * (y ^ 2 ^ k)⁻¹ * s⁻¹) by group]
      exact mul_mem hzP (B5a.conj_mem_P h hs (inv_mem hzP))

noncomputable def x0 : H := by
  classical
  exact if hBP : h.P ≤ normalizer (h.B : Set H) then h.x else (h.exists_isX0 hBP).choose

theorem x0_eq (hBP : h.P ≤ normalizer (h.B : Set H)) : h.x0 = h.x := by
  rw [x0, dite_eq_left_of_eq_true (eq_true hBP)]

theorem isX0_x0 (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) : h.IsX0 h.x0 := by
  rw [x0, dite_eq_right_of_eq_false (eq_false hBP)]
  exact (h.exists_isX0 hBP).choose_spec

theorem x0_mem_S : h.x0 ∈ h.S := by
  by_cases hBP : h.P ≤ normalizer (h.B : Set H)
  · rw [h.x0_eq hBP]
    exact h.x_mem
  · exact (mem_inf.mp (h.isX0_x0 hBP).1).1

theorem x0_sq_mem_T : h.x0 ^ 2 ∈ h.T := by
  by_cases hBP : h.P ≤ normalizer (h.B : Set H)
  · rw [h.x0_eq hBP]
    obtain ⟨⟨hS, hC⟩, hN⟩ := mem_inf.mp h.x_sq_mem
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hS, hN⟩, mem_inf.mpr ⟨hS, hC⟩⟩
  · exact (h.isX0_x0 hBP).2.2.1

@[expose] def B0 : Subgroup H := h.B ⊓ conjugate h.B h.x0

@[expose] def S0 : Subgroup H := h.S ⊓ normalizer (h.B0 : Set H)

@[expose] def P0 : Subgroup H := h.S0 ⊓ h.P

@[expose] def J0 : Subgroup H := GSLit.fixedLayer h.J h.B0

abbrev G0 : Subgroup H := normalizer (h.B0 : Set H)

abbrev G0bar : Type := ↥h.G0 ⧸ h.B0.subgroupOf h.G0

theorem B0_le_B : h.B0 ≤ h.B := inf_le_left

theorem isPGroup_B0 : IsPGroup 2 h.B0 := (B5a.isPGroup_B h).to_le h.B0_le_B

theorem B0_eq_bot (hBP : h.P ≤ normalizer (h.B : Set H)) : h.B0 = ⊥ := by
  rw [B0, h.x0_eq hBP]
  exact h.inf_conjugate_x

theorem mem_G0_of {g : H} (hg1 : g ∈ normalizer (h.B : Set H))
    (hg2 : g ∈ normalizer (conjugate h.B h.x0 : Set H)) : g ∈ h.G0 := by
  rw [mem_normalizer_iff]
  intro y
  rw [B0, mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hg1 y) (mem_normalizer_iff.mp hg2 y)

theorem mem_normalizer_conjugate {g : H} (hg : h.x0 * g * h.x0⁻¹ ∈ normalizer (h.B : Set H)) :
    g ∈ normalizer (conjugate h.B h.x0 : Set H) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_conjugate_iff, mem_conjugate_iff,
    show h.x0 * (g * y * g⁻¹) * h.x0⁻¹ =
      (h.x0 * g * h.x0⁻¹) * (h.x0 * y * h.x0⁻¹) * (h.x0 * g * h.x0⁻¹)⁻¹ by group]
  exact mem_normalizer_iff.mp hg _

theorem a_mem_G0 : h.a ∈ h.G0 := by
  refine h.mem_G0_of h.a_mem_normalizer (h.mem_normalizer_conjugate ?_)
  have hx : h.x0 ∈ centralizer ({h.a} : Set H) := (mem_inf.mp (h.S_le h.x0_mem_S)).1
  rw [show h.x0 * h.a * h.x0⁻¹ = h.a by
    rw [mem_centralizer_singleton_iff.mp hx, mul_inv_cancel_right]]
  exact h.a_mem_normalizer

theorem x0_mem_G0 : h.x0 ∈ h.G0 := by
  have hx2 : h.x0 ^ 2 ∈ normalizer (h.B : Set H) := (mem_inf.mp (mem_inf.mp h.x0_sq_mem_T).1).2
  rw [mem_normalizer_iff]
  intro y
  rw [B0, mem_inf, mem_inf, mem_conjugate_iff, mem_conjugate_iff]
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨hy2, ?_⟩
    rw [show h.x0 * (h.x0 * y * h.x0⁻¹) * h.x0⁻¹ = h.x0 ^ 2 * y * (h.x0 ^ 2)⁻¹ by
      rw [pow_two]; group]
    exact (mem_normalizer_iff.mp hx2 y).mp hy1
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, hy1⟩
    rw [show h.x0 * (h.x0 * y * h.x0⁻¹) * h.x0⁻¹ = h.x0 ^ 2 * y * (h.x0 ^ 2)⁻¹ by
      rw [pow_two]; group] at hy2
    exact (mem_normalizer_iff.mp hx2 y).mpr hy2

theorem conj_x0_mem (hBP : ¬ h.P ≤ normalizer (h.B : Set H)) {g : H} (hg : g ∈ h.S) :
    h.x0 * g * h.x0⁻¹ ∈ h.T ⊔ zpowers g ∧ (g ∈ h.T → h.x0 * g * h.x0⁻¹ ∈ h.T) ∧
      (g ∈ h.Q → h.x0 * g * h.x0⁻¹ ∈ h.Q) := by
  have hc := (h.isX0_x0 hBP).2.2.2 g hg
  have heq : h.x0 * g * h.x0⁻¹ = ⁅h.x0, g⁆ * g := by
    rw [commutatorElement_def]
    group
  refine ⟨?_, fun hgT => ?_, fun hgQ => ?_⟩
  · rw [heq]
    exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_zpowers g))
  · rw [heq]
    exact mul_mem hc hgT
  · rw [heq]
    exact mul_mem ((mem_inf.mp hc).1) hgQ

theorem B_le_G0 : h.B ≤ h.G0 := by
  intro b hb
  by_cases hBP : h.P ≤ normalizer (h.B : Set H)
  · show b ∈ normalizer (h.B0 : Set H)
    rw [h.B0_eq_bot hBP, normalizer_eq_top]
    exact mem_top _
  · refine h.mem_G0_of (le_normalizer hb) (h.mem_normalizer_conjugate ?_)
    have hbT : b ∈ h.T := B5a.B_le_T h hb
    exact (mem_inf.mp (mem_inf.mp ((h.conj_x0_mem hBP hbT.1.1).2.1 hbT)).1).2

theorem a_mem_S0 : h.a ∈ h.S0 :=
  mem_inf.mpr ⟨B5a.a_mem_S h, h.a_mem_G0⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
