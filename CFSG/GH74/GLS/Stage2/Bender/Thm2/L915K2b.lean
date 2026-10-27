module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Subgroup
open scoped commutatorElement

theorem comm_mul_left {X : Type} [Group X] (g h x : X) :
    ⁅g * h, x⁆ = g * ⁅h, x⁆ * g⁻¹ * ⁅g, x⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_comm_eq_one {X : Type} [Group X] (a b x : X) (hu : ⁅a, x⁆ ∈ center X)
    (hv : ⁅b, x⁆ ∈ center X) : ⁅⁅a, b⁆, x⁆ = 1 := by
  have hcu : ∀ g : X, g * ⁅a, x⁆ = ⁅a, x⁆ * g := fun g => Subgroup.mem_center_iff.mp hu g
  have hcv : ∀ g : X, g * ⁅b, x⁆ = ⁅b, x⁆ * g := fun g => Subgroup.mem_center_iff.mp hv g
  have h1 : ⁅a * b, x⁆ = ⁅b, x⁆ * ⁅a, x⁆ := by
    rw [comm_mul_left, hcv a]; group
  have h2 : ⁅b * a, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := by
    rw [comm_mul_left, hcu b]; group
  have h3 : a * b = ⁅a, b⁆ * (b * a) := by
    rw [commutatorElement_def]; group
  have hc : ∀ w : X, w ∈ center X → ∀ g : X, g * w * g⁻¹ = w := fun w hw g => by
    rw [Subgroup.mem_center_iff.mp hw g]; group
  have h4 : ⁅a * b, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ * ⁅⁅a, b⁆, x⁆ := by
    rw [h3, comm_mul_left, h2, hc _ (Subgroup.mul_mem _ hu hv)]
  have h5 : ⁅b, x⁆ * ⁅a, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ := hcu ⁅b, x⁆
  rw [h1, h5] at h4
  have : ⁅a, x⁆ * ⁅b, x⁆ * ⁅⁅a, b⁆, x⁆ = ⁅a, x⁆ * ⁅b, x⁆ * 1 := by rw [mul_one]; exact h4.symm
  exact mul_left_cancel this

section Lift

variable {X : Type} [Group X]

theorem eq_one_of_sq_eq_one_of_odd_center (hZ : Odd (Nat.card ↥(center X))) {c : X}
    (hc : c ∈ center X) (hc2 : c * c = 1) : c = 1 := by
  have h1 : orderOf (⟨c, hc⟩ : ↥(center X)) ∣ Nat.card ↥(center X) := orderOf_dvd_natCard _
  have h2 : orderOf (⟨c, hc⟩ : ↥(center X)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hc2
  have h3 : Nat.gcd 2 (Nat.card ↥(center X)) = 1 := Nat.coprime_two_left.mpr hZ
  have h4 : orderOf (⟨c, hc⟩ : ↥(center X)) = 1 := Nat.dvd_one.mp (h3 ▸ Nat.dvd_gcd h2 h1)
  have := orderOf_eq_one_iff.mp h4
  exact congrArg Subtype.val this

theorem exists_involution_lift [Finite X] (hZ : Odd (Nat.card ↥(center X))) {y : X ⧸ center X}
    (hy2 : y * y = 1) : ∃ x : X, x * x = 1 ∧ (QuotientGroup.mk x : X ⧸ center X) = y := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hw : y₀ * y₀ ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hy2
  set m := Nat.card ↥(center X) with hm
  refine ⟨y₀ ^ m, ?_, ?_⟩
  · have h1 : (⟨y₀ * y₀, hw⟩ : ↥(center X)) ^ m = 1 := pow_card_eq_one'
    have h2 : (y₀ * y₀) ^ m = 1 := congrArg Subtype.val h1
    calc y₀ ^ m * y₀ ^ m = (y₀ * y₀) ^ m := by
          rw [← pow_add, ← two_mul, pow_mul, pow_two]
      _ = 1 := h2
  · obtain ⟨k, hk⟩ := hZ
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, pow_two]
    have : (QuotientGroup.mk y₀ * QuotientGroup.mk y₀ : X ⧸ center X) = 1 := hy2
    rw [this, one_pow, one_mul]

theorem involution_lift_unique (hZ : Odd (Nat.card ↥(center X))) {x x' : X} (hx : x * x = 1)
    (hx' : x' * x' = 1) (h : (QuotientGroup.mk x : X ⧸ center X) = QuotientGroup.mk x') : x = x' := by
  have hc : x⁻¹ * x' ∈ center X := QuotientGroup.eq.mp h
  set c := x⁻¹ * x' with hcdef
  have hxc : x * c = c * x := Subgroup.mem_center_iff.mp hc x
  have e : x' = x * c := by rw [hcdef]; group
  have h2 : c * c = 1 := by
    calc c * c = (x * x) * (c * c) := by rw [hx, one_mul]
      _ = x * (x * c) * c := by group
      _ = x * (c * x) * c := by rw [hxc]
      _ = (x * c) * (x * c) := by group
      _ = x' * x' := by rw [← e]
      _ = 1 := hx'
  have h3 : c = 1 := eq_one_of_sq_eq_one_of_odd_center hZ hc h2
  rw [e, h3, mul_one]

end Lift

section Gen

variable {X : Type} [Group X]

theorem mem_derived2_centralizer_of_hom [Finite X] (hZ : Odd (Nat.card ↥(center X)))
    {D : Type} [Group D] (Φ : D →* X ⧸ center X) {σ c : D} (hσ : σ * σ = 1)
    (hD : (⊤ : Subgroup D) = ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ ⊔ zpowers σ)
    (hc : c ∈ ⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆⁆)
    (hcc : ∀ d : D, d * c = c * d) {x : X} (hx : x * x = 1)
    (hxc : Φ c = QuotientGroup.mk x) :
    x ∈ ⁅⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆,
      ⁅centralizer ({x} : Set X), centralizer ({x} : Set X)⁆⁆ := by
  classical
  set π : X →* X ⧸ center X := QuotientGroup.mk' (center X) with hπ
  set C : Subgroup X := centralizer ({x} : Set X) with hC
  set E : Subgroup (X ⧸ center X) := C.map π with hE
  have hπx : π x = Φ c := by rw [hxc]; rfl
  have hcomm_iff : ∀ a : X, π a * Φ c = Φ c * π a → ⁅a, x⁆ ∈ center X := by
    intro a ha
    rw [← hπx] at ha
    have h1 : π ⁅a, x⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr ha
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hΦcomm : ∀ d : D, Φ d * Φ c = Φ c * Φ d := fun d => by
    rw [← map_mul, ← map_mul, hcc]
  have hmemC : ∀ a : X, ⁅a, x⁆ = 1 → a ∈ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp ha
  have hA : ∀ d₁ d₂ : D, Φ ⁅d₁, d₂⁆ ∈ E := by
    intro d₁ d₂
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Φ d₁)
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (Φ d₂)
    have ha' : π a = Φ d₁ := ha
    have hb' : π b = Φ d₂ := hb
    have hca : ⁅a, x⁆ ∈ center X := hcomm_iff a (by rw [ha']; exact hΦcomm d₁)
    have hcb : ⁅b, x⁆ ∈ center X := hcomm_iff b (by rw [hb']; exact hΦcomm d₂)
    have h0 := comm_comm_eq_one a b x hca hcb
    refine ⟨⁅a, b⁆, hmemC _ h0, ?_⟩
    rw [map_commutatorElement, ha', hb', map_commutatorElement]
  have hB : Φ σ ∈ E := by
    obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (Φ σ)
    have hs' : π s = Φ σ := hs
    have hcs : ⁅s, x⁆ ∈ center X := hcomm_iff s (by rw [hs']; exact hΦcomm σ)
    have hss : s * s ∈ center X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      have : (QuotientGroup.mk s : X ⧸ center X) = Φ σ := hs
      rw [this, ← map_mul, hσ, map_one]
    have h1 : ⁅s * s, x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hss x |>.symm
    have h2 : ⁅s * s, x⁆ = ⁅s, x⁆ * ⁅s, x⁆ := by
      rw [comm_mul_left]
      have := Subgroup.mem_center_iff.mp hcs s
      rw [this]; group
    have h3 : ⁅s, x⁆ = 1 :=
      eq_one_of_sq_eq_one_of_odd_center hZ hcs (by rw [← h2]; exact h1)
    exact ⟨s, hmemC s h3, hs'⟩
  have hTop : (⊤ : Subgroup D).map Φ ≤ E := by
    rw [hD, Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨d₁, -, rfl⟩ := hg₁
      obtain ⟨d₂, -, rfl⟩ := hg₂
      rw [← map_commutatorElement]
      exact hA d₁ d₂
    · rw [Subgroup.zpowers_le]
      exact hB
  have hE1 : ⁅E, E⁆ = (⁅C, C⁆).map π := (Subgroup.map_commutator C C π).symm
  have hStep1 : (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆).map Φ ≤ (⁅C, C⁆).map π := by
    rw [Subgroup.map_commutator, ← hE1]
    exact Subgroup.commutator_mono hTop hTop
  have hStep2 : (⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆⁆).map Φ
      ≤ (⁅⁅C, C⁆, ⁅C, C⁆⁆).map π := by
    have e1 : (⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆⁆).map Φ =
        ⁅(⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆.map Φ), (⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆.map Φ)⁆ :=
      Subgroup.map_commutator _ _ _
    have e2 : (⁅⁅C, C⁆, ⁅C, C⁆⁆).map π = ⁅((⁅C, C⁆).map π), ((⁅C, C⁆).map π)⁆ :=
      Subgroup.map_commutator _ _ _
    rw [e1, e2]
    exact Subgroup.commutator_mono hStep1 hStep1
  obtain ⟨y, hy, hyπ⟩ := hStep2 (Subgroup.mem_map_of_mem Φ hc)
  have hyx : (QuotientGroup.mk y : X ⧸ center X) = QuotientGroup.mk x := by
    have : π y = Φ c := hyπ
    rw [← hπx] at this
    exact this
  have hw : y⁻¹ * x ∈ center X := QuotientGroup.eq.mp hyx
  set m := Nat.card ↥(center X) with hm
  have hwm : (y⁻¹ * x) ^ m = 1 := by
    have h1 : (⟨y⁻¹ * x, hw⟩ : ↥(center X)) ^ m = 1 := pow_card_eq_one'
    exact congrArg Subtype.val h1
  have hxy : x = y * (y⁻¹ * x) := by group
  have hcomm : Commute y (y⁻¹ * x) := Subgroup.mem_center_iff.mp hw y
  have hxm : x = y ^ m := by
    have h1 : x ^ m = y ^ m * (y⁻¹ * x) ^ m := by
      rw [← hcomm.mul_pow, ← hxy]
    rw [hwm, mul_one] at h1
    have h2 : x ^ m = x := by
      obtain ⟨k, hk⟩ := hZ
      rw [hk, pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]
    rw [← h2, h1]
  rw [hxm]
  exact Subgroup.pow_mem _ hy m

end Gen

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
