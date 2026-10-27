module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem eq_one_of_sq_eq_one_of_odd_center (hodd : Odd (Nat.card (center X))) {z : X}
    (hz : z ∈ center X) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : ↥(center X)) ∣ Nat.card (center X) := orderOf_dvd_natCard _
  have h2 : orderOf (⟨z, hz⟩ : ↥(center X)) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]
    exact Subtype.ext hzz
  have h3 : orderOf (⟨z, hz⟩ : ↥(center X)) = 1 := by
    have h4 := Nat.dvd_gcd h1 h2
    have h5 : Nat.gcd (Nat.card (center X)) 2 = 1 := by
      rw [Nat.gcd_comm]
      exact Nat.coprime_two_left.2 hodd
    rw [h5] at h4
    exact Nat.dvd_one.1 h4
  have := orderOf_eq_one_iff.1 h3
  exact congrArg Subtype.val this

omit [Finite X] in
theorem eq_of_mk_eq_of_sq (hodd : Odd (Nat.card (center X))) {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (h : (x : X ⧸ center X) = y) : x = y := by
  have hz0 : x⁻¹ * y ∈ center X := QuotientGroup.eq.1 h
  obtain ⟨z, hzdef⟩ : ∃ z, z = x⁻¹ * y := ⟨_, rfl⟩
  rw [← hzdef] at hz0
  have hzx : x * z = z * x := mem_center_iff.1 hz0 x
  have hyz : y = x * z := by rw [hzdef]; group
  have hzz : z * z = 1 := by
    have h1 : y * y = z * z := by
      calc y * y = (x * z) * (x * z) := by rw [← hyz]
        _ = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hzx]
        _ = (x * x) * (z * z) := by group
        _ = z * z := by rw [hx, one_mul]
    rw [← h1]
    exact hy
  have hz1 := eq_one_of_sq_eq_one_of_odd_center hodd hz0 hzz
  rw [hzdef, inv_mul_eq_one] at hz1
  exact hz1

omit [Finite X] in
theorem commute_of_mk_commute (hodd : Odd (Nat.card (center X))) {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (h : ((x * y : X) : X ⧸ center X) = ((y * x : X) : X ⧸ center X)) :
    x * y = y * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hz0 : (y * x)⁻¹ * (x * y) ∈ center X := QuotientGroup.eq.1 h.symm
  obtain ⟨z, hzdef⟩ : ∃ z, z = (y * x)⁻¹ * (x * y) := ⟨_, rfl⟩
  rw [← hzdef] at hz0
  have hz' : z = x * y * x * y := by
    rw [hzdef, mul_inv_rev, hxi, hyi]
    group
  have hzx : x * z = z * x := mem_center_iff.1 hz0 x
  have hzz : z * z = 1 := by
    have h1 : x * z * x = z := by
      rw [hzx, mul_assoc, hx, mul_one]
    have h2 : x * z * x = z⁻¹ := by
      calc x * z * x = x * (x * y * x * y) * x := by rw [← hz']
        _ = (x * x) * y * x * y * x := by group
        _ = y * x * y * x := by rw [hx, one_mul]
        _ = (x * y * x * y)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hxi, hyi]
          group
        _ = z⁻¹ := by rw [← hz']
    have h3 : z = z⁻¹ := h1.symm.trans h2
    calc z * z = z * z⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel z
  have hz1 := eq_one_of_sq_eq_one_of_odd_center hodd hz0 hzz
  rw [hz'] at hz1
  have h4 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * y * x * y := by group
      _ = 1 := hz1
  have h5 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left h4
  rw [h5, mul_inv_rev, hxi, hyi]

omit [Finite X] in
theorem nonabelian_quotient_of_quasisimple (hq : CFSG.IsQuasisimple X) :
    ∃ a b : X ⧸ center X, a * b ≠ b * a := hq.2.2

theorem exists_fused_lift (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (center X))) {u : X}
    (hu : u * u = 1) (hu1 : (u : X ⧸ center X) ≠ 1) :
    ∃ y : X, y * u * y⁻¹ ≠ u ∧ (y * u * y⁻¹) * u = u * (y * u * y⁻¹) := by
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have hu2 : orderOf (u : X ⧸ center X) = 2 := by
    refine orderOf_eq_prime ?_ hu1
    rw [pow_two, ← QuotientGroup.mk_mul, hu]
    rfl
  obtain ⟨g, hne, hcomm⟩ :=
    exists_fused_commuting_involution (nonabelian_quotient_of_quasisimple hq) hu2
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  have hu3 : (y * u * y⁻¹) * (y * u * y⁻¹) = 1 := by
    calc (y * u * y⁻¹) * (y * u * y⁻¹) = y * (u * u) * y⁻¹ := by group
      _ = 1 := by rw [hu]; group
  refine ⟨y, fun h => hne ?_, ?_⟩
  · rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  · refine commute_of_mk_commute hodd hu3 hu ?_
    simpa only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] using hcomm

end Abstract

section Action

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

omit [Finite H] in
theorem act_mk {g : H} (hg : g ∈ normalizer (L : Set H)) (x : ↥L) :
    normalizerAction L ⟨g, hg⟩ (x : ↥L ⧸ center ↥L) =
      ((⟨g * (x : H) * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩ : ↥L) : ↥L ⧸ center ↥L) :=
  normalizerAction_apply ⟨g, hg⟩ x _ rfl

omit [Finite H] in
theorem exists_fixed_lift (hodd : Odd (Nat.card ↥(center ↥L))) {g : H}
    (hg : g ∈ normalizer (L : Set H)) (hgg : g * g = 1) {q : ↥L ⧸ center ↥L}
    (hfix : normalizerAction L ⟨g, hg⟩ q = q) :
    ∃ y : ↥L, (y : ↥L ⧸ center ↥L) = q ∧ g * (y : H) * g⁻¹ = y := by
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hmem : ∀ x : ↥L, g * (x : H) * g⁻¹ ∈ L := fun x => (mem_normalizer_iff.1 hg x).1 x.2
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : ↥L, (y₁ : H) = g * (y₀ : H) * g⁻¹ := ⟨⟨_, hmem y₀⟩, rfl⟩
  rw [normalizerAction_apply ⟨g, hg⟩ y₀ y₁ hy₁] at hfix
  have hz : y₀⁻¹ * y₁ ∈ center ↥L := QuotientGroup.eq.1 hfix.symm
  obtain ⟨z, hzdef⟩ : ∃ z : ↥L, z = y₀⁻¹ * y₁ := ⟨_, rfl⟩
  rw [← hzdef] at hz
  obtain ⟨j, hj⟩ := hodd
  have hzn : z ^ (2 * j + 1) = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨z, hz⟩)
    rw [hj] at this
    exact congrArg Subtype.val this
  have hb : ((z : ↥L) : H) = (y₀ : H)⁻¹ * (g * (y₀ : H) * g⁻¹) := by
    rw [hzdef, Subgroup.coe_mul, Subgroup.coe_inv, hy₁]
  have hbn : ((z : ↥L) : H) ^ (2 * j + 1) = 1 := by
    have := congrArg Subtype.val hzn
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a : H, a = (y₀ : H) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : H, b = ((z : ↥L) : H) := ⟨_, rfl⟩
  rw [← ha, ← hbd] at hb
  rw [← hbd] at hbn
  have hconj : g * a * g⁻¹ = a * b := by rw [hb]; group
  have hinv : g * b * g⁻¹ = b⁻¹ := by
    have e1 : g * (g * a * g⁻¹) * g⁻¹ = a := by
      calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g * g)⁻¹ := by group
        _ = a := by rw [hgg]; group
    have e2 : g * (a * b) * g⁻¹ = a := by
      rw [← hconj]
      exact e1
    have e2' : (a * b) * (g * b * g⁻¹) = a := by
      calc (a * b) * (g * b * g⁻¹) = (g * a * g⁻¹) * (g * b * g⁻¹) := by rw [hconj]
        _ = g * (a * b) * g⁻¹ := by group
        _ = a := e2
    have e3 : b * (g * b * g⁻¹) = 1 := by
      calc b * (g * b * g⁻¹) = a⁻¹ * ((a * b) * (g * b * g⁻¹)) := by group
        _ = 1 := by rw [e2']; group
    exact eq_inv_of_mul_eq_one_right e3
  refine ⟨y₀ * z ^ (j + 1), ?_, ?_⟩
  · have hzc : z ^ (j + 1) ∈ center ↥L := pow_mem hz _
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (z ^ (j + 1))).2 hzc, mul_one]
  · rw [Subgroup.coe_mul, Subgroup.coe_pow, ← ha, ← hbd]
    have hc : b * (b⁻¹) ^ (j + 1) = b ^ (j + 1) := by
      have h1 : b ^ (j + 1) * b ^ (j + 1) = b := by
        rw [← pow_add]
        have : j + 1 + (j + 1) = (2 * j + 1) + 1 := by ring
        rw [this, pow_succ, hbn, one_mul]
      rw [inv_pow]
      calc b * (b ^ (j + 1))⁻¹ = (b ^ (j + 1) * b ^ (j + 1)) * (b ^ (j + 1))⁻¹ := by rw [h1]
        _ = b ^ (j + 1) := by group
    calc g * (a * b ^ (j + 1)) * g⁻¹ = (g * a * g⁻¹) * (g * b ^ (j + 1) * g⁻¹) := by group
      _ = (a * b) * (g * b * g⁻¹) ^ (j + 1) := by rw [hconj, conj_pow]
      _ = (a * b) * (b⁻¹) ^ (j + 1) := by rw [hinv]
      _ = a * (b * (b⁻¹) ^ (j + 1)) := by group
      _ = a * b ^ (j + 1) := by rw [hc]

omit [Finite H] in
theorem exists_umoves_lift (hodd : Odd (Nat.card ↥(center ↥L)))
    (hY : UMovesCond (↥L ⧸ center ↥L)) {u s : H} (hu : u ∈ L) (huu : u * u = 1)
    (hu1 : (⟨u, hu⟩ : ↥L) ∉ center ↥L) (hs : s ∈ normalizer (L : Set H)) (hss : s * s = 1) :
    ∃ h ∈ L, (h * u * h⁻¹) * s = s * (h * u * h⁻¹) := by
  have hu₀ : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext huu
  have hū2 : orderOf ((⟨u, hu⟩ : ↥L) : ↥L ⧸ center ↥L) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hu₀]
      rfl
    · intro h1
      exact hu1 ((QuotientGroup.eq_one_iff _).1 h1)
  have hαα : normalizerAction L ⟨s, hs⟩ * normalizerAction L ⟨s, hs⟩ = 1 := by
    rw [← map_mul, ← map_one (normalizerAction L)]
    congr 1
    exact Subtype.ext hss
  obtain ⟨hh, hfix⟩ := hY _ hū2 (normalizerAction L ⟨s, hs⟩) hαα
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective hh
  set u₂ : ↥L := h₀ * ⟨u, hu⟩ * h₀⁻¹ with hu₂
  have hu₂u₂ : u₂ * u₂ = 1 := by
    calc u₂ * u₂ = h₀ * (⟨u, hu⟩ * ⟨u, hu⟩) * h₀⁻¹ := by rw [hu₂]; group
      _ = 1 := by rw [hu₀]; group
  have hmk : ((u₂ : ↥L) : ↥L ⧸ center ↥L) =
      (h₀ : ↥L ⧸ center ↥L) * ((⟨u, hu⟩ : ↥L) : ↥L ⧸ center ↥L) * (h₀ : ↥L ⧸ center ↥L)⁻¹ := by
    rw [hu₂, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmem : (s * (u₂ : H) * s⁻¹) ∈ L := (mem_normalizer_iff.1 hs u₂).1 u₂.2
  have hact := normalizerAction_apply ⟨s, hs⟩ u₂ ⟨s * (u₂ : H) * s⁻¹, hmem⟩ rfl
  rw [← hmk] at hfix
  rw [hact] at hfix
  have hu₃ : (⟨s * (u₂ : H) * s⁻¹, hmem⟩ : ↥L) * ⟨s * (u₂ : H) * s⁻¹, hmem⟩ = 1 := by
    apply Subtype.ext
    have : (u₂ : H) * (u₂ : H) = 1 := congrArg Subtype.val hu₂u₂
    calc s * (u₂ : H) * s⁻¹ * (s * (u₂ : H) * s⁻¹) = s * ((u₂ : H) * (u₂ : H)) * s⁻¹ := by
          group
      _ = 1 := by rw [this]; group
  have heq := eq_of_mk_eq_of_sq hodd hu₃ hu₂u₂ hfix
  have heq' : s * (u₂ : H) * s⁻¹ = u₂ := congrArg Subtype.val heq
  refine ⟨(h₀ : H), h₀.2, ?_⟩
  have hcoe : (u₂ : H) = (h₀ : H) * u * (h₀ : H)⁻¹ := rfl
  rw [← hcoe]
  calc (u₂ : H) * s = (s * (u₂ : H) * s⁻¹) * s := by rw [heq']
    _ = s * u₂ := by group

end Action

end CFSG.EvenSporadicStandard.Induction.Closing
