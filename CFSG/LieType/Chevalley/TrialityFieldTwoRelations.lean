module

public import CFSG.LieType.Chevalley.TrialityFieldTwoLifts

public noncomputable section

namespace CFSG.LieType.Chevalley.TrialityFieldTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Chevalley.TrialityCover
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Identities

variable {G : Type*} [Group G]

theorem commute_commutatorElement {g a b : G} (ha : Commute g a) (hb : Commute g b) :
    Commute g ⁅a, b⁆ := by
  rw [commutatorElement_def]
  exact ((ha.mul_right hb).mul_right ha.inv_right).mul_right hb.inv_right

theorem commutatorElement_mul_left' (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right' (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem coe_commutatorElement_sub {H : Subgroup G} (x y : H) :
    ((⁅x, y⁆ : H) : G) = ⁅(x : G), (y : G)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]

theorem conj_commutatorElement' (g a b : G) :
    g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_eq_of_commutators {a b c d w w₀ : G} (hab : a * b = b * a) (h1 : ⁅b, c⁆ = d * w)
    (h2 : ⁅a, c⁆ = w₀) (haw : a * w = w * a) (hbw₀ : b * w₀ = w₀ * b) (hdw₀ : d * w₀ = w₀ * d)
    (hww₀ : w * w₀ = w₀ * w) : a * d * a⁻¹ = d := by
  have e1 : b * c * b⁻¹ = d * w * c := by
    rw [← h1, commutatorElement_def]
    group
  have e2 : a * c * a⁻¹ = w₀ * c := by
    rw [← h2, commutatorElement_def]
    group
  have hw : a * w * a⁻¹ = w := by rw [haw, mul_inv_cancel_right]
  have l : a * b * c * (a * b)⁻¹ = a * d * a⁻¹ * w * w₀ * c :=
    calc a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by group
      _ = a * d * a⁻¹ * (a * w * a⁻¹) * (a * c * a⁻¹) := by rw [e1]; group
      _ = a * d * a⁻¹ * w * w₀ * c := by rw [hw, e2]; group
  have r : b * a * c * (b * a)⁻¹ = d * w * w₀ * c :=
    calc b * a * c * (b * a)⁻¹ = b * (a * c * a⁻¹) * b⁻¹ := by group
      _ = b * w₀ * c * b⁻¹ := by rw [e2]; group
      _ = w₀ * (b * c * b⁻¹) := by rw [hbw₀]; group
      _ = w₀ * d * w * c := by rw [e1]; group
      _ = d * w * w₀ * c := by rw [← hdw₀, mul_assoc d, ← hww₀]; group
  have key : a * d * a⁻¹ * w * w₀ * c = d * w * w₀ * c := by rw [← l, ← r, hab]
  simpa using key

theorem commutatorElement_triple {g₁ g₂ g₃ d y₅ y₆ : G} (h₁ : ⁅g₁, d⁆ = y₆) (h₃ : ⁅g₃, d⁆ = y₅)
    (h₂ : g₂ * d = d * g₂) (hy₁ : y₅ * g₁ = g₁ * y₅) (hy₂ : y₅ * g₂ = g₂ * y₅) :
    ⁅g₁ * g₂ * g₃, d⁆ = y₅ * y₆ := by
  have e3 : g₃ * d * g₃⁻¹ = y₅ * d := by rw [← h₃, commutatorElement_def]; group
  have e1 : g₁ * d * g₁⁻¹ = y₆ * d := by rw [← h₁, commutatorElement_def]; group
  have e2 : g₂ * d * g₂⁻¹ = d := by rw [h₂, mul_inv_cancel_right]
  calc ⁅g₁ * g₂ * g₃, d⁆ = g₁ * (g₂ * (g₃ * d * g₃⁻¹) * g₂⁻¹) * g₁⁻¹ * d⁻¹ := by
        rw [commutatorElement_def]; group
    _ = g₁ * (g₂ * y₅ * d * g₂⁻¹) * g₁⁻¹ * d⁻¹ := by rw [e3]; group
    _ = g₁ * (y₅ * (g₂ * d * g₂⁻¹)) * g₁⁻¹ * d⁻¹ := by rw [← hy₂]; group
    _ = g₁ * y₅ * d * g₁⁻¹ * d⁻¹ := by rw [e2]; group
    _ = y₅ * (g₁ * d * g₁⁻¹) * d⁻¹ := by rw [← hy₁]; group
    _ = y₅ * y₆ := by rw [e1]; group

end Identities

section Pairs

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
include hσ

theorem commute_short_long :
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 0) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 4) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 0) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 5) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 2) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 1) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 2) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 4) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 2) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 5) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 3) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 1) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 3) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 4) e)) ∧
    (∀ (c : K) (e : trialityFixedField K σ.toRingHom),
      Commute (trialityOrbitProd K σ.toRingHom (trialityRoot 3) c : ModGL TwistTag.D4.tag K)
        (pinnedX TwistTag.D4.tag K (trialityRoot 5) e)) := by
  obtain ⟨-, -, -, h15, h16, h23, h24, -, h35, h36, h45, h46, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom (toRingHom_pow_three σ hσ)
  exact ⟨fun c e => (h15 c e).map (adjointGroup TwistTag.D4.tag K).subtype,
    fun c e => (h16 c e).map (adjointGroup TwistTag.D4.tag K).subtype,
    fun c e => ((h23 e c).map (adjointGroup TwistTag.D4.tag K).subtype).symm,
    fun c e => (h35 c e).map (adjointGroup TwistTag.D4.tag K).subtype,
    fun c e => (h36 c e).map (adjointGroup TwistTag.D4.tag K).subtype,
    fun c e => ((h24 e c).map (adjointGroup TwistTag.D4.tag K).subtype).symm,
    fun c e => (h45 c e).map (adjointGroup TwistTag.D4.tag K).subtype,
    fun c e => (h46 c e).map (adjointGroup TwistTag.D4.tag K).subtype⟩

theorem commutator_short_trace
    (s t : K) :
    ⁅(trialityOrbitProd K σ.toRingHom (trialityRoot 0) s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ.toRingHom (trialityRoot 3) t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K (trialityRoot 4)
        (trialityTrace K σ.toRingHom (toRingHom_pow_three σ hσ) (s * t) : K) ∧
    ⁅(trialityOrbitProd K σ.toRingHom (trialityRoot 2) s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ.toRingHom (trialityRoot 3) t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5)
        (trialityTrace K σ.toRingHom (toRingHom_pow_three σ hσ) (s * t) : K) := by
  obtain ⟨h14, h34, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom (toRingHom_pow_three σ hσ)
  exact ⟨(coe_commutatorElement_adjoint _ _).symm.trans (congrArg Subtype.val (h14 s t)),
    (coe_commutatorElement_adjoint _ _).symm.trans (congrArg Subtype.val (h34 s t))⟩

end Pairs

theorem height_trialityRoot_ge_four : ∀ j : Fin 6, 4 ≤ height (trialityRoot j) →
    j = 4 ∨ j = 5 := by
  decide +kernel

theorem height_trialityRoot_ge_three : ∀ j : Fin 6, 3 ≤ height (trialityRoot j) →
    j = 3 ∨ j = 4 ∨ j = 5 := by
  decide +kernel

namespace TwoCover

variable
    {K : Type} [Field K] [Finite K] [CharP K 2] {E : Type*} [Group E] (D : TwoCover K E)

theorem trace_one :
    (trialityTrace K D.σ.toRingHom (toRingHom_pow_three D.σ D.hσ) 1 : K) = 1 := by
  rw [trialityTrace_one]
  rfl

theorem sq_symm
    (c : K) : D.σ.symm c ^ 2 = c := by
  rw [← D.hq, RingEquiv.apply_symm_apply]

include D in
theorem exists_unit_sq_mul
    {s : K} (hs : s ≠ 0) :
    ∃ a : Kˣ, ((a ^ 2 : Kˣ) : K) * s = 1 ∧ (((a ^ 2)⁻¹ : Kˣ) : K) = s := by
  have h0 : D.σ.symm s⁻¹ ≠ 0 := by
    intro h
    have h' := congrArg D.σ h
    rw [RingEquiv.apply_symm_apply, map_zero] at h'
    exact inv_ne_zero hs h'
  refine ⟨Units.mk0 _ h0, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, D.sq_symm, inv_mul_cancel₀ hs]
  · rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0, D.sq_symm, inv_inv]

theorem coe_trace (z : K) :
    (trialityTrace K D.σ.toRingHom (toRingHom_pow_three D.σ D.hσ) z : K) =
      z + D.σ z + D.σ (D.σ z) :=
  rfl

theorem trace_cases (z : K) :
    z + D.σ z + D.σ (D.σ z) = 0 ∨ (z + 1) + D.σ (z + 1) + D.σ (D.σ (z + 1)) = 0 := by
  rcases fixedField_eq_zero_or_one D.σ D.hk
    (trialityTrace K D.σ.toRingHom (toRingHom_pow_three D.σ D.hσ) z) with h | h
  · left
    rw [← D.coe_trace, h]
    rfl
  · right
    have h1 : z + D.σ z + D.σ (D.σ z) = 1 := by
      rw [← D.coe_trace, h]
      rfl
    rw [map_add, map_add, map_one, map_one]
    linear_combination h1 + 2 * (CharTwo.two_eq_zero : (2 : K) = 0)

structure Lifts
    where
  L0 : D.ShortLift 0 (Or.inl rfl)
  L2 : D.ShortLift 2 (Or.inr (Or.inl rfl))
  L3 : D.ShortLift 3 (Or.inr (Or.inr rfl))

theorem nonempty_lifts :
    Nonempty D.Lifts := by
  obtain ⟨L0⟩ := D.exists_shortLift 0 (Or.inl rfl)
  obtain ⟨L2⟩ := D.exists_shortLift 2 (Or.inr (Or.inl rfl))
  obtain ⟨L3⟩ := D.exists_shortLift 3 (Or.inr (Or.inr rfl))
  exact ⟨⟨L0, L2, L3⟩⟩

namespace Lifts

variable
    {D} (L : D.Lifts)

theorem A_zero
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) : A.A 0 = 1 := by
  have h := A.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem A_mul_self
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) (c : K) :
    A.A c * A.A c = 1 := by
  rw [← A.add, CharTwo.add_self_eq_zero, A_zero]

theorem A_inv
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) (c : K) :
    (A.A c)⁻¹ = A.A c :=
  inv_eq_of_mul_eq_one_right (A_mul_self A c)

theorem A_comm
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) (c c' : K) :
    Commute (A.A c) (A.A c') := by
  rw [Commute, SemiconjBy, ← A.add, ← A.add, add_comm]

theorem coe_map_A
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) (c : K) :
    (D.η (A.A c) : ModGL TwistTag.D4.tag K) =
      (trialityOrbitProd K D.σ.toRingHom (trialityRoot j) c : ModGL TwistTag.D4.tag K) := by
  rw [A.map, coe_shortX]

theorem map_A_mem
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) (c : K) :
    (D.η (A.A c) : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j := by
  rw [A.map]
  exact mem_trialityGroup_shortX D.σ D.hσ j hj c

theorem exists_A_eq
    {j : Fin 6} {hj : j = 0 ∨ j = 2 ∨ j = 3} (A : D.ShortLift j hj) {y : E}
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j) :
    ∃ c, D.η (A.A c) = D.η y := by
  obtain ⟨c, hc⟩ := exists_trialityOrbitProd_eq' hj hy
  exact ⟨c, Subtype.ext ((coe_map_A A c).trans hc)⟩

theorem comm0
    (l : Fin 6) (hl : l = 4 ∨ l = 5) (y : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) (c : K) :
    Commute y (L.L0.A c) := by
  obtain ⟨h04, h05, -⟩ := commute_short_long D.σ D.hσ
  rcases hl with rfl | rfl
  · exact L.L0.comm 4 (by decide) h04 y hy c
  · exact L.L0.comm 5 (by decide) h05 y hy c

theorem comm2
    (l : Fin 6) (hl : l = 1 ∨ l = 4 ∨ l = 5) (y : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) (c : K) :
    Commute y (L.L2.A c) := by
  obtain ⟨-, -, h21, h24, h25, -⟩ := commute_short_long D.σ D.hσ
  rcases hl with rfl | rfl | rfl
  · exact L.L2.comm 1 (by decide) h21 y hy c
  · exact L.L2.comm 4 (by decide) h24 y hy c
  · exact L.L2.comm 5 (by decide) h25 y hy c

theorem comm3
    (l : Fin 6) (hl : l = 1 ∨ l = 4 ∨ l = 5) (y : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ l) (c : K) :
    Commute y (L.L3.A c) := by
  obtain ⟨-, -, -, -, -, h31, h34, h35⟩ := commute_short_long D.σ D.hσ
  rcases hl with rfl | rfl | rfl
  · exact L.L3.comm 1 (by decide) h31 y hy c
  · exact L.L3.comm 4 (by decide) h34 y hy c
  · exact L.L3.comm 5 (by decide) h35 y hy c

theorem coe_map_b5
    (s t : K) :
    (D.η ⁅L.L0.A s, L.L3.A t⁆ : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 4)
        (trialityTrace K D.σ.toRingHom (toRingHom_pow_three D.σ D.hσ) (s * t) : K) := by
  rw [map_commutatorElement, coe_commutatorElement_sub, coe_map_A, coe_map_A]
  exact (commutator_short_trace D.σ D.hσ s t).1

theorem coe_map_b6
    (s t : K) :
    (D.η ⁅L.L2.A s, L.L3.A t⁆ : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5)
        (trialityTrace K D.σ.toRingHom (toRingHom_pow_three D.σ D.hσ) (s * t) : K) := by
  rw [map_commutatorElement, coe_commutatorElement_sub, coe_map_A, coe_map_A]
  exact (commutator_short_trace D.σ D.hσ s t).2

theorem b5_mem
    (s t : K) :
    (D.η ⁅L.L0.A s, L.L3.A t⁆ : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 4 := by
  rw [coe_map_b5]
  exact pinnedX_trialityRoot_mem (Or.inr (Or.inl rfl)) _

theorem b6_mem
    (s t : K) :
    (D.η ⁅L.L2.A s, L.L3.A t⁆ : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 5 := by
  rw [coe_map_b6]
  exact pinnedX_trialityRoot_mem (Or.inr (Or.inr rfl)) _

theorem map_Y5
    : D.η ⁅L.L0.A 1, L.L3.A 1⁆ = longX D.σ 4 (Or.inr (Or.inl rfl)) :=
  Subtype.ext (by rw [coe_map_b5, mul_one, D.trace_one, coe_longX, OneMemClass.coe_one])

theorem map_Y6
    : D.η ⁅L.L2.A 1, L.L3.A 1⁆ = longX D.σ 5 (Or.inr (Or.inr rfl)) :=
  Subtype.ext (by rw [coe_map_b6, mul_one, D.trace_one, coe_longX, OneMemClass.coe_one])

include L in
theorem lift_comm_five_six
    (z z' : E) (hz : (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 4)
    (hz' : (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 5) : Commute z z' := by
  have hY : Commute z' ⁅L.L0.A 1, L.L3.A 1⁆ :=
    commute_commutatorElement (L.comm0 5 (Or.inr rfl) z' hz' 1) (L.comm3 5 (by decide) z' hz' 1)
  rcases D.long_cases (Or.inr (Or.inl rfl)) hz with h | h
  · exact D.commute_of_map_eq_one h z'
  · exact (D.commute_of_map_eq (L.map_Y5.trans h.symm) hY.symm)

include L in
theorem long_comm_deep
    (j j' : Fin 6) (hj : j = 4 ∨ j = 5) (hj' : j' = 4 ∨ j' = 5) (z z' : E)
    (hz : (D.η z : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j)
    (hz' : (D.η z' : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j') : Commute z z' := by
  rcases hj with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact D.long_lift_comm (by decide) z z' hz hz'
  · exact L.lift_comm_five_six z z' hz hz'
  · exact (L.lift_comm_five_six z' z hz' hz).symm
  · exact D.long_lift_comm (by decide) z z' hz hz'

theorem W_comm_lift
    (a : E) (ha : ∀ j : Fin 6, (j = 4 ∨ j = 5) → ∀ y : E,
      (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ j → Commute y a)
    (w : E) (hw : (D.η w : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4) :
    Commute w a :=
  D.lift_commute_of_heightSeries 4 a
    (fun j hj y hy => ha j (height_trialityRoot_ge_four j hj) y hy) w hw

theorem W_comm_short
    (w : E)
    (hw : (D.η w : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4) (c : K) :
    Commute w (L.L0.A c) ∧ Commute w (L.L2.A c) ∧ Commute w (L.L3.A c) :=
  ⟨W_comm_lift _ (fun j hj y hy => L.comm0 j hj y hy c) w hw,
    W_comm_lift _ (fun j hj y hy => L.comm2 j (Or.inr hj) y hy c) w hw,
    W_comm_lift _ (fun j hj y hy => L.comm3 j (Or.inr hj) y hy c) w hw⟩

include L in
theorem W_comm
    (w w' : E)
    (hw : (D.η w : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4)
    (hw' : (D.η w' : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4) :
    Commute w w' :=
  W_comm_lift w' (fun j hj y hy => (W_comm_lift y (fun j' hj' z hz =>
    L.long_comm_deep j' j hj' hj z y hz hy) w' hw').symm) w hw

theorem b5_comm0 (s t s' : K) : Commute ⁅L.L0.A s, L.L3.A t⁆ (L.L0.A s') :=
  L.comm0 4 (Or.inl rfl) _ (L.b5_mem s t) s'

theorem b5_comm3 (s t t' : K) : Commute ⁅L.L0.A s, L.L3.A t⁆ (L.L3.A t') :=
  L.comm3 4 (by decide) _ (L.b5_mem s t) t'

theorem b6_comm2 (s t s' : K) : Commute ⁅L.L2.A s, L.L3.A t⁆ (L.L2.A s') :=
  L.comm2 5 (by decide) _ (L.b6_mem s t) s'

theorem b6_comm3 (s t t' : K) : Commute ⁅L.L2.A s, L.L3.A t⁆ (L.L3.A t') :=
  L.comm3 5 (by decide) _ (L.b6_mem s t) t'

theorem b5_add_left
    (s s' t : K) :
    ⁅L.L0.A (s + s'), L.L3.A t⁆ = ⁅L.L0.A s, L.L3.A t⁆ * ⁅L.L0.A s', L.L3.A t⁆ := by
  rw [L.L0.add, commutatorElement_mul_left', (L.b5_comm0 s' t s).symm.eq, mul_inv_cancel_right]
  exact (D.long_lift_comm (by decide) _ _ (L.b5_mem s' t) (L.b5_mem s t))

theorem b5_add_right (s t t' : K) :
    ⁅L.L0.A s, L.L3.A (t + t')⁆ = ⁅L.L0.A s, L.L3.A t⁆ * ⁅L.L0.A s, L.L3.A t'⁆ := by
  rw [L.L3.add, commutatorElement_mul_right', (L.b5_comm3 s t' t).symm.eq, mul_inv_cancel_right]

theorem b6_add_left
    (s s' t : K) :
    ⁅L.L2.A (s + s'), L.L3.A t⁆ = ⁅L.L2.A s, L.L3.A t⁆ * ⁅L.L2.A s', L.L3.A t⁆ := by
  rw [L.L2.add, commutatorElement_mul_left', (L.b6_comm2 s' t s).symm.eq, mul_inv_cancel_right]
  exact (D.long_lift_comm (by decide) _ _ (L.b6_mem s' t) (L.b6_mem s t))

theorem b6_add_right (s t t' : K) :
    ⁅L.L2.A s, L.L3.A (t + t')⁆ = ⁅L.L2.A s, L.L3.A t⁆ * ⁅L.L2.A s, L.L3.A t'⁆ := by
  rw [L.L3.add, commutatorElement_mul_right', (L.b6_comm3 s t' t).symm.eq, mul_inv_cancel_right]

theorem b5_torus
    (a : Kˣ) (s t : K) :
    ⁅L.L0.A ((a ^ 2 : Kˣ) * s), L.L3.A (((a ^ 2)⁻¹ : Kˣ) * t)⁆ = ⁅L.L0.A s, L.L3.A t⁆ := by
  obtain ⟨g, hg⟩ := D.surj (torusX D.σ D.hσ (a, 1))
  obtain ⟨w0, -, -, w3, -, -⟩ := weights_two D.σ D.hσ D.hk (a, 1)
  dsimp only at w0 w3
  have h0 := L.L0.torus g (a, 1) hg s
  have h3 := L.L3.torus g (a, 1) hg t
  rw [w0] at h0
  rw [w3] at h3
  rw [← h0, ← h3, ← conj_commutatorElement']
  exact D.torus_conj_long (by decide) g _ (a, 1) hg (L.b5_mem s t)

theorem b6_torus
    (a : Kˣ) (s t : K) :
    ⁅L.L2.A ((a ^ 2 : Kˣ) * s), L.L3.A (((a ^ 2)⁻¹ : Kˣ) * t)⁆ = ⁅L.L2.A s, L.L3.A t⁆ := by
  obtain ⟨g, hg⟩ := D.surj (torusX D.σ D.hσ (a, 1))
  obtain ⟨-, -, w2, w3, -, -⟩ := weights_two D.σ D.hσ D.hk (a, 1)
  dsimp only at w2 w3
  have h2 := L.L2.torus g (a, 1) hg s
  have h3 := L.L3.torus g (a, 1) hg t
  rw [w2] at h2
  rw [w3] at h3
  rw [← h2, ← h3, ← conj_commutatorElement']
  exact D.torus_conj_long (by decide) g _ (a, 1) hg (L.b6_mem s t)

theorem b5_eq
    (s t : K) : ⁅L.L0.A s, L.L3.A t⁆ = ⁅L.L0.A 1, L.L3.A (s * t)⁆ := by
  by_cases hs : s = 0
  · rw [hs, zero_mul, A_zero, A_zero, commutatorElement_one_left, commutatorElement_one_right]
  obtain ⟨a, ha, ha'⟩ := D.exists_unit_sq_mul hs
  rw [← L.b5_torus a s t, ha, ha']

theorem b6_eq
    (s t : K) : ⁅L.L2.A s, L.L3.A t⁆ = ⁅L.L2.A 1, L.L3.A (s * t)⁆ := by
  by_cases hs : s = 0
  · rw [hs, zero_mul, A_zero, A_zero, commutatorElement_one_left, commutatorElement_one_right]
  obtain ⟨a, ha, ha'⟩ := D.exists_unit_sq_mul hs
  rw [← L.b6_torus a s t, ha, ha']

theorem w_mem
    (s t : K) :
    (D.η ((L.L3.A (D.σ s * D.σ (D.σ t) + D.σ (D.σ s) * D.σ t))⁻¹ * ⁅L.L0.A s, L.L2.A t⁆) :
      ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4 := by
  rw [map_mul, map_inv, map_commutatorElement, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_commutatorElement_sub, coe_map_A, coe_map_A, coe_map_A]
  exact orbitProd_commutator_mem_four (toRingHom_pow_three D.σ D.hσ) s t

theorem B5_trace_eq_one
    (z : K) : ⁅L.L0.A 1, L.L3.A (D.σ z + D.σ (D.σ z))⁆ = 1 := by
  have hw := L.w_mem z 1
  have hw₀ := L.w_mem 1 1
  simp only [map_one, mul_one, CharTwo.add_self_eq_zero, A_zero, inv_one, one_mul] at hw hw₀
  set d := L.L3.A (D.σ z + D.σ (D.σ z))
  set w := d⁻¹ * ⁅L.L0.A z, L.L2.A 1⁆
  set w₀ := ⁅L.L0.A 1, L.L2.A 1⁆
  have hdw₀ := (L.W_comm_short w₀ hw₀ (D.σ z + D.σ (D.σ z))).2.2
  have key := conj_eq_of_commutators (a := L.L0.A 1) (b := L.L0.A z) (c := L.L2.A 1) (d := d)
    (w := w) (w₀ := w₀) (A_comm L.L0 1 z).eq (mul_inv_cancel_left d _).symm rfl
    ((L.W_comm_short w hw 1).1.symm.eq) ((L.W_comm_short w₀ hw₀ z).1.symm.eq)
    hdw₀.symm.eq (L.W_comm w w₀ hw hw₀).eq
  rw [commutatorElement_def, key, mul_inv_cancel]

theorem B6_trace_eq_one
    (z : K) : ⁅L.L2.A 1, L.L3.A (D.σ (D.σ z) + D.σ z)⁆ = 1 := by
  have hv := L.w_mem 1 z
  have hw₀ := L.w_mem 1 1
  simp only [map_one, mul_one, one_mul, CharTwo.add_self_eq_zero, A_zero, inv_one] at hv hw₀
  set d := L.L3.A (D.σ (D.σ z) + D.σ z)
  set v := d⁻¹ * ⁅L.L0.A 1, L.L2.A z⁆
  have hv' : (D.η v⁻¹ : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 4 := by
    rw [map_inv, Subgroup.coe_inv]
    exact inv_mem hv
  have hw₀' : (D.η ⁅L.L2.A 1, L.L0.A 1⁆ : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 4 := by
    rw [← commutatorElement_inv, map_inv, Subgroup.coe_inv]
    exact inv_mem hw₀
  have hdv : Commute d v := (L.W_comm_short v hv (D.σ (D.σ z) + D.σ z)).2.2.symm
  have h1 : ⁅L.L2.A z, L.L0.A 1⁆ = d⁻¹ * v⁻¹ := by
    have e : ⁅L.L0.A 1, L.L2.A z⁆ = d * v := (mul_inv_cancel_left d _).symm
    rw [← commutatorElement_inv, e, mul_inv_rev, (hdv.inv_inv).eq]
  have key := conj_eq_of_commutators (a := L.L2.A 1) (b := L.L2.A z) (c := L.L0.A 1) (d := d⁻¹)
    (w := v⁻¹) (w₀ := ⁅L.L2.A 1, L.L0.A 1⁆) (A_comm L.L2 1 z).eq h1 rfl
    ((L.W_comm_short v⁻¹ hv' 1).2.1.symm.eq) ((L.W_comm_short _ hw₀' z).2.1.symm.eq)
    ((L.W_comm_short _ hw₀' (D.σ (D.σ z) + D.σ z)).2.2.symm.inv_left.eq)
    (L.W_comm v⁻¹ _ hv' hw₀').eq
  have key' : L.L2.A 1 * d * (L.L2.A 1)⁻¹ = d := by
    have := congrArg (·⁻¹) key
    simpa [mul_assoc] using this
  rw [commutatorElement_def, key', mul_inv_cancel]

theorem Y5_mul_self
    : ⁅L.L0.A 1, L.L3.A 1⁆ * ⁅L.L0.A 1, L.L3.A 1⁆ = 1 := by
  rw [← L.b5_add_right, CharTwo.add_self_eq_zero, A_zero, commutatorElement_one_right]

theorem Y6_mul_self
    : ⁅L.L2.A 1, L.L3.A 1⁆ * ⁅L.L2.A 1, L.L3.A 1⁆ = 1 := by
  rw [← L.b6_add_right, CharTwo.add_self_eq_zero, A_zero, commutatorElement_one_right]

theorem B5_cases (z : K) :
    ⁅L.L0.A 1, L.L3.A z⁆ = 1 ∨ ⁅L.L0.A 1, L.L3.A z⁆ = ⁅L.L0.A 1, L.L3.A 1⁆ := by
  rcases D.trace_cases z with h | h
  · left
    rw [eq_of_trace_eq_zero D.σ h]
    exact L.B5_trace_eq_one z
  · right
    have hB : ⁅L.L0.A 1, L.L3.A (z + 1)⁆ = 1 := by
      rw [eq_of_trace_eq_zero D.σ h]
      exact L.B5_trace_eq_one (z + 1)
    rw [L.b5_add_right] at hB
    rw [eq_inv_of_mul_eq_one_left hB, inv_eq_of_mul_eq_one_right L.Y5_mul_self]

theorem B6_cases (z : K) :
    ⁅L.L2.A 1, L.L3.A z⁆ = 1 ∨ ⁅L.L2.A 1, L.L3.A z⁆ = ⁅L.L2.A 1, L.L3.A 1⁆ := by
  rcases D.trace_cases z with h | h
  · left
    rw [eq_of_trace_eq_zero D.σ h, add_comm]
    exact L.B6_trace_eq_one z
  · right
    have hB : ⁅L.L2.A 1, L.L3.A (z + 1)⁆ = 1 := by
      rw [eq_of_trace_eq_zero D.σ h, add_comm]
      exact L.B6_trace_eq_one (z + 1)
    rw [L.b6_add_right] at hB
    rw [eq_inv_of_mul_eq_one_left hB, inv_eq_of_mul_eq_one_right L.Y6_mul_self]

theorem b5_cases (s t : K) :
    ⁅L.L0.A s, L.L3.A t⁆ = 1 ∨ ⁅L.L0.A s, L.L3.A t⁆ = ⁅L.L0.A 1, L.L3.A 1⁆ := by
  rw [L.b5_eq]
  exact L.B5_cases (s * t)

theorem b6_cases (s t : K) :
    ⁅L.L2.A s, L.L3.A t⁆ = 1 ∨ ⁅L.L2.A s, L.L3.A t⁆ = ⁅L.L2.A 1, L.L3.A 1⁆ := by
  rw [L.b6_eq]
  exact L.B6_cases (s * t)

theorem V3_comm
    (y : E)
    (hy : (D.η y : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 3) :
    Commute y (L.L3.A 1) ∧ Commute y ⁅L.L0.A 1, L.L3.A 1⁆ := by
  constructor
  · refine D.lift_commute_of_heightSeries 3 _ (fun j hj z hz => ?_) y hy
    rcases height_trialityRoot_ge_three j hj with rfl | rfl | rfl
    · exact D.lift_commute_short 3 (Or.inr (Or.inr rfl)) z _ hz (map_A_mem L.L3 1)
    · exact L.comm3 4 (by decide) z hz 1
    · exact L.comm3 5 (by decide) z hz 1
  · refine D.lift_commute_of_heightSeries 3 _ (fun j hj z hz => ?_) y hy
    rcases height_trialityRoot_ge_three j hj with rfl | rfl | rfl
    · obtain ⟨c, hc⟩ := exists_A_eq L.L3 hz
      exact D.commute_of_map_eq hc (L.comm3 4 (by decide) _ (L.b5_mem 1 1) c).symm
    · exact D.long_lift_comm (by decide) z _ hz (L.b5_mem 1 1)
    · exact (L.lift_comm_five_six _ z (L.b5_mem 1 1) hz).symm

section Y2

variable
    {Y2 : E} (hY2 : D.η Y2 = longX D.σ 1 (Or.inl rfl))
include hY2

theorem Y2_mem
    : (D.η Y2 : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 1 := by
  rw [hY2]
  exact mem_trialityGroup_longX D.σ 1 _

theorem Y2_comm2
    (c : K) : Commute Y2 (L.L2.A c) :=
  L.comm2 1 (Or.inl rfl) Y2 (Y2_mem hY2) c

theorem Y2_comm3
    (c : K) : Commute Y2 (L.L3.A c) :=
  L.comm3 1 (Or.inl rfl) Y2 (Y2_mem hY2) c

theorem Y2_comm_Y6 : Commute Y2 ⁅L.L2.A 1, L.L3.A 1⁆ :=
  commute_commutatorElement (L.Y2_comm2 hY2 1) (L.Y2_comm3 hY2 1)

include L in
theorem Y2_mul_self :
    Y2 * Y2 = 1 := by
  set w := TwistTag.D4.orbitReflection ⟨1, by decide⟩ * TwistTag.D4.orbitReflection ⟨0, by decide⟩
  have hw : w ∈ relWeylTwist TwistTag.D4 :=
    mul_mem (TwistTag.D4.orbitReflection_mem _) (TwistTag.D4.orbitReflection_mem _)
  have hwinv : w⁻¹ ∈ relWeylTwist TwistTag.D4 := inv_mem hw
  have hmap := map_conj_orbitGroup D.σ hwinv (isRoot_trialityRoot' 5)
  have hα : w⁻¹ • trialityRoot 5 = trialityRoot 1 := by
    rw [inv_smul_eq_iff, mul_smul, orbitReflection_smul_trialityRoot]
  rw [hα] at hmap
  have hP6 : ∀ y : E, (D.η y : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 5 → y * y = 1 := by
    intro y hy
    rcases D.long_cases (Or.inr (Or.inr rfl)) hy with h | h
    · rw [← pow_two]
      exact D.sq y h
    · have hc : D.η (⁅L.L2.A 1, L.L3.A 1⁆⁻¹ * y) = 1 :=
        D.map_inv_mul_eq_one (L.map_Y6.trans h.symm)
      have hcc := D.sq _ hc
      have hyY := D.commute_of_map_eq (L.map_Y6.trans h.symm)
        (Commute.refl ⁅L.L2.A 1, L.L3.A 1⁆)
      calc y * y = (⁅L.L2.A 1, L.L3.A 1⁆ * y * ⁅L.L2.A 1, L.L3.A 1⁆⁻¹) * y := by
            rw [← hyY.eq, mul_inv_cancel_right]
        _ = ⁅L.L2.A 1, L.L3.A 1⁆ * ⁅L.L2.A 1, L.L3.A 1⁆ *
            (⁅L.L2.A 1, L.L3.A 1⁆⁻¹ * y) ^ 2 := by rw [pow_two]; group
        _ = 1 := by rw [L.Y6_mul_self, hcc, one_mul]
  obtain ⟨m, hm⟩ := D.surj ⟨_, canonicalRep_mem_graphFixedRootGroup (K := K)
    (σ := D.σ.toRingHom) hwinv⟩
  have hmM : (D.η m : ModGL TwistTag.D4.tag K) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w⁻¹ := by rw [hm]
  have hconj : (D.η (m⁻¹ * Y2 * m⁻¹⁻¹) : ModGL TwistTag.D4.tag K) ∈ trialityGroup D.σ 5 := by
    have hz := Y2_mem hY2
    rw [orbitGroup_trialityRoot, orbitGroup_trialityRoot] at hmap
    rw [← hmap] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    rw [coe_map_conj', map_inv, Subgroup.coe_inv, hmM, ← hxz]
    simpa [MulAut.conj_apply, mul_assoc] using hx
  have h := hP6 _ hconj
  calc Y2 * Y2 = m * (m⁻¹ * Y2 * m⁻¹⁻¹ * (m⁻¹ * Y2 * m⁻¹⁻¹)) * m⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem Y2_conj_Y5 :
    Y2 * ⁅L.L0.A 1, L.L3.A 1⁆ * Y2⁻¹ = ⁅L.L2.A 1, L.L3.A 1⁆ * ⁅L.L0.A 1, L.L3.A 1⁆ := by
  have hm : (D.η ((L.L2.A 1)⁻¹ * ⁅Y2, L.L0.A 1⁆) : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 3 := by
    rw [map_mul, map_inv, map_commutatorElement, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_commutatorElement_sub, coe_map_A, coe_map_A, hY2, coe_longX, OneMemClass.coe_one]
    exact commutator_orbitProd_mem_three 1
  set m := (L.L2.A 1)⁻¹ * ⁅Y2, L.L0.A 1⁆ with hmdef
  have hya : Y2 * L.L0.A 1 * Y2⁻¹ = L.L2.A 1 * m * L.L0.A 1 := by
    rw [hmdef, mul_inv_cancel_left, commutatorElement_def]
    group
  have hyd : Y2 * L.L3.A 1 * Y2⁻¹ = L.L3.A 1 := by
    rw [(L.Y2_comm3 hY2 1).eq, mul_inv_cancel_right]
  obtain ⟨hmd, hmY⟩ := L.V3_comm m hm
  rw [conj_commutatorElement', hya, hyd,
    commutatorElement_triple (g₁ := L.L2.A 1) (g₂ := m) (g₃ := L.L0.A 1) (d := L.L3.A 1) rfl rfl
      hmd.eq (L.comm2 4 (by decide) _ (L.b5_mem 1 1) 1).eq
      hmY.symm.eq]
  exact (L.lift_comm_five_six _ _ (L.b5_mem 1 1) (L.b6_mem 1 1)).eq

end Y2

end Lifts

end TwoCover

end CFSG.LieType.Chevalley.TrialityFieldTwo
