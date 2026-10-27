module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace TwA5Big

section Certs

variable {n q : ℕ} {F : Type} [Field F] [Finite F]

@[expose] noncomputable def twA5EParam {ζu : Fˣ} :
    (Fin 3 → Subgroup.zpowers ζu) →* (Fin 4 → Subgroup.zpowers ζu) where
  toFun c := fun i =>
    if i = 0 then c 0 * c 1 * c 2
    else if i = 1 then c 0 * c 1 * (c 2 ^ 2)⁻¹
    else if i = 2 then c 0 * c 1 * (c 2 ^ 2)⁻¹
    else c 0 * (c 1 ^ 2)⁻¹ * c 2
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' c c' := by
    funext i
    fin_cases i <;>
      · simp
        apply Subtype.ext
        apply Units.ext
        push_cast
        ring

@[simp] theorem twA5EParam_apply_zero {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5EParam c 0 = c 0 * c 1 * c 2 := by simp [twA5EParam]

@[simp] theorem twA5EParam_apply_one {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5EParam c 1 = c 0 * c 1 * (c 2 ^ 2)⁻¹ := by simp [twA5EParam]

@[simp] theorem twA5EParam_apply_two {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5EParam c 2 = c 0 * c 1 * (c 2 ^ 2)⁻¹ := by simp [twA5EParam]

@[simp] theorem twA5EParam_apply_three {ζu : Fˣ} (c : Fin 3 → Subgroup.zpowers ζu) :
    twA5EParam c 3 = c 0 * (c 1 ^ 2)⁻¹ * c 2 := by simp [twA5EParam]

@[expose] noncomputable def twA5E (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) : Subgroup (unitaryPSU h 6) :=
  ((unitaryProj h 6).comp ((twA5TorusHom h hζ).comp twA5EParam)).range

theorem twA5E_le (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1) :
    twA5E h hζ ≤ twA5B h hζ := by
  rintro x ⟨c, rfl⟩
  exact ⟨twA5EParam c, rfl⟩

private theorem pow_three_injective {ζu : Fˣ} (hζo : orderOf ζu = q) (hq : q.Prime)
    (hq3 : ¬ q ∣ 3) : Function.Injective (fun x : Subgroup.zpowers ζu => x ^ 3) := by
  have hcop : (Nat.card (Subgroup.zpowers ζu)).Coprime 3 := by
    rw [Nat.card_zpowers, hζo]
    exact (Nat.Prime.coprime_iff_not_dvd hq).2 hq3
  exact (Nat.Coprime.pow_left_bijective hcop).1

private theorem mul_rotate {ζu : Fˣ} (a b c : Subgroup.zpowers ζu) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_assoc, mul_comm b c]

private theorem mul_cube_lemma {ζu : Fˣ} (a b c : Subgroup.zpowers ζu) :
    a * b * c = (a * b * (c ^ 2)⁻¹) * c ^ 3 := by
  apply Subtype.ext
  show (a : Fˣ) * b * c = ((a : Fˣ) * b * ((c : Fˣ) ^ 2)⁻¹) * (c : Fˣ) ^ 3
  group

private theorem mul_cube_lemma' {ζu : Fˣ} (a b c : Subgroup.zpowers ζu) :
    a * b * c = (a * (b ^ 2)⁻¹ * c) * b ^ 3 := by
  have h := mul_cube_lemma a c b
  calc a * b * c = a * c * b := mul_rotate a b c
    _ = (a * c * (b ^ 2)⁻¹) * b ^ 3 := h
    _ = (a * (b ^ 2)⁻¹ * c) * b ^ 3 := by
        rw [mul_rotate a c ((b ^ 2)⁻¹)]

theorem twA5EParam_injective {ζu : Fˣ} (hζo : orderOf ζu = q) (hq : q.Prime) (hq3 : ¬ q ∣ 3) :
    Function.Injective (twA5EParam (ζu := ζu)) := by
  intro c c' hcc
  have h0 : c 0 * c 1 * c 2 = c' 0 * c' 1 * c' 2 := by
    simpa using congrFun hcc 0
  have h1 : c 0 * c 1 * (c 2 ^ 2)⁻¹ = c' 0 * c' 1 * (c' 2 ^ 2)⁻¹ := by
    simpa using congrFun hcc 1
  have h3 : c 0 * (c 1 ^ 2)⁻¹ * c 2 = c' 0 * (c' 1 ^ 2)⁻¹ * c' 2 := by
    simpa using congrFun hcc 3
  have hc : c 2 = c' 2 := by
    have h2 : (c 0 * c 1 * (c 2 ^ 2)⁻¹) * (c 2 ^ 3) =
        (c' 0 * c' 1 * (c' 2 ^ 2)⁻¹) * (c' 2 ^ 3) := by
      rw [← mul_cube_lemma, ← mul_cube_lemma, h0]
    have h2' : (c 0 * c 1 * (c 2 ^ 2)⁻¹) * (c 2 ^ 3) =
        (c 0 * c 1 * (c 2 ^ 2)⁻¹) * (c' 2 ^ 3) := by rw [h2, h1]
    exact pow_three_injective hζo hq hq3 (mul_left_cancel h2')
  have hb : c 1 = c' 1 := by
    have h2 : (c 0 * (c 1 ^ 2)⁻¹ * c 2) * (c 1 ^ 3) =
        (c' 0 * (c' 1 ^ 2)⁻¹ * c' 2) * (c' 1 ^ 3) := by
      rw [← mul_cube_lemma', ← mul_cube_lemma', h0]
    have h2' : (c 0 * (c 1 ^ 2)⁻¹ * c 2) * (c 1 ^ 3) =
        (c 0 * (c 1 ^ 2)⁻¹ * c 2) * (c' 1 ^ 3) := by rw [h2, h3]
    exact pow_three_injective hζo hq hq3 (mul_left_cancel h2')
  have ha : c 0 = c' 0 := by
    rw [hc, hb] at h0
    exact mul_right_cancel (by rwa [mul_assoc, mul_assoc] at h0)
  funext i
  fin_cases i <;> assumption

theorem card_twA5E (h : UnitaryFieldData 2 n F) {ζu : Fˣ} (hζ : h.norm (ζu : F) = 1)
    (hζo : orderOf ζu = q) (hq : q.Prime) (hq3 : ¬ q ∣ 3) (hq6 : ¬ q ∣ 6) :
    Nat.card (twA5E h hζ) = q ^ 3 := by
  have hdom : Nat.card (Fin 3 → Subgroup.zpowers ζu) = q ^ 3 := by
    rw [Nat.card_pi]
    simp [Nat.card_zpowers, hζo]
  have hinj : Function.Injective ((unitaryProj h 6).comp ((twA5TorusHom h hζ).comp twA5EParam)) := by
    intro c c' hcc
    have h1 : (twA5TorusHom h hζ) (twA5EParam c) = (twA5TorusHom h hζ) (twA5EParam c') :=
      unitaryProj_injective_on_twA5Torus h hζ hζo hq hq6 _ ⟨_, rfl⟩ _ ⟨_, rfl⟩ hcc
    exact twA5EParam_injective hζo hq hq3 (twA5TorusHom_injective h hζ h1)
  rw [twA5E, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hdom]

theorem twA5E_isElemAbelian (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) (hζo : orderOf ζu = q) :
    IsElemAbelian q (twA5E h hζ) := by
  constructor
  · refine ⟨⟨fun A B => ?_⟩⟩
    obtain ⟨a, ha⟩ := A.2
    obtain ⟨b, hb⟩ := B.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm a b]
  · intro A hA
    obtain ⟨a, ha⟩ := hA
    rw [← ha, ← map_pow]
    have h1 : a ^ q = 1 := by
      funext i
      apply Subtype.ext
      apply Units.ext
      have h2 : ((a i : Fˣ)) ^ q = 1 := by
        have h3 : orderOf ((a i : Fˣ)) ∣ Nat.card ↥(Subgroup.zpowers ζu) := by
          have h := orderOf_dvd_natCard (⟨(a i : Fˣ), (a i).2⟩ : Subgroup.zpowers ζu)
          rwa [Subgroup.orderOf_mk] at h
        rw [Nat.card_zpowers, hζo] at h3
        exact orderOf_dvd_iff_pow_eq_one.1 h3
      exact congrArg (fun u : Fˣ => (u : F)) h2
    rw [h1, map_one]

theorem diagFiveLast_mem_twA5E (h : UnitaryFieldData 2 n F) {ζu : Fˣ}
    (hζ : h.norm (ζu : F) = 1) :
    unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ∈ twA5E h hζ := by
  refine ⟨fun i => if i = 0 then ⟨ζu, Subgroup.mem_zpowers ζu⟩ else 1, ?_⟩
  show unitaryProj h 6 (twA5TorusHom h hζ (twA5EParam
      (fun i => if i = 0 then ⟨ζu, Subgroup.mem_zpowers ζu⟩ else 1))) =
    unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [twA5TorusHom_apply, twA5Diag, coe_diagSU, coe_diagFiveLast]
  congr 1
  funext i
  fin_cases i <;> simp [twA5Vec, twA5EParam, diagFiveLastEntries]
  rw [show ((ζu : F) ^ 5) = ((ζu : F) ^ 2) * ((ζu : F) ^ 2) * (ζu : F) by ring]
  rw [mul_inv]
  ring

end Certs

end TwA5Big

end CFSG.LocalAnalysis.GLTheoremA.Y10F
