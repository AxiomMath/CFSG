module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverLargeSplit

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutatorElement_mul_comm_identity (g₀ y y' : G) :
    ⁅g₀, y * y'⁆⁻¹ * (⁅g₀, y⁆ * ⁅g₀, y'⁆) =
      y * y' * ⁅(g₀ * y' * g₀⁻¹)⁻¹, y⁻¹⁆ * y⁻¹ * y'⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_central_mul_left {c : G} (hc : c ∈ Subgroup.center G) (a b : G) :
    ⁅c * a, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def,
    show c * a * b * (c * a)⁻¹ * b⁻¹ = c * (a * b * a⁻¹) * c⁻¹ * b⁻¹ by group,
    conj_eq_of_mem_center hc]

variable {g₀ : G} {M V : Subgroup G} (hg₀ : ∀ y ∈ M, g₀ * y * g₀⁻¹ ∈ M)
  (hMV : ∀ y ∈ M, ∀ y' ∈ M, ⁅y, y'⁆ ∈ V) (hVM : ∀ v ∈ V, ∀ y ∈ M, v * y = y * v)

include hg₀ in
theorem commutatorElement_mem_of_normalizes {y : G} (hy : y ∈ M) : ⁅g₀, y⁆ ∈ M := by
  rw [commutatorElement_def]
  exact mul_mem (hg₀ y hy) (inv_mem hy)

include hg₀ hMV hVM in
theorem commutatorElement_mul_mem {y y' : G} (hy : y ∈ M) (hy' : y' ∈ M) :
    ⁅g₀, y * y'⁆⁻¹ * (⁅g₀, y⁆ * ⁅g₀, y'⁆) ∈ V := by
  have hw := hMV _ (inv_mem (hg₀ y' hy')) _ (inv_mem hy)
  have hc := hVM _ hw _ (mul_mem hy hy')
  rw [commutatorElement_mul_comm_identity]
  have e : y * y' * ⁅(g₀ * y' * g₀⁻¹)⁻¹, y⁻¹⁆ * y⁻¹ * y'⁻¹ =
      ⁅(g₀ * y' * g₀⁻¹)⁻¹, y⁻¹⁆ * ⁅y, y'⁆ := by
    rw [← hc, commutatorElement_def y y']
    group
  rw [e]
  exact mul_mem hw (hMV _ hy _ hy')

include hg₀ hMV hVM in
theorem commutatorElement_inv_mem {y : G} (hy : y ∈ M) : ⁅g₀, y⁻¹⁆⁻¹ * ⁅g₀, y⁆⁻¹ ∈ V := by
  have h1 := commutatorElement_mul_mem hg₀ hMV hVM hy (inv_mem hy)
  rw [mul_inv_cancel, commutatorElement_one_right, inv_one, one_mul] at h1
  have h2 := inv_mem h1
  rwa [_root_.mul_inv_rev] at h2

@[expose] def radLift (g₀ : G) (M V : Subgroup G) (hg₀ : ∀ y ∈ M, g₀ * y * g₀⁻¹ ∈ M)
    (hMV : ∀ y ∈ M, ∀ y' ∈ M, ⁅y, y'⁆ ∈ V) (hVM : ∀ v ∈ V, ∀ y ∈ M, v * y = y * v) :
    Subgroup G where
  carrier := {z | ∃ y ∈ M, ⁅g₀, y⁆⁻¹ * z ∈ V}
  one_mem' := ⟨1, one_mem _, by
    rw [commutatorElement_one_right, inv_one, one_mul]
    exact one_mem _⟩
  mul_mem' := by
    rintro z z' ⟨y, hy, hz⟩ ⟨y', hy', hz'⟩
    refine ⟨y * y', mul_mem hy hy', ?_⟩
    have hcomm := hVM _ hz _ (commutatorElement_mem_of_normalizes hg₀ hy')
    have e : ⁅g₀, y * y'⁆⁻¹ * (z * z') = (⁅g₀, y * y'⁆⁻¹ * (⁅g₀, y⁆ * ⁅g₀, y'⁆)) *
        ((⁅g₀, y⁆⁻¹ * z) * (⁅g₀, y'⁆⁻¹ * z')) := by
      calc ⁅g₀, y * y'⁆⁻¹ * (z * z') = ⁅g₀, y * y'⁆⁻¹ * ⁅g₀, y⁆ * ((⁅g₀, y⁆⁻¹ * z) * ⁅g₀, y'⁆) *
            (⁅g₀, y'⁆⁻¹ * z') := by group
        _ = ⁅g₀, y * y'⁆⁻¹ * ⁅g₀, y⁆ * (⁅g₀, y'⁆ * (⁅g₀, y⁆⁻¹ * z)) * (⁅g₀, y'⁆⁻¹ * z') := by
            rw [hcomm]
        _ = _ := by group
    rw [e]
    exact mul_mem (commutatorElement_mul_mem hg₀ hMV hVM hy hy') (mul_mem hz hz')
  inv_mem' := by
    rintro z ⟨y, hy, hz⟩
    refine ⟨y⁻¹, inv_mem hy, ?_⟩
    have hcomm := hVM _ (inv_mem hz) _
      (inv_mem (commutatorElement_mem_of_normalizes hg₀ (inv_mem hy)))
    have e : ⁅g₀, y⁻¹⁆⁻¹ * z⁻¹ = (⁅g₀, y⁆⁻¹ * z)⁻¹ * (⁅g₀, y⁻¹⁆⁻¹ * ⁅g₀, y⁆⁻¹) := by
      calc ⁅g₀, y⁻¹⁆⁻¹ * z⁻¹ = ⁅g₀, y⁻¹⁆⁻¹ * (⁅g₀, y⁆⁻¹ * z)⁻¹ * ⁅g₀, y⁆⁻¹ := by group
        _ = (⁅g₀, y⁆⁻¹ * z)⁻¹ * ⁅g₀, y⁻¹⁆⁻¹ * ⁅g₀, y⁆⁻¹ := by rw [← hcomm]
        _ = _ := by group
    rw [e]
    exact mul_mem (inv_mem hz) (commutatorElement_inv_mem hg₀ hMV hVM hy)

theorem mem_radLift {hMV : ∀ y ∈ M, ∀ y' ∈ M, ⁅y, y'⁆ ∈ V}
    {hVM : ∀ v ∈ V, ∀ y ∈ M, v * y = y * v} {z : G} :
    z ∈ radLift g₀ M V hg₀ hMV hVM ↔ ∃ y ∈ M, ⁅g₀, y⁆⁻¹ * z ∈ V :=
  Iff.rfl

end Group

variable {f : ℕ} {K : Type} [Field K] [CharP K 2] {h : UnitaryFieldData 2 f K} {r : ℕ}
  {E : Type*} [Group E] {θ : E →* hypPSU h r 1} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
theorem lift_scalar_commute {σ : Kˣ} {g₀ : E}
    (hg₀ : θ g₀ = hypProj h r 1 (lHom h r (hTorusGL fun _ => σ))) {B : GL (Fin r) K} {u : E}
    (hu : θ u = hypProj h r 1 (lHom h r B)) : θ u * θ g₀ = θ g₀ * θ u := by
  rw [hu, hg₀, ← map_mul (hypProj h r 1), ← map_mul (hypProj h r 1), lHom_scalar_commute σ B]

omit [CharP K 2] in
include hC in
theorem conj_scalar_lift_mem_center {σ : Kˣ} {g₀ : E}
    (hg₀ : θ g₀ = hypProj h r 1 (lHom h r (hTorusGL fun _ => σ))) {B : GL (Fin r) K} {u : E}
    (hu : θ u = hypProj h r 1 (lHom h r B)) : u * g₀ * u⁻¹ * g₀⁻¹ ∈ Subgroup.center E :=
  hC (by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      lift_scalar_commute hg₀ hu]
    group)

include hθ hC in
theorem exists_radical_complement_even [Finite E] (hf : 2 ≤ f) (hr : 2 ≤ r)
    (h2 : IsPGroup 2 θ.ker) :
    ∃ M₀ : Subgroup E, M₀ ≤ preN θ ∧ (∀ y ∈ M₀, θ y = 1 → y = 1) ∧
      (∀ {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hx : IsRad h x C),
        ∃ y ∈ M₀, θ y = hypProj h r 1 (nElt hx)) ∧
      ∀ (A : SpecialLinearGroup (Fin r) K) (u : E),
        θ u = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) →
          ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀ := by
  have := h.finite
  obtain ⟨Vt, hVt⟩ := exists_levi_complement hθ hC hf h2
  obtain ⟨σ, hσ, hσ1⟩ := UnitaryEvenCover.exists_fixed_unit (h := h) hf
  obtain ⟨g₀, hg₀⟩ := hθ (hypProj h r 1 (lHom h r (hTorusGL fun _ => σ)))
  have hg₀M : ∀ y ∈ preN θ, g₀ * y * g₀⁻¹ ∈ preN θ := fun y hy =>
    conj_mem_preN_of_lift_even hg₀ hy
  have hMV : ∀ y ∈ preN θ, ∀ y' ∈ preN θ, ⁅y, y'⁆ ∈ Vt := fun y hy y' hy' =>
    commutatorElement_mem_levi_complement hθ hC hVt hf hr hy hy'
  have hVM : ∀ v ∈ Vt, ∀ y ∈ preN θ, v * y = y * v := fun v hv y hy =>
    mul_comm_of_mem_preV_of_mem_preN_even hθ hC hf hr (hVt.le hv) hy
  have hVle : Vt ≤ preN θ := hVt.le.trans preV_le_preN
  set M₀ := radLift g₀ (preN θ) Vt hg₀M hMV hVM with hM₀
  have hM₀N : M₀ ≤ preN θ := by
    rintro z ⟨y, hy, hz⟩
    rw [show z = ⁅g₀, y⁆ * (⁅g₀, y⁆⁻¹ * z) by group]
    exact mul_mem (commutatorElement_mem_of_normalizes hg₀M hy) (hVle hz)
  have := Fintype.ofFinite K
  have hm : Odd (Nat.card Kˣ) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' n.ne_zero).mpr even_two) odd_one
  have hg₀m : θ (g₀ ^ Nat.card Kˣ) = 1 := by
    rw [map_pow, hg₀, ← map_pow, ← map_pow]
    have : (hTorusGL fun _ => σ : GL (Fin r) K) ^ Nat.card Kˣ = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, hTorusGL_coe, diagonal_pow, Units.val_one, ← diagonal_one]
      congr 1
      funext i
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]
    rw [this, map_one, map_one]
  refine ⟨M₀, hM₀N, ?_, fun {x C₁} hx => ?_, fun A u hu y => ?_⟩
  ·
    rintro z ⟨y, hy, hz⟩ hz1
    have hc : z ∈ Subgroup.center E := hC hz1
    set v := ⁅g₀, y⁆⁻¹ * z with hv
    have hstep : g₀ * y * g₀⁻¹ = z * v⁻¹ * y := by
      rw [hv, commutatorElement_def]
      group
    have hk : ∀ k : ℕ, ∃ w ∈ Vt, g₀ ^ k * y * (g₀ ^ k)⁻¹ = z ^ k * w * y := by
      intro k
      induction k with
      | zero => exact ⟨1, one_mem _, by simp⟩
      | succ k ih =>
        obtain ⟨w, hw, hwk⟩ := ih
        refine ⟨g₀ * w * g₀⁻¹ * v⁻¹, mul_mem (hVt.conj _ g₀ hg₀ w hw) (inv_mem hz), ?_⟩
        have hzc := Subgroup.mem_center_iff.mp hc (g₀ * w * g₀⁻¹)
        calc g₀ ^ (k + 1) * y * (g₀ ^ (k + 1))⁻¹ = g₀ * (g₀ ^ k * y * (g₀ ^ k)⁻¹) * g₀⁻¹ := by
              group
          _ = g₀ * (z ^ k * w * y) * g₀⁻¹ := by rw [hwk]
          _ = (g₀ * z ^ k * g₀⁻¹) * (g₀ * w * g₀⁻¹) * (g₀ * y * g₀⁻¹) := by group
          _ = z ^ k * ((g₀ * w * g₀⁻¹) * z) * v⁻¹ * y := by
              rw [conj_central (Subgroup.pow_mem _ hc k), hstep]
              group
          _ = z ^ (k + 1) * (g₀ * w * g₀⁻¹ * v⁻¹) * y := by
              rw [hzc, pow_succ]
              group
    obtain ⟨w, hw, hwn⟩ := hk (Nat.card Kˣ)
    rw [conj_eq_of_mem_center (hC hg₀m)] at hwn
    have hzw : z ^ Nat.card Kˣ * w = 1 := mul_eq_right.mp hwn.symm
    have hzn : z ^ Nat.card Kˣ = 1 := by
      have hmem : z ^ Nat.card Kˣ ∈ Vt := by
        rw [eq_inv_of_mul_eq_one_left hzw]
        exact inv_mem hw
      exact hVt.inj _ hmem (by rw [map_pow, hz1, one_pow])
    obtain ⟨a, ha⟩ := h2 ⟨z, hz1⟩
    have ha' : z ^ 2 ^ a = 1 := by
      simpa using congrArg (fun w : θ.ker => (w : E)) ha
    have hcop : Nat.Coprime (2 ^ a) (Nat.card Kˣ) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hzn))
  ·
    have hσ1' : (σ : K) + 1 ≠ 0 := fun h0 => hσ1 (by
      rw [← sub_eq_zero, CharTwo.sub_eq_add]
      exact h0)
    obtain ⟨y, hy⟩ := exists_isN hθ (((σ : K) + 1)⁻¹ • x)
    have hφ : IsN θ x ⁅g₀, y⁆ := by
      rw [commutatorElement_def]
      refine ((hy.conj_scalar hσ hg₀).mul hy.inv).congr ?_
      rw [smul_smul, ← sub_eq_add_neg, ← sub_smul, ← sub_one_mul, CharTwo.sub_eq_add,
        mul_inv_cancel₀ hσ1', one_smul]
    obtain ⟨m, hm⟩ := hθ (hypProj h r 1 (nElt hx))
    have hmN : IsN θ x m := ⟨C₁, hx, hm⟩
    obtain ⟨c, v, hc1, hv, hcv⟩ := hVt.dec _ (hφ.inv_mul_mem hmN)
    refine ⟨⁅g₀, y⁆ * v, ⟨y, hy.mem, by rw [inv_mul_cancel_left]; exact hv⟩, ?_⟩
    have hθv : θ v = θ (⁅g₀, y⁆⁻¹ * m) := by rw [hcv, map_mul, hc1, one_mul]
    rw [map_mul, hθv, ← map_mul, mul_inv_cancel_left, hm]
  ·
    have key : ∀ (B : GL (Fin r) K) (u : E), θ u = hypProj h r 1 (lHom h r B) →
        ∀ z ∈ M₀, u * z * u⁻¹ ∈ M₀ := by
      rintro B u hu z ⟨y, hy, hz⟩
      have hc := conj_scalar_lift_mem_center hC hg₀ hu
      have hug₀ : u * g₀ * u⁻¹ = (u * g₀ * u⁻¹ * g₀⁻¹) * g₀ := by group
      refine ⟨u * y * u⁻¹, conj_mem_preN_of_lift_even hu hy, ?_⟩
      have e : ⁅g₀, u * y * u⁻¹⁆ = u * ⁅g₀, y⁆ * u⁻¹ := by
        rw [conjugate_commutatorElement, hug₀, commutatorElement_central_mul_left hc]
      rw [e, show (u * ⁅g₀, y⁆ * u⁻¹)⁻¹ * (u * z * u⁻¹) = u * (⁅g₀, y⁆⁻¹ * z) * u⁻¹ by group]
      exact hVt.conj B u hu _ hz
    refine ⟨key _ u hu y, fun hy => ?_⟩
    have := key _ u⁻¹ (by rw [map_inv, hu, ← map_inv, ← map_inv]) _ hy
    rwa [show u⁻¹ * (u * y * u⁻¹) * u⁻¹⁻¹ = y by group] at this

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover
