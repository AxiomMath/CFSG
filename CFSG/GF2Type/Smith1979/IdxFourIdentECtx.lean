module

public import CFSG.GF2Type.Smith1979.IdxFourIdentAdj43
public import CFSG.GF2Type.Smith1979.IdxFourIdentAtilde
public import CFSG.GF2Type.Smith1979.IdxFourIdentFrameData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.Case25.U43Weights
open CFSG.LieType.Multipliers.U43 (X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six

structure ECtx where
  E : Subgroup G12
  hEg : E ≤ gammaU
  hEcard : Nat.card E = 9797760
  π : E →* X₀
  hπs : Function.Surjective π
  hπk : π.ker = Subgroup.center E
  hZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers theta0e

namespace ECtx

variable (C : ECtx)

theorem card_E : Nat.card C.E = 9797760 := C.hEcard

theorem theta0e_pow_three : theta0e ^ 3 = 1 := Ctx.theta0e_pow_three

theorem orderOf_theta0e : orderOf theta0e = 3 := Ctx.orderOf_theta0e

theorem theta0e_mem_E : theta0e ∈ C.E := by
  have : theta0e ∈ (Subgroup.center C.E).map C.E.subtype := by
    rw [C.hZ]; exact Subgroup.mem_zpowers _
  obtain ⟨z, -, hz⟩ := this
  rw [← hz]
  exact z.2

theorem mem_center_iff (e : C.E) :
    e ∈ Subgroup.center C.E ↔ (e : G12) ∈ Subgroup.zpowers theta0e := by
  rw [← C.hZ]
  constructor
  · intro h
    exact ⟨e, h, rfl⟩
  · rintro ⟨z, hz, hze⟩
    have : z = e := Subtype.ext hze
    rwa [this] at hz

theorem theta0e_mem_center : (⟨theta0e, C.theta0e_mem_E⟩ : C.E) ∈ Subgroup.center C.E := by
  rw [C.mem_center_iff]
  exact Subgroup.mem_zpowers _

theorem theta0e_comm (e : C.E) : (e : G12) * theta0e = theta0e * e := by
  have h := Subgroup.mem_center_iff.mp C.theta0e_mem_center e
  exact congrArg Subtype.val h

theorem card_center : Nat.card (Subgroup.center C.E) = 3 := by
  have h1 : Nat.card ((Subgroup.center C.E).map C.E.subtype) = Nat.card (Subgroup.center C.E) :=
    Subgroup.card_map_of_injective C.E.subtype_injective
  rw [C.hZ, Nat.card_zpowers, orderOf_theta0e] at h1
  exact h1.symm

theorem pow_three_of_mem_center {z : C.E} (hz : z ∈ Subgroup.center C.E) : z ^ 3 = 1 := by
  rw [C.mem_center_iff] at hz
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Subtype.ext ?_
  show (z : G12) ^ 3 = 1
  rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, theta0e_pow_three,
    one_zpow]

@[expose] noncomputable def AtildeE : Subgroup C.E := thetaBar.range.comap C.π

theorem mem_AtildeE {e : C.E} : e ∈ C.AtildeE ↔ C.π e ∈ thetaBar.range := Iff.rfl

theorem AtildeE_comm {x y : C.E} (hx : x ∈ C.AtildeE) (hy : y ∈ C.AtildeE) : x * y = y * x :=
  commute_of_mem_range C.hπs C.hπk.le hx hy

theorem AtildeE_pow_three {x : C.E} (hx : x ∈ C.AtildeE) : x ^ 3 = 1 := by
  obtain ⟨y, hy, hy3⟩ := exists_lift_of_mem_range C.hπs C.hπk.le hx
  have hz : y⁻¹ * x ∈ C.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hzc : y⁻¹ * x ∈ Subgroup.center C.E := C.hπk ▸ hz
  have hz3 := C.pow_three_of_mem_center hzc
  have hcomm : Commute y (y⁻¹ * x) := Subgroup.mem_center_iff.mp hzc y
  calc x ^ 3 = (y * (y⁻¹ * x)) ^ 3 := by rw [mul_inv_cancel_left]
    _ = y ^ 3 * (y⁻¹ * x) ^ 3 := hcomm.mul_pow 3
    _ = 1 := by rw [hy3, hz3, one_mul]

theorem card_AtildeE : Nat.card C.AtildeE = 243 := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  haveI : Finite X₀ := Finite.of_surjective C.π C.hπs
  have h := card_comap_of_surjective C.π C.hπs thetaBar.range
  rw [C.hπk, C.card_center, card_range_thetaBar] at h
  exact h.trans (by norm_num)

theorem theta0_mem_AtildeE : (⟨theta0e, C.theta0e_mem_E⟩ : C.E) ∈ C.AtildeE := by
  have h : C.π ⟨theta0e, C.theta0e_mem_E⟩ = 1 := by
    rw [← MonoidHom.mem_ker, C.hπk]
    exact C.theta0e_mem_center
  rw [mem_AtildeE, h]
  exact one_mem _

@[expose] noncomputable def psiE : C.AtildeE →* A4 :=
  (MonoidHom.ofInjective thetaBar_injective).symm.toMonoidHom.comp
    ((C.π.domRestrict C.AtildeE).codRestrict thetaBar.range (fun a => a.2))

theorem thetaBar_psiE (a : C.AtildeE) : thetaBar (C.psiE a) = C.π a := by
  have h := (MonoidHom.ofInjective thetaBar_injective).apply_symm_apply
    ⟨C.π a, a.2⟩
  exact congrArg Subtype.val h

theorem psiE_surjective : Function.Surjective C.psiE := by
  intro x
  obtain ⟨e, he⟩ := C.hπs (thetaBar x)
  refine ⟨⟨e, by rw [mem_AtildeE, he]; exact ⟨x, rfl⟩⟩, ?_⟩
  apply thetaBar_injective
  rw [C.thetaBar_psiE]
  exact he

theorem psiE_eq_one_iff (a : C.AtildeE) : C.psiE a = 1 ↔ (a : C.E) ∈ Subgroup.center C.E := by
  rw [← C.hπk, MonoidHom.mem_ker, ← C.thetaBar_psiE, ← map_one thetaBar]
  exact thetaBar_injective.eq_iff.symm

@[expose] noncomputable def levLift (k : Gen) : C.E := (C.hπs (levBar k)).choose

theorem π_levLift (k : Gen) : C.π (C.levLift k) = levBar k := (C.hπs (levBar k)).choose_spec

theorem levLift_normalizes {k : Gen} {a : C.E} (ha : a ∈ C.AtildeE) :
    C.levLift k * a * (C.levLift k)⁻¹ ∈ C.AtildeE := by
  obtain ⟨x, hx⟩ := ha
  rw [mem_AtildeE, map_mul, map_mul, map_inv, C.π_levLift, ← hx, levBar_conj]
  exact ⟨_, rfl⟩

theorem psiE_levLift_conj {k : Gen} (a : C.AtildeE) :
    C.psiE ⟨C.levLift k * a * (C.levLift k)⁻¹, C.levLift_normalizes a.2⟩ = sg k (C.psiE a) := by
  apply thetaBar_injective
  rw [C.thetaBar_psiE, ← levBar_conj]
  show C.π (C.levLift k * a * (C.levLift k)⁻¹) = _
  rw [map_mul, map_mul, map_inv, C.π_levLift, C.thetaBar_psiE]

theorem levLift_pow_three_mem_center (k : Gen) : C.levLift k ^ 3 ∈ Subgroup.center C.E := by
  rw [← C.hπk, MonoidHom.mem_ker, map_pow, C.π_levLift, Ctx.levBar_pow_three]

noncomputable instance instCommGroupAtilde : CommGroup C.AtildeE :=
  { (inferInstance : Group C.AtildeE) with
    mul_comm := fun a b => Subtype.ext (C.AtildeE_comm a.2 b.2) }

@[expose] noncomputable def rhoA : C.AtildeE →* G12 := C.E.subtype.comp C.AtildeE.subtype

@[expose] noncomputable def thetaA : C.AtildeE := ⟨⟨theta0e, C.theta0e_mem_E⟩, C.theta0_mem_AtildeE⟩

theorem mem_zpowers_thetaA_iff (a : C.AtildeE) :
    a ∈ Subgroup.zpowers C.thetaA ↔ ((a : C.E) : G12) ∈ Subgroup.zpowers theta0e := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : (((C.thetaA ^ n : C.AtildeE) : C.E) : G12) = theta0e ^ n := by
      simp [ECtx.thetaA]
    rw [h1]
    exact hn

theorem E_le_gammaU : C.E ≤ gammaU := C.hEg

theorem rhoA_injective : Function.Injective C.rhoA := fun a b h =>
  Subtype.ext (Subtype.ext h)

theorem rhoA_mem_gammaU (a : C.AtildeE) : C.rhoA a ∈ gammaU := C.E_le_gammaU a.1.2

theorem levLift_comm (k : Gen) :
    ((C.levLift k : C.E) : G12) * theta0e = theta0e * ((C.levLift k : C.E) : G12) :=
  C.theta0e_comm _

theorem levLift_pow_three_mem_zpowers (k : Gen) :
    ((C.levLift k : C.E) : G12) ^ 3 ∈ Subgroup.zpowers theta0e := by
  have h := (C.mem_center_iff _).1 (C.levLift_pow_three_mem_center k)
  simpa using h

theorem frame_of_ectx : ∃ (g : G12) (c : Gen → Fin 6 → ZMod 3) (p : Gen → Equiv.Perm (Fin 6))
    (ψ' : D5 →* A4), g ∈ gammaU ∧ g * theta0e = theta0e * g ∧
    (∀ a : C.AtildeE, g⁻¹ * C.rhoA a * g ∈ D5) ∧
    (∀ d ∈ D5, ∃ a : C.AtildeE, g⁻¹ * C.rhoA a * g = d) ∧
    (∀ k, g⁻¹ * ((C.levLift k : C.E) : G12) * g = diagE (c k) * permE (p k)) ∧
    (∀ k, p k ^ 3 = 1) ∧
    (∀ (a : C.AtildeE) (h : g⁻¹ * C.rhoA a * g ∈ D5), ψ' ⟨g⁻¹ * C.rhoA a * g, h⟩ = C.psiE a) ∧
    Function.Surjective ψ' ∧ (∀ d : D5, ψ' d = 1 ↔ (d : G12) ∈ Subgroup.zpowers theta0e) ∧
    (∀ (k : Gen) (d : D5) (h : permE (p k) * (d : G12) * (permE (p k))⁻¹ ∈ D5),
      ψ' ⟨permE (p k) * (d : G12) * (permE (p k))⁻¹, h⟩ = sg k (ψ' d)) := by
  haveI : Finite C.E := Nat.finite_of_card_ne_zero (by rw [C.card_E]; norm_num)
  refine frame_data (A := C.AtildeE) (fun a => Subtype.ext (C.AtildeE_pow_three a.2))
    C.card_AtildeE (ρ := C.rhoA) C.rhoA_injective C.rhoA_mem_gammaU (θ := C.thetaA) rfl C.psiE
    C.psiE_surjective (fun a => ?_) (fun k => ((C.levLift k : C.E) : G12))
    (fun k => C.E_le_gammaU (C.levLift k).2) C.levLift_comm C.levLift_pow_three_mem_zpowers
    (fun k a => ?_)
  · rw [C.psiE_eq_one_iff, C.mem_center_iff, C.mem_zpowers_thetaA_iff]
  · refine ⟨⟨C.levLift k * a * (C.levLift k)⁻¹, C.levLift_normalizes a.2⟩, rfl, ?_⟩
    exact C.psiE_levLift_conj a

theorem exists_adjacent : ∃ (y : C.E) (a₀ a₀' a₁ : C.AtildeE),
    y * (a₀ : C.E) * y⁻¹ = (a₀' : C.E) ∧
    C.psiE a₀ = Multiplicative.ofAdd ((1, 2, 1, 1) : T4) ∧
    C.psiE a₀' = Multiplicative.ofAdd ((1, 0, 0, 0) : T4) ∧
    ∀ a : C.E, a ∈ C.AtildeE → y * (a₁ : C.E) * y⁻¹ ≠ a := by
  obtain ⟨y, hy⟩ := C.hπs yBar
  obtain ⟨a₀, ha₀⟩ := C.psiE_surjective (Multiplicative.ofAdd ((1, 2, 1, 1) : T4))
  obtain ⟨a₁, ha₁⟩ := C.psiE_surjective (Multiplicative.ofAdd ((0, 1, 0, 0) : T4))
  have h1 : C.π (y * (a₀ : C.E) * y⁻¹) = thetaBar (Multiplicative.ofAdd ((1, 0, 0, 0) : T4)) := by
    rw [map_mul, map_mul, map_inv, hy, ← C.thetaBar_psiE, ha₀, mul_inv_eq_iff_eq_mul]
    exact yBar_mul_thetaBar
  have hmem : y * (a₀ : C.E) * y⁻¹ ∈ C.AtildeE := by
    rw [mem_AtildeE, h1]; exact ⟨_, rfl⟩
  refine ⟨y, a₀, ⟨_, hmem⟩, a₁, rfl, ha₀, ?_, ?_⟩
  · apply thetaBar_injective
    rw [C.thetaBar_psiE]
    exact h1
  · intro a ha hEq
    obtain ⟨x', hx'⟩ : ∃ x', thetaBar x' = C.π a := ha
    apply yBar_mul_thetaBar_ne x'
    rw [hx', ← hEq, map_mul, map_mul, map_inv, hy, ← C.thetaBar_psiE a₁, ha₁]
    group

end ECtx

end CFSG.GF2Type.Smith1979.IdxFour
