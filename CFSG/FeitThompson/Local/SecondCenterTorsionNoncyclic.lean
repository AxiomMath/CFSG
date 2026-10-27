module

public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.AbelianPlaneCentralizerNoncentralOrbit
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.CentralCommutatorPowers
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} {R : Type*} [Group R]

private theorem finrank_eq_two_of_natCard_eq_sq [Fact p.Prime] (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (h : Nat.card V = p ^ 2) :
    Module.finrank (ZMod p) V = 2 := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have h1 : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  rw [h] at h1
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm

theorem smul_displacement_fixed {A : Type*} [CommGroup A] [Module (ZMod p) (Additive A)]
    [Fact p.Prime] [Finite A] {Q : Type*} [Group Q] (hQ : IsPGroup p Q) (σ : Q →* MulAut A)
    (hcard : Nat.card A = p ^ 2) (q : Q) (a : A) (s : Q) : σ s (σ q a * a⁻¹) = σ q a * a⁻¹ := by
  have hfin' : Finite (Additive A) := ‹Finite A›
  have hV : Module.finrank (ZMod p) (Additive A) = 2 :=
    finrank_eq_two_of_natCard_eq_sq _ (by rw [← hcard]; exact Nat.card_congr Additive.toMul)
  set ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) (Additive A) := mulAutToGL.comp σ with hρ
  have key : ∀ (t : Q) (x : A),
      ((ρ t : LinearMap.GeneralLinearGroup (ZMod p) (Additive A)) :
        Module.End (ZMod p) (Additive A)) (Additive.ofMul x) = Additive.ofMul (σ t x) := by
    intro t x; rw [hρ]; simp
  rcases card_range_eq_one_or_eq_prime hV hQ ρ with h | h
  ·
    have hbot : ρ.range = ⊥ := Subgroup.card_eq_one.mp h
    have hq1 : ρ q = 1 := by
      have hmem : ρ q ∈ ρ.range := ⟨q, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem; exact hmem
    have hqa : σ q a = a := by
      have h2 := key q a
      rw [hq1] at h2
      simpa using Additive.ofMul.injective h2.symm
    rw [hqa, mul_inv_cancel, map_one]
  ·
    obtain ⟨N, hN0, hN2, hrange⟩ := exists_sq_eq_zero_range_coe_eq hV ρ h
    obtain ⟨c, hc⟩ : (ρ q : Module.End (ZMod p) (Additive A))
        ∈ Set.range fun c : ZMod p => 1 + c • N := hrange ▸ ⟨q, rfl⟩
    have hdisp : Additive.ofMul (σ q a * a⁻¹) = c • N (Additive.ofMul a) := by
      rw [← div_eq_mul_inv, ofMul_div, ← key q a, ← hc]; simp
    have hmem : Additive.ofMul (σ q a * a⁻¹) ∈ LinearMap.ker N := by
      rw [ker_eq_range_of_mul_self_eq_zero hV hN0 hN2, hdisp]
      exact Submodule.smul_mem _ _ ⟨_, rfl⟩
    have h3 := apply_eq_self_of_mem_ker ρ hrange s hmem
    rw [key s] at h3
    exact Additive.ofMul.injective h3

theorem commutatorElement_mem_center_of_normal_plane (hp : p.Prime) (hR : IsPGroup p R)
    {B : Subgroup R} [B.Normal] (hBcomm : IsMulCommutative ↥B) (hBexp : ∀ x ∈ B, x ^ p = 1)
    (hBcard : Nat.card ↥B = p ^ 2) (r : R) {b : R} (hb : b ∈ B) :
    ⁅r, b⁆ ∈ Subgroup.center R := by
  have := Fact.mk hp
  have hfinB : Finite ↥B :=
    Nat.finite_of_card_ne_zero (by rw [hBcard]; exact pow_ne_zero _ hp.ne_zero)
  let _ : CommGroup ↥B := hBcomm.instCommGroup
  have hexp' : ∀ x : ↥B, x ^ p = 1 := fun x => Subtype.ext (by simpa using hBexp x.1 x.2)
  let _inst : Module (ZMod p) (Additive ↥B) := AddCommGroup.zmodModule (n := p) fun x => by
    calc p • x = Additive.ofMul ((Additive.toMul x) ^ p) := by simp
      _ = 0 := by rw [hexp']; rfl
  have hkey := smul_displacement_fixed (p := p) hR (MulAut.conjNormal (H := B)) hBcard r ⟨b, hb⟩
  rw [Subgroup.mem_center_iff]
  intro s
  have h2 := congrArg (Subtype.val (p := fun x : R => x ∈ B)) (hkey s)
  simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [commutatorElement_def]
  have h3 : s * (r * b * r⁻¹ * b⁻¹) * s⁻¹ = r * b * r⁻¹ * b⁻¹ := by
    simpa [mul_assoc] using h2
  calc s * (r * b * r⁻¹ * b⁻¹) = s * (r * b * r⁻¹ * b⁻¹) * s⁻¹ * s := by group
    _ = r * b * r⁻¹ * b⁻¹ * s := by rw [h3]

theorem commutatorElement_mem_center_of_mem_upperCentralSeries_two
    {x : R} (hx : x ∈ Subgroup.upperCentralSeries R 2) (y : R) : ⁅x, y⁆ ∈ Subgroup.center R := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff] at hx
  simpa [Subgroup.upperCentralSeries_one] using hx y

theorem mem_upperCentralSeries_two_of_forall {x : R}
    (hx : ∀ y : R, ⁅x, y⁆ ∈ Subgroup.center R) : x ∈ Subgroup.upperCentralSeries R 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  simpa [Subgroup.upperCentralSeries_one] using hx

theorem center_le_upperCentralSeries_two :
    Subgroup.center R ≤ Subgroup.upperCentralSeries R 2 := by
  rw [← Subgroup.upperCentralSeries_one]
  exact Subgroup.upperCentralSeries_mono (G := R) (by norm_num)

theorem commutator_upperCentralSeries_two_le_center :
    _root_.commutator ↥(Subgroup.upperCentralSeries R 2)
      ≤ Subgroup.center ↥(Subgroup.upperCentralSeries R 2) := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro g
  refine Subtype.ext ?_
  have hc : ⁅(a : R), (b : R)⁆ ∈ Subgroup.center R :=
    commutatorElement_mem_center_of_mem_upperCentralSeries_two a.2 (b : R)
  have h := (Subgroup.mem_center_iff.1 hc) (g : R)
  push_cast [commutatorElement_def]
  simpa [commutatorElement_def] using h

def secondCenterTorsion (p : ℕ) (R : Type*) [Group R] : Subgroup R :=
  (omega1 p ↥(Subgroup.upperCentralSeries R 2)).map (Subgroup.upperCentralSeries R 2).subtype

instance secondCenterTorsion_characteristic : (secondCenterTorsion p R).Characteristic :=
  Subgroup.characteristic_of_characteristic_of_characteristic

theorem secondCenterTorsion_le : secondCenterTorsion p R ≤ Subgroup.upperCentralSeries R 2 :=
  Subgroup.map_subtype_le _

theorem mem_secondCenterTorsion_iff {w : R} :
    w ∈ secondCenterTorsion p R ↔ ∃ h : w ∈ Subgroup.upperCentralSeries R 2,
      (⟨w, h⟩ : ↥(Subgroup.upperCentralSeries R 2)) ∈ omega1 p _ := by
  simp only [secondCenterTorsion, Subgroup.mem_map, Subgroup.coe_subtype]
  exact ⟨fun ⟨x, hx, hxw⟩ => hxw ▸ ⟨x.2, hx⟩, fun ⟨h, hw⟩ => ⟨⟨w, h⟩, hw, rfl⟩⟩

theorem mem_secondCenterTorsion_of_mem_of_pow_eq_one {w : R}
    (hw : w ∈ Subgroup.upperCentralSeries R 2) (hwp : w ^ p = 1) :
    w ∈ secondCenterTorsion p R :=
  mem_secondCenterTorsion_iff.2 ⟨hw, mem_omega1_of_pow_eq_one (Subtype.ext (by simpa using hwp))⟩

theorem pow_eq_one_of_mem_secondCenterTorsion (hodd : Odd p) {w : R}
    (hw : w ∈ secondCenterTorsion p R) : w ^ p = 1 := by
  obtain ⟨h, hw⟩ := mem_secondCenterTorsion_iff.1 hw
  have h2 := pow_eq_one_of_mem_omega1 hodd commutator_upperCentralSeries_two_le_center hw
  simpa using congrArg (Subtype.val (p := fun x : R => x ∈ Subgroup.upperCentralSeries R 2)) h2

theorem coe_secondCenterTorsion (hodd : Odd p) :
    (secondCenterTorsion p R : Set R)
      = {w : R | w ∈ Subgroup.upperCentralSeries R 2 ∧ w ^ p = 1} :=
  Set.Subset.antisymm
    (fun _ hw => ⟨secondCenterTorsion_le hw, pow_eq_one_of_mem_secondCenterTorsion hodd hw⟩)
    fun _ hw => mem_secondCenterTorsion_of_mem_of_pow_eq_one hw.1 hw.2

theorem mem_secondCenterTorsion_iff_pow_eq_one (hodd : Odd p) {w : R} :
    w ∈ secondCenterTorsion p R ↔ w ∈ Subgroup.upperCentralSeries R 2 ∧ w ^ p = 1 :=
  Set.ext_iff.mp (coe_secondCenterTorsion hodd) w

theorem exponent_secondCenterTorsion_dvd (hodd : Odd p) :
    Monoid.exponent ↥(secondCenterTorsion p R) ∣ p :=
  Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simpa using pow_eq_one_of_mem_secondCenterTorsion hodd g.2)

theorem centerTorsionBy_le_secondCenterTorsion :
    centerTorsionBy R p ≤ secondCenterTorsion p R := fun _ hz =>
  mem_secondCenterTorsion_of_mem_of_pow_eq_one
    (center_le_upperCentralSeries_two (mem_center_of_mem_centerTorsionBy hz))
    (pow_eq_one_of_mem_centerTorsionBy hz)

theorem commutator_secondCenterTorsion_top_le_centerTorsionBy (hodd : Odd p) :
    ⁅secondCenterTorsion p R, (⊤ : Subgroup R)⁆ ≤ centerTorsionBy R p := by
  rw [Subgroup.commutator_le]
  intro w hw r _
  have hcen : ⁅w, r⁆ ∈ Subgroup.center R :=
    commutatorElement_mem_center_of_mem_upperCentralSeries_two (secondCenterTorsion_le hw) r
  refine mem_centerTorsionBy_of_mem_center hcen ?_
  rw [← commutatorElement_pow_left_of_mem_center hcen p,
    pow_eq_one_of_mem_secondCenterTorsion hodd hw]
  simp

theorem not_isCyclic_of_natCard_eq_sq_of_exponent (hp : p.Prime) {E : Subgroup R}
    (hE : Nat.card ↥E = p ^ 2) (hexp : ∀ x ∈ E, x ^ p = 1) : ¬ IsCyclic ↥E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
  rw [hE] at hg
  have h1 : g ^ p = 1 := Subtype.ext (by simpa using hexp g.1 g.2)
  have hdvd : p ^ 2 ∣ p := hg ▸ orderOf_dvd_of_pow_eq_one h1
  have := Nat.le_of_dvd hp.pos hdvd
  nlinarith [hp.two_le]

theorem exists_le_secondCenterTorsion_natCard_eq_sq [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) :
    ∃ B : Subgroup R, B ≤ secondCenterTorsion p R ∧ Nat.card ↥B = p ^ 2 ∧
      ∀ x ∈ B, x ^ p = 1 := by
  obtain ⟨B, -, hBnorm, ⟨e⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hR
    (⊤ : Subgroup R)
    (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup R).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩))
  have hcard : Nat.card ↥B = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]
  have hexp : ∀ x ∈ B, x ^ p = 1 := fun x hx => by
    have h : (⟨x, hx⟩ : ↥B) ^ p = 1 :=
      e.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one])
    simpa using congrArg (Subtype.val (p := fun y : R => y ∈ B)) h
  have hcomm : IsMulCommutative ↥B :=
    IsMulCommutative.of_comm fun a b => e.injective (by simpa using mul_comm (e a) (e b))
  refine ⟨B, fun b hb => ?_, hcard, hexp⟩
  refine mem_secondCenterTorsion_of_mem_of_pow_eq_one ?_ (hexp b hb)
  refine mem_upperCentralSeries_two_of_forall fun y => ?_
  have h := commutatorElement_mem_center_of_normal_plane hp hR hcomm hexp hcard y hb
  rw [show ⁅b, y⁆ = ⁅y, b⁆⁻¹ by rw [← commutatorElement_inv]]
  exact inv_mem h

theorem not_isCyclic_secondCenterTorsion [Finite R] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) : ¬ IsCyclic ↥(secondCenterTorsion p R) := by
  intro hcyc
  obtain ⟨B, hBW, hcard, hexp⟩ := exists_le_secondCenterTorsion_natCard_eq_sq hp hodd hR hnc
  exact not_isCyclic_of_natCard_eq_sq_of_exponent hp hcard hexp (Subgroup.isCyclic_of_le hBW)

theorem secondCenterTorsion_spec [Finite R] (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R)
    (hnc : ¬ IsCyclic R) :
    (Subgroup.upperCentralSeries R 2).Characteristic ∧
      (secondCenterTorsion p R).Characteristic ∧
      ¬ IsCyclic ↥(secondCenterTorsion p R) ∧
      (∀ w ∈ secondCenterTorsion p R, w ^ p = 1) ∧
      ⁅secondCenterTorsion p R, (⊤ : Subgroup R)⁆ ≤ centerTorsionBy R p ∧
      centerTorsionBy R p ≤ secondCenterTorsion p R :=
  ⟨inferInstance, inferInstance, not_isCyclic_secondCenterTorsion hp hodd hR hnc,
    fun _ hw => pow_eq_one_of_mem_secondCenterTorsion hodd hw,
    commutator_secondCenterTorsion_top_le_centerTorsionBy hodd,
    centerTorsionBy_le_secondCenterTorsion⟩

end CFSG.FeitThompson
