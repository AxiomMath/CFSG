module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModBurn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModFacX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModLin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModTor
public import CFSG.RankThree.PartOne.S15K.SL2Model

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec12S8Mod_lin_V {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (g c w : MulAut ↥V) (hg5 : g ^ 5 = 1) (hgfix : ∀ v : ↥V, g v = v → v = 1)
    (hc3 : c ^ 3 = 1) (hc16 : Nat.card {v : ↥V // c v = v} = 16) (hgc : g * c = c * g)
    (hwg : w * g * w⁻¹ = g⁻¹) (hwc : w * c * w⁻¹ = c⁻¹) : False := by
  classical
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.2]; positivity)
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := hV.1.1.is_comm.comm }
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h : x.toMul ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hV.1.2 x.toMul x.toMul.2
    calc (2 : ℕ) • x = Additive.ofMul (x.toMul ^ 2) := by
          simp [ofMul_pow]
      _ = 0 := by rw [h]; rfl
  let ρ : MulAut ↥V →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    { toFun := fun g => (MulEquiv.toAdditive g).toLinearEquiv
        (fun k v => ZMod.map_smul (MulEquiv.toAdditive g) k v)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        apply Additive.ext
        simp
      map_mul' g h := by
        apply LinearEquiv.ext
        intro v
        apply Additive.ext
        simp [mul_assoc] }
  have hρ : ∀ (a : MulAut ↥V) (v : Additive ↥V), (ρ a v).toMul = a v.toMul := fun a v => rfl
  refine sec12S8Mod_lin (W := Additive ↥V) hV.2 (ρ g) (ρ c) (ρ w) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hg5, map_one]
  · intro v hv
    exact Additive.ext (hgfix v.toMul (by rw [← hρ]; exact congrArg Additive.toMul hv))
  · rw [← map_pow, hc3, map_one]
  · rw [← hc16]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v => by
      rw [← hρ]
      exact ⟨fun h => congrArg Additive.toMul h, fun h => Additive.ext h⟩)
  · rw [← map_mul, ← map_mul, hgc]
  · rw [← map_mul, ← map_inv, ← map_mul, hwg, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hwc, map_inv]

theorem asc82S8NoL216_of : Asc82S8NoL216 := by
  intro G _ V X V1 V2 Z hV hsup hinf hA5 hn1 hn2 hXZ hL
  have hmod := LieModel.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0) hL
  obtain ⟨-, F, hF, hFin, hchar, hcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.S15K.exists_mulEquiv_sl2_of_model hmod
  have hF16 : Nat.card F = 16 := by rw [hcard]; norm_num
  obtain ⟨g, h, hgX, hhX, hg5, hgfix, hh3, hh1, hhfix⟩ :=
    sec12S8Mod_facX hV hsup hinf hA5 hn1 hn2
  have hgZ : g ∈ Z := hXZ hgX
  have hhZ : h ∈ Z := hXZ hhX
  have hg1 : g ≠ 1 := by
    intro h1
    haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.2]; positivity)
    have hsub : Subsingleton ↥V :=
      ⟨fun a b => by rw [hgfix a (by simp [h1]), hgfix b (by simp [h1])]⟩
    have := Finite.card_le_one_iff_subsingleton.2 hsub
    rw [hV.2] at this
    omega
  set gz : ↥Z := ⟨g, hgZ⟩ with hgz
  set hz : ↥Z := ⟨h, hhZ⟩ with hhz
  have hg5' : (e gz) ^ 5 = 1 := by
    rw [← map_pow, show gz ^ 5 = 1 from Subtype.ext hg5, map_one]
  have hh3' : (e hz) ^ 3 = 1 := by
    rw [← map_pow, show hz ^ 3 = 1 from Subtype.ext hh3, map_one]
  have hg1' : e gz ≠ 1 := fun h' =>
    hg1 (show g = 1 from congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)))
  have hh1' : e hz ≠ 1 := fun h' =>
    hh1 (show h = 1 from congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)))
  obtain ⟨c', w', r', hcg, hc3, hc1, hwg, hwc, hrh⟩ :=
    sec12S8Mod_torus hF16 (e gz) (e hz) hg5' hg1' hh3' hh1'
  set c : ↥Z := e.symm c' with hc
  set w : ↥Z := e.symm w' with hw
  set r : ↥Z := e.symm r' with hr
  have hcg' : (c : MulAut ↥V) * g = g * c := by
    have := congrArg e.symm hcg
    simpa [c, gz, map_mul] using congrArg Subtype.val this
  have hc3' : (c : MulAut ↥V) ^ 3 = 1 := by
    have := congrArg e.symm hc3
    simpa [c, map_pow] using congrArg Subtype.val this
  have hwg' : (w : MulAut ↥V) * g * (w : MulAut ↥V)⁻¹ = g⁻¹ := by
    have := congrArg e.symm hwg
    simpa [w, gz, map_mul, map_inv] using congrArg Subtype.val this
  have hwc' : (w : MulAut ↥V) * c * (w : MulAut ↥V)⁻¹ = (c : MulAut ↥V)⁻¹ := by
    have := congrArg e.symm hwc
    simpa [w, c, map_mul, map_inv] using congrArg Subtype.val this
  have hrh' : (r : MulAut ↥V) * h * (r : MulAut ↥V)⁻¹ = c := by
    have := congrArg e.symm hrh
    simpa [r, c, hz, map_mul, map_inv] using congrArg Subtype.val this
  have hc16 : Nat.card {v : ↥V // (c : MulAut ↥V) v = v} = 16 := by
    rw [← hhfix, ← hrh']
    exact sec12S8Mod_burn_conj (Q := MulAut ↥V) (Ω := ↥V) h r
  exact sec12S8Mod_lin_V hV g c w hg5 hgfix hc3' hc16 hcg'.symm hwg' hwc'

end CFSG.OddStandard.SmallF3.Omega
