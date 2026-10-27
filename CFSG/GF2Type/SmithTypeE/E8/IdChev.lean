module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
open CFSG.SeitzReduction.EPilot (torusGroup_eq_bot_of_forall_units_eq_one)


theorem chv_units_zmod_two (u : (ZMod 2)ˣ) : u = 1 := by
  revert u
  decide

theorem chv_e7Chi56_one : e7Chi56 (1 : ↥(adjointGroup .E7 (ZMod 2))) = 1 := by
  unfold e7Chi56
  rw [map_one]
  simp [e7Y56]

theorem chv_sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ c : ZMod 2, f c = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide]
  exact Finset.sum_pair (by decide)

theorem chv_heckeT {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) ↥(adjointGroup .E7 (ZMod 2)) V)
    (i : Fin (Tag.rank .E7)) (y : V) :
    (chevDatum .E7 (ZMod 2) 2 exists_weyl_neg_E7).heckeT ρ i y =
      ρ (nC .E7 (ZMod 2) i) y + ρ (xC .E7 (ZMod 2) i 1 * nC .E7 (ZMod 2) i) y := by
  rw [heckeT_chevDatum, chv_sum_zmod_two]
  have h0 : xC .E7 (ZMod 2) i 0 = 1 := Subtype.ext (xUnit_zero i)
  rw [h0, one_mul]

theorem chv_add_eq_zero_iff_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {w w' : V} :
    w + w' = 0 ↔ w' = w := by
  have h2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v]
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_smul]
  constructor
  · intro h
    have := eq_neg_of_add_eq_zero_right h
    rw [this, neg_eq_iff_add_eq_zero.mpr (h2 w)]
  · intro h
    rw [h, h2]

theorem chv_borel_le_parabolic (J : Set (Fin (Tag.rank .E7))) :
    borelGroup .E7 (ZMod 2) ≤ parabolicSubgroup .E7 (ZMod 2) J := le_sup_left

theorem chv_posUnipotent_le_borel : posUnipotent .E7 (ZMod 2) ≤ borelGroup .E7 (ZMod 2) :=
  le_sup_right

theorem chv_neg_one_units : (-1 : (ZMod 2)ˣ) = 1 := by decide

theorem chv_nx_conj (i : Fin (Tag.rank .E7)) :
    weylElt .E7 (ZMod 2) i 1 * xUnit .E7 (ZMod 2) i 1 * (weylElt .E7 (ZMod 2) i 1)⁻¹ =
      yUnit .E7 (ZMod 2) i 1 := by
  rw [weylElt_mul_xUnit_mul_inv]
  congr 1

theorem chv_weylElt_inv_eq (i : Fin (Tag.rank .E7)) :
    (weylElt .E7 (ZMod 2) i 1)⁻¹ = weylElt .E7 (ZMod 2) i 1 := by
  rw [Chevalley.weylElt_inv, chv_neg_one_units]

theorem chv_weylElt_eq_xyx (i : Fin (Tag.rank .E7)) :
    weylElt .E7 (ZMod 2) i 1 =
      xUnit .E7 (ZMod 2) i 1 * yUnit .E7 (ZMod 2) i 1 * xUnit .E7 (ZMod 2) i 1 := by
  have h := CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul (τ := .E7) (K := ZMod 2) i 1
  refine h.trans ?_
  congr 2

theorem chv_yUnit_mem_parabolic_iff (J : Set (Fin (Tag.rank .E7))) (i : Fin (Tag.rank .E7)) :
    yUnit .E7 (ZMod 2) i 1 ∈ parabolicSubgroup .E7 (ZMod 2) J ↔ i ∈ J := by
  have hn := (standard_parabolic_cells .E7 (ZMod 2)).2.2.1 J i
  have hx : xUnit .E7 (ZMod 2) i 1 ∈ parabolicSubgroup .E7 (ZMod 2) J :=
    chv_borel_le_parabolic J (xUnit_mem_borelGroup i 1)
  rw [← hn]
  constructor
  · intro hy
    rw [chv_weylElt_eq_xyx]
    exact mul_mem (mul_mem hx hy) hx
  · intro hnn
    rw [← chv_nx_conj]
    exact mul_mem (mul_mem hnn hx) (inv_mem hnn)

theorem chv_nxn (i : Fin (Tag.rank .E7)) :
    weylElt .E7 (ZMod 2) i 1 * xUnit .E7 (ZMod 2) i 1 * weylElt .E7 (ZMod 2) i 1 =
      yUnit .E7 (ZMod 2) i 1 := by
  have := chv_nx_conj i
  rwa [chv_weylElt_inv_eq] at this

theorem chv_nC_inv_mul_xC_mul_nC (i : Fin (Tag.rank .E7)) :
    (nC .E7 (ZMod 2) i)⁻¹ * xC .E7 (ZMod 2) i 1 * nC .E7 (ZMod 2) i = yC .E7 (ZMod 2) i 1 := by
  refine Subtype.ext ?_
  show ((weylElt .E7 (ZMod 2) i 1)⁻¹ * xUnit .E7 (ZMod 2) i 1 * weylElt .E7 (ZMod 2) i 1 :
    ModGL .E7 (ZMod 2)) = yUnit .E7 (ZMod 2) i 1
  rw [chv_weylElt_inv_eq, chv_nxn]

theorem chv_conj_fix_iff {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G V) (g h : G) (y : V) :
    ρ (g⁻¹ * h * g) y = y ↔ ρ h (ρ g y) = ρ g y := by
  have hg : ∀ w : V, ρ g (ρ g⁻¹ w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hg' : ∀ w : V, ρ g⁻¹ (ρ g w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  constructor
  · intro h1
    have := congrArg (ρ g) h1
    rwa [hg] at this
  · intro h1
    rw [h1, hg']

theorem isChevType_of_stab {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) ↥(adjointGroup .E7 (ZMod 2)) V)
    (y : V) (hy : y ≠ 0)
    (hstab : ∀ g : ↥(adjointGroup .E7 (ZMod 2)), ρ g y = y ↔
      (g : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6}) :
    IsChevType .E7 (ZMod 2) 2 exists_weyl_neg_E7 ρ y e7Chi56 (Finset.univ.erase e7n6) := by
  refine ⟨?_, hy, ?_, fun i => ?_⟩
  · intro u hu
    have hu' : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) := hu
    exact (hstab u).mpr (chv_borel_le_parabolic _ (chv_posUnipotent_le_borel hu'))
  · intro h hh
    have hh' : (h : ModGL .E7 (ZMod 2)) ∈ torusGroup .E7 (ZMod 2) := hh
    rw [torusGroup_eq_bot_of_forall_units_eq_one chv_units_zmod_two, Subgroup.mem_bot] at hh'
    have : h = 1 := Subtype.ext hh'
    subst this
    rw [map_one, chv_e7Chi56_one, one_smul]
    rfl
  · have hone : ∀ t : (ZMod 2)ˣ, e7Chi56 (dC .E7 (ZMod 2) i t) = 1 := fun t => by
      rw [chv_units_zmod_two t, dC_one, chv_e7Chi56_one]
    rw [chv_heckeT]
    have hkey : ρ (nC .E7 (ZMod 2) i) y + ρ (xC .E7 (ZMod 2) i 1 * nC .E7 (ZMod 2) i) y = 0 ↔
        ρ (yC .E7 (ZMod 2) i 1) y = y := by
      rw [chv_add_eq_zero_iff_eq, ← chv_nC_inv_mul_xC_mul_nC, chv_conj_fix_iff, map_mul,
        Module.End.mul_apply]
    have hY : ρ (yC .E7 (ZMod 2) i 1) y = y ↔ i ≠ e7n6 := by
      rw [hstab]
      exact chv_yUnit_mem_parabolic_iff {i | i ≠ e7n6} i
    rw [hkey, hY]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun hi => ⟨hone, hi⟩, fun h => h.2⟩

end CFSG.GF2Type.SmithTypeE.E8
