module

public import CFSG.GF2Type.Widths1112.Co2Orbits
public import CFSG.GF2Type.Widths1112.Co2Forms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2.Native
  CFSG.GF2W1112 Matrix

private theorem uni1_hcase : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

private theorem uni1_additive_eq_dot {f : Vec22 → ZMod 2} (hadd : ∀ u v, f (u + v) = f u + f v)
    (y : Vec22) : f y = (fun i => f (Pi.single i 1)) ⬝ᵥ y := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    linear_combination -h
  let g : Vec22 →+ ZMod 2 := AddMonoidHom.mk' f hadd
  have key : f y = ∑ j, y j * f (Pi.single j 1) := by
    calc f y = g y := rfl
      _ = g (∑ j, Pi.single j (y j)) := by rw [Finset.univ_sum_single]
      _ = ∑ j, g (Pi.single j (y j)) := map_sum g _ _
      _ = ∑ j, y j * f (Pi.single j 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        show f (Pi.single j (y j)) = y j * f (Pi.single j 1)
        rcases uni1_hcase (y j) with h | h
        · rw [h, Pi.single_zero, h0, zero_mul]
        · rw [h, one_mul]
  rw [key]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem uni1_bil_zero_left (y : Vec22) : bil₀₂ 0 y = 0 := by
  unfold bil₀₂
  rw [zero_dotProduct]

private theorem uni1_inv_additive_zero
    (f : Vec22 → ZMod 2) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hinv : ∀ (g : NativeSporadic.Co2) (v : Vec22), f (co2Act g v) = f v) : f = 0 := by
  have hf : ∀ y, f y = (fun i => f (Pi.single i 1)) ⬝ᵥ y := uni1_additive_eq_dot hadd
  have hc : (fun i => f (Pi.single i 1)) = 0 :=
    co2_dual_fixed_zero fun g v => by rw [← hf, ← hf, hinv]
  funext y
  rw [hf y, hc, zero_dotProduct]
  rfl

theorem co2_invariant_quadratic
    {q : Vec22 → ZMod 2}
    (hbil : ∀ u u' v, q (u + u' + v) - q (u + u') - q v =
      (q (u + v) - q u - q v) + (q (u' + v) - q u' - q v))
    (hinv : ∀ (g : NativeSporadic.Co2) (v : Vec22), q (co2Act g v) = q v) :
    q = 0 ∨ q = q₀₂ := by
  have hq0 : q 0 = 0 := by
    have h := hbil 0 0 0
    simp only [add_zero] at h
    linear_combination h
  have hcomm : ∀ u v : Vec22, q (u + v) - q u - q v = q (v + u) - q v - q u := by
    intro u v
    rw [add_comm u v]
    ring
  have hright : ∀ u y y' : Vec22, q (u + (y + y')) - q u - q (y + y') =
      (q (u + y) - q u - q y) + (q (u + y') - q u - q y') := by
    intro u y y'
    rw [hcomm u (y + y'), hbil y y' u, hcomm y u, hcomm y' u]
  have hinv_polar : ∀ (g : NativeSporadic.Co2) (u v : Vec22),
      q (co2Act g u + co2Act g v) - q (co2Act g u) - q (co2Act g v) =
        q (u + v) - q u - q v := by
    intro g u v
    rw [← co2Act_add, hinv, hinv, hinv]
  obtain ⟨r0, hr0⟩ : ∃ r : Vec22, r = toVecD 22 (w12Co2Rep 0) := ⟨_, rfl⟩
  have hc : ∀ y, q (r0 + y) - q r0 - q y =
      (fun i => q (r0 + Pi.single i 1) - q r0 - q (Pi.single i 1)) ⬝ᵥ y :=
    uni1_additive_eq_dot (f := fun y => q (r0 + y) - q r0 - q y) (hright r0)
  have hdot_of_stab : ∀ (g : NativeSporadic.Co2), co2Act g (toVecD 22 (w12Co2Rep 0)) =
      toVecD 22 (w12Co2Rep 0) → ∀ y,
      (fun i => q (r0 + Pi.single i 1) - q r0 - q (Pi.single i 1)) ⬝ᵥ co2Act g y =
        (fun i => q (r0 + Pi.single i 1) - q r0 - q (Pi.single i 1)) ⬝ᵥ y := by
    intro g hg y
    rw [← hr0] at hg
    have h2 := hinv_polar g r0 y
    rw [hg] at h2
    exact ((hc (co2Act g y)).symm.trans h2).trans (hc y)
  obtain ⟨c, hc'⟩ : ∃ c : ZMod 2, ∀ y, q (r0 + y) - q r0 - q y = c * bil₀₂ r0 y := by
    rcases co2_dual_fixed_stab hdot_of_stab with h0 | hl
    · refine ⟨0, fun y => ?_⟩
      rw [hc y, h0, zero_dotProduct, zero_mul]
    · refine ⟨1, fun y => ?_⟩
      rw [hc y, hl y, one_mul, hr0]
  have hmem : ∀ u ∈ co2Orbit 0, ∀ y, q (u + y) - q u - q y = c * bil₀₂ u y := by
    intro u hu y
    obtain ⟨g, hg⟩ := hu
    have hu' : u = co2Act g r0 := by
      rw [hr0]
      exact hg.symm
    subst hu'
    obtain ⟨y', rfl⟩ : ∃ y', y = co2Act g y' :=
      ⟨co2Act g⁻¹ y, (co2Act_apply_inv g y).symm⟩
    rw [hinv_polar g r0 y', bil₀₂_co2Act g r0 y']
    exact hc' y'
  have hzero : ∀ y, q (0 + y) - q 0 - q y = c * bil₀₂ 0 y := fun y => by
    rw [zero_add, hq0, uni1_bil_zero_left, mul_zero]
    ring
  have hall : ∀ u ∈ Submodule.span (ZMod 2) (co2Orbit 0),
      ∀ y, q (u + y) - q u - q y = c * bil₀₂ u y := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu => exact hmem u hu
    | zero => exact hzero
    | add u v _ _ hu hv =>
      intro y
      linear_combination hbil u v y + hu y + hv y - c * bil₀₂_add_left u v y
    | smul a u _ hu =>
      intro y
      rcases uni1_hcase a with rfl | rfl
      · rw [zero_smul]
        exact hzero y
      · rw [one_smul]
        exact hu y
  have hall' : ∀ u y, q (u + y) - q u - q y = c * bil₀₂ u y := fun u y =>
    hall u (by rw [co2_orbit_spans]; exact Submodule.mem_top) y
  rcases uni1_hcase c with rfl | rfl
  ·
    have hadd : ∀ u v, q (u + v) = q u + q v := by
      intro u v
      have h := hall' u v
      rw [zero_mul] at h
      linear_combination h
    exact Or.inl (uni1_inv_additive_zero q hadd hinv)
  ·
    have hDadd : ∀ u v, (fun v => q v - q₀₂ v) (u + v) =
        (fun v => q v - q₀₂ v) u + (fun v => q v - q₀₂ v) v := by
      intro u v
      have h1 := hall' u v
      have h2 := polar_q₀₂ u v
      rw [one_mul] at h1
      show q (u + v) - q₀₂ (u + v) = (q u - q₀₂ u) + (q v - q₀₂ v)
      linear_combination h1 - h2
    have hDinv : ∀ (g : NativeSporadic.Co2) (v : Vec22),
        (fun v => q v - q₀₂ v) (co2Act g v) = (fun v => q v - q₀₂ v) v := by
      intro g v
      show q (co2Act g v) - q₀₂ (co2Act g v) = q v - q₀₂ v
      rw [hinv, q₀₂_co2Act]
    have hD := uni1_inv_additive_zero (fun v => q v - q₀₂ v) hDadd hDinv
    refine Or.inr (funext fun v => ?_)
    have hv : q v - q₀₂ v = 0 := congrFun hD v
    exact sub_eq_zero.1 hv

end CFSG.GF2Type.Widths1112
