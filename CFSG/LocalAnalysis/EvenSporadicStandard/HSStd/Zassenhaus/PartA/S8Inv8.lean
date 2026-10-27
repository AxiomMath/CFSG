module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Inv4

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Comm2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

theorem ubG_sq (a : PA5 L t E z) : ubG a * ubG a = 1 := Subtype.ext (PA5.ub_sq a)

include hb a hK hcj hall

theorem inv_in_CT (k : ↥K) (hk : k⁻¹ * sigmaK hb a hK hcj hall k ∈ center ↥K) :
    ((k : ↥(Cen a.ub)) ∈ CT hb a.toPA6.toPA5) ∨
      ∃ hd : a.dcase = DCase.d8, u1G a hd * (k : ↥(Cen a.ub)) ∈ CT hb a.toPA6.toPA5 := by
  set T := tG hb a.toPA6.toPA5 with hT
  have hf : ∀ y ∈ K, ((k : ↥(Cen a.ub))⁻¹ * (T * k * T⁻¹)) * y =
      y * ((k : ↥(Cen a.ub))⁻¹ * (T * k * T⁻¹)) := by
    intro y hy
    have := Subgroup.mem_center_iff.1 hk ⟨y, hy⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, sigmaK_apply] at h2
    exact h2.symm
  rcases inv_KD hb a hK hcj hall k hf with h | ⟨h, hd⟩
  · left
    rw [mem_CT]
    have h1 : (k : ↥(Cen a.ub)) = T * k * T⁻¹ := inv_mul_eq_one.1 h
    exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
  · right
    refine ⟨hd, ?_⟩
    rw [mem_CT]
    have hX : T * (k : ↥(Cen a.ub)) * T⁻¹ = (k : ↥(Cen a.ub)) * ubG a.toPA6.toPA5 := by
      have := congrArg (fun x => (k : ↥(Cen a.ub)) * x) h
      simpa using this
    have hc := ubG_central a.toPA6.toPA5
    have hsq := ubG_sq a.toPA6.toPA5
    have e : T * (u1G a hd * (k : ↥(Cen a.ub))) * T⁻¹ = u1G a hd * (k : ↥(Cen a.ub)) := by
      calc T * (u1G a hd * (k : ↥(Cen a.ub))) * T⁻¹
          = (T * u1G a hd * T⁻¹) * (T * (k : ↥(Cen a.ub)) * T⁻¹) := by group
        _ = (ubG a.toPA6.toPA5 * u1G a hd) * ((k : ↥(Cen a.ub)) * ubG a.toPA6.toPA5) := by
          rw [t_conj_u1 hb a hd, hX]
        _ = (ubG a.toPA6.toPA5 * (u1G a hd * (k : ↥(Cen a.ub)))) * ubG a.toPA6.toPA5 := by
          simp only [mul_assoc]
        _ = ((u1G a hd * (k : ↥(Cen a.ub))) * ubG a.toPA6.toPA5) * ubG a.toPA6.toPA5 := by
          rw [hc (u1G a hd * (k : ↥(Cen a.ub)))]
        _ = u1G a hd * (k : ↥(Cen a.ub)) := by rw [mul_assoc, hsq, mul_one]
    exact (mul_inv_eq_iff_eq_mul.1 e).symm

end Comm2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
