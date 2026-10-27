module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End3

public section

open CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412 Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem sylow_eq_image (hN11a : S_N11a) (hN11c : S_N11c) {X : Type} [Group X] [Finite X]
    {S : Sylow 2 X} {V : Subgroup X} {W : Fin 4 → Subgroup X} {ρ : Fin 4 → X}
    (hX : XData S V W ρ) {M : Subgroup X} [M.Normal] (hVM : V ≤ M) (hB : IsCaseB S V M) :
    (S : Subgroup X).subgroupOf M = V.subgroupOf M ∧
      ∃ D : Sylow 2 (Mbar M), (D : Subgroup (Mbar M)) = (V.subgroupOf M).map (mbarMk M) := by
  classical
  obtain ⟨Ts, hTs, hVΩ⟩ := hB.syl
  have hVab : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext (hX.comm a a.2 b b.2)⟩⟩
  have hΩ : IsMulCommutative (Omega1 (Ts : Subgroup (Mbar M))) := by
    rw [← hVΩ]
    exact isMulCommutative_map (isMulCommutative_subgroupOf hVab M) (mbarMk M)
  have hcomm := omega1_commutes_of_layer hN11a hN11c hB.o2
    (CFSG.Goldschmidt.goldschmidtOddCore_quotient_eq_bot ↥M) hB.layer hB.comps Ts hΩ
  have hVMleSM : V.subgroupOf M ≤ (S : Subgroup X).subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hX.le_S (Subgroup.mem_subgroupOf.mp hx))
  have hSMleVM : (S : Subgroup X).subgroupOf M ≤ V.subgroupOf M := by
    intro x hx
    have hxS : (x : X) ∈ (S : Subgroup X) := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr (hX.centS (x : X) hxS ?_)
    intro v hv
    let v' : ↥M := ⟨v, hVM hv⟩
    have hv'VM : v' ∈ V.subgroupOf M := Subgroup.mem_subgroupOf.mpr hv
    have hv'SM : v' ∈ (S : Subgroup X).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (hX.le_S hv)
    have hπx : mbarMk M x ∈ (Ts : Subgroup (Mbar M)) := by
      rw [hTs]
      exact Subgroup.mem_map_of_mem (mbarMk M) hx
    have hπv : mbarMk M v' ∈ Omega1 (Ts : Subgroup (Mbar M)) := by
      rw [← hVΩ]
      exact Subgroup.mem_map_of_mem (mbarMk M) hv'VM
    have hcomm' : mbarMk M x * mbarMk M v' = mbarMk M v' * mbarMk M x :=
      hcomm (mbarMk M x) hπx (mbarMk M v') hπv
    let w' : ↥M := ⟨(x : X) * v * (x : X)⁻¹,
      M.mul_mem (M.mul_mem x.2 (hVM hv)) (M.inv_mem x.2)⟩
    have hw'V : (w' : X) ∈ V := hX.normS (x : X) hxS v hv
    have hw'VM : w' ∈ V.subgroupOf M := Subgroup.mem_subgroupOf.mpr hw'V
    have hw'SM : w' ∈ (S : Subgroup X).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (hX.le_S hw'V)
    have hw'eq : w' = x * v' * x⁻¹ := Subtype.ext rfl
    have hπw' : mbarMk M w' = mbarMk M v' := by
      rw [hw'eq, map_mul, map_mul, map_inv, hcomm']
      rw [mul_assoc, mul_inv_cancel, mul_one]
    have hw'v' : w' = v' := hB.inj w' hw'SM v' hv'SM hπw'
    have hconj : (x : X) * v * (x : X)⁻¹ = v := congrArg Subtype.val hw'v'
    have h2 := congrArg (fun z : X => z * (x : X)) hconj
    simpa [mul_assoc] using h2
  have hSMeq : (S : Subgroup X).subgroupOf M = V.subgroupOf M := le_antisymm hSMleVM hVMleSM
  exact ⟨hSMeq, Ts, by rw [hTs, hSMeq]⟩

end CFSG.OddStandard.SmallF3.Omega
