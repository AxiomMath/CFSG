module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128ClPerf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128F4
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_closure_inter {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : IsElemAb2 V 8) (Y Xt : Subgroup (MulAut ↥V)) (hXY : Xt ≤ Y)
    (hXperf : ⁅Xt.subgroupOf Y, Xt.subgroupOf Y⁆ = Xt.subgroupOf Y)
    (hcent : ∀ o ∈ oddCore ↥Y, ∀ x ∈ Xt.subgroupOf Y, x * o = o * x)
    (hD : Nat.card ↥(Subgroup.centralizer (Xt : Set (MulAut ↥V))) ∣ 6 ∧
      ∀ c ∈ Subgroup.centralizer (Xt : Set (MulAut ↥V)), c ^ 3 = 1 → c ≠ 1 →
        ∀ v : ↥V, c v = v → v = 1) :
    normalClosure ((Xt.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ⊓ oddCore ↥Y = ⊥ := by
  classical
  set Xy : Subgroup ↥Y := Xt.subgroupOf Y with hXy
  set Zy : Subgroup ↥Y := normalClosure (Xy : Set ↥Y) with hZy
  set O : Subgroup ↥Y := oddCore ↥Y with hO
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hle : Zy ≤ centralizer (O : Set ↥Y) := by
    refine Subgroup.normalClosure_le_normal fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro o ho
    exact (hcent o ho x hx).symm
  have hZc : ∀ z ∈ Zy, ∀ o ∈ O, z * o = o * z := fun z hz o ho =>
    ((Subgroup.mem_centralizer_iff.mp (hle hz)) o ho).symm
  have hZperf : ⁅Zy, Zy⁆ = Zy := sec128_normalClosure_perfect Xy hXperf
  set Z : Subgroup (MulAut ↥V) := Zy.map Y.subtype with hZdef
  have hZ : _root_.commutator ↥Z = ⊤ := by
    apply sec128_perfect_of_comm_eq
    rw [hZdef, ← Subgroup.map_commutator, hZperf]
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc => ?_
  obtain ⟨hcZ, hcO⟩ := Subgroup.mem_inf.mp hc
  by_contra hc1
  have hc'cent : (c : MulAut ↥V) ∈ Subgroup.centralizer (Xt : Set (MulAut ↥V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (hcent c hcO ⟨x, hXY hx⟩ hx)
  have hordO : orderOf c ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hcO
  have hord6 : orderOf c ∣ 6 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hc'cent
    rw [show orderOf (c : MulAut ↥V) = orderOf c from
      orderOf_injective Y.subtype Y.subtype_injective c] at h1
    exact h1.trans hD.1
  have hodd : Odd (orderOf c) := hOodd.of_dvd_nat hordO
  have hc3 : c ^ 3 = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, m = orderOf c := ⟨_, rfl⟩
    rw [← hm] at hord6 hodd
    have hm6 : m ≤ 6 := Nat.le_of_dvd (by norm_num) hord6
    have hm1 : m = 1 ∨ m = 3 := by
      interval_cases m <;> first | omega | (exfalso; revert hord6 hodd; decide)
    rcases hm1 with h | h
    · exfalso
      rw [h] at hm
      exact hc1 (orderOf_eq_one_iff.mp hm.symm)
    · rw [← pow_orderOf_eq_one c, ← hm, h]
  have hc'3 : (c : MulAut ↥V) ^ 3 = 1 := by
    have := congrArg (fun y : ↥Y => (y : MulAut ↥V)) hc3
    simpa using this
  have hc'1 : (c : MulAut ↥V) ≠ 1 := fun h => hc1 (Subtype.ext h)
  refine sec128_no_central_three V hV Z hZ (c : MulAut ↥V) ⟨c, hcZ, rfl⟩ ?_ hc'3 hc'1
    (hD.2 _ hc'cent hc'3 hc'1)
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (hZc y hy c hcO)

end CFSG.OddStandard.SmallF3.Omega
