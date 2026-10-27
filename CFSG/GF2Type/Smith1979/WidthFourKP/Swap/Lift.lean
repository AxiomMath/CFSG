module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Interface
public import CFSG.GF2Type.Smith1979.CharTwoLift
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Bar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap.Thompson

open CFSG.Open CFSG.LargeExtraspecial
open Subgroup

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g x : G} {K Y : Subgroup S.O}

theorem mem_Y_iff_stab (T : ThompsonInput S g x K Y) (m : S.O) :
    m ∈ Y ↔ m ∈ CFSG.GF2Type.Smith1979.IdxFour.stab S (S.cl x) := by
  rw [CFSG.GF2Type.Smith1979.IdxFour.mem_stab]
  exact T.mem_Y m

theorem K_le_Y (T : ThompsonInput S g x K Y) : K ≤ Y :=
  CFSG.ClassicalInvolution.isSubnormal_le T.subnormal

theorem exists_lift (T : ThompsonInput S g x K Y) {m : S.O} (hm : m ∈ Y) :
    ∃ s : S.M, S.ρ s = m ∧ (s : G) * x = x * (s : G) := by
  have hx1 : x ≠ 1 := by
    intro h
    have := T.orderOf_eq
    rw [h, orderOf_one] at this
    omega
  obtain ⟨s, hsx, hsρ⟩ :=
    CFSG.GF2Type.Smith1979.IdxFour.exists_centralizer_lift S T.mem_QG hx1 T.ne_z
      ((mem_Y_iff_stab T m).mp hm)
  exact ⟨s, hsρ, hsx⟩

theorem exists_odd_order_lift (T : ThompsonInput S g x K Y) {k : S.O} (hkK : k ∈ K)
    (hkodd : Odd (orderOf k)) (hk1 : k ≠ 1) :
    ∃ y : S.M, S.ρ y = k ∧ (y : G) * x = x * (y : G) ∧
      Odd (orderOf (y : G)) ∧ (y : G) ≠ 1 := by
  obtain ⟨s, hsρ, hsx⟩ := exists_lift T (K_le_Y T hkK)
  have hsodd : Odd (orderOf (S.ρ s)) := by rwa [hsρ]
  obtain ⟨y, hyz, hyodd, hyρ⟩ :=
    CFSG.ComponentClassification.AS76b.Lemma39.exists_odd_preimage S.ρ s hsodd
  have hyx : (y : G) * x = x * (y : G) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyz
    have hcoe : (y : G) = ((s : S.M) : G) ^ n := by
      rw [← hn]
      rfl
    rw [hcoe]
    exact ((show Commute (s : G) x from hsx).zpow_left n).eq
  refine ⟨y, ?_, hyx, ?_, ?_⟩
  · rw [hyρ, hsρ]
  · rwa [Subgroup.orderOf_coe]
  · intro h1
    apply hk1
    rw [← hyρ.trans hsρ]
    have hy1 : y = 1 := Subtype.ext (by simpa using h1)
    simpa using congrArg S.ρ hy1

end CFSG.GF2Type.Smith1979.W4Swap.Thompson
