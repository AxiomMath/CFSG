module

public import CFSG.ClassicalInvolution.Q3.Quasisimple
import CFSG.ClassicalInvolution.Q3.SP3Member
import CFSG.ClassicalInvolution.Q3.SP3Odd
import CFSG.ClassicalInvolution.Q3.SP3Twin

public section

namespace CFSG.ClassicalInvolution.Q3.SP3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.Twin
open CFSG.ComponentClassification
open scoped MatrixGroups commutatorElement

section Member

variable {Y : Type} [Group Y] [Finite Y]

theorem nonempty_equiv_sl2_of_member (hsolv : Group.IsSolvable Y)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) : Nonempty (↥L ≃* SL(2, ZMod 3)) := by
  have hUn : (pCore 2 Y).Normal := pCore_normal
  exact h.nonempty_equiv_sl2_of_solvable pCore_isPGroup (centralizer_pCore_le hsolv hO)

theorem commute_involution_of_member {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {L L' : Subgroup Y} {z z' : Y}
    (h : IsClassicalMember3 L z) (h' : IsClassicalMember3 L' z') : ∀ y ∈ L', z * y = y * z := by
  obtain ⟨e⟩ := h.nonempty_equiv_sl2_of_solvable hU hC
  obtain ⟨e'⟩ := h'.nonempty_equiv_sl2_of_solvable hU hC
  obtain ⟨g, hgL, hg3, hg1⟩ := exists_order_three e
  obtain ⟨g', hg'L, hg'3, hg'1⟩ := exists_order_three e'
  have hz2' : z ^ 2 = 1 := by rw [← h.orderOf_eq_two]; exact pow_orderOf_eq_one z
  have hz2 : z * z = 1 := by rw [← sq]; exact hz2'
  have hz'2 : z' * z' = 1 := by
    rw [← sq, ← h'.orderOf_eq_two]; exact pow_orderOf_eq_one z'
  have hQU : quatIn e ≤ U := quatIn_le_of_member hU hC e hz2 h.subnormal
  have hQ'U : quatIn e' ≤ U := quatIn_le_of_member hU hC e' hz'2 h'.subnormal
  have hall := commutator_mem_quatIn_of_member' hU hC e h.orderOf_eq_two h.mem h.subnormal hgL
    hg3 hg1
  have hall' := commutator_mem_quatIn_of_member' hU hC e' h'.orderOf_eq_two h'.mem h'.subnormal
    hg'L hg'3 hg'1
  have hzU : z ∈ U := hQU (involution_mem_quatIn e h.mem hz2')
  have hzc := mul_comm_involution_of_member e hQU h.orderOf_eq_two h.mem hgL hg3 hg1 hall
  have hg'z := mul_comm_of_involution_central e' h'.orderOf_eq_two h'.mem hg'L hg'3 hall' hzU
    hzc hz2
  have hle : quatIn e' ⊔ Subgroup.zpowers g' ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine sup_le (fun q hq => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc q (hQ'U hq))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hg'z
  intro y hy
  rw [← quatIn_sup_zpowers e' hg'L hg'3 hg'1] at hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem involution_central {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ)
    {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z) : ∀ y : Y, z * y = y * z := by
  have hle : (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({z} : Set Y) := by
    rw [← hΛ.generated]
    refine iSup₂_le fun L' hL' y hy => ?_
    obtain ⟨z', h'⟩ := hΛ.classical L' hL'
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_involution_of_member hU hC h h' y hy).symm
  intro y
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))).symm

omit [Finite Y] in
theorem isSubnormal_of_central {L : Subgroup Y} {z : Y} (h : IsClassicalMember3 L z)
    (hzc : ∀ y : Y, z * y = y * z) : L.IsSubnormal := by
  have hCz : Subgroup.centralizer ({z} : Set Y) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc y).symm
  have hsn := h.subnormal
  rw [hCz] at hsn
  exact Components.mathlib_subnormal_of_chain hsn Subgroup.IsSubnormal.top

theorem member_properties (hsolv : Group.IsSolvable Y)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) {Λ : Set (Subgroup Y)}
    (hΛ : InClass3 Λ) {L : Subgroup Y} (hL : L ∈ Λ) :
    Nonempty (↥L ≃* SL(2, ZMod 3)) ∧ (∃ z : Y, IsClassicalMember3 L z ∧ z ∈ Subgroup.center Y) ∧
      L.IsSubnormal := by
  have hUn : (pCore 2 Y).Normal := pCore_normal
  have hU2 : IsPGroup 2 (pCore 2 Y) := pCore_isPGroup
  have hCU : Subgroup.centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y := centralizer_pCore_le hsolv hO
  obtain ⟨z, hz⟩ := hΛ.classical L hL
  have hc := involution_central hU2 hCU hΛ hz
  exact ⟨nonempty_equiv_sl2_of_member hsolv hO hz,
    ⟨z, hz, Subgroup.mem_center_iff.mpr fun y => (hc y).symm⟩, isSubnormal_of_central hz hc⟩

theorem commutes_of_ne (hsolv : Group.IsSolvable Y)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) {Λ : Set (Subgroup Y)}
    (hΛ : InClass3 Λ) {K L : Subgroup Y} (hK : K ∈ Λ) (hL : L ∈ Λ) (hne : K ≠ L) :
    Commutes K L := by
  obtain ⟨⟨eK⟩, ⟨z, hz, hzc⟩, hKs⟩ := member_properties hsolv hO hΛ hK
  obtain ⟨⟨eL⟩, -, hLs⟩ := member_properties hsolv hO hΛ hL
  rcases twin_of_central hsolv hO hKs hLs eK eL hz.orderOf_eq_two hz.mem
    (fun y => (Subgroup.mem_center_iff.mp hzc y).symm) with h | h
  · exact absurd h hne
  · intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ ⁅K, L⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot] at hxy
    exact commutatorElement_eq_one_iff_mul_comm.mp hxy

end Member

theorem solvableConnected3 : SolvableConnected3 := by
  intro Y _ _ Λ hΛ hO hconn hsolv
  have hO' : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥ := fun N hN hodd =>
    le_bot_iff.mp (hO ▸ le_sSup ⟨hN, hodd⟩)
  have hbot : nonCommGraph Λ = ⊥ := by
    ext K L
    simp only [nonCommGraph_adj, SimpleGraph.bot_adj, iff_false, not_and, not_not]
    intro hne
    exact commutes_of_ne hsolv hO' hΛ K.2 L.2 (fun h => hne (Subtype.ext h))
  obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
  have hone : ∀ L ∈ Λ, L = L₀ := by
    intro L hL
    have hr := hconn.preconnected ⟨L, hL⟩ ⟨L₀, hL₀⟩
    rw [hbot, SimpleGraph.reachable_bot] at hr
    exact congrArg Subtype.val hr
  have hΛeq : Λ = {L₀} := by
    ext L
    exact ⟨fun hL => hone L hL, fun hL => by rw [Set.mem_singleton_iff.mp hL]; exact hL₀⟩
  have htop : L₀ = ⊤ := by
    rw [← hΛ.generated, hΛeq]
    simp
  obtain ⟨z₀, hz₀⟩ := hΛ.classical L₀ hL₀
  obtain ⟨e₀⟩ := nonempty_equiv_sl2_of_member hsolv hO' hz₀
  exact ⟨⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e₀)⟩,
    by rw [hΛeq, htop]⟩

end CFSG.ClassicalInvolution.Q3.SP3
