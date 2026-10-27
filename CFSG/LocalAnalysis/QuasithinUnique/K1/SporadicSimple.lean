module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicZStar
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Open

theorem even_card_of_simple_nonabelian {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Even (Nat.card X) := by
  by_contra hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨a, b, hab⟩ := h
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem nonabelian_quotient_of_not_centralizes {G : Type} [Group G] {L : Subgroup G}
    (hperf : Group.IsPerfect L) {w : G} (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) :
    ∃ a b : L ⧸ Subgroup.center L, a * b ≠ b * a := by
  by_contra hex
  have hcomm : ∀ a b : L ⧸ Subgroup.center L, a * b = b * a := fun a b => by
    by_contra h
    exact hex ⟨a, b, h⟩
  apply hnc
  have hcen : ∀ x y : L, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center L := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    have := hcomm (x : L ⧸ Subgroup.center L) (y : L ⧸ Subgroup.center L)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (x : L ⧸ Subgroup.center L) * y * (x : L ⧸ Subgroup.center L)⁻¹ *
        (y : L ⧸ Subgroup.center L)⁻¹ = (y * x) * (x : L ⧸ Subgroup.center L)⁻¹ *
        (y : L ⧸ Subgroup.center L)⁻¹ := by rw [this]
      _ = 1 := by group
  have hle : (⊤ : Subgroup L) ≤ Subgroup.center L := by
    rw [← hperf.commutator_eq_top]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcen x y
  have hcomm' : ∀ x y : L, x * y = y * x := fun x y =>
    (Subgroup.mem_center_iff.mp (hle (Subgroup.mem_top x)) y).symm
  have : IsMulCommutative L := ⟨⟨hcomm'⟩⟩
  have : Subsingleton L := inferInstance
  intro y hy
  have : (⟨y, hy⟩ : L) = 1 := Subsingleton.elim _ _
  have hy1 : y = 1 := congrArg Subtype.val this
  rw [hy1]
  exact Subgroup.one_mem _

theorem false_of_simple_of_noStronglyClosed {G : Type} [Group G] [Finite G] {H S U L : Subgroup G}
    (h : StrongClosureComponent H S U L) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (e : (L ⧸ Subgroup.center L) ≃* Y) (hY : NoStronglyClosedElemAbelian Y) {w : G} (hwU : w ∈ U)
    (hnc : ¬ L ≤ Subgroup.centralizer ({w} : Set G)) : False := by
  have hperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr h.perfect
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := e.isSimpleGroup
  have heven : Even (Nat.card (L ⧸ Subgroup.center L)) :=
    even_card_of_simple_nonabelian (nonabelian_quotient_of_not_centralizes hperf hnc)
  have hodd := oddCoreFree_of_simple_even heven
  have hX := NoStronglyClosedElemAbelian.of_mulEquiv e hY
  have hall := centralizes_of_noStronglyClosed h.sylow h.le_S h.elem h.closed h.le_H hperf
    h.normalizes hX hodd w hwU
  exact hnc fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hall y hy)

end CFSG.QuasithinUnique.K1
