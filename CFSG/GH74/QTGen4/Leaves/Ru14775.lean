module

public import CFSG.GH74.SectionalRank
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.GH74.QTGen4.Ru14775

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem sq_eq_one_of_closure {G : Type} [Group G] (S : Set G)
    (habel : IsMulCommutative ↥(Subgroup.closure S)) (hS : ∀ s ∈ S, s ^ 2 = 1) :
    ∀ k ∈ Subgroup.closure S, k ^ 2 = 1 := by
  have := habel
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y :=
      congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(Subgroup.closure S)) ⟨y, hy⟩)
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem sq_eq_one_of_conjClosure {G : Type} [Group G] (Z H : Subgroup G)
    (hZ : ∀ z ∈ Z, z ^ 2 = 1) (habel : IsMulCommutative ↥(conjClosure Z H)) :
    ∀ k ∈ conjClosure Z H, k ^ 2 = 1 := by
  refine sq_eq_one_of_closure _ habel ?_
  rintro x ⟨h, -, z, hz, rfl⟩
  rw [conj_pow, hZ z hz, mul_one, mul_inv_cancel]

theorem isElemAbelian_fsuU {G : Type} [Group G] (T V : Subgroup G)
    (hV : ∀ v ∈ V, v ^ 2 = 1) (habel : IsMulCommutative ↥(fsuU T V)) :
    IsElemAbelian 2 (fsuU T V) :=
  ⟨habel, sq_eq_one_of_conjClosure V _ hV habel⟩

theorem card_fsuU_le_of_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G) (T V : Subgroup G)
    (hV : ∀ v ∈ V, v ^ 2 = 1) (habel : IsMulCommutative ↥(fsuU T V)) :
    Nat.card ↥(fsuU T V) ≤ 2 ^ 4 :=
  SectionalTwoRankLE.card_le_of_elementary (r := 4) hG (fsuU T V)
    (isElemAbelian_fsuU T V hV habel)

end CFSG.GH74.QTGen4.Ru14775

end
