module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

theorem comm_of_forall_sq' {G : Type} [Group G] {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have hab : (a * b) * (a * b) = 1 := hE _ (mul_mem ha hb)
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hE b hb)
  calc a * b = (a * b)⁻¹ := h1.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem isElemAb_of_sq_one {G : Type} [Group G] {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) :
    IsElementaryAbelian 2 ↥E :=
  { is_comm := ⟨fun a b => Subtype.ext (comm_of_forall_sq' hE a.2 b.2)⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      simpa [pow_two] using hE x x.2 }

theorem le_pRank_of_elem {G : Type} [Group G] [Finite G] {E : Subgroup G}
    (hE : IsElementaryAbelian 2 ↥E) {r : ℕ} (hr : Nat.card ↥E = 2 ^ r) : r ≤ CFSG.pRank 2 G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hE, hr⟩
  rintro r' ⟨B, -, hB⟩
  calc r' ≤ 2 ^ r' := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
