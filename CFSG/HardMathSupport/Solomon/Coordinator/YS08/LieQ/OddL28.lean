module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28Abstract
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddInner
public import CFSG.Quasithin.Background.F6ResL28
import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.F6 CFSG.Assembly.LowTwoRank

section L28

open L28Res in
@[expose] def g8T (a b c d : ℕ) : T8 :=
  (CFSG.Quasithin.GF8.ofNat' a, CFSG.Quasithin.GF8.ofNat' b, CFSG.Quasithin.GF8.ofNat' c,
    CFSG.Quasithin.GF8.ofNat' d)

open L28Res in
@[expose] def g8Wits : List T8 :=
  [g8T 0 1 1 1, g8T 0 6 3 3, g8T 0 7 4 4, g8T 0 2 5 5, g8T 0 3 6 6, g8T 0 4 7 7,
    g8T 0 5 2 2, g8T 0 1 1 0, g8T 0 6 3 0, g8T 0 7 4 0, g8T 0 2 5 0, g8T 0 3 6 0,
    g8T 0 4 7 0, g8T 0 5 2 0, g8T 0 1 1 3, g8T 0 6 3 5, g8T 0 7 4 7, g8T 0 2 5 4,
    g8T 0 3 6 1, g8T 0 4 7 2, g8T 0 5 2 6, g8T 0 1 1 2, g8T 0 6 3 6, g8T 0 7 4 3,
    g8T 0 2 5 1, g8T 0 3 6 7, g8T 0 4 7 5, g8T 0 5 2 4, g8T 0 1 1 5, g8T 0 6 3 4,
    g8T 0 7 4 2, g8T 0 2 5 7, g8T 0 3 6 3, g8T 0 4 7 6, g8T 0 5 2 1, g8T 0 1 1 4,
    g8T 0 6 3 7, g8T 0 7 4 6, g8T 0 2 5 2, g8T 0 3 6 5, g8T 0 4 7 1, g8T 0 5 2 3,
    g8T 0 1 1 7, g8T 0 6 3 2, g8T 0 7 4 1, g8T 0 2 5 6, g8T 0 3 6 4, g8T 0 4 7 3,
    g8T 0 5 2 5, g8T 0 1 1 6, g8T 0 6 3 1, g8T 0 7 4 5, g8T 0 2 5 3, g8T 0 3 6 2,
    g8T 0 4 7 4, g8T 0 5 2 7]

open L28Res in
@[expose] def g8MkG (t : T8) : G8 := if h : tdet t = 1 then ⟨t, h⟩ else 1

open L28Res in
@[expose] def g8Y0 : G8 := g8MkG (g8T 0 1 1 1)

open L28Res in
theorem g8_conj3 : ∀ y : G8, y ≠ 1 → y ^ 3 = 1 →
    ∃ t ∈ g8Wits, g8MkG t * g8Y0 * (g8MkG t)⁻¹ = y := by
  decide +kernel

open L28Res in
theorem g8_cent_y0 : Fintype.card {x : G8 // x * g8Y0 = g8Y0 * x} = 9 := by
  decide +kernel

open L28Res in
theorem g8_cent_conj (g : G8) :
    Fintype.card {x : G8 // x * (g * g8Y0 * g⁻¹) = (g * g8Y0 * g⁻¹) * x} = 9 := by
  rw [← g8_cent_y0]
  symm
  refine Fintype.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun x => ?_)
  change x * g8Y0 = g8Y0 * x ↔
    (g * x * g⁻¹) * (g * g8Y0 * g⁻¹) = (g * g8Y0 * g⁻¹) * (g * x * g⁻¹)
  have e1 : g * x * g⁻¹ * (g * g8Y0 * g⁻¹) = g * (x * g8Y0) * g⁻¹ := by group
  have e2 : g * g8Y0 * g⁻¹ * (g * x * g⁻¹) = g * (g8Y0 * x) * g⁻¹ := by group
  rw [e1, e2, mul_left_inj, mul_right_inj]

open L28Res in
theorem g8_centralizer_nine (y : G8) (hy : orderOf y = 3) :
    Nat.card (Subgroup.centralizer ({y} : Set G8)) = 9 := by
  have h1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have h3 : y ^ 3 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have key : ∀ y : G8, y ≠ 1 → y ^ 3 = 1 → Fintype.card {x : G8 // x * y = y * x} = 9 := by
    intro y hy1 hy3
    obtain ⟨t, -, rfl⟩ := g8_conj3 y hy1 hy3
    exact g8_cent_conj (g8MkG t)
  have := key y h1 h3
  rw [← this, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    rw [Subgroup.mem_centralizer_singleton_iff])

theorem exists_equiv_g8 {S : Type} [Group S] (h : StatedClassicalModel S .PSL 2 2 3) :
    Nonempty (S ≃* L28Res.G8) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨g⟩ := L28Res.nonempty_equiv K (by rw [hcard]; norm_num)
  exact ⟨e.trans g⟩

theorem psl28Inner : Psl28Inner := by
  intro S _ _ hs hna h
  obtain ⟨e⟩ := exists_equiv_g8 h
  have hsG8 : IsSimpleGroup L28Res.G8 := (MulEquiv.isSimpleGroup_congr e).1 hs
  haveI : Finite L28Res.G8 := Finite.of_equiv S e.toEquiv
  exact ⟨(radRigidInner_three_of_centralizers L28Res.card_G8 g8_centralizer_nine).of_mulEquiv e.symm,
    (holds_three_of_centralizers hsG8 L28Res.card_G8 g8_centralizer_nine).of_mulEquiv e.symm⟩

@[expose] def Psl28Full : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    StatedClassicalModel S .PSL 2 2 3 → RadRigid 3 S ∧ Holds S 3

theorem psl28Full : Psl28Full := by
  intro S _ _ hs hna h
  obtain ⟨e⟩ := exists_equiv_g8 h
  have hsG8 : IsSimpleGroup L28Res.G8 := (MulEquiv.isSimpleGroup_congr e).1 hs
  haveI : Finite L28Res.G8 := Finite.of_equiv S e.toEquiv
  have hnaG8 : ∃ a b : L28Res.G8, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h'
  haveI : Finite (MulAut L28Res.G8) := L28Res.finite_mulAut
  have hAut : Nat.card (MulAut L28Res.G8) = 3 * Nat.card L28Res.G8 := by
    rw [L28Res.card_mulAut, L28Res.card_G8]
  exact ⟨(radRigid_three_of_centralizers hsG8 hnaG8 L28Res.card_G8 g8_centralizer_nine
      hAut).of_mulEquiv e.symm,
    (holds_three_of_centralizers hsG8 L28Res.card_G8 g8_centralizer_nine).of_mulEquiv e.symm⟩

end L28

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
