module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddL28Abstract
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddInner
public import CFSG.Quasithin.Background.F6ResL28

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.F6 CFSG.Assembly.LowTwoRank

section L28

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
    decide +kernel
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
