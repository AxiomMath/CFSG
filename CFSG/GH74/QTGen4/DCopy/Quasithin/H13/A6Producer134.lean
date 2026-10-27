module

public import CFSG.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

open scoped IsMulCommutative in

theorem exists_setting134_F4 (h1332 : Stmt13_3_2_F4) [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
    (h : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : Nonempty (Setting134 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1

  have hc : Nat.card V = 2 ^ 5 ∧
      FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥ := by
    rcases hmod with h1 | h2 | h3 | h4 | h5
    · exact absurd h1.2 hZV
    · exact absurd h2.2 hZV
    · exact ⟨h3.1, h3.2.2⟩
    · exact absurd h4.2.2 hZV
    · exact absurd h5.2.2 hZV
  obtain ⟨R⟩ := exists_rawData6 hLV hc.2
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 5) hc.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV

  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame5 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    frame := F }⟩

end CFSG.Quasithin.H13.A6
