module

public import CFSG.Quasithin.H13.A6Producer4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G]

open scoped IsMulCommutative in

theorem exists_setting4_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4) [CFSG.GH74.QTGen4.Finite4 G]
    {T L V : Subgroup G} (h : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1

  have hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
      obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLV
      exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
    · exact h6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
    · exact (h13316 G T L h hu).elim
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
    centralQuot := hA6
    frame := F }⟩

end CFSG.Quasithin.H13.A6
