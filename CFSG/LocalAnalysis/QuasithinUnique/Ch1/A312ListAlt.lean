module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsSix
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Quasithin CFSG.QuasithinUnique.Unc25K1.Six

theorem isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  let _ : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem isSylowTwoOf_top_of_card {X : Type} [Group X] [Finite X] {T : Subgroup X} {a m : ℕ}
    (hT : Nat.card T = 2 ^ a) (hX : Nat.card X = 2 ^ a * m) (hm : ¬ 2 ∣ m) :
    CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, IsPGroup.of_card hT, ?_⟩
  rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T]
  have h := Subgroup.card_mul_index T
  rw [hT, hX] at h
  have hpos : 0 < 2 ^ a := pow_pos (by norm_num) a
  have hidx : T.index = m := Nat.eq_of_mul_eq_mul_left hpos h
  rwa [hidx]

theorem card_alt_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

noncomputable def T6 : Subgroup ↥A6s := D0.subgroupOf A6s

theorem card_T6 : Nat.card T6 = 8 := by
  rw [T6, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_A6).toEquiv, card_D0]

theorem isSylowTwoOf_T6 : CFSG.QuasithinUnique.IsSylowTwoOf T6 ⊤ :=
  isSylowTwoOf_top_of_card (a := 3) (m := 45) (by rw [card_T6]; norm_num)
    (by rw [card_alt_six]; norm_num) (by decide)

theorem isSolvable_of_overgroup_six
    (M : Subgroup ↥A6s) (hM : T6 ≤ M) (hne : M ≠ ⊤) :
    Group.IsSolvable ↥M := by
  have hY1 : D0 ≤ M.map A6s.subtype := fun x hx =>
    ⟨⟨x, D0_le_A6 hx⟩, hM (show (⟨x, D0_le_A6 hx⟩ : ↥A6s) ∈ D0.subgroupOf A6s from hx), rfl⟩
  have hY2 : M.map A6s.subtype ≤ A6s := Subgroup.map_subtype_le M
  have hcard : Nat.card (M.map A6s.subtype) = Nat.card M :=
    Subgroup.card_map_of_injective A6s.subtype_injective
  rcases six_overgroups _ hY1 hY2 with h | h | h | h
  · exact isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [← hcard, h, card_D0]; norm_num)
  · exact isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [← hcard, h, card_Sa]; norm_num)
  · exact isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [← hcard, h, card_Sb]; norm_num)
  · exfalso
    apply hne
    apply Subgroup.eq_top_of_card_eq
    rw [← hcard, h]

theorem alt6 : FamAlt6 := by
  intro X _ _ hq h
  obtain ⟨e⟩ := h
  have hqY : CFSG.IsQuasisimple ↥A6s := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  exact A312For.of_mulEquiv e
    (A312For.of_solvable_overgroups hqY T6 isSylowTwoOf_T6 isSolvable_of_overgroup_six)

end CFSG.QuasithinUnique.Vol2Native.A312L
