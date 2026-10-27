module

public import CFSG.LargeExtraspecial.S97RYSound
public import CFSG.LargeExtraspecial.S97RYData
public import CFSG.LargeExtraspecial.S97RXMain
public import CFSG.CGT.Timmesfeld75.ListWCMathieu

public section

namespace CFSG.LargeExtraspecial.S11

open CFSG.CGT.Timmesfeld75 CFSG.Sporadic.Th CFSG.Blueprint PairCheck

@[expose] def A9PairCheck : Prop := pairCheck a9PData = true

@[expose] def M22PairCheck : Prop := pairCheck m22PData = true

section A9

abbrev a9a : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [0, 1, 2], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

abbrev a9b : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8], by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

noncomputable def a9gen (l : ℤ) : alternatingGroup (Fin 9) :=
  if l = 1 then a9a else if l = -1 then a9a⁻¹ else if l = 2 then a9b else
    if l = -2 then a9b⁻¹ else 1

theorem rep_a9gen (l : ℤ) : CFSG.Sporadic.Th.Rep 9 (a9gens l) (a9gen l) := by
  unfold a9gens a9gen
  split_ifs
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · unfold CFSG.Sporadic.Th.Rep
    decide
  · exact Rep.idT (by norm_num)

theorem a9gen_neg (l : ℤ) : a9gen (-l) = (a9gen l)⁻¹ := by
  unfold a9gen
  split_ifs <;> first | omega | simp_all

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 2 ^ a9PData.D.pc.length * 2835 := by
  rw [show 2 ^ a9PData.D.pc.length * 2835 = 181440 from rfl, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem a9_pairProp (h : A9PairCheck) {T : Subgroup (alternatingGroup (Fin 9))} (hT : IsWC T)
    (h8 : Nat.card T = 8) : PairProp T 1 true :=
  pairProp_of_pairCheck (P := a9PData) (M := alternatingGroup (Fin 9)) rep_a9gen a9gen_neg
    ⟨2835, by decide, card_alt9⟩ h hT h8

end A9

theorem a9WCPairFact_of (h : A9PairCheck) : A9WCPairFact := by
  intro Λ _ _ he T hT h8
  obtain ⟨e⟩ := he
  have hcard : Nat.card (T.map e.toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, h8]
  obtain ⟨c, hc, hp⟩ := PairProp.of_map e (a9_pairProp h (hT.map_mulEquiv e) hcard)
  exact ⟨c, Subgroup.card_eq_one.1 hc, hp rfl⟩

theorem m22_pairProp (h : M22PairCheck)
    {T : Subgroup NativeSporadic.M22} (hT : IsWC T) (h16 : Nat.card T = 16) :
    PairProp T 4 false :=
  pairProp_of_pairCheck (P := m22PData) (M := NativeSporadic.M22) rep_m22gen m22gen_neg
    ⟨3465, by decide, by
      rw [show 2 ^ m22PData.D.pc.length * 3465 = 443520 from rfl]
      exact CFSG.Sporadic.Mathieu.card_M22⟩ h hT h16

theorem m22WCPairFact_of (h : M22PairCheck) :
    M22WCPairFact := by
  intro Λ _ _ he T hT h16
  obtain ⟨e⟩ : Nonempty (Λ ≃* NativeSporadic.M22) := he
  have hcard : Nat.card (T.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective e.injective, h16]
  obtain ⟨c, hc, -⟩ := PairProp.of_map e (m22_pairProp h (hT.map_mulEquiv e) hcard)
  refine ⟨c, fun hbot => ?_, by rw [hc, h16]⟩
  rw [hbot, Subgroup.card_bot] at hc
  exact absurd hc (by decide)

end CFSG.LargeExtraspecial.S11
