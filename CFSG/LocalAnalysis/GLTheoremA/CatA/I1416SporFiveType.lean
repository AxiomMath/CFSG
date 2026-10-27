module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSevenType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd241920
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder720
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA


theorem chev_card_dvd_241920_cases (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    {r : ℕ} (hC : IsChevSimple r T) (hd : Nat.card T ∣ 241920) (hle : Nat.card T ≤ 5040) :
    Nat.card T = 60 ∨ Nat.card T = 168 ∨
      (Nat.card T = 360 ∧ Nonempty (T ≃* ↥(alternatingGroup (Fin 6)))) ∨
      (Nat.card T = 504 ∧ Nonempty (T ≃* ↥CFSG.GH74.KGroups.L28.QP.originalSubgroup)) := by
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hlie : ∀ d : TauCeti.ValidLieTypeIndex, Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) →
      Nat.card T = 60 ∨ Nat.card T = 168 ∨
        (Nat.card T = 360 ∧ Nonempty (T ≃* ↥(alternatingGroup (Fin 6)))) ∨
        (Nat.card T = 504 ∧ Nonempty (T ≃* ↥CFSG.GH74.KGroups.L28.QP.originalSubgroup)) := by
    intro d ⟨e⟩
    have hn := hb d T ⟨e⟩
    have hm := OrderDvd241920.lieOrderFormula_dvd_241920 d.2 (hn ▸ hd)
    simp only [OrderDvd241920.ords, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · exact Or.inl (hn.trans h)
    · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
        Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [hn, h]; norm_num))).elim
    · exact Or.inr (Or.inl (hn.trans h))
    · exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2 h).elim
    · obtain ⟨q, hdq, hq8⟩ := Order504.lieOrderFormula_eq_504 d.2 h
      obtain ⟨d, hv⟩ := d
      simp only at hdq
      subst hdq
      exact Or.inr (Or.inr (Or.inr ⟨hn.trans h, nonempty_equiv_L28_of_catalog_A1 q hv hq8 e⟩))
    · exact (Order720.lieOrderFormula_ne_720 d.2 h).elim
    · omega
    · omega
    · omega
  rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d => exact hlie d ⟨e⟩
    | _ => exact hi.elim
  · cases i with
    | lie d => exact hlie d ⟨e⟩
    | alternating n hn5 =>
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl (by rw [hcn]; decide)
      · exact Or.inr (Or.inr (Or.inl ⟨by rw [hcn]; decide, ⟨e⟩⟩))
      · exfalso
        rw [hcn] at hle
        revert hle
        decide
    | _ => exact hi.elim

theorem not_sq_five_dvd_card_mulAut_of_chev_241920
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    {r : ℕ} (hC : IsChevSimple r T) (hd : Nat.card T ∣ 241920) (hle : Nat.card T ≤ 5040) :
    ¬ 5 ^ 2 ∣ Nat.card (MulAut T) := by
  rcases chev_card_dvd_241920_cases hb hnab hC hd hle with h | h | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
    rw [CFSG.GH74.KGroups.A5.card_mulAut e']
    norm_num
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨h8, hP⟩ := sylow7_facts_168 h
    obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
    have hdvd := card_mulAut_dvd_factorial (hP P).2
    rw [h8] at hdvd
    intro h25
    have := h25.trans hdvd
    revert this
    decide
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 (K := T) ⟨e⟩
    rw [CFSG.GH74.KGroups.A6.card_mulAut e']
    norm_num
  · rw [card_mulAut_of_equiv_L28 e]
    norm_num

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
