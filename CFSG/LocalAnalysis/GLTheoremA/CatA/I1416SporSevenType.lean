module

public import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder504
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrderDvd2520
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.GH74.KGroups CFSG.GH74.KGroups.L28 CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin
  CFSG.Blueprint


theorem card_centralizer_conj' {Y : Type} [Group Y] [Finite Y] (g x : Y) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set Y)) := by
  rw [CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_conj g x,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem card_mulAut_of_equiv_L28 {K : Type} [Group K]
    (e : K ≃* ↥CFSG.GH74.KGroups.L28.QP.originalSubgroup) : Nat.card (MulAut K) = 1512 := by
  have ho := orders_ok
  obtain ⟨M, -, hA⟩ := CFSG.GH74.KGroups.autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 3 (by norm_num)
    (by norm_num) ws ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1)
    ((orderIs_iff _ (by norm_num)).1 ho.2.1) ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok
    norm_ok cent_ok e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem nonempty_equiv_L28_of_catalog_A1 {T : Type} [Group T] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq8 : q.card = 8)
    (e : T ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :
    Nonempty (T ≃* ↥CFSG.GH74.KGroups.L28.QP.originalSubgroup) := by
  obtain ⟨p, k, hp, hk⟩ := q
  have hc : p ^ k = 8 := by
    have := TauCeti.PrimePower.card_def ⟨p, k, hp, hk⟩
    rw [hq8] at this
    exact this.symm
  have hp2 : p = 2 := by
    have hd : p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hc]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  subst hp2
  have hk3 : k = 3 := by
    have : (2 : ℕ) ^ k = 2 ^ 3 := by rw [hc]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  subst hk3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := equiv_psl_P
  exact ⟨((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 ⟨2, 3, hp, hk⟩ hv)).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 3 (by norm_num) card_GF8)
      (Fin 2)).symm).trans e1⟩

theorem chev_card_dvd_2520_cases (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    {r : ℕ} (hC : IsChevSimple r T) (hd : Nat.card T ∣ 2520) :
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
    have hm := OrderDvd2520.lieOrderFormula_dvd_2520 d.2 (hn ▸ hd)
    simp only [OrderDvd2520.ords, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h
    · omega
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
        rw [hcn] at hd
        revert hd
        decide
    | _ => exact hi.elim

theorem not_sq_seven_dvd_card_mulAut_of_chev
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    {r : ℕ} (hC : IsChevSimple r T) (hd : Nat.card T ∣ 2520) :
    ¬ 7 ^ 2 ∣ Nat.card (MulAut T) := by
  rcases chev_card_dvd_2520_cases hb hnab hC hd with h | h | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
    rw [CFSG.GH74.KGroups.A5.card_mulAut e']
    norm_num
  · exact not_sq_seven_dvd_card_mulAut_of_card_168 h
  · obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 (K := T) ⟨e⟩
    rw [CFSG.GH74.KGroups.A6.card_mulAut e']
    norm_num
  · rw [card_mulAut_of_equiv_L28 e]
    norm_num

theorem typeOK_seven_of_card_dvd_2520
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hd : Nat.card T ∣ 2520) : TypeOK 7 T :=
  fun hC h49 _ => absurd h49 (not_sq_seven_dvd_card_mulAut_of_chev hb hnab hC hd)

theorem qtypeOK_seven_of_card_dvd_2520
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a)
    (hd : Nat.card T ∣ 2520) : CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeOK 7 T :=
  fun _ _ _ _ hC hA => not_sq_seven_dvd_card_mulAut_of_chev hb hnab hC hd
    (CFSG.LocalAnalysis.GLTheoremA.I1416QRows.sq_dvd_card_mulAut_of_elemAb (by norm_num) hA)

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
