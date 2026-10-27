module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder240
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder720
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder120
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem typeOK_three_of_card_dvd_720
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 720) :
    TypeOK 3 T := by
  intro hC h9 _
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 60 ∨ Nat.card T = 72 ∨ Nat.card T = 80 ∨ Nat.card T = 144 ∨
      Nat.card T = 90 ∨ Nat.card T = 120 ∨ Nat.card T = 180 ∨ Nat.card T = 240 ∨
      Nat.card T = 360 ∨ Nat.card T = 720 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc12 : c ≤ 12 := by
      by_contra h
      have : Nat.card T * 13 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  rcases hcases with h | h | h | h | hrest
  · exfalso
    obtain ⟨fA⟩ := CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h
    obtain ⟨e'⟩ := CFSG.GH74.KGroups.A5.equiv_of_alt fA
    rw [CFSG.GH74.KGroups.A5.card_mulAut e'] at h9
    norm_num at h9
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [h]; norm_num))).elim
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_five (by norm_num) (a := 4) (b := 1) (by rw [h]; norm_num))).elim
  · exact (hns (CFSG.LocalAnalysis.GLTheoremA.KDSpor.isSolvable_of_card_eq Nat.prime_two
      Nat.prime_three (by norm_num) (a := 4) (b := 2) (by rw [h]; norm_num))).elim
  · have hlie : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
        Nonempty (T ≃* (TauCeti.CFSGIndex.lie d).Group) → False := by
      intro d hd2 he
      have hn := hb d T he
      obtain ⟨v, M, hv, hM⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.lie_char_part d.1 d.2
      rw [hd2] at hv hM
      have hsmall : ∀ N : ℕ, CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d.1 = N → N ≤ 720 → (N = 90 ∨ N = 180) → False := by
        intro N hN hle hN'
        rw [hN] at hv
        have hv10 : v < 10 := by
          by_contra hv10
          have : 2 ^ 10 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hM0 : 0 < M := by rcases Nat.eq_zero_or_pos M with h0 | h0 <;> simp_all
          nlinarith
        rcases hN' with rfl | rfl <;> interval_cases v <;> omega
      rcases hrest with h | h | h | h | h | h
      · exact hsmall 90 (hn.symm.trans h) (by norm_num) (Or.inl rfl)
      · exact Order120.lieOrderFormula_ne_120 d.2 (hn.symm.trans h)
      · exact hsmall 180 (hn.symm.trans h) (by norm_num) (Or.inr rfl)
      · exact Order240.lieOrderFormula_ne_240 d.2 (hn.symm.trans h)
      · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieOrderFormula_ne_360 d.2
          (hn.symm.trans h)
      · exact Order720.lieOrderFormula_ne_720 d.2 (hn.symm.trans h)
    rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
    · cases i with
      | lie d => exact (hlie d hi ⟨e⟩).elim
      | _ => exact hi.elim
    · cases i with
      | lie d =>
        exfalso
        have hn := hb d T ⟨e⟩
        have hval := CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.amb_lie_order 2 d.1 d.2 hi
        rcases hrest with h | h | h | h | h | h <;> rw [h] at hn <;>
          rcases hval with h' | h' | h' | h' <;> omega
      | alternating n hn5 =>
        have hcn : Nat.card T = n.factorial / 2 :=
          (Nat.card_congr e.toEquiv).trans
            (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
        have hn6 : n = 6 := by
          rcases Nat.lt_or_ge n 7 with hlt | hge
          · interval_cases n <;> simp [Nat.factorial] at hcn <;> omega
          · have h7 : Nat.factorial 7 ∣ n.factorial := Nat.factorial_dvd_factorial hge
            have : 2520 ≤ n.factorial / 2 := by
              have := Nat.le_of_dvd (Nat.factorial_pos n) h7
              simp [Nat.factorial] at this
              omega
            rcases hrest with h | h | h | h | h | h <;> omega
        subst hn6
        exact ⟨rfl, TauCeti.CFSGIndex.alternating 6 hn5, Or.inl rfl, ⟨e⟩⟩
      | _ => exact hi.elim

theorem compOK_three_of_card_dvd_2160
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 2160) : CompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 2160 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact typeOK_three_of_card_dvd_720 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

section Ru

open CFSG.Sporadic.Schreier CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.RuStd.S2


theorem row_Ru_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .Ru 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Ru ≃* ↥ruP := ruEquivP
  have hfin : Finite ↥ruP := Finite.of_equiv _ e.toEquiv
  have hs : IsSimpleGroup ↥ruP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e.symm
  have hc : Nat.card ↥ruP = 145926144000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hpr : ¬ (Nat.card ↥ruP).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥ruP, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥ruP _ hfin hs hpr
  have b : ↥ruP ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group := e.symm.trans (hbr .Ru).some
  obtain ⟨hC0eq, hC0card⟩ := ruThreeC0_spec
  have hcard0 : Nat.card (Subgroup.centralizer ({ruThreeX0} : Set ↥ruP)) = 2160 := by
    have hmapc := CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype ruP ruThreeX0
    rw [← Subgroup.card_map_of_injective ruP.subtype_injective, hmapc, ← hC0card, hC0eq]
    rfl
  refine @row_of_model .Ru 3 ↥ruP _ hfin hs hOut b hnc fun k hk => ?_
  obtain ⟨c, hcz⟩ := exists_conj_ruThree k hk
  have hk' : orderOf (c * ruThreeX0 * c⁻¹) = 3 := by
    rw [← Nat.card_zpowers, hcz, Nat.card_zpowers, hk]
  have hcent : Subgroup.centralizer ({k} : Set ↥ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ↥ruP) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.centralizer_singleton_eq_of_zpowers hcz).symm
  refine CompOK.of_centralizer_eq hcent.symm ?_
  refine compOK_three_of_card_dvd_2160 hb hk' ?_
  rw [CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.centralizer_conj c ruThreeX0,
    Subgroup.card_map_of_injective (MulAut.conj c).injective, hcard0]

end Ru

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
