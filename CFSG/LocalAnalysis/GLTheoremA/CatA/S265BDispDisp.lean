module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispAlpha
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeUni
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispOrd
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispNum
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispWit
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispCls
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BDispExc
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BRank
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieInn
import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdList
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (CompIdxAt lieCompIdx_linear lieCompIdx_unitary
  lieCompIdx_classicalBCD lieCompIdx_triality lieCompIdx_excUntwisted lieCompIdx_excTwisted)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge LieSemisimpleCent fixSubgroup
  lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (lieSemisimpleCent)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (bal209TwoInnerCompType_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.Milestones (cl_lit_griess_schur_multipliers_all_models_statement)

private theorem lie_field (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group)
    {G : Type} [Group G] [Finite G] (hS : IsSimpleGroup G) (hnc : ∃ a b : G, a * b ≠ b * a)
    {e : TauCeti.LieTypeIndex} {hv : e.Valid} (f : G ≃* (TauCeti.CFSGIndex.lie ⟨e, hv⟩).Group)
    (hd : e.characteristic = 2) {α : MulAut G} (hα : α ∈ innAutDerived G)
    (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {J : Subgroup G} (hJ : GLAPComponent 3 (fixSubgroup α) J)
    (hJT : catalogIs (PSimple 3 J) fun i => S9.isU5two i ∨ S9.isU6two i) {k : ℕ}
    (hk : k = 13685760 ∨ k = 9196830720) (hdvd : k ∣ Nat.card G) (hlt : k < Nat.card G) :
    KD264Lie.fieldSize e = 2 ∧ 11 ∣ lieOrderFormula e ∧ 13685760 < lieOrderFormula e := by
  obtain ⟨i, J', hrel, ⟨φ⟩, i', hi', hf⟩ := H1431c.lieSInn_component_index hL hS hnc ⟨e, hv⟩ hd
    f (hI ⟨e, hv⟩ hd) hα hα3 hα1 ⟨J, hJ, hJT⟩
  have hfs := fieldSize_two_of_compRelC_unTwo hB ⟨e, hv⟩ hd i hrel φ (hi'.elim
    (fun h => .inl (CatDistinct.card_isU5two hB ⟨i', h, hf⟩))
    fun h => .inr (CatDistinct.card_isU6two hB ⟨i', h, hf⟩))
  rw [hB ⟨e, hv⟩ G ⟨f⟩] at hdvd hlt
  rcases hk with rfl | rfl
  · exact ⟨hfs, dvd_trans (by norm_num) hdvd, hlt⟩
  · exact ⟨hfs, dvd_trans (by norm_num) hdvd, (by norm_num : 13685760 < 9196830720).trans hlt⟩


theorem qsBRes_of_branches (hSp : QSBResSp10) (hOm : QSBResOm10m) (hU6 : QSBResU6two)
    (hE6 : QSBResTwE6) (hR1 : TwE6U5Inv) : QSBRes := by
  intro Ω _ _ S B T x D K hN hK hB hT
  by_cases hc : (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)
  · exact (hN.false_of_comm_le_centralizer hK hB hT hc).elim
  have hk : Nat.card (PSimple 3 K) = 13685760 ∨ Nat.card (PSimple 3 K) = 9196830720 :=
    hK.imp (CatDistinct.card_isU5two lieOrderBridge_holds)
      (CatDistinct.card_isU6two lieOrderBridge_holds)
  have h3 : 3 ∣ Nat.card ↥K := by
    have hKK : Nat.card (PSimple 3 K) ∣ Nat.card ↥K :=
      (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)
    refine dvd_trans ?_ hKK
    rcases hk with h | h <;> rw [h] <;> norm_num
  obtain ⟨d₀, hdD, hdx, hd3, hcs, hKd, _, hα3, hα1, hder, hJ, ⟨e⟩, hdvd, hlt⟩ :=
    hN.exists_alphaD h3
  obtain ⟨hsimp, hnc⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hN.cfg.comp
  obtain ⟨i, hi, ⟨f⟩⟩ := hN.cfg.chev.resolve_right fun ⟨_, hi, ⟨f⟩⟩ => by
    have := GLTheoremB.MovingAround.Inputs141c.card_le_of_ambiguousChev_two hi f
    rcases hk with h | h <;> rw [h] at hlt <;> omega
  cases i with
  | lie d =>
    obtain ⟨e', hv⟩ := d
    obtain ⟨hfs, h11, h13⟩ := lie_field lieSemisimpleCent lieOrderBridge_holds
      (I1431C2.compIdxAt_three_of_families lieCompIdx_linear lieCompIdx_unitary
        lieCompIdx_classicalBCD lieCompIdx_triality lieCompIdx_excUntwisted lieCompIdx_excTwisted)
      hsimp hnc f hi hder hα3 hα1 hJ
      (hK.elim (fun ⟨j, h, ⟨g⟩⟩ => ⟨j, .inl h, ⟨e.symm.trans g⟩⟩)
        fun ⟨j, h, ⟨g⟩⟩ => ⟨j, .inr h, ⟨e.symm.trans g⟩⟩) hk hdvd hlt
    have hW := hN.cfg.false_of_lieWit cl_lit_griess_schur_multipliers_all_models_statement hB.le f
    rcases cases_of_eleven hv hi hfs h11 h13 with ⟨n, q, rfl, hq, hn⟩ | ⟨n, q, rfl, hq, hn⟩ |
        ⟨n, q, rfl, hq, hn⟩ | ⟨n, q, rfl, hq, hn⟩ | ⟨n, q, rfl, hq, hn⟩ | ⟨q, rfl, hq⟩ |
        ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
    · exact (hW (fun h => absurd h.2 (by omega)) (exists_twoLocal_five_A hv hq hn)).elim
    · rcases hn.eq_or_lt with rfl | h6
      · exact hU6 Ω S B T x D K hN ⟨.lie ⟨.twistedA 5 q, hv⟩, hq, ⟨f⟩⟩ hK hB hc
      · haveI := hsimp
        haveI := f.injective.nontrivial
        obtain ⟨eL⟩ := HStdList.centerQuot_equiv_of_pSimple hN.cfg.quasi f
        obtain ⟨E, hE, h5, hZ, hTL⟩ :=
          T171S.uniHighWit_of_griess cl_lit_griess_schur_multipliers_all_models_statement n q hv hq h6 _
            hN.cfg.quasi ⟨eL⟩
        exact (hN.cfg.false_of_twoLocal_five hB.le hE h5.ge hZ hTL).elim
    · rcases hn.eq_or_lt with rfl | h6
      · exact hSp Ω S B T x D K hN ⟨.lie ⟨.B 5 q, hv⟩, hq, ⟨f⟩⟩ hK hB hc
      · exact (hW (fun h => absurd h.1 (by omega)) (exists_twoLocal_five_B hv hq h6)).elim
    · exact (hW id (exists_twoLocal_five_D hv hq hn)).elim
    · rcases hn.eq_or_lt with rfl | h6
      · exact hOm Ω S B T x D K hN ⟨.lie ⟨.twistedD 5 q, hv⟩, hq, ⟨f⟩⟩ hK hB hc
      · exact (hW id (exists_twoLocal_five_twistedD hv hq h6)).elim
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := Finite.of_equiv _ f.toEquiv
      exact (hW id (exists_twoLocal_five_exc.1 q hv hq)).elim
    · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := Finite.of_equiv _ f.toEquiv
      exact (hW id (exists_twoLocal_five_exc.2 q hv hq)).elim
    · have hS : catalogIs (PSimple 3 S) S9.isTE6two := ⟨.lie ⟨.twistedE6 q, hv⟩, hq, ⟨f⟩⟩
      rcases hK with hK5 | hK6
      · exact (hN.false_of_twE6_u5two bal209TwoInnerCompType_holds lieOrderBridge_holds hR1 hS
          hK5 hB.le hdD hdx hd3 hcs hKd).elim
      · exact hE6 Ω S B T x D K hN hS hK6 hB hc
  | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.S265

end
