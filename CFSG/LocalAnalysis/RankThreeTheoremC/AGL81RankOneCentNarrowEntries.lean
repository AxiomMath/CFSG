module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCriteria
public import CFSG.LieType.SeitzGeneration.SeitzStatus
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Model
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Gen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open

section Seitz


theorem narrowGamma_eq_top_of_seitz_rank {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center K = ⊥)
    (h2 : 2 ≤ Open.pRank p (⊤ : Subgroup K)) (T : Sylow p K) :
    narrowGamma p (T : Subgroup K) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, -, hA, hAc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  exact narrowGamma_eq_top_of_le_sylow hp (MulEquiv.refl K) hA.isPGroup
    (narrowGamma_eq_top_of_seitz CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hp hp2 hpd
      hexc e hZ le_rfl hA hAc) T

theorem narrowGamma_eq_top_g28 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q) {K : Type} [Group K]
    [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center K = ⊥)
    (T : Sylow 3 K) : narrowGamma 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨q, hq2, -, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .G2 q := hdq
  refine narrowGamma_eq_top_of_seitz_rank Nat.prime_three (by norm_num) ?_ ?_ e hZ
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_G2 hv e) T
  · change 3 ≠ (TauCeti.LieTypeIndex.G2 q).characteristic
    rw [TauCeti.LieTypeIndex.characteristic_G2]
    omega
  · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

theorem narrowGamma_eq_top_sp48 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q) {K : Type} [Group K]
    [Finite K] (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center K = ⊥)
    (T : Sylow 3 K) : narrowGamma 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨q, hq2, -, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .B 2 q := hdq
  refine narrowGamma_eq_top_of_seitz_rank Nat.prime_three (by norm_num) ?_ ?_ e hZ
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_B2 hv e) T
  · change 3 ≠ (TauCeti.LieTypeIndex.B 2 q).characteristic
    rw [TauCeti.LieTypeIndex.characteristic_B]
    omega
  · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

theorem two_le_pRank_five_reeF4 {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .reeF4 2) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : 2 ≤ Open.pRank 5 (⊤ : Subgroup K) := by
  have hX := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 hd
  obtain ⟨a, L, _, _, _, -, hfa, hL, ⟨f⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
  obtain rfl : a = 2 := by omega
  obtain ⟨E, hE, hc⟩ := CFSG.AGLEmbedding.exists_elemAbelian_twentyfive_reeGamma (K := L) hL
  let g : K ≃* _ := e.trans f
  exact CFSG.SectionRank.le_pRank (by norm_num) (le_top : E.map g.symm.toMonoidHom ≤ ⊤)
    (hE.map _) (by rw [Subgroup.card_map_of_injective g.symm.injective, hc])

theorem narrowGamma_eq_top_reeF4 {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1 = .reeF4 2) {K : Type} [Group K] [Finite K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center K = ⊥) (T : Sylow 5 K) :
    narrowGamma 5 (T : Subgroup K) = ⊤ := by
  refine narrowGamma_eq_top_of_seitz_rank Nat.prime_five (by norm_num) ?_ ?_ e hZ
    (two_le_pRank_five_reeF4 hd e) T
  · rw [hd, TauCeti.LieTypeIndex.characteristic_reeF4]
    norm_num
  · rw [hd]
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]

end Seitz

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier CFSG.RankThree.Native in
theorem narrowGamma_eq_top_onan
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group)) (T : Sylow 7 K) :
    narrowGamma 7 (T : Subgroup K) = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  obtain ⟨eK⟩ := hK
  have hQP : onSevenQ ≤ Pv := onSeven_mem_P.1
  obtain ⟨E₀, hE₀Q, hE₀, hE₀2⟩ := exists_isElemAbelian_card_sq_of_card_cube (X := Pv) (p := 7)
    (E := onSevenQ.subgroupOf Pv)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, card_onSevenQ]; norm_num)
    fun x hx => Subtype.ext (by simpa using onSevenQ_pow_seven (Subgroup.mem_subgroupOf.1 hx))
  have hE₀F : E₀ ≤ on7F 0 := fun x hx =>
    Subgroup.mem_subgroupOf.2 (onSevenQ_le_F0 (Subgroup.mem_subgroupOf.1 (hE₀Q hx)))
  obtain ⟨S, hS⟩ := on7_sevenModel.syl
  refine narrowGamma_eq_top_of_sylow (by norm_num) ((onEquivPv.symm.trans b).trans eK.symm) S ?_ T
  rw [hS]
  exact narrowGamma_eq_top_of_sevenModel on7_sevenModel hE₀F hE₀ hE₀2

open CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Fi24 in
theorem narrowGamma_eq_top_fi24
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)) (T : Sylow 7 K) :
    narrowGamma 7 (T : Subgroup K) = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcx : Commute Fi7.C7 Fi7.X7 := Fi7.fi7_cube.2.2.2.1
  have hc7 : Fi7.C7 ^ 7 = 1 := Fi7.C7_pow_seven
  have hx7 : Fi7.X7 ^ 7 = 1 := Fi7.fi7_cube.1
  have hxc : Fi7.X7 ∉ Subgroup.zpowers Fi7.C7 := by
    simpa [Fi7.cube7] using Fi7.cube7_not_mem_zpowers (t := 49) (by norm_num) (by norm_num)
  have hE : IsElemAbelian 7 (Subgroup.closure ({Fi7.C7, Fi7.X7} : Set J)) :=
    @IsElemAbelian.closure_of_commute J (Subgroup.toGroup _) 7 _
      (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hcx, hcx.symm, rfl])
      (by rintro a (rfl | rfl); exacts [hc7, hx7])
  have hE49 : Nat.card (Subgroup.closure ({Fi7.C7, Fi7.X7} : Set J)) = 7 ^ 2 :=
    card_closure_pair_sq hcx hc7 hx7 Fi7.C7_ne_one hxc
  have hEQ : Subgroup.closure ({Fi7.C7, Fi7.X7} : Set J) ≤ Fi7.Q7 := by
    rw [Subgroup.closure_le]
    rintro a (rfl | rfl)
    · exact Fi7.sevenLine_c.mem
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
  have D : SevenModel J 7 Fi7.Q7 Fi7.C7 Fi7.gens7 :=
    ⟨Fi7.sevenLine_c, Fi7.Q7_sylow, Fi7.fi7_gens_top, Fi7.fi7_gens_good,
      Fi7.fi7_rankOK Fi7.fi7_order_four⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  obtain ⟨eK⟩ := hK
  obtain ⟨S, hS⟩ := Fi7.Q7_sylow
  have hΓ := @narrowGamma_eq_top_of_sevenModel 7 J (Subgroup.toGroup _) inferInstance _ _ _ _ D _
    hEQ hE hE49
  refine @narrowGamma_eq_top_of_sylow 7 J K (Subgroup.toGroup _) inferInstance _ _ (by norm_num)
    ((fi24EquivJ.symm.trans e).trans eK.symm) S ?_ T
  rw [hS]
  exact hΓ

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
