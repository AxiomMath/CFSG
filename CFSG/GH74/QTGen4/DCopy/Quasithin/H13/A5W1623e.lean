module

public import CFSG.Quasithin.H13.A5W1623e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1620Tc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (quotPCore_subgroupOf_equiv pRank_subgroupOf_eq
  map_oPrimeResidualOf_top)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem eq_oPrime_of_sl4_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (e4 : ↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    K = oPrimeResidualOf 3 (Subgroup.centralizer ({S.v12} : Set G)) := by
  have hl := SBc5.isPSL_two_of_statedSL (n := 4) (by norm_num) e4
  have hX := hKF.l42 _ hl
  have hcard : Nat.card ↥(S.plus K) = 20160 := by
    rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  let eX : ↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K) ≃* ↥(S.plus K) :=
    quotCenterEquivOfEqBot hX.center_eq_bot
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 :=
    (Nat.card_congr eX.toEquiv).trans hcard
  obtain ⟨hq, hZ⟩ := S.kbar_cases_big_F4 h1222 h517 hF h36 h37 h38 hK hYz hT (Or.inl hN)
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hqP := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  have hnt : Nontrivial ↥(S.plus K) := by
    obtain ⟨a, b, hab⟩ := hqP.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hker := ker_le_center_of_isQuasisimple hq π hπ hnt
  have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
  let eA : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥(S.plus K) :=
    (centerQuotEquiv π hπ hker).trans eX
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
      (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF)
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  rcases hZ with hZ | hZ3
  · exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38' hGv hK hq
      ((quotCenterEquivOfEqBot hZ).symm.trans eA) hX
  · have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60480 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _),
        Nat.card_congr eA.toEquiv, hZ3, hcard]
    refine eq_oPrime_of_center_three hF318 h36 h38' hGv hK hq hZ3 hX eA ?_
      (fun Y _ hY => hcK ▸ card_hat_ne_60480 hY)

    intro s q hSL
    have hcK' : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 * 20160 := hcK
    cases s
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK' ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := card_statedSU_three_of hK'
      rw [← Nat.card_congr eK.toEquiv, hcK'] at h2
      exact (sl3_su3_card_big hq2).1 h2.symm
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
      rw [← Nat.card_congr eK.toEquiv, hcK', hK'] at h2
      have hq2 : 2 ≤ q := hK' ▸ Finite.one_lt_card
      have hq4 := (sl3_su3_card_big hq2).2.2.2 h2.symm
      have hP := isPSL_quot_center_of_statedSL (hK'.trans hq4) eK
      exact hX.noImage _ true 2 2 Nat.prime_two (by norm_num) hP (by decide)
        (eA.toMonoidHom.comp (MonoidHom.id _)) eA.surjective

end Setting

theorem o3Prime1367_of_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) : O3Prime1367_F4 := by
  intro G _ _ T L V S hH K hK hYz hT ⟨e4⟩
  exact S.eq_oPrime_of_sl4_F4 h1222 h517 hF318 h36 h37 h38 hKF hH.hF hK hYz hT e4

end CFSG.Quasithin.H13.A5
