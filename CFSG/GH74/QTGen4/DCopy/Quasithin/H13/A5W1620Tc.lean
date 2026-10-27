module

public import CFSG.Quasithin.H13.A5W1620Tc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1620P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622r

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd
  quotPCore_subgroupOf_equiv pRank_subgroupOf_eq map_oPrimeResidualOf_top)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_cases_big_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 9999360) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨
        Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) = 3) := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective
  have hcen : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      Nat.card (Subgroup.center ↥(modO2Image Gv K)) :=
    Nat.card_congr (Subgroup.centerCongr eX).toEquiv
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) hK
  rcases hA with ⟨hcomp, hsimp, -⟩ | ⟨hcomp, h3, -⟩ | h3 | h4
  · refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1, Or.inl ?_⟩
    have hZ : Subgroup.center ↥(modO2Image Gv K) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(modO2Image Gv K)) with h | h
      · exact h
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := hcomp.1
        apply hab
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        rw [(QuotientGroup.eq_one_iff a).mpr (h ▸ Subgroup.mem_top a),
          (QuotientGroup.eq_one_iff b).mpr (h ▸ Subgroup.mem_top b)]
    rw [hZ, Subgroup.card_bot] at hcen
    exact Subgroup.card_eq_one.mp hcen
  · exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1, Or.inr (by rw [hcen, h3])⟩
  · exfalso
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact sl2_order_ne_big hc1 hc2 hN hcard.symm
  · exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rcases hN with h | h <;> rw [h] at hcard <;> omega

theorem Lv_le_of_exclusion_big_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {X : Type} [Group X] [Finite X]
    (hX : A318Exclusion X) (e : ↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K) ≃* X)
    (hcard : Nat.card X = 20160 ∨ Nat.card X = 9999360) : S.Lv ≤ K := by
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = Nat.card X :=
    Nat.card_congr e.toEquiv
  obtain ⟨hq, hZ⟩ := S.kbar_cases_big_F4 h1222 h517 hF h36 h37 h38 hK hYz hT (hN ▸ hcard)
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
  let eA : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X :=
    (centerQuotEquiv π hπ hker).trans e
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian
      (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF)
  have h38' : A38ForSQTK := a38ForSQTK_of_cat h38
  refine S.Lv_le_of_eq_oPrime_or_theta ?_
  rcases hZ with hZ | hZ3
  · left
    exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 h38' hGv hK hq
      ((quotCenterEquivOfEqBot hZ).symm.trans eA) hX
  · refine eq_oPrime_or_theta_of_center_three' hF318 h36 h38' hGv hK hq hZ3 hX eA ?_

    have hcK : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 * Nat.card X := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center _),
        Nat.card_congr eA.toEquiv, hZ3, mul_comm]
    intro s q hSL
    cases s
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK' ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := card_statedSU_three_of hK'
      rw [← Nat.card_congr eK.toEquiv, hcK] at h2
      rcases hcard with h | h <;> rw [h] at h2
      · exact (sl3_su3_card_big hq2).1 h2.symm
      · exact (sl3_su3_card_big hq2).2.2.1 h2.symm
    ·
      obtain ⟨K', _, _, hK', ⟨eK⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K')
      rw [← Nat.card_congr eK.toEquiv, hcK, hK'] at h2
      have hq2 : 2 ≤ q := hK' ▸ Finite.one_lt_card
      rcases hcard with h | h <;> rw [h] at h2
      · have hq4 := (sl3_su3_card_big hq2).2.2.2 h2.symm
        have hP := isPSL_quot_center_of_statedSL (hK'.trans hq4) eK
        exact hX.noImage _ true 2 2 Nat.prime_two (by norm_num) hP (by decide)
          (eA.toMonoidHom.comp (MonoidHom.id _)) eA.surjective
      · exact (sl3_su3_card_big hq2).2.1 h2.symm

end Setting

theorem lemma13620L45_of_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) : Lemma13620L45_F4 := by
  intro G _ _ T L V S hH K hK hYz hT h45
  have hF := hH.hF
  rcases h45 with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hl := SBc5.isPSL_two_of_statedSL (n := 4) (by norm_num) e4
    have hX := hKF.l42 _ hl
    have hcard : Nat.card ↥(S.plus K) = 20160 := by
      rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    exact S.Lv_le_of_exclusion_big_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hX
      (quotCenterEquivOfEqBot hX.center_eq_bot) (Or.inl hcard)
  · obtain ⟨e5⟩ := h5
    have hl := SBc5.isPSL_two_of_statedSL (n := 5) (by norm_num) e5
    have hX := hKF.l52 _ hl
    have hcard : Nat.card ↥(S.plus K) = 9999360 := by
      rw [Nat.card_congr e5.toEquiv, ← Nat.card_congr
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
      decide
    exact S.Lv_le_of_exclusion_big_F4 h1222 h517 hF318 h36 h37 h38 hF hK hYz hT hX
      (quotCenterEquivOfEqBot hX.center_eq_bot) (Or.inr hcard)

end CFSG.Quasithin.H13.A5
