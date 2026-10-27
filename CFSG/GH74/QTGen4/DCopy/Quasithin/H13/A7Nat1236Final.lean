module

public import CFSG.Quasithin.H13.A7Nat1236Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1236Comp
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7NatMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7_centralizer_le_six_F4
    (h12212 : Stmt12_2_12_F4) (h1225 : Stmt12_2_5_F4)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hC27 : ASC27Statement_F4 G)
    (hC129 : ASC129Statement G) (hF : A318Facts) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecSix)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) :
    centralizer ({(e : G)} : Set G) ≤ normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, hKn, hQsyl, hC23, hHchar, hcgs, hLeMe, -, hLeq⟩ :=
    A7Le_comp_six_F4 h12212 h1225 a38ForSQTKCat_holds h39 hC27 hI1 hI2 hyp h he heZ
  have hMeM : hyp.Mv e ≤ normalizer (L : Set G) := inf_le_left
  have hLeH : hyp.Lv e ≤ hyp.Gv e := le_of_mem_cComp hK

  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, vec_one] at he
    exact absurd he (by decide)
  have he2 : orderOf (e : G) = 2 := by
    refine orderOf_eq_prime ?_ he1
    rw [pow_two]
    exact congrArg Subtype.val (sq_eq_one_of_vec ψ e)
  have hH2 : pCoreOf 2 (hyp.Gv e) ≠ ⊥ := by
    have hle : zpowers (e : G) ≤ pCoreOf 2 (hyp.Gv e) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) ?_
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one]))
      rw [normalizer_zpowers_eq_centralizer' he2]
    intro hbot
    apply he1
    have := hle (mem_zpowers (e : G))
    rw [hbot, mem_bot] at this
    exact this

  obtain ⟨-, hA6⟩ := quasisimple_Le_six h.L_le h.Lact h.Lonto hyp.quasisimple he rfl
  have hθ : thetaOf (hyp.Gv e) ≤ hyp.Lv e :=
    thetaOf_le_of_A6 hF (a38ForSQTK_of_cat a38ForSQTKCat_holds) hyp.qtke hyp.simple
      hyp.nonabelian hH2 hK hKn hLeq hA6

  set Y := centralizerSection (hyp.Gv e) (hyp.Lv e) (pCoreOf 2 (hyp.Lv e)) with hYdef
  have hYH : Y ≤ hyp.Gv e := centralizerSection_le_left _ _ _
  have hHLe : hyp.Gv e ≤ normalizer (hyp.Lv e : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLeH).1 hKn
  have hHY : hyp.Gv e ≤ normalizer (Y : Set G) := centralizerSection_normal hHLe
  have hfr := B6.frattini_two hYH hHY hQsyl
  have hQne : hyp.Q ≠ ⊥ := hyp.maximal.1.2.2.2
  have hNQ : hyp.Gv e ⊓ normalizer (hyp.Q : Set G) ≤ hyp.Mv e :=
    (inf_normalizer_le_cgsIn hQne).trans hcgs

  have hQY : hyp.Q ≤ Y := hQsyl.1
  have hC23Y : HypC23 Y hyp.Q (hyp.Mv e ⊓ Y) := by
    refine ⟨hC23.sqtk.mono hYH, isTwoRadicalIn_of_sylow hQY hQsyl.2.1 hQsyl.2.2 hQne,
      inf_le_right, le_inf ((C2Nine.cgsIn_mono_left hYH _).trans hC23.cgs) (cgsIn_le Y _), ?_⟩
    refine B6.isSylowTwoOf_mono hQsyl (le_conjClosure _ _) (conjClosure_le fun m hm r hr => ?_)
    exact Y.mul_mem (Y.mul_mem hm.2 (hQY hr)) (Y.inv_mem hm.2)
  have hYchar : QuasithinUnique.CharTwo Y := A4.charTwo_of_normal hYH hHY hHchar
  obtain ⟨r, Lb, hLb, hprod⟩ := c2_5 hC129 hC23Y hQsyl hYchar

  have hLbM : ∀ i, Lb i ≤ normalizer (L : Set G) := fun i =>
    (le_thetaOf_of_isChi0Block (hLb i)).trans ((theta_mono ((hLb i).1.2.1.trans hYH)).trans
      (hθ.trans (hLeMe.trans hMeM)))
  have hYM : Y ≤ normalizer (L : Set G) := by
    intro x hx
    obtain ⟨m, hm, y, hy, rfl⟩ := hprod x hx
    refine mul_mem (hMeM hm.1) (Subgroup.list_prod_mem _ fun a ha => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hLbM j (hy j)
  exact hfr.trans (sup_le hYM (hNQ.trans hMeM))

theorem stmt12_3_6_of_inputs_F4
    (h1222 : Stmt12_2_2_F4) (h331 : Stmt3_3_1_F4) (h12212 : Stmt12_2_12_F4)
    (h1225 : Stmt12_2_5_F4) (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hF : A318Facts)
    (hI1 : Insp1236) (hI2 : InspSL2NoA6) : Stmt12_3_6_F4 := by
  intro G _ _ T L V hyp _ ψ hLact hLonto e heZ hew

  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223_F4 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ :=
    ⟨hVT, hLV, hTV, hLact, hLonto, nact_of_lact hLV hLact hLonto hNM, hNM, hTI⟩
  obtain ⟨ψ', hpre', hψ'⟩ := hpre.exists_relabel_vecSix hew
  exact A7_centralizer_le_six_F4 h12212 h1225 h39 (hC27 G) (hC129 G) hF hI1 hI2 hyp hpre' hψ' heZ

end CFSG.Quasithin.H13.A7
