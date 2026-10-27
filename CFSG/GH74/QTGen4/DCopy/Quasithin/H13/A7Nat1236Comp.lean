module

public import CFSG.Quasithin.H13.A7Nat1236Comp
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem12Stmt
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem A7Le_comp_six_F4
    (h12212 : Stmt12_2_12_F4) (h1225 : Stmt12_2_5_F4)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (hC27 : ASC27Statement_F4 G) (hI1 : Insp1236) (hI2 : InspSL2NoA6)
    (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecSix)
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) :
    hyp.Lv e ∈ cComp (hyp.Gv e) ∧ ((hyp.Lv e).subgroupOf (hyp.Gv e)).Normal ∧
      QuasithinUnique.IsSylowTwoOf hyp.Q
        (centralizerSection (hyp.Gv e) (hyp.Lv e) (pCoreOf 2 (hyp.Lv e))) ∧
      HypC23 (hyp.Gv e) hyp.Q (hyp.Mv e) ∧ QuasithinUnique.CharTwo (hyp.Gv e) ∧
      cgsIn (hyp.Gv e) hyp.Q ≤ hyp.Mv e ∧ hyp.Lv e ≤ hyp.Mv e ∧ T ≤ hyp.Gv e ∧
      CFSG.IsQuasisimple (↥(hyp.Lv e) ⧸ CFSG.pCore 2 ↥(hyp.Lv e)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hyp.simple

  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, vec_one] at he
    exact absurd he (by decide)
  have he2 : orderOf (e : G) = 2 := by
    refine orderOf_eq_prime ?_ he1
    rw [pow_two]
    exact congrArg Subtype.val (sq_eq_one_of_vec ψ e)
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ hyp.Gv e := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC heZ) t ht))

  obtain ⟨hLeMe, hMeN, -, hcgs, -⟩ := h1225 G T L V hyp e e.2 he1
  have hTMe : T ≤ hyp.Mv e := le_inf hyp.normalizes hTe
  have hTLe : T ≤ normalizer (hyp.Lv e : Set G) := hTMe.trans hMeN

  have hTv : hyp.Tv e = T := inf_eq_left.2 hTe
  have hsylMe : QuasithinUnique.IsSylowTwoOf (hyp.Tv e) (hyp.Mv e) := by
    rw [hTv]
    exact isSylowTwoOf_of_le hyp.sylow hTMe
  have hLeL : hyp.Lv e ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hO2 : pCoreOf 2 (autOn (hyp.Lv e ⊔ hyp.Tv e) V) = ⊥ :=
    pCoreOf_autOn_eq_bot_six h he
      (sup_le (hLeL.trans h.L_le) (inf_le_left.trans h.T_le))
      (sup_le ((oTwoUpper_le _).trans inf_le_right) inf_le_right) le_sup_left
  obtain ⟨⟨-, hQsyl, hC23⟩, -⟩ := h12212 G T L V hyp e e.2 he1 hsylMe hO2

  obtain ⟨hLeq, -⟩ := quasisimple_Le_six h.L_le h.Lact h.Lonto hyp.quasisimple he rfl
  have hLeF : hyp.Lv e ∈ lFamily T := by
    show hyp.Lv e ∈ cComp (hyp.Lv e ⊔ T)
    refine mem_cComp_of_quasisimple_quotient
      (fun N _ hN => oTwoUpper_eq_top_of_isPGroup_quotient _ N hN) hLeq
      (A3.subnormal_of_normal le_sup_left ?_)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le le_normalizer hTLe)

  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
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
  have hSylH : QuasithinUnique.IsSylowTwoOf T (hyp.Gv e) := isSylowTwoOf_of_le hyp.sylow hTe
  have hLeH : hyp.Lv e ≤ hyp.Gv e := (oTwoUpper_le _).trans inf_le_right
  obtain ⟨K, ⟨hK, hLeK⟩, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_existsUnique hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h39 hH2 hSylH hLeH hLeF
  have hKn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h38 hH2 hSylH hLeF hLeK hK hTLe
  have hKH : K ≤ hyp.Gv e := le_of_mem_cComp hK
  have hTK : T ≤ normalizer (K : Set G) :=
    hTe.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).1 hKn)

  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    obtain ⟨hcases, -, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hLocal
      QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved hH2 hK
    rcases hcases with hc | h34
    · obtain ⟨eK⟩ := modO2_mulEquiv hK
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hc.1
    · exfalso
      obtain ⟨-, ⟨e6⟩⟩ := quasisimple_Le_six h.L_le h.Lact h.Lonto hyp.quasisimple he rfl
      refine not_case34_of_le hI2 hK hLeK (g := e6.toMonoidHom.comp
        ((QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥(hyp.Lv e))))) ?_ h34
      exact e6.surjective.comp ((QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective _))

  have hHchar : QuasithinUnique.CharTwo (hyp.Gv e) := by
    obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
      ⟨_, IsPGroup.toSylow_coe hyp.sylow.1 hyp.sylow.2⟩
    exact hyp.qtke.2.1 _ (isTwoLocal_centralizer' he2) ⟨Ts, hTs ▸ hTe⟩
  have hKchar : QuasithinUnique.CharTwo K := A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK)
    hHchar

  have hLeK' : hyp.Lv e = K := by
    by_contra hne
    have hlt : hyp.Lv e < K := lt_of_le_of_ne hLeK hne
    have hKMe : ¬ K ≤ hyp.Mv e := by
      intro hKMe
      have hn : ((hyp.Lv e).subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLeK).2 (hKMe.trans hMeN)
      exact hK.2.2.2 _ hlt hLeF.1 (perfect_of_mem_cComp hLeF)
        (IsSubnormal.step hLeK hn (subnormal_of_mem_cComp hK))
    have hQT : hyp.Q ≤ T :=
      QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
        (isSylowTwoOf_of_le hyp.sylow le_sup_right)
    have hQK : hyp.Q ≤ normalizer (K : Set G) := hQT.trans hTK
    have hconcl : C27Concl (hyp.Gv e) hyp.Q (hyp.Mv e) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ hyp.Q))) :=
      hC27 _ _ _ K _ hC23 hK hKq hKchar hKMe hQK rfl
    obtain ⟨-, ⟨e6⟩⟩ := quasisimple_Le_six h.L_le h.Lact h.Lonto hyp.quasisimple he rfl
    exact hI1 G _ _ _ K _ T (hyp.Lv e) hC23 hK hKq hKchar hKMe hQK rfl hconcl hSylH hQT hTK
      (le_inf hLeK hLeMe) hTLe hLeq ⟨e6⟩
  rw [← hLeK'] at hK hKn
  exact ⟨hK, hKn, hQsyl, hC23, hHchar, hcgs, hLeMe, hTe, hLeq⟩

end CFSG.Quasithin.H13.A7
