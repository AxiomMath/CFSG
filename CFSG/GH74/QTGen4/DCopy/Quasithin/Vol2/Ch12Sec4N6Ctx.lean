module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Lemma5

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem exists_ctx_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9_F4) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T L V : Subgroup G} (hcx : Cx1242 G T L V)
    (h3 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {E : Subgroup G} (hEV : E ≤ V) (hE4 : Nat.card E = 4)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) :
    ∃ (z v : G) (_ : IsMulCommutative ↥V), Ctx T L V E z v := by
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hcx (Or.inl h3)
  have := hf.comm
  obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module_F4 h1222 hcx hf h3
  have hQ := pCoreOf_sup_eq_of_hyp1223_F4 h1222 h3228 hyp
  obtain ⟨hTsyl, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
  obtain ⟨hZL, hZQ, hoff⟩ := lemma12_4_5_of_F4 h331 h1222 hpre h3228 h1229 h51 G T L V hcx h3 E hEV
    hE4 hTE

  obtain ⟨v, hvE, hvL⟩ : ∃ v ∈ E, v ∉ Subgroup.centralizer (L : Set G) := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (le_inf hEV (fun x hx => h x hx) :
      E ≤ V ⊓ Subgroup.centralizer (L : Set G))
    rw [hE4, hf.card_zV] at this
    omega
  have hcc := hyp.conjClosure_eq
  have huniq := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow
    hyp.maximal
  rw [hcc] at huniq
  have hO2 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hyp.maximal.1.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hchar : QuasithinUnique.CharTwo (L ⊔ T) := by
    have hH : InH (S : Subgroup G) (L ⊔ (S : Subgroup G)) := ⟨le_sup_right, hS ▸ hO2⟩
    have := charTwo_of_inH hyp.qtke.2.1 S hH
    rwa [hS] at this
  have hMloc := huniq.1.1
  refine ⟨z, v, this, ⟨hcx, h3, hf, hV16, hGrs, hGr, hnat, hQ, hTeq, hTsyl, hEV, hE4, hTE, hvE,
    hvL, hZL, hZQ, hoff, huniq, fun g hg => ?_, hchar, hyp.faithful.2.1,
    cComp_of_isLocal hyp.maximal.1,
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hO2,
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian
      (pCoreOf_ne_bot_of_isTwoLocal hMloc.1), hyp.qtke.2.1, hyp.sylow⟩⟩
  have h := lemma_1_2_7_four hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow hyp.maximal
    (g := g) (by rwa [hcc])
  rwa [hcc] at h

end N1246

end CFSG.Quasithin.H13
