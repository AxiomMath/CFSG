module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbCtx11
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbStmt4
import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem Ctx13.Q_le_CK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxQ t tau x₁ x₂ rho ≤
      ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  refine le_inf hc.normal_Q_K.1 ?_
  obtain ⟨e⟩ := hc.q_iso
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have h : e ⟨b, hb⟩ * e ⟨a, ha⟩ = e ⟨a, ha⟩ * e ⟨b, hb⟩ := mul_comm _ _
  have h2 : (⟨b, hb⟩ : ctxQ t tau x₁ x₂ rho) * ⟨a, ha⟩ = ⟨a, ha⟩ * ⟨b, hb⟩ :=
    e.injective (by rw [map_mul, map_mul, h])
  exact congrArg Subtype.val h2

theorem harris1981_bound (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt) (h43 : Lemma4_3Stmt)
    (h411 : Lemma4_11Stmt) (h411c : Ctx11OfTMStmt) (h412 : Lemma4_12Stmt)
    (h413 : Lemma4_13Stmt) (h413c : Ctx13ExistsStmt) (h417 : Lemma4_17Stmt)
    (h418 : Lemma4_18Stmt) (hI : Sec4Inputs) (hB : Sec4BInputs) : FritzII.Harris1981Bound := by
  intro G _ _ _ L t hyp hkp hcat hdvd
  have hG : Sec4Glob G :=
    { simple := inferInstance, kproper := hkp, not_catalog := hcat, dvd := hdvd }
  obtain ⟨S, x₁, x₂, lam, rho, h0⟩ := exists_ctx0_of_hyp hyp
  obtain ⟨tau, h10⟩ := lemma4_1_to_10 h41 h41c h43 hI hG h0
  obtain ⟨tau', h11⟩ := ctx11_exists h411 h411c hI hG hB h10
  have h12 := h412 h11
  have h13 := h413 hG h11 h12
  obtain ⟨om, hc⟩ := h413c hG h11 h12 h13
  obtain ⟨𝒮, h𝒮, hU⟩ := S4B.exists_isSylowIn_of_le hc.U_le_K hc.U_sylow.2.1
  have htop : CFSG.generalizedFitting G = ⊤ :=
    CFSG.Adapters.generalizedFitting_eq_top_of_isSimpleGroup G
  have hF : ¬ FstarConcl t := fun h => h.1 (htop ▸ Subgroup.mem_top t)
  rcases hc.Q_le_CK.lt_or_eq with hlt | heq
  · exact hF (h417 hG hc h𝒮 hU hlt).1
  · exact hF (h418 hG hc h𝒮 hU heq.symm).1

end CFSG.OddStandard.SmallF3.HarrisU33
