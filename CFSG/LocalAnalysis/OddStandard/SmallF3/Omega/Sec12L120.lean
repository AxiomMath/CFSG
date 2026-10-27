module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma120_of (hp : Asc82Pre11) : Asc82Lemma120 := by
  intro G _ _ t L S z K1 K2 E hctx
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  have hN : secM t S L ≤ normalizer (E : Set G) := sec12E_sylow_normal F hE
  have hBA : secB S L ≤ secA t S L := le_sup_left
  have hAE : secA t S L ≤ E := sec120_A_le_E F hE
  have hEC : E ⊓ centralizer (secA t S L : Set G) = secA t S L := sec120_E_inf_C F hE
  refine ⟨⟨hAE, hEC⟩, ⟨fun e he e' he' => hBA (sec120_comm_mem_B F hE he he'),
    fun e he => hBA (sec120_sq_mem_B F hE he), sec120_relIndex_A F hE⟩, ?_,
    ⟨fun e he => sec12E_f_mem F (hE.1 he), fun b hb => sec120_f_surj_E F hE hb, ?_⟩,
    sec120_natMod F hE, ⟨fun e he e' he' => sec120_comm_mem_B F hE he he',
    fun e he => sec120_sq_mem_B F hE he, sec120_relIndex_B F hE⟩⟩
  · rw [inf_eq_left.mpr hN]
    rfl
  · intro e he
    constructor
    · intro h1
      have hC : e ∈ centralizer (secA t S L : Set G) := (sec12E_f_eq_one F (hE.1 he)).1 h1
      rw [← hEC]
      exact ⟨he, hC⟩
    · intro hA
      refine (sec12E_f_eq_one F (hE.1 he)).2 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact sec12E_A_comm F ha hA

end CFSG.OddStandard.SmallF3.Omega
