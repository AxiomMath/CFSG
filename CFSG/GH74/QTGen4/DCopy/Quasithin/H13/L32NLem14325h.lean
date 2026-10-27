module

public import CFSG.Quasithin.H13.L32NLem14325h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14325c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

theorem exists_ctxI_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12810 : Lemma12_8_10_F4)
    (C : Ctx14325 G T L V V₂ g D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hi : Case14323i T L V g D) : CtxI G T L V V₂ g D := by
  obtain ⟨hzd, hcard, hiso, hsup, hKM⟩ := hi.zU C.zUg_ne
  obtain ⟨-, -, hLTV, -, -⟩ := stmtL32NModule_of_inputs_F4 h1332 h1334 G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨-, -, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  obtain ⟨e1, e2, e3, -, -, -⟩ := h6
  obtain ⟨hsq, hcomm⟩ := L14332.sq_mem_and_comm_mem C.U2
    (display12_8_frattini_F4 h1222 h12213 G T L V 3 (fsuV1 T V) V₂ C.setting).le
  refine ⟨C, hd, hzd, hcard, hiso, hsup, hKM, hi.l1_normal, hLTV, fun z hz hzE => ?_, ?_,
    hi, hsq, fun u hu w hw => by simpa [commutatorElement_def] using hcomm u hu w hw⟩
  · have h1 : z ∈ CFSG.conjugate (zU128 V (fsuV1 T V)) g ⊓
        centralizerMod (zU128 V (fsuV1 T V)) (Subgroup.normalizer (fsuV1 T V : Set G))
          (u128 V (fsuV1 T V)) := ⟨hz, hzE⟩
    rw [e1, e2, e3] at h1
    exact h1.2
  · rw [C.relIndex_inf_conj_F4 h12810, hcard]

end L14325

end CFSG.Quasithin.H13
