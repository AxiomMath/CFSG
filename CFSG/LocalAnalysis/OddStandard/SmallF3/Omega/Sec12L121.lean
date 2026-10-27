module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120G
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Compat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma121_of (hp : Asc82Pre11) (hPr : Asc82Prince) : Asc82Lemma121 := by
  intro G _ _ t L S z K1 K2 E hctx
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  obtain ⟨φ₀, hperm⟩ := sec121_exists_perm F
  have hVE : secV t S L E ≤ E := sec121_V_le_E F hE
  have hPB : secCMB t S L ≤ normalizer (secB S L : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hYB : secM t S L ⊓ L ≤ normalizer (secB S L : Set G) := by
    rw [F.bdata.2.2.2.2.1]
    exact inf_le_right
  obtain ⟨φ', hmod, hφ'f⟩ := exists_natMod_lift_of_hom (V := secV t S L E) (K := secB S L)
    (B := secB S L) (H := secM t S L ⊓ L) (sec12f t) (sec121_B_le_V F hE)
    (hVE.trans (hE.1.trans hPB)) (sec121_Y_le_normalizer_V F hE) hYB
    (fun v hv => sec12E_f_mem F (hE.1 (hVE hv)))
    (fun v hv w hw => sec12E_f_mul F (hE.1 (hVE hv)) (hE.1 (hVE hw)))
    (fun v hv => sec121_f_eq_one_iff_V F hE hv) (fun b hb => sec121_f_surj_V F hE hb)
    (fun h hh v _ => sec12E_f_conj (Subgroup.mem_centralizer_iff.mp F.htC h hh.2) v) hperm
  exact ⟨hPr G (secB S L) (secV t S L E) (secM t S L ⊓ L) φ' φ₀ hmod hperm
    (sec121_prince_compat F hE hmod.2.2.2.2.1 hφ'f), sec121_V_sup_zpowers F hE,
    sec121_V_inf_zpowers F hE, sec121_E_le_normalizer_V F hE, sec121_autIn_equiv F, ⟨φ₀, hperm⟩,
    ⟨φ', hmod⟩⟩

end CFSG.OddStandard.SmallF3.Omega
