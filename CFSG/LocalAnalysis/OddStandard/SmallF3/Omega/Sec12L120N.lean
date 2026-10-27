module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120G

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec120_natMod (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) :
    IsNatModA5 E (secA t S L) (secM t S L ⊓ L) := by
  have hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G) := F.bdata.2.2.2.2.1
  obtain ⟨φ, hperm, -⟩ := F.bdata.2.2.2.2.2
  have hPM : secCMB t S L ≤ secM t S L := inf_le_left
  refine isNatModA5_of_hom (V := E) (K := secA t S L) (B := secB S L) (H := secM t S L ⊓ L)
    (sec12f t) (sec120_A_le_E F hE) (hE.1.trans hPM)
    (inf_le_left.trans (sec12E_sylow_normal F hE)) inf_le_left
    (fun v hv => sec12E_f_mem F (hE.1 hv))
    (fun v hv w hw => sec12E_f_mul F (hE.1 hv) (hE.1 hw))
    (fun v hv => sec120_f_eq_one_iff F hE hv)
    (fun b hb => sec120_f_surj_E F hE hb) ?_ ⟨φ, by rw [hML]; exact hperm⟩
  intro h hh v _
  exact sec12E_f_conj (Subgroup.mem_centralizer_iff.mp F.htC h hh.2) v

end CFSG.OddStandard.SmallF3.Omega
