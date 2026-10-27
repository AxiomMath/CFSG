module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1PermSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Tits
public import Certificates.Certificate753512
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Sporadic.Schreier.Tits Certificates.CoreE1Perm
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem tits_e1_check :
    Certificates.CoreE1Perm.check (titsE1Data ()) = true :=
  Certificates.certificate753512

theorem tits_e1_tab_a : TabRep (titsE1Data ()).aT (titsDGen 0) := by
  have h : (titsE1Data ()).aT = Certificates.CoreD2Perm.titsData.aT := rfl
  rw [h]
  exact tits_core_tab_a

theorem tits_e1_tab_b : TabRep (titsE1Data ()).bT (titsDGen 1) := by
  have h : (titsE1Data ()).bT = Certificates.CoreD2Perm.titsData.bT := rfl
  rw [h]
  exact tits_core_tab_b

theorem coreE1Datum_titsD :
    CFSG.AGLEmbedding.CoreE1.Datum ↥titsD :=
  CFSG.AGLEmbedding.CoreE1.datum_of_check (D := titsE1Data ()) (a := titsDGen 0) (b := titsDGen 1)
    titsD_eq_closure_pair rfl tits_e1_tab_a tits_e1_tab_b
    (fun P => by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact CFSG.GroupTheory.GL52.card_sylow_of_card_eq_pow_mul (k := 3) (m := 665600)
        (by rw [card_titsD]; norm_num) (by norm_num) P)
    tits_e1_check

end CFSG.AGLEmbeddingD2
