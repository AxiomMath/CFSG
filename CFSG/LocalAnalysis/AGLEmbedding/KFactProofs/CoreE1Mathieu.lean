module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1PermSound
public import Certificates.Certificate753511
import CFSG.Sporadic.Mathieu.M12
import CFSG.GroupTheory.GL52.SylowTools
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2MathieuBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint Certificates.CoreE1Perm
open CFSG.ComponentClassification.PSL3Four (TabRep)

theorem m12_e1_check : check m12E1Data = true :=
  Certificates.certificate753511

theorem m12_e1_tab_a : TabRep m12E1Data.aT m12CoreA := ⟨rfl, by decide⟩

theorem m12_e1_tab_b : TabRep m12E1Data.bT m12CoreB := ⟨rfl, by decide⟩

theorem coreE1Datum_M12 :
    CoreE1.Datum ↥NativeSporadic.M12 :=
  CoreE1.datum_of_check (a := m12CoreA) (b := m12CoreB) rfl rfl m12_e1_tab_a m12_e1_tab_b
    (fun P => by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact CFSG.GroupTheory.GL52.card_sylow_of_card_eq_pow_mul (k := 3) (m := 3520)
        (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) (by norm_num) P)
    m12_e1_check

end CFSG.AGLEmbedding
