module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporClsGlue
public import CFSG.Sporadic.Schreier.PairJ2Faithful
public import CFSG.Sporadic.J2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import Certificates.Certificate5194

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Certificates Cls67

theorem triples_false_J2 :
    ∀ (r s : ℕ) (a b y : NativeSporadic.J2), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False :=
  triples_false_of_equiv j2PermEquiv Certificates.certificate5194

theorem noN2_J2 :
    ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .J2 → NoN2 Y := by
  intro Y _ hY
  obtain ⟨e⟩ := hY
  have e' : Y ≃* NativeSporadic.J2 := e
  have hcard : Nat.card (MulAut NativeSporadic.J2) ≤ 2 * Nat.card NativeSporadic.J2 :=
    CFSG.ComponentClassification.J2Cover.j2_mulAut_card.le
  have hcenter : Subgroup.center NativeSporadic.J2 = ⊥ := by
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    refine center_eq_bot_of_simple_card ?_
    rw [CFSG.Sporadic.J2.card_J2]
    norm_num
  exact NoN2.of_mulEquiv e' (noN2_of_outer_card hcenter hcard triples_false_J2)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
