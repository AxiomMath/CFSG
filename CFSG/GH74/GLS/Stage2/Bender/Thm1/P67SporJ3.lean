module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporClsGlue
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate5195

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Certificates Cls67

theorem triples_false_J3P :
    ∀ (r s : ℕ) (a b y : ↥j3P), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False :=
  Certificates.certificate5195

theorem noN2_J3 :
    ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .J3 → NoN2 Y := by
  intro Y _ hY
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j3P := (e : Y ≃* NativeSporadic.J3).trans j3PermEquiv
  have hcard : Nat.card (MulAut ↥j3P) ≤ 2 * Nat.card ↥j3P := by
    obtain ⟨-, -, -, -, h⟩ := CFSG.Sporadic.SmallOddCore.ctuc_j3_full_automorphism_permutation_model
    rw [h, card_j3P]
  have hcenter : Subgroup.center ↥j3P = ⊥ := by
    have : IsSimpleGroup ↥j3P :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 j3PermEquiv.symm
    refine center_eq_bot_of_simple_card ?_
    rw [card_j3P]
    norm_num
  exact NoN2.of_mulEquiv e' (noN2_of_outer_card hcenter hcard triples_false_J3P)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
