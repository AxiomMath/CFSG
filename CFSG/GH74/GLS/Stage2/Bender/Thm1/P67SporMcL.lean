module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporClsGlue
public import CFSG.Sporadic.SmallOddCore.McLAut
public import Certificates.Certificate5196

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Certificates Cls67

theorem triples_false_McLP :
    ∀ (r s : ℕ) (a b y : ↥mclP), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False :=
  Certificates.certificate5196

theorem noN2_McL :
    ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .McL → NoN2 Y := by
  intro Y _ hY
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥mclP := (e : Y ≃* NativeSporadic.McL).trans mclPermEquiv
  have hcard : Nat.card (MulAut ↥mclP) ≤ 2 * Nat.card ↥mclP := by
    obtain ⟨-, -, -, -, h⟩ := CFSG.Sporadic.SmallOddCore.mcl_full_automorphism_model
    rw [h, card_mclP]
  have hcenter : Subgroup.center ↥mclP = ⊥ := by
    have : IsSimpleGroup ↥mclP :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL mclPermEquiv.symm
    refine center_eq_bot_of_simple_card ?_
    rw [card_mclP]
    norm_num
  exact NoN2.of_mulEquiv e' (noN2_of_outer_card hcenter hcard triples_false_McLP)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
