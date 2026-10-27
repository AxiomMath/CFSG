module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXElem
public import CFSG.RankThree.PartOne.KS.Suz
public import Certificates.Certificate22616

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore SporX

theorem suz_elem {i : ℕ} (hi : i < 4) :
    ∃ E : Subgroup (Equiv.Perm (Fin 1782)), E ≤ suzM ⊓ centralizer {suzInv i} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      (suzInv i ∈ suzM → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E :=
  Certificates.certificate22616 i hi

theorem hinFor_spor_Suz :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .Suz := by
  intro Y _ _ _ ⟨e₀⟩ _ p m _ _ _ _ _ τ hτ _
  refine hinConcl_of_autModel CFSG.RankThree.PartOne.suz_autModel
    (Rp := fun ρ => ∃ i < 4, ρ = suzInv i) ?_ ?_ (e₀.trans suzEquivM) p m τ hτ
  · intro t ht ht2
    obtain ⟨i, ⟨hi, c, hc, hct⟩, -⟩ := suzT_involution_class ht ht2
    exact ⟨_, ⟨i, hi, rfl⟩, c, hc, hct.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨E, hE, hc, hs, h16, h8⟩ := suz_elem hi
    exact ⟨E, hE, hc, hs, fun hM => lt_of_lt_of_le (by norm_num) (h16 hM),
      fun _ => lt_of_lt_of_le (by norm_num) h8⟩

end CFSG.ComponentClassification.HarrisLit.Hin
