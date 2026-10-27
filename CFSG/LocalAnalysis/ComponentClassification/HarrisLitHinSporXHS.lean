module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXElem
public import CFSG.Sporadic.SmallOddCore.HSAut
public import Certificates.Certificate22614

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier SporX

theorem hs_elem {r : ClassRow} (hr : r ∈ hsRows) :
    ∃ E : Subgroup (Equiv.Perm (Fin 3850)), E ≤ hsC r ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      (∀ a ∈ E, a ^ 2 = 1) ∧ (r.outer = false → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E :=
  Certificates.certificate22614 r hr

theorem hinFor_spor_HS :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .HS := by
  intro Y _ _ _ ⟨e₀⟩ _ p m _ _ _ _ _ τ hτ _
  obtain ⟨-, -, -, hrows, hcover, -⟩ := hs_involution_centralizers
  have hA := hs_autModel
  refine hinConcl_of_autModel hA (Rp := fun ρ => ∃ r ∈ hsRows, ρ = tp 3850 r.rep) ?_ ?_
    (e₀.trans hsPermEquiv) p m τ hτ
  · intro t ht ht2
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht2
    exact ⟨_, ⟨r, hr, rfl⟩, g, hA.le hg, rfl⟩
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨-, -, hout, hC, -⟩ := hrows r hr
    obtain ⟨E, hE, hc, hs, h16, h8⟩ := hs_elem hr
    refine ⟨E, hE.trans hC.le, hc, hs, fun hP => ?_, fun _ => lt_of_lt_of_le (by norm_num) h8⟩
    have hin : r.outer = false := by
      cases h : r.outer
      · rfl
      · exact absurd hP (hout.mp h)
    exact lt_of_lt_of_le (by norm_num) (h16 hin)

end CFSG.ComponentClassification.HarrisLit.Hin
