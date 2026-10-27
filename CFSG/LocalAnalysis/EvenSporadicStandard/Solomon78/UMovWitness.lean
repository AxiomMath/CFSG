module

public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.SmallOddCore

@[expose] def umovWitOK (n : ℕ) (sift : Table → Bool) (l r r' : Table) : Bool :=
  permOK n l && sift l && invOK n l (invT n l) && permOK n r && permOK n r' &&
    commTT n (conjT n l (invT n l) r) r'

theorem umovWit_spec {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {sift : Table → Bool}
    (hsift : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → sift T = true → g ∈ P)
    {l r r' : Table} {a b : Equiv.Perm (Fin n)} (hr : Rep n r a) (hr' : Rep n r' b)
    (h : umovWitOK n sift l r r' = true) :
    ∃ x ∈ P, (x * a * x⁻¹) * b = b * (x * a * x⁻¹) := by
  simp only [umovWitOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl, hsl⟩, hli⟩, -⟩, -⟩, hc⟩ := h
  have rl := rep_tp hl
  refine ⟨tp n l, hsift l _ rl hsl, ?_⟩
  have rc : Rep n (conjT n l (invT n l) r) (tp n l * a * (tp n l)⁻¹) :=
    Rep.compT (Rep.compT rl hr) (rep_invT rl hli)
  exact (commTT_iff rc hr').1 hc

end CFSG.EvenSporadicStandard.Solomon78
