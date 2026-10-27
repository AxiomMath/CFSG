module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Leaves
import CFSG.GH74.SmallRanks
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint

namespace Ivk93M12TwoRank

theorem three_le_twoRank {J : Type} [Group J] [Finite J] {y : J} (hD : Ivk93M12Data J y) :
    3 ≤ CFSG.Open.twoRank J := by
  obtain ⟨E, -, hEab, hEsq, hEcard⟩ := hD.elemAbelian_cent
  exact CFSG.SectionRank.le_pRank Nat.one_lt_two (le_top : E ≤ ⊤)
    ⟨⟨⟨fun a b => Subtype.ext (hEab a a.2 b b.2)⟩⟩, hEsq⟩ (k := 3) (by rw [hEcard]; norm_num)

end Ivk93M12TwoRank

theorem ivk93m12_l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93M12Empty (fun X _ => LieModel X .PSL 2 p f) := by
  intro p f hp hp2 hf J _ _ hJ y hD
  have h1 := CFSG.GH74.twoRank_le_two_of_lieModel_PSL_two_odd hp hp2 hJ
  have h2 := Ivk93M12TwoRank.three_le_twoRank hD
  omega

end CFSG.GH74.GLS.IVK.Proofs2
