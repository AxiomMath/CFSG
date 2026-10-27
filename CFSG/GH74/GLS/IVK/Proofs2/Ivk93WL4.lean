module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ivk93w_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93WEmpty (fun X _ => LieModel X .PSL 4 p f) := by
  intro p f hp hp2 hf _ J _ _ hJ x q B h _
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have : Finite (StatedProj (StatedSL 4 F)) := Finite.of_equiv _ e.toEquiv
  exact (h.of_equiv e).false_of_psl_four_five hodd (Or.inl rfl)

end CFSG.GH74.GLS.IVK.Proofs2
