module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Field
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Sp4Rec

theorem ivk93_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93Eq (fun X _ => LieModel X .PSL 4 p f) (p ^ f) := by
  intro p f hp hp2 hf _ J _ _ hJ x hx q L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Finite (StatedProj (StatedSL 4 F)) := Finite.of_equiv _ e.toEquiv
  have h' := h.of_equiv e
  obtain ⟨a, b, ha, hb, hab, ⟨e₁⟩, -⟩ := h'.two_blocks h2 (by norm_num)
  have ha2 : a = 2 := by omega
  subst ha2
  rw [← hF]
  exact h'.q_eq_of_equiv_sl2 hodd (h'.five_le_of_equiv_sl2 e₁) e₁

end CFSG.GH74.GLS.IVK.Proofs2
