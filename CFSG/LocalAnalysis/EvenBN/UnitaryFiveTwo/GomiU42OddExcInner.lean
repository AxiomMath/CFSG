module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcDiv
import CFSG.LocalAnalysis.SteinbergBMOddResidualToral

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_innerDiag_false
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F))
    {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) =
      (g : ModGL τ F) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hdvd : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ∣ 51840) :
    False := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨b, hb, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.SteinbergBM.exists_mulEquiv_toralCentralizer_of_innerDiagonal hτ' hF hαg hα
  have hcard : Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) =
      Nat.card ↥(toralCentralizer τ F b) := Nat.card_congr e.toEquiv
  by_cases hne : ∃ i, b i = -1
  · have hτ4 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    have h5 := gomi_toral_pow_five_dvd (F := F) hτ4 b hb hne
    rw [← hcard] at h5
    exact gomi_not_pow_five_dvd hF Finite.one_lt_card (h5.trans hdvd)
  · have hb1 : b = 1 := funext fun i => (hb i).resolve_right fun hi => hne ⟨i, hi⟩
    have hTC : toralCentralizer τ F b = adjointGroup τ F := by
      unfold toralCentralizer
      rw [hb1, rootDiagUnit_one]
      refine inf_eq_left.2 fun x _ => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp
    have hcardT : Nat.card ↥(toralCentralizer τ F b) = Nat.card ↥(adjointGroup τ F) := by
      rw [hTC]
    have htop : α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)) = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (hcard.trans hcardT)
    refine hα1 (MulEquiv.ext fun h => ?_)
    have hh : h ∈ α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)) := by
      rw [htop]
      exact Subgroup.mem_top h
    exact hh

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
