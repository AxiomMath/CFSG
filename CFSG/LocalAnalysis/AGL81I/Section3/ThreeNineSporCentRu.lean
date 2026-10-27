module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporCentLines
public import Certificates.Certificate1322012

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.Open Certificates.CoreD2Perm

theorem centralizers_eq_top_Ru
    (K : Type*) [Group K] [Finite K]
    (hK : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Ru)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) (Y : Subgroup K)
    (hY : ∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) : Y = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨E, hEc, hE⟩ := Certificates.certificate1322012
  refine eq_top_of_mulEquiv_cent Nat.prime_five
    (e₁.trans CFSG.Sporadic.RuSchreier.ruEquivP) hEc ?_
    (fun B hBE hBe hBc => (hE B hBE hBe hBc).elim fun _ hΓ => eq_top_of_cent_gens hΓ.1 hΓ.2)
    A hA hc Y hY
  rw [← Nat.card_congr CFSG.Sporadic.RuSchreier.ruEquivP.toEquiv, CFSG.Sporadic.Ru.card_Ru]
  exact factorization_eq_of_pow_dvd Nat.prime_five (by norm_num) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_ru
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Ru) : False := by
  obtain ⟨e⟩ := hs
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e
  have hcK : Nat.card ↥K = 145926144000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
  refine h.false_of_centralizers_eq_top
    (SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)) ?_
    (SporCent.centralizers_eq_top_Ru ↥K ⟨e⟩)
  rw [Nat.card_congr (equivalence (e.trans CFSG.Sporadic.RuSchreier.ruEquivP)).toEquiv,
    CFSG.Sporadic.RuSchreier.card_outer_ruP]
  norm_num

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
