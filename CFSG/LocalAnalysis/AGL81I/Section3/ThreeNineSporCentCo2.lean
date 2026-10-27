module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporCentLines
public import Certificates.Certificate1322011

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open CFSG.Open Certificates.CoreD2Perm

theorem centralizers_eq_top_Co2
    (K : Type*) [Group K] [Finite K]
    (hK : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.Co2)) (A : Subgroup K)
    (hA : IsElemAbelian 5 A) (hc : Nat.card A = 5 ^ 2) (Y : Subgroup K)
    (hY : ∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) : Y = ⊤ := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨E, hEc, hE⟩ := Certificates.certificate1322011
  refine eq_top_of_mulEquiv_cent Nat.prime_five
    (e₁.trans CFSG.Sporadic.Co2Cert.co2PermEquiv) hEc ?_
    (fun B hBE hBe hBc => (hE B hBE hBe hBc).elim fun _ hΓ => eq_top_of_cent_gens hΓ.1 hΓ.2)
    A hA hc Y hY
  rw [← Nat.card_congr CFSG.Sporadic.Co2Cert.co2PermEquiv.toEquiv, CFSG.Sporadic.Co2.card_Co2]
  exact factorization_eq_of_pow_dvd Nat.prime_five (by norm_num) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_co2
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    {d : ℕ} (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Co2) : False := by
  obtain ⟨e⟩ := hs
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e
  have hcK : Nat.card ↥K = 42305421312000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co2.card_Co2
  have hP : ∀ x : Outer CFSG.Sporadic.Co2Cert.co2P, x = 1 := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, rfl⟩ := CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
    exact (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  have hcP : Nat.card (Outer CFSG.Sporadic.Co2Cert.co2P) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hP a).trans (hP b).symm⟩, ⟨1⟩⟩
  refine h.false_of_centralizers_eq_top
    (SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)) ?_
    (SporCent.centralizers_eq_top_Co2 ↥K ⟨e⟩)
  rw [Nat.card_congr (equivalence (e.trans CFSG.Sporadic.Co2Cert.co2PermEquiv)).toEquiv, hcP]
  norm_num

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
