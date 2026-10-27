module

public import CFSG.ClassicalInvolution.Q3.TL4StarSecUP
public import CFSG.ClassicalInvolution.Q3.TL4StarSecSU4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem starNbr_of_spin {c : CompData}
    (hsingle : ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g : c.G, R' = conjSub g R)
    (hpair : ∃ R₁ ∈ c.fund, ∃ R₂ ∈ c.fund, ∃ W,
      Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂)
    (hR : TypeRFam 3 Φ) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h : SecIdQ8Shape c Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  obtain ⟨ψ, -, hker, hfund⟩ := h
  obtain ⟨R₁, hR₁, R₂, hR₂, W, hW⟩ := hpair
  refine starNbr_of_unitaryPair hker hfund (fun R hR' R' hR'' => ?_) hR₁ hR₂ hW hR htr
  obtain ⟨g, rfl⟩ := hsingle R hR' R' hR''
  exact ⟨ψ g, Q3AM.map_conj_eq_conjSub ψ (R₀ := R) (g := g) rfl⟩


theorem starNbr_of_odd3 (hR : TypeRFam 3 Φ) (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h : SecIdQ8Shape (CompData.model .POmegaOdd 3) Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hs := ModelFacts.fundamentalSingleClass .POmegaOdd 3 3 1 Nat.prime_three trivial hadm
    (by decide) (by decide)
  exact starNbr_of_spin (c := CompData.model .POmegaOdd 3) (fun R hR' R' hR'' => hs R hR' R' hR'')
    Q3W.exists_unitaryPair_odd3 hR htr h

theorem starNbr_of_minus4 (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L')
    (h : SecIdQ8Shape (CompData.model .POmegaMinus 4) Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hs := ModelFacts.fundamentalSingleClass .POmegaMinus 4 3 1 Nat.prime_three trivial hadm
    (by decide) (by decide)
  exact starNbr_of_spin (c := CompData.model .POmegaMinus 4) (fun R hR' R' hR'' => hs R hR' R' hR'')
    Q3W.exists_unitaryPair_minus3 hR htr h

theorem starNbr_of_lieS4 (hR : TypeRFam 3 Φ)
    (htr : ∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') (h : SecIdLieS4 Φ) :
    ∀ L ∈ Φ, ∃ L' ∈ Φ, L' ∈ omegaStarNbr Φ L ∧ L' ∉ omegaNbr Φ L := by
  rcases h with h | h | h
  · exact starNbr_of_su4 hR htr h
  · exact starNbr_of_odd3 hR htr h
  · exact starNbr_of_minus4 hR htr h

end CFSG.ClassicalInvolution.Q3.TL4
