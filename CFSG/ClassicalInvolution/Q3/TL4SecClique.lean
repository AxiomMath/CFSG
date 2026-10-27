module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.Q3.TL4SecOrbit
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

section Leaves


@[expose] def SecIdE2Clique5 : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightInO2 t → ∀ B : Fin 5 → Subgroup Y,
        (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) →
          DConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def SecIdE2Triangle : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightInO2 t → ∀ B : Fin 3 → Subgroup Y,
        (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) →
          T3.DStarConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def SecIdLieClique5 : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      SecIdLie3 R t → ∀ B : Fin 5 → Subgroup Y,
        (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) →
          DConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def SecIdLieTriangle : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      SecIdLie3 R t → ∀ B : Fin 3 → Subgroup Y,
        (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) →
          T3.DStarConnected (CoreAssembly.conjClass (tightCore R))

end Leaves

section Cit3


theorem tightSec5CliqueR_of_plus {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (hE2 : SecIdE2Clique5) (hE4 : SecIdE4NoClique5)
    (hLie : SecIdLieClique5) :
    TightSec5CliqueR 3 n := by
  intro X _ _ hn Φ h hO hgen _ B hB hinj hadj
  by_cases htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g (B 0) = L
  · obtain ⟨S, z, hd, hc, hfam⟩ := exists_datum_of_omegaTransitive h hO hgen (hB 0) htr
    have hB' : ∀ i, B i ∈ CoreAssembly.conjClass (tightCore (B 0)) := fun i => hfam ▸ hB i
    have hadj' : ∀ i j, i ≠ j →
        B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (B i) := fun i j hij =>
      hfam ▸ hadj i j hij
    rw [← hfam]
    by_cases hE2' : TightInO2 z
    · exact hE2 n hA hP X hn (B 0) S z hd hc hE2' B hB' hinj hadj'
    rcases secIdentDatum3_of hP hA X hn (B 0) S z hd hc with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4 | hl
    · exact absurd h2 hE2'
    · exact absurd (Or.inl (hadj' 0 1 (by decide))) (he _ (hB' 0) _ (hB' 1))
    · exact absurd (Or.inl (hadj' 0 1 (by decide))) (he _ (hB' 0) _ (hB' 1))
    · exact absurd hadj' (hE4 X (B 0) S z hd hc hE2' h4.1 h4.2 B hB' hinj)
    · exact hLie n hA hP X hn (B 0) S z hd hc hl B hB' hinj hadj'
  · push Not at htr
    obtain ⟨L, hL, hnc⟩ := htr
    exact dConnected_of_not_conj h4 h hO hn (hB 0) hL fun ⟨g, hg, e⟩ => hnc g hg e

theorem tightSecTriangleR_of_plus {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (hE2 : SecIdE2Triangle) (hE4 : SecIdE4DStar)
    (hLie : SecIdLieTriangle) :
    TightSecTriangleR 3 n := by
  intro X _ _ hn Φ h hO hgen _ B hB hinj hadj
  by_cases htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g (B 0) = L
  · obtain ⟨S, z, hd, hc, hfam⟩ := exists_datum_of_omegaTransitive h hO hgen (hB 0) htr
    have hB' : ∀ i, B i ∈ CoreAssembly.conjClass (tightCore (B 0)) := fun i => hfam ▸ hB i
    have hadj' : ∀ i j, i ≠ j →
        B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (B i) := fun i j hij =>
      hfam ▸ hadj i j hij
    rw [← hfam]
    by_cases hE2' : TightInO2 z
    · exact hE2 n hA hP X hn (B 0) S z hd hc hE2' B hB' hinj hadj'
    rcases secIdentDatum3_of hP hA X hn (B 0) S z hd hc with h2 | ⟨he, -⟩ | ⟨he, -⟩ | h4 | hl
    · exact absurd h2 hE2'
    · exact absurd (Or.inl (hadj' 0 1 (by decide))) (he _ (hB' 0) _ (hB' 1))
    · exact absurd (Or.inl (hadj' 0 1 (by decide))) (he _ (hB' 0) _ (hB' 1))
    · exact hE4 X (B 0) S z hd hc hE2' h4.1 h4.2
    · exact hLie n hA hP X hn (B 0) S z hd hc hl B hB' hinj hadj'
  · push Not at htr
    obtain ⟨L, hL, hnc⟩ := htr
    exact dstarConnected_of_dConnected h.hyp
      (dConnected_of_not_conj h4 h hO hn (hB 0) hL fun ⟨g, hg, e⟩ => hnc g hg e)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
