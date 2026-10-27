module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6SqSpor
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Catalog

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA (KGA6Sq)

@[expose] def A6LieArm (P : (S : Type) → [Group S] → MulAut S → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ τ : MulAut S, P S τ → orderOf τ = 2 → Nat.card (autCentralizer τ) ≤ 5760 →
    Nonempty (↥(commutator ↥(autCentralizer τ)) ≃* alternatingGroup (Fin 6)) →
    129600 ∣ Nat.card S → False

@[expose] def A6OddArm : Prop := A6LieArm fun S _ _ => OddLieType S

@[expose] def A6EvenArm : Prop :=
  A6LieArm fun S _ τ => EvenLieType S ∧ τ ∉ (MulAut.conj : S →* MulAut S).range

theorem kgA6Sq_of_arms (I : ArmInputs) (hodd : A6OddArm) (heven : A6EvenArm) : KGA6Sq := by
  intro S _ _ hcat hS τ hτ2 hC hC' A hq hA6 hcomm
  haveI := hS
  have hna : ∃ a b : S, a * b ≠ b * a := nonabelian_of_quasisimple hq
  have hτ1 : τ ≠ 1 := a6sq_ne_one τ hq hcomm
  have hτ : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  obtain ⟨e⟩ := hC'
  obtain ⟨D, hD, -, ⟨eD⟩, ⟨eDZ⟩⟩ := a6sq_commutator_component τ e
  have h129 : 129600 ∣ Nat.card S := a6sq_card_dvd τ hA6 hcomm
  have h360 : 360 ∣ Nat.card (fixedSubgroup τ) := a6sq_dvd_card_fixed τ e
  have hCfix : Nat.card (fixedSubgroup τ) ≤ 5760 := by
    rw [← autCentralizer_eq_fixedSubgroup]; exact hC
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hτ hD with
    ⟨n, k, hn6, hk5, hkn, hpar, ⟨θ⟩, hDk⟩ | ⟨hodd', -⟩ | ⟨heven', hout, -⟩ | ⟨s, ⟨es⟩⟩
  · have hk6 : k = 6 :=
      EvenSporadicStandard.HSStd.Zassenhaus.Outer.alt_degree_unique (a := k) (b := 6)
        (by omega) (by norm_num) hDk ⟨eDZ⟩
    subst hk6
    exact a6sq_alt_false θ (by omega) (by obtain ⟨m, hm⟩ := hpar; exact ⟨m + 3, by omega⟩) hτ
      hCfix h360 h129 hA6 hcomm
  · exact hodd S hS hna τ hodd' hτ hC ⟨e⟩ h129
  · exact heven S hS hna τ ⟨heven', hout⟩ hτ hC ⟨e⟩ h129
  · refine a6sq_sporadic_false I hna es hτ hD ?_ h129
    rw [Nat.card_congr eDZ.toEquiv, a6sq_card]

end CFSG.ComponentClassification.CatFC
