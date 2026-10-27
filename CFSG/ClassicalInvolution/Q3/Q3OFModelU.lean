module

public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.Q3.Q3WALoc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Models
open scoped MatrixGroups commutatorElement

@[expose] def KindFund3 (c : CompData) : Prop :=
  ∀ {X : Type} [Group X] (φ : c.G →* X), φ.ker ≤ Subgroup.center c.G →
    ∀ R ∈ c.fund, Nat.card (R.map φ) = 24 → Nonempty (↥R ≃* SL(2, ZMod 3))

section Inj

variable {K X : Type} [Group K] [Group X]

theorem injOn_of_card_map_eq {φ : K →* X} {R : Subgroup K} [Finite R] [Finite (R.map φ)]
    (hR : Nat.card R = Nat.card (R.map φ)) : ∀ a ∈ R, ∀ b ∈ R, φ a = φ b → a = b := by
  let f : ↥R →* ↥(R.map φ) :=
    (φ.comp R.subtype).codRestrict (R.map φ) (fun a => ⟨a, a.2, rfl⟩)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hbij : Function.Bijective f := (Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hR⟩
  intro a ha b hb hab
  have := hbij.1 (show f ⟨a, ha⟩ = f ⟨b, hb⟩ from Subtype.ext hab)
  exact congrArg Subtype.val this

end Inj

section Kinds

theorem kindFund3_model {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (hft : IsFundTag t)
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) : KindFund3 (CompData.model t n) := by
  intro _ _ _ _ R hR _
  obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (by norm_num)
    hft hadm hG2 hD4 hR
  obtain ⟨ε⟩ := nonempty_ringEquiv_zmod_three card_gf3
  exact ⟨e.trans (slEquiv ε 2)⟩

end Kinds

end CFSG.ClassicalInvolution.Q3.Q3OF
