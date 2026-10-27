module

public import CFSG.LocalAnalysis.LargeEvenClassification.EvenActionGeneratorBound
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourAction

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] noncomputable def smallCfourEvenCoordinateEquiv :
    smallCfourEvenSubgroup ≃* Multiplicative (RankTwoBinaryResidue 1) :=
  (MonoidHom.ofInjective smallCfourEvenHom_injective).symm

theorem smallCfourEvenCoordinateEquiv_spec (u : smallCfourEvenSubgroup) :
    smallCfourEvenUnit (smallCfourEvenCoordinateEquiv u).toAdd = u.val :=
  congrArg Subtype.val ((MonoidHom.ofInjective smallCfourEvenHom_injective).apply_symm_apply u)

@[expose] noncomputable def smallCfourEvenCoordinateHom
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourEvenSubgroup) :
    Q →* Multiplicative (RankTwoBinaryResidue 1) :=
  smallCfourEvenCoordinateEquiv.toMonoidHom.comp (Q.inclusion hle)

theorem smallCfourEvenCoordinateHom_injective
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourEvenSubgroup) :
    Function.Injective (smallCfourEvenCoordinateHom Q hle) := by
  intro u v h
  have h' := smallCfourEvenCoordinateEquiv.injective h
  have hval := congrArg Subtype.val h'
  apply Subtype.ext
  exact hval

theorem smallCfourEvenCoordinateHom_spec
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourEvenSubgroup) (u : Q) :
    smallCfourEvenUnit (smallCfourEvenCoordinateHom Q hle u).toAdd = u.val :=
  smallCfourEvenCoordinateEquiv_spec (Q.inclusion hle u)

theorem binaryHom_injective_generator_rank {G F : Type*} [Group G] [Finite G]
    [AddCommGroup F] [Module (ZMod 2) F] (hpgroup : IsPGroup 2 G)
    (f : G →* Multiplicative F) (hinjective : Function.Injective f) :
    pGeneratorRank 2 G = Module.finrank (ZMod 2) (binaryHomRange f) := by
  have h := binaryHom_quotient_generator_rank hpgroup (⊥ : Subgroup G) f
    (MonoidHom.ker_eq_bot f hinjective)
  rw [pGeneratorRank_mulEquiv Nat.prime_two (hpgroup.to_quotient ⊥)
    (QuotientGroup.quotientBot (G := G))] at h
  exact h

theorem smallCfourEvenCoordinateHom_generator_rank
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourEvenSubgroup)
    (hpgroup : IsPGroup 2 Q) :
    pGeneratorRank 2 Q = Module.finrank (ZMod 2) (binaryHomRange (smallCfourEvenCoordinateHom Q hle)) :=
  binaryHom_injective_generator_rank hpgroup _ (smallCfourEvenCoordinateHom_injective Q hle)

theorem smallCfour_proper_even_generator_rank
    (Q : Subgroup (ResidualRing 1)ˣ) (hle : Q ≤ smallCfourEvenSubgroup)
    (hne : Q ≠ smallCfourEvenSubgroup) (hpgroup : IsPGroup 2 Q) :
    pGeneratorRank 2 Q ≤ 3 := by
  let coordinates := smallCfourEvenCoordinateHom Q hle
  let W := binaryHomRange coordinates
  have hproper : W ≠ ⊤ := by
    intro htop
    apply hne
    apply le_antisymm hle
    intro u hu
    let x := smallCfourEvenCoordinateEquiv ⟨u, hu⟩
    have hx : x.toAdd ∈ W := htop ▸ Submodule.mem_top
    obtain ⟨q, hq⟩ := (binaryHomRange_mem coordinates _).mp hx
    have heq : q.val = u := by
      have h := congrArg (fun z : Multiplicative (RankTwoBinaryResidue 1) => smallCfourEvenUnit z.toAdd) hq
      exact (smallCfourEvenCoordinateHom_spec Q hle q).symm.trans
        (h.trans (smallCfourEvenCoordinateEquiv_spec ⟨u, hu⟩))
    exact heq ▸ q.property
  have hsmall := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  rw [finrank_top, rankTwoBinaryResidue_finrank] at hsmall
  rw [smallCfourEvenCoordinateHom_generator_rank Q hle hpgroup]
  exact Nat.le_of_lt_succ hsmall

theorem smallCfour_even_units_commute
    (u v : (ResidualRing 1)ˣ) (hu : u ∈ smallCfourEvenSubgroup) (hv : v ∈ smallCfourEvenSubgroup) :
    Commute u v := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

end CFSG.LargeEvenClassification.Helpers
