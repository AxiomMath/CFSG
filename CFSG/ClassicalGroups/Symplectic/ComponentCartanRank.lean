module

public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank

theorem center_statedSp_eq_bot_of_charP_two {m : ℕ} {F : Type} [Field F] [CharP F 2]
    (hm : 1 ≤ m) : Subgroup.center (StatedSp m F) = ⊥ := by
  have hcenter : Subgroup.center (StatedSp m F) =
      (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf (StatedSp m F) := by
    rw [show StatedSp m F = TauCeti.GLSymplectic (Fin m) F from
      statedSp_eq_GLSymplectic (n := m) (K := F)]
    exact center_GLSymplectic_eq (n := m) (K := F)
  rw [hcenter]
  haveI : NeZero m := ⟨by omega⟩
  exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.spScalars_eq_bot_of_charTwo
    (r := m) (K := F)

theorem exists_central_cover_sp_of_section
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.B m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hsec : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      Nat.card F = Q.card →
      ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSp m F),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
          ∃ σ : StatedSp m F →* E, ∀ g, π (σ g) = g) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (π : StatedSp m F →* L),
      Nat.card F = Q.card ∧ Function.Surjective π ∧
      π.ker ≤ Subgroup.center (StatedSp m F) := by
  classical
  let X := (TauCeti.CFSGIndex.lie
    (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group
  haveI : Fact (Nat.Prime Q.p) := ⟨Q.prime_p⟩
  let F := GaloisField Q.p Q.exponent
  have hcardF : Nat.card F = Q.card := by
    rw [GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  haveI : CharP F 2 := CharP.congr Q.p hQ
  haveI : Finite F := inferInstance
  obtain ⟨eB⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
      (r := m) (q := Q) hv hQ hm hcardF
  have hcenter : Subgroup.center (StatedSp m F) =
      (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf (StatedSp m F) := by
    rw [show StatedSp m F = TauCeti.GLSymplectic (Fin m) F from
      statedSp_eq_GLSymplectic (n := m) (K := F)]
    exact center_GLSymplectic_eq (n := m) (K := F)
  let eC : StatedSp m F ⧸ Subgroup.center (StatedSp m F) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans eB
  let ρC : StatedSp m F →* X :=
    eC.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (StatedSp m F)))
  let ρK : L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hρC : Function.Surjective ρC :=
    eC.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρK : Function.Surjective ρK :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcK : ρK.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hmk : (QuotientGroup.mk' (Subgroup.center L)) x = 1 := by
      apply e.injective
      rw [map_one]
      simpa [ρK] using hx
    exact (QuotientGroup.eq_one_iff x).1 hmk
  have hperf : Group.IsPerfect L := Group.isPerfect_def.2 hL.1
  obtain ⟨φ, hφ, hφsurj⟩ :=
    CFSG.LieType.SemisimpleCentralizers.HeldLang.exists_surjective_lift
      ρC ρK hρC hρK hcK hperf (hsec F hcardF)
  refine ⟨F, inferInstance, inferInstance, inferInstance, φ, hcardF, hφsurj, ?_⟩
  intro x hx
  have hxρ : x ∈ ρC.ker := by
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker] at hx
    rw [← hφ x, hx, map_one]
  have hkerC : ρC.ker = Subgroup.center (StatedSp m F) := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      have hmk : (QuotientGroup.mk' (Subgroup.center (StatedSp m F))) y = 1 := by
        apply eC.injective
        rw [map_one]
        simpa [ρC] using hy
      exact (QuotientGroup.eq_one_iff y).1 hmk
    · intro hy
      have hmk : (QuotientGroup.mk' (Subgroup.center (StatedSp m F))) y = 1 :=
        (QuotientGroup.eq_one_iff y).2 hy
      simpa [ρC, hmk]
  rw [← hkerC]
  exact hxρ

end CFSG.ClassicalGroups.Symplectic

end
