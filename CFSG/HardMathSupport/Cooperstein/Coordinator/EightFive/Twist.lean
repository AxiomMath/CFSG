module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm

variable {V : Type} [CommGroup V] {n : ℕ}

@[expose] def NatThrough (L : Subgroup (MulAut V)) (α : ↥L →* Perm (Fin n)) (U : Subgroup V) :
    Prop :=
  ∃ π : ↥U →* Multiplicative (altHeart n), Function.Surjective π ∧
    π.ker = (U ⊓ fixV L).subgroupOf U ∧
    ∀ (l : ↥L) (u v : ↥U), (v : V) = (l : MulAut V) (u : V) →
      Multiplicative.toAdd (π v) = altAct (α l) (Multiplicative.toAdd (π u))

theorem isAltNaturalSection_iff_natThrough {L : Subgroup (MulAut V)} {U : Subgroup V} :
    IsAltNaturalSection L U n ↔ ∃ α : ↥L →* alternatingGroup (Fin n), Function.Surjective α ∧
      NatThrough L ((alternatingGroup (Fin n)).subtype.comp α) U := by
  constructor
  · rintro ⟨α, hα, π, hπ, hker, heq⟩
    refine ⟨α, hα, π, hπ, hker, fun l u v huv => ?_⟩
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
    rw [heq l u v huv x hx.symm, ← hx, altAct_mk]
    rfl
  · rintro ⟨α, hα, π, hπ, hker, heq⟩
    refine ⟨α, hα, π, hπ, hker, fun l u v huv x hx => ?_⟩
    rw [heq l u v huv, hx, altAct_mk]
    rfl

theorem NatThrough.conj {L : Subgroup (MulAut V)} {α α' : ↥L →* Perm (Fin n)} {U : Subgroup V}
    (h : NatThrough L α U) (σ : Perm (Fin n)) (hα : ∀ l, α' l = σ * α l * σ⁻¹) :
    NatThrough L α' U := by
  obtain ⟨π, hπ, hker, heq⟩ := h
  let φ : Multiplicative (altHeart n) →* Multiplicative (altHeart n) :=
    AddMonoidHom.toMultiplicative (altAct σ)
  have hφ : ∀ y, Multiplicative.toAdd (φ y) = altAct σ (Multiplicative.toAdd y) := fun _ => rfl
  refine ⟨φ.comp π, fun y => ?_, ?_, fun l u v huv => ?_⟩
  · obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (altAct σ⁻¹ (Multiplicative.toAdd y)))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [MonoidHom.comp_apply, hφ, hu, toAdd_ofAdd, altAct_apply_inv]
  · rw [← hker]
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h1
      have h2 := congrArg (fun y => altAct σ⁻¹ (Multiplicative.toAdd y)) h1
      simp only [hφ, altAct_inv_apply, toAdd_one, map_zero] at h2
      exact Multiplicative.toAdd.injective h2
    · intro h1
      rw [h1, map_one]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφ, hφ, heq l u v huv, hα, altAct_mul,
      altAct_mul, altAct_inv_apply]

theorem natThrough_of_isAltNaturalSection {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin n)}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) {U : Subgroup V}
    (h : IsAltNaturalSection (altPre ψ) U n) :
    NatThrough (altPre ψ) (ψ.comp (Subgroup.inclusion altPre_le)) U := by
  obtain ⟨α, hα, hnat⟩ := isAltNaturalSection_iff_natThrough.1 h
  have hbij : Function.Bijective (altPreHom ψ) :=
    ⟨altPreHom_injective hψ, altPreHom_surjective hA⟩
  let e := MulEquiv.ofBijective (altPreHom ψ) hbij
  let β : alternatingGroup (Fin n) →* alternatingGroup (Fin n) := α.comp e.symm.toMonoidHom
  have hβs : Function.Surjective β := hα.comp e.symm.surjective
  have hβi : Function.Injective β := Finite.injective_iff_surjective.2 hβs
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6).2
      (MulEquiv.ofBijective β ⟨hβi, hβs⟩)
  have hαl : ∀ l : ↥(altPre ψ), ((α l : alternatingGroup (Fin n)) : Perm (Fin n)) =
      σ * ψ (Subgroup.inclusion altPre_le l) * σ⁻¹ := by
    intro l
    have h1 : MulAut.conjNormal σ (altPreHom ψ l) = β (altPreHom ψ l) := by
      rw [hσ]; rfl
    have h2 : β (altPreHom ψ l) = α l := by
      change α (e.symm (e l)) = α l
      rw [e.symm_apply_apply]
    rw [← h2, ← h1, MulAut.conjNormal_apply, coe_altPreHom]
  refine hnat.conj σ⁻¹ fun l => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hαl, inv_inv]
  group

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
