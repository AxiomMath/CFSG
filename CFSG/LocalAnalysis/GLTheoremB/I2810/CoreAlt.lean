module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLModels
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSym
import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSp
import CFSG.HardMathSupport.Cooperstein.StructureLie.McLaughlinShape

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

theorem altHeart_bridge_proof (m : ℕ) :
    ∃ γ : CFSG.RankThree.PartTwo.altHeart m ≃+ AltHeart m,
      ∀ (σ : Equiv.Perm (Fin m)) (x : CFSG.QuasithinUnique.evenWeight m),
        γ (CFSG.RankThree.PartTwo.evenWeightPerm σ x : CFSG.RankThree.PartTwo.altHeart m) =
          altHeartAct m σ (γ (x : CFSG.RankThree.PartTwo.altHeart m)) := by
  have hE : CFSG.QuasithinUnique.evenWeight m = evenWt m := by
    ext x
    simp only [CFSG.QuasithinUnique.evenWeight, evenWt, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply,
      AddMonoidHom.finsetSum_apply, Pi.evalAddMonoidHom_apply]
  let e : ↥(CFSG.QuasithinUnique.evenWeight m) ≃+ ↥(evenWt m) :=
    { toFun := fun x => ⟨x.1, by rw [← hE]; exact x.2⟩
      invFun := fun y => ⟨y.1, by rw [hE]; exact y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hmap : (CFSG.RankThree.PartTwo.evenWeightOnes m).map e.toAddMonoidHom =
      (constWt m ⊓ evenWt m).addSubgroupOf (evenWt m) := by
    ext y
    have h1 : y ∈ (CFSG.RankThree.PartTwo.evenWeightOnes m).map e.toAddMonoidHom ↔
        e.symm y ∈ CFSG.RankThree.PartTwo.evenWeightOnes m := AddSubgroup.mem_map_equiv
    rw [h1, CFSG.RankThree.PartTwo.evenWeightOnes, AddSubgroup.mem_addSubgroupOf,
      AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h
      exact ⟨h, y.2⟩
    · intro h
      exact h.1
  let γ : CFSG.RankThree.PartTwo.altHeart m ≃+ AltHeart m :=
    QuotientAddGroup.congr (CFSG.RankThree.PartTwo.evenWeightOnes m)
      ((constWt m ⊓ evenWt m).addSubgroupOf (evenWt m)) e hmap
  refine ⟨γ, fun σ x => ?_⟩
  show QuotientAddGroup.mk (e (CFSG.RankThree.PartTwo.evenWeightPerm σ x)) =
    altHeartAct m σ (QuotientAddGroup.mk (e x))
  rfl

theorem sym_isAlt_of_perfect {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} (hsym : SymSpShape H)
    (hL : L = ⁅H, H⁆) (hperf : ⁅L, L⁆ = L) (hL1 : L ≠ ⊥) : ∃ m : ℕ, 5 ≤ m ∧ IsAltModel L m := by
  haveI : FiniteDimensional (ZMod 2) P := Module.Finite.of_finite
  have h3 : 3 ≤ Module.finrank (ZMod 2) P := by
    by_contra hlt
    exact hL1 (eq_bot_of_isPerfect_of_finrank_le_two (by omega) L hperf)
  rcases hsym with ⟨h4, f, hnd, halt, hH⟩ | ⟨he, hsym⟩
  · obtain ⟨β, hβ⟩ :=
      exists_heartSix_of_symplectic_four f hnd halt h4 (heartRep_injective (by norm_num))
    exact ⟨6, by norm_num, isAltModel_of_heart (by norm_num) β (by rw [hH]; exact hβ) hL⟩
  · obtain ⟨k, hk⟩ := he
    rcases hsym with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · exact ⟨Module.finrank (ZMod 2) P + 1, by omega,
        isAltModel_of_sumZero (by omega) ⟨k, by omega⟩ β hβ hL⟩
    · exact ⟨Module.finrank (ZMod 2) P + 2, by omega, isAltModel_of_heart (by omega) β hβ hL⟩

section AltModel
variable {X : Type} [Group X] [Finite X] {W K : Subgroup X} [W.Normal]

theorem altModel_of_isAlt_proof {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P]
    [Module (ZMod 2) P] [Finite P]
    {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P} {φs : ↥U₁ →* Multiplicative P}
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φs)
    (htriv : ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1) {m : ℕ} (hm : 5 ≤ m)
    (σ : Equiv.Perm (Fin m)) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
    (θ : ↥((K.subgroupOf (Mof K a)).map ρ) ≃* ↥(alternatingGroup (Fin m))) (hσ : σ.IsSwap)
    (hφ : ∀ (g : ↥((K.subgroupOf (Mof K a)).map ρ)) (w : P)
      (x : CFSG.QuasithinUnique.evenWeight m), φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
            CFSG.RankThree.PartTwo.altHeart m))
    (hσθ : ∀ g g' : ↥((K.subgroupOf (Mof K a)).map ρ),
      (g' : LinearMap.GeneralLinearGroup (ZMod 2) P) = ρ (aM K a) * g * (ρ (aM K a))⁻¹ →
        (θ g' : Equiv.Perm (Fin m)) = σ * (θ g : Equiv.Perm (Fin m)) * σ⁻¹) :
    AltModel W K a U₁ U₂ := by
  obtain ⟨γ, hγ⟩ := altHeart_bridge_proof m
  let incl : ↥K →* ↥(Mof K a) := Subgroup.inclusion (le_sup_left : K ≤ Mof K a)
  let θ' : ↥K →* ↥(alternatingGroup (Fin m)) := θ.toMonoidHom.comp (rhoK K a ρ)
  have hrho : ∀ k : ↥K, ((rhoK K a ρ k : ↥((K.subgroupOf (Mof K a)).map ρ)) :
      LinearMap.GeneralLinearGroup (ZMod 2) P) = ρ (incl k) := fun k => rfl
  refine ⟨m, θ', σ, hm, ?_, ?_, hσ, ?_, ?_⟩
  ·
    intro y
    obtain ⟨z, rfl⟩ := θ.surjective y
    obtain ⟨z, m', hm', rfl⟩ := z
    refine ⟨⟨m', Subgroup.mem_subgroupOf.1 hm'⟩, ?_⟩
    show θ (rhoK K a ρ ⟨m', _⟩) = θ _
    congr 1
  · intro k hk
    show θ (rhoK K a ρ k) = 1
    have : rhoK K a ρ k = 1 := Subtype.ext (by rw [hrho]; exact htriv k hk)
    rw [this, map_one]
  · intro k k' hk'
    have e : incl k' = aM K a * incl k * (aM K a)⁻¹ := Subtype.ext (by simp [incl, aM, hk'])
    exact hσθ (rhoK K a ρ k) (rhoK K a ρ k') (by rw [hrho, hrho, e, map_mul, map_mul, map_inv])
  ·
    let ψ : Multiplicative P →* Multiplicative (AltHeart m) :=
      AddMonoidHom.toMultiplicative (γ.toAddMonoidHom.comp φ.toAddMonoidHom)
    refine ⟨ψ.comp φs, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨p, hp⟩ := (γ.surjective.comp φ.surjective) (Multiplicative.toAdd y)
      obtain ⟨u, hu⟩ := hd.surj (Multiplicative.ofAdd p)
      refine ⟨u, ?_⟩
      show Multiplicative.ofAdd (γ (φ (Multiplicative.toAdd (φs u)))) = y
      rw [hu]
      simpa using congrArg Multiplicative.ofAdd hp
    · intro u
      rw [← hd.ker u]
      have key : (ψ.comp φs) u = Multiplicative.ofAdd (γ (φ (Multiplicative.toAdd (φs u)))) := rfl
      constructor
      · intro h1
        have h1' := key.symm.trans h1
        have h2 : γ (φ (Multiplicative.toAdd (φs u))) = 0 := by
          have := congrArg Multiplicative.toAdd h1'
          simpa using this
        have h3 : Multiplicative.toAdd (φs u) = 0 := by
          apply φ.injective
          apply γ.injective
          rw [h2, φ.map_zero]
          exact γ.map_zero.symm
        rw [← ofAdd_toAdd (φs u), h3]; rfl
      · intro h1
        refine key.trans ?_
        rw [h1]
        show Multiplicative.ofAdd (γ (φ 0)) = 1
        rw [φ.map_zero]
        exact congrArg Multiplicative.ofAdd γ.map_zero
    · intro ℓ u u' hu'
      have h1 := hd.equiv (incl ℓ) u u' hu'
      show Multiplicative.ofAdd (γ (φ (Multiplicative.toAdd (φs u')))) =
        Multiplicative.ofAdd (altHeartAct m ((θ' ℓ : ↥(alternatingGroup (Fin m))) :
          Equiv.Perm (Fin m)) (γ (φ (Multiplicative.toAdd (φs u)))))
      rw [h1, toAdd_ofAdd]
      obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (φ (Multiplicative.toAdd (φs u)))
      have h2 := hφ (rhoK K a ρ ℓ) (Multiplicative.toAdd (φs u)) x hx.symm
      rw [hrho] at h2
      rw [h2, hγ, ← hx]
      rfl

end AltModel

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
