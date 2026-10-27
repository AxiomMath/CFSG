module

public import CFSG.HardMathSupport.U4FF.Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.HardMathSupport.U4FF

namespace ClassFinal

open CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing repD)

variable {S : Type} [CommGroup S] [Fact (∀ s : S, s * s = 1)]

@[expose] noncomputable def binRep {G : Type} [Group G] (L : Subgroup (MulAut S)) (η : ↥L ≃* G) :
    Representation (ZMod 2) G (Additive S) :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := Additive S)).comp
    ((binaryLin.comp L.subtype).comp η.symm.toMonoidHom)

theorem binRep_apply {G : Type} [Group G] (L : Subgroup (MulAut S)) (η : ↥L ≃* G) (g : G)
    (w : Additive S) :
    binRep L η g w = binaryLin (((η.symm g : ↥L)) : MulAut S) w := rfl

theorem binRep_eta {G : Type} [Group G] (L : Subgroup (MulAut S)) (η : ↥L ≃* G) (x : ↥L)
    (s : S) : binRep L η (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut S) s) := by
  rw [binRep_apply, MulEquiv.symm_apply_apply, binaryLin_apply]

theorem binRep_eta_lin {G : Type} [Group G] (L : Subgroup (MulAut S)) (η : ↥L ≃* G) (x : ↥L) :
    binRep L η (η x) = (binaryLin ((x : ↥L) : MulAut S) : Additive S →ₗ[ZMod 2] Additive S) := by
  apply LinearMap.ext
  intro w
  rw [binRep_apply, MulEquiv.symm_apply_apply]
  rfl

theorem binRep_ne_one {G : Type} [Group G] (L : Subgroup (MulAut S)) (η : ↥L ≃* G) (x : ↥L)
    (hx : x ≠ 1) : binRep L η (η x) ≠ 1 := by
  intro h
  apply hx
  have h1 : binaryLin ((x : ↥L) : MulAut S) = 1 := by
    apply LinearEquiv.ext
    intro w
    have := LinearMap.congr_fun h w
    rwa [binRep_apply, MulEquiv.symm_apply_apply, Module.End.one_apply] at this
  have h2 := binaryLin_injective (W := S) (h1.trans (map_one binaryLin).symm)
  exact Subtype.ext h2

theorem nontrivial_of_isU4Group {n : ℕ} {L : Subgroup (MulAut S)} (hL : IsU4Group n L) :
    Nontrivial S ∧ ∃ x : ↥L, x ≠ 1 := by
  haveI := isSimpleGroup_of_isU4Group hL
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
  refine ⟨?_, x, hx⟩
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hx
  apply Subtype.ext
  exact MulEquiv.ext fun s => Subsingleton.elim _ _

theorem binRep_isIrreducible {G : Type} [Group G] {L : Subgroup (MulAut S)} (η : ↥L ≃* G)
    [Nontrivial S] (hirr : IsIrrOn L) : (binRep L η).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  let W : Subgroup S :=
    { carrier := {s | Additive.ofMul s ∈ U}
      mul_mem' := fun {a b} ha hb => by
        have : Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b := rfl
        show Additive.ofMul (a * b) ∈ U
        rw [this]
        exact U.add_mem ha hb
      one_mem' := by
        show Additive.ofMul (1 : S) ∈ U
        exact U.zero_mem
      inv_mem' := fun {a} ha => by
        have : Additive.ofMul a⁻¹ = -Additive.ofMul a := rfl
        show Additive.ofMul a⁻¹ ∈ U
        rw [this]
        exact U.neg_mem ha }
  have hW : ∀ x ∈ L, ∀ w ∈ W, x w ∈ W := by
    intro x hx w hw
    have h1 := hU (η ⟨x, hx⟩) (Additive.ofMul w) hw
    rwa [binRep_eta] at h1
  rcases hirr W hW with h | h
  · left
    rw [eq_bot_iff]
    intro u hu
    have : Additive.toMul u ∈ W := by
      show Additive.ofMul (Additive.toMul u) ∈ U
      exact hu
    rw [h, Subgroup.mem_bot] at this
    rw [Submodule.mem_bot]
    exact Additive.toMul.injective this
  · right
    rw [eq_top_iff]
    intro u _
    have : Additive.toMul u ∈ W := by rw [h]; trivial
    exact this

variable [Finite S]

theorem exists_coords {G : Type} [Group G] {L : Subgroup (MulAut S)} (η : ↥L ≃* G)
    (ρ : Representation (ZMod 2) G (Additive S)) [Fact ρ.IsIrreducible]
    (hρ : ∀ (x : ↥L) (s : S), ρ (η x) (Additive.ofMul s) = Additive.ofMul ((x : MulAut S) s))
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) (Additive S)) :
    ∃ (ε : S ≃* Multiplicative (Fin m → EndRing ρ)) (R : ↥L →* GL (Fin m) (EndRing ρ)),
      (∀ (x : ↥L) (s : S), ε ((x : MulAut S) s) = Multiplicative.ofAdd
          ((R x : Matrix (Fin m) (Fin m) (EndRing ρ)).mulVec (Multiplicative.toAdd (ε s)))) ∧
      ∀ x : ↥L, ((R x : GL (Fin m) (EndRing ρ)) : Matrix (Fin m) (Fin m) (EndRing ρ)) =
        CFSG.QuasithinUnique.Setup.SL2Modules.matRep b (η x) := by
  let ε : S ≃* Multiplicative (Fin m → EndRing ρ) :=
    { toFun := fun s => Multiplicative.ofAdd (b.equivFun (Additive.ofMul s))
      invFun := fun v => Additive.toMul (b.equivFun.symm (Multiplicative.toAdd v))
      left_inv := fun s => by
        show Additive.toMul (b.equivFun.symm (Multiplicative.toAdd
          (Multiplicative.ofAdd (b.equivFun (Additive.ofMul s))))) = s
        rw [toAdd_ofAdd, LinearEquiv.symm_apply_apply]
        rfl
      right_inv := fun v => by
        show Multiplicative.ofAdd (b.equivFun (Additive.ofMul (Additive.toMul
          (b.equivFun.symm (Multiplicative.toAdd v))))) = v
        rw [ofMul_toMul, LinearEquiv.apply_symm_apply]
        rfl
      map_mul' := fun s t => by
        have : Additive.ofMul (s * t) = Additive.ofMul s + Additive.ofMul t := rfl
        simp only [this, map_add, ofAdd_add] }
  let R : ↥L →* GL (Fin m) (EndRing ρ) :=
    ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b).toHomUnits).comp η.toMonoidHom
  refine ⟨ε, R, fun x s => ?_, fun x => rfl⟩
  have hcoord : ∀ (g : G) (w : Additive S),
      (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).mulVec (b.equivFun w) =
        b.equivFun (ρ g w) := fun g w =>
    LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
  have h1 : Additive.ofMul ((x : MulAut S) s) = ρ (η x) (Additive.ofMul s) := (hρ x s).symm
  change Multiplicative.ofAdd (b.equivFun (Additive.ofMul ((x : MulAut S) s))) = _
  rw [h1, ← hcoord]
  rfl

end ClassFinal

end CFSG.HardMathSupport.U4FF
