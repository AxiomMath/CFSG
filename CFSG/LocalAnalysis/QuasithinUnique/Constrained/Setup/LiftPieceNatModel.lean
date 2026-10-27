module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannNat

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.Lift
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement

universe v

section ActSub

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

def actSub (L : Subgroup (V ≃ₗ[ZMod 2] V)) (I : Submodule (ZMod 2) V)
    (hI : ∀ l ∈ L, ∀ u ∈ I, l u ∈ I) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {y | ∃ l ∈ L, ∀ u ∈ I, y u = l u}
  one_mem' := ⟨1, L.one_mem, fun u _ => rfl⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨l₁, hl₁, h₁⟩ ⟨l₂, hl₂, h₂⟩
    refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, fun u hu => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₂ u hu, h₁ _ (hI l₂ hl₂ u hu)]
  inv_mem' := by
    rintro y ⟨l, hl, h⟩
    refine ⟨l⁻¹, L.inv_mem hl, fun u hu => ?_⟩
    have hlu : l⁻¹ u ∈ I := hI l⁻¹ (L.inv_mem hl) u hu
    have e : y (l⁻¹ u) = u := by rw [h _ hlu]; exact gl_apply_inv l u
    exact (LinearEquiv.symm_apply_eq y).2 e.symm

theorem natural_le_actSub {H T S : Subgroup (V ≃ₗ[ZMod 2] V)} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (layer : EvenSL2LayerOutput H T r F Lc)
    (hS : S = ⨆ j, T ⊓ Lc j) (i : Fin r) :
    Lc i ⊔ S ≤ actSub (Lc i) (commGL (Lc i) ⊤)
      (fun l hl u hu => isInvariant_commGL_self (Lc i) l hl u hu) := by
  refine sup_le (fun l hl => ⟨l, hl, fun u _ => rfl⟩) ?_
  rw [hS]
  refine iSup_le fun j => ?_
  by_cases hji : j = i
  · subst hji
    exact fun y hy => ⟨y, hy.2, fun u _ => rfl⟩
  · exact fun y hy => ⟨1, (Lc i).one_mem, fun u hu => by
      rw [layer.others_fix i j hji y hy.2 u hu]
      rfl⟩

end ActSub

section Rho

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

theorem natural_rho_model {H T S : Subgroup (V ≃ₗ[ZMod 2] V)} {F : Type} [Field F] {r : ℕ}
    {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)} (layer : EvenSL2LayerOutput H T r F Lc)
    (hnat : NaturalFamily H F r Lc) (hS : S = ⨆ j, T ⊓ Lc j) (i : Fin r) :
    ∃ (ϱ : ↥(Lc i ⊔ S) →* SL(2, F))
      (β : (↥(commGL (Lc i) ⊤) ⧸ fixIn (Lc i) (commGL (Lc i) ⊤)) ≃+ (Fin 2 → F)),
      (∀ (x : ↥(Lc i ⊔ S)) (u u' : ↥(commGL (Lc i) ⊤)),
        (u' : V) = (x : V ≃ₗ[ZMod 2] V) (u : V) →
          β (Submodule.Quotient.mk u') =
            (ϱ x : Matrix (Fin 2) (Fin 2) F).mulVec (β (Submodule.Quotient.mk u))) ∧
      (∀ g : SL(2, F), ∃ x : ↥(Lc i ⊔ S), ϱ x = g) ∧
      ∀ u : ↥(commGL (Lc i) ⊤),
        β (Submodule.Quotient.mk u) = 0 ↔ ∀ l ∈ Lc i, l (u : V) = (u : V) := by
  classical
  obtain ⟨θ, β, hcompat, -⟩ := hnat.model i
  have hLn : ∀ j, Lc j ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := by
    intro j
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (layer.commute j i hji)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hAn : S ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [hS]
    exact iSup_le fun j => inf_le_right.trans (hLn j)
  have hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i ⊔ S) (commGL (Lc i) ⊤) :=
    isInvariant_sup_subgroup (isInvariant_commGL_self (Lc i))
      (isInvariant_commGL_of_le_normalizer hAn)
  have key : ∀ l : ↥(Lc i), conjEnd β (actW (Lc i) S (commGL (Lc i) ⊤) hAn hI
      ⟨l, Subgroup.mem_sup_left l.2⟩) = natEndHom F (θ l) :=
    conjEnd_actW_of_mem hAn hI θ β hcompat
  have hact := natural_le_actSub layer hS i
  set φ := actW (Lc i) S (commGL (Lc i) ⊤) hAn hI with hφ
  have hex : ∀ x : ↥(Lc i ⊔ S), ∃ g : SL(2, F), conjEnd β (φ x) = natEndHom F g := by
    intro x
    obtain ⟨l, hl, hxl⟩ := hact x.2
    refine ⟨θ ⟨l, hl⟩, ?_⟩
    rw [← key ⟨l, hl⟩]
    congr 1
    apply LinearEquiv.ext
    intro q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hφ, actW_mk hAn hI, actW_mk hAn hI]
    congr 1
    apply Subtype.ext
    rw [resSub_apply, resSub_apply]
    exact hxl w w.2
  choose ρf hρf using hex
  have hmul : ∀ x y : ↥(Lc i ⊔ S), ρf (x * y) = ρf x * ρf y := by
    intro x y
    apply natEndHom_injective (F := F)
    rw [map_mul, ← hρf, ← hρf, ← hρf, map_mul, map_mul]
  have hone : ρf 1 = 1 := by
    apply natEndHom_injective (F := F)
    rw [map_one, ← hρf, map_one, map_one]
  refine ⟨{ toFun := ρf, map_one' := hone, map_mul' := hmul }, β, ?_, ?_, ?_⟩
  · intro x u u' hu
    have h1 : conjEnd β (φ x) (β (Submodule.Quotient.mk u)) = β (Submodule.Quotient.mk u') := by
      rw [conjEnd_apply, AddEquiv.symm_apply_apply, hφ, actW_mk hAn hI]
      congr 2
      apply Subtype.ext
      rw [resSub_apply]
      exact hu.symm
    rw [← h1, hρf x]
    rfl
  · intro g
    refine ⟨⟨(θ.symm g : ↥(Lc i)), Subgroup.mem_sup_left (θ.symm g).2⟩, ?_⟩
    apply natEndHom_injective (F := F)
    show natEndHom F (ρf _) = _
    rw [← hρf, key, θ.apply_symm_apply]
  · intro u
    rw [AddEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    exact Iff.rfl

end Rho

end CFSG.QuasithinUnique.Setup.Lift.Piece
