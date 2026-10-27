module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerConj

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

@[expose] def fixIn (L : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V) : Submodule k ↥I :=
  (fixGL L).comap I.subtype

theorem mem_fixIn {L : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V} {w : ↥I} :
    w ∈ fixIn L I ↔ ∀ l ∈ L, l (w : V) = w := Iff.rfl

theorem fixIn_invariant {L X : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
    (hXL : X ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) X I) :
    ∀ x : ↥X, ∀ z ∈ fixIn L I,
      resSub (MonoidHom.id (V ≃ₗ[k] V)) X I hI x z ∈ fixIn L I := by
  intro x z hz l hl
  have hc := conj_inv_mem_of_mem_normalizer (hXL x.2) hl
  have hz' : ((x : V ≃ₗ[k] V)⁻¹ * l * (x : V ≃ₗ[k] V)) (z : V) = z := hz _ hc
  have e : ((resSub (MonoidHom.id (V ≃ₗ[k] V)) X I hI x z : ↥I) : V) = (x : V ≃ₗ[k] V) z :=
    resSub_apply _ _ _ _ _ _
  show l ((resSub (MonoidHom.id (V ≃ₗ[k] V)) X I hI x z : ↥I) : V) =
    ((resSub (MonoidHom.id (V ≃ₗ[k] V)) X I hI x z : ↥I) : V)
  rw [e]
  have h4 : (x : V ≃ₗ[k] V)⁻¹ (l ((x : V ≃ₗ[k] V) z)) = z := hz'
  calc l ((x : V ≃ₗ[k] V) z) = (x : V ≃ₗ[k] V) ((x : V ≃ₗ[k] V)⁻¹ (l ((x : V ≃ₗ[k] V) z))) :=
        (gl_apply_inv _ _).symm
    _ = (x : V ≃ₗ[k] V) z := by rw [h4]

@[expose] noncomputable def actW (L A : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I) :
    ↥(L ⊔ A) →* ((↥I ⧸ fixIn L I) ≃ₗ[k] (↥I ⧸ fixIn L I)) :=
  quotHom (resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I hI) (fixIn L I)
    (fixIn_invariant (sup_le Subgroup.le_normalizer hAn) hI)

@[expose] noncomputable def actOn (L A : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V)
    (hAn : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I) (S : Subgroup (V ≃ₗ[k] V))
    (hS : S ≤ L ⊔ A) : ↥S →* ((↥I ⧸ fixIn L I) ≃ₗ[k] (↥I ⧸ fixIn L I)) :=
  (actW L A I hAn hI).comp (Subgroup.inclusion hS)

structure ComponentSection (L A : Subgroup (V ≃ₗ[k] V)) (I : Submodule k V) : Prop where
  A_norm : A ≤ Subgroup.normalizer (L : Set (V ≃ₗ[k] V))
  L_perf : ⁅L, A⁆ = L
  inv_L : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) L I
  inv_A : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) A I
  comm : commGL L I = I
  irr : IsIrrQuot (MonoidHom.id (V ≃ₗ[k] V)) L I
  inj : ∀ x : ↥(L ⊔ A),
    actW L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) x = 1 →
      resSub (MonoidHom.id (V ≃ₗ[k] V)) (L ⊔ A) I (isInvariant_sup_subgroup inv_L inv_A) x = 1
  Lbar_ne : (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) L le_sup_left).range ≠ ⊥
  Lbar_qs : CFSG.IsQuasisimple
    ↥(actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) L le_sup_left).range
  Abar_ne : (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) A le_sup_right).range ≠ ⊥
  Abar_elem : CFSG.IsElementaryAbelian 2
    ↥(actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) A le_sup_right).range
  Abar_off : Nat.card (↥I ⧸ fixIn L I) ≤ weight (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] _))
    (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) A le_sup_right).range
  Abar_quad : QuadAct (MonoidHom.id ((↥I ⧸ fixIn L I) ≃ₗ[k] _))
    (actOn L A I A_norm (isInvariant_sup_subgroup inv_L inv_A) A le_sup_right).range
  AI_max : ∀ B : Subgroup (↥I ≃ₗ[k] ↥I),
    B ≤ (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I inv_A).range →
      weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) B ≤
        weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I inv_A).range
  AI_strict : ∀ B : Subgroup (↥I ≃ₗ[k] ↥I),
    B ≤ (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I inv_A).range → ⊥ < B →
      B < (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I inv_A).range →
        weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) B <
          weight (MonoidHom.id (↥I ≃ₗ[k] ↥I)) (resSub (MonoidHom.id (V ≃ₗ[k] V)) A I inv_A).range

end CFSG.QuasithinUnique.Setup.Layer
