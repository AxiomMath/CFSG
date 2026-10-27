module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect3

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped commutatorElement

universe v

section Generic

theorem conjSub_map_hom {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (a : X)
    (K : Subgroup X) : conjSub (f a) (K.map f) = (conjSub a K).map f := by
  ext y
  rw [mem_conjSub, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨a * x * a⁻¹, ?_, ?_⟩
    · rw [mem_conjSub]
      simpa [mul_assoc] using hx
    · rw [map_mul, map_mul, hxy, map_inv]
      group
  · rintro ⟨x, hx, rfl⟩
    refine ⟨a⁻¹ * x * a, mem_conjSub.1 hx, ?_⟩
    rw [map_mul, map_mul, map_inv]

end Generic

section Main

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem actOn_range {H A : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
    (hAn : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)))
    (hI : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I) (S : Subgroup (V ≃ₗ[k] V))
    (hS : S ≤ H ⊔ A) :
    (actOn H A I hAn hI S hS).range = (S.subgroupOf (H ⊔ A)).map (actW H A I hAn hI) := by
  unfold actOn
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

theorem isIrrAct_actW {H A : Subgroup (V ≃ₗ[k] V)} {I : Submodule k V}
    (hAn : A ≤ Subgroup.normalizer (H : Set (V ≃ₗ[k] V)))
    (hinv : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I)
    (hinvH : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H I)
    (hirr : IsIrrQuot (MonoidHom.id (V ≃ₗ[k] V)) H I) :
    IsIrrAct ((H.subgroupOf (H ⊔ A)).map (actW H A I hAn hinv)) := by
  intro U hU
  let U' : Submodule k V := (U.comap (fixIn H I).mkQ).map I.subtype
  have hU'inv : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H U' := by
    rintro h hh _ ⟨ũ, hũ, rfl⟩
    refine ⟨resSub (MonoidHom.id (V ≃ₗ[k] V)) H I hinvH ⟨h, hh⟩ ũ, ?_,
      resSub_apply (MonoidHom.id (V ≃ₗ[k] V)) H I hinvH ⟨h, hh⟩ ũ⟩
    have h0 : resSub (MonoidHom.id (V ≃ₗ[k] V)) H I hinvH ⟨h, hh⟩ ũ =
        resSub (MonoidHom.id (V ≃ₗ[k] V)) (H ⊔ A) I hinv ⟨h, Subgroup.mem_sup_left hh⟩ ũ :=
      Subtype.ext (by rw [resSub_apply, resSub_apply])
    have h1 : actW H A I hAn hinv ⟨h, Subgroup.mem_sup_left hh⟩
        (Submodule.Quotient.mk ũ : ↥I ⧸ fixIn H I) =
        Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) H I hinvH ⟨h, hh⟩ ũ) := by
      rw [actW_mk, h0]
    show (Submodule.Quotient.mk (resSub (MonoidHom.id (V ≃ₗ[k] V)) H I hinvH ⟨h, hh⟩ ũ) :
      ↥I ⧸ fixIn H I) ∈ U
    rw [← h1]
    exact hU _ ⟨⟨h, Subgroup.mem_sup_left hh⟩, hh, rfl⟩ _ hũ
  have hU'le : U' ≤ I := Submodule.map_subtype_le I _
  have hfix : I ⊓ fixSub (MonoidHom.id (V ≃ₗ[k] V)) H ≤ U' := by
    rintro u ⟨huI, hufix⟩
    refine ⟨⟨u, huI⟩, ?_, rfl⟩
    show (Submodule.Quotient.mk (⟨u, huI⟩ : ↥I) : ↥I ⧸ fixIn H I) ∈ U
    have hmem : (⟨u, huI⟩ : ↥I) ∈ fixIn H I := hufix
    rw [(Submodule.Quotient.mk_eq_zero _).2 hmem]
    exact U.zero_mem
  rcases hirr.2 U' hU'inv hfix hU'le with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun w hw => ?_
    obtain ⟨ũ, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hm : (ũ : V) ∈ U' := ⟨ũ, hw, rfl⟩
    rw [h] at hm
    exact (Submodule.Quotient.mk_eq_zero _).2 hm.2
  · right
    refine (Submodule.eq_top_iff').2 fun w => ?_
    obtain ⟨ũ, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hm : (ũ : V) ∈ U' := by
      rw [h]
      exact ũ.2
    obtain ⟨ũ', hũ', hũ'eq⟩ := hm
    have : ũ' = ũ := Subtype.ext hũ'eq
    rw [this] at hũ'
    exact hũ'

end Main

end CFSG.QuasithinUnique.Setup.Layer
