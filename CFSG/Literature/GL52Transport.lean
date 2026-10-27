module

public import CFSG.Literature.GL52Group
import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Literature.GL52

open CFSG

variable {G : Type*} [Group G] (φ : G ≃* G)

theorem map_centralizer_equiv (S : Set G) :
    (Subgroup.centralizer S).map φ.toMonoidHom = Subgroup.centralizer (φ '' S) := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    have := congrArg φ (h s hs)
    simpa using this
  · intro h s hs
    have := congrArg φ.symm (h (φ s) ⟨s, hs, rfl⟩)
    simpa using this

theorem map_centralizer_subgroup (H : Subgroup G) :
    (Subgroup.centralizer (H : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ((H.map φ.toMonoidHom : Subgroup G) : Set G) := by
  rw [map_centralizer_equiv, Subgroup.coe_map]
  rfl

theorem map_centralizer_singleton (x : G) :
    (Subgroup.centralizer {x}).map φ.toMonoidHom = Subgroup.centralizer {φ x} := by
  rw [map_centralizer_equiv, Set.image_singleton]

theorem map_zpowers_equiv (x : G) :
    (Subgroup.zpowers x).map φ.toMonoidHom = Subgroup.zpowers (φ x) :=
  MonoidHom.map_zpowers _ x

theorem map_inf_equiv (H K : Subgroup G) :
    (H ⊓ K).map φ.toMonoidHom = H.map φ.toMonoidHom ⊓ K.map φ.toMonoidHom :=
  Subgroup.map_inf_eq H K φ.toMonoidHom φ.injective

theorem map_bot_equiv : (⊥ : Subgroup G).map φ.toMonoidHom = ⊥ := Subgroup.map_bot _

@[expose] noncomputable def equivMap (H : Subgroup G) : H ≃* H.map φ.toMonoidHom :=
  H.equivMapOfInjective _ φ.injective

theorem sylow_eq_map_conj [Finite G] {p : ℕ} [Fact p.Prime] (P Q : Sylow p G) :
    ∃ g : G, (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

end CFSG.Literature.GL52
