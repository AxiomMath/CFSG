module

public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74.GLS.Bg

theorem layer_eq_bot_of_mulEquiv_of_layer_eq_bot {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hX : layer X = ⊥) : layer Y = ⊥ := by
  refine sSup_eq_bot.mpr fun L hL => ?_
  have hL' : IsComponent (L.map e.symm.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e.symm hL
  have hle : L.map e.symm.toMonoidHom ≤ layer X := le_sSup hL'
  rw [hX, le_bot_iff] at hle
  have hnt : Nontrivial ↥(L.map e.symm.toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  exact absurd hle ((Subgroup.nontrivial_iff_ne_bot _).mp hnt)

theorem layer_inf_eq_bot_of_isSubnormal {M : Type*} [Group M] {J D : Subgroup M}
    (hJ : J.IsSubnormal) (hD : layer ↥D = ⊥) : layer ↥(J ⊓ D) = ⊥ := by
  refine sSup_eq_bot.mpr fun L hL => ?_
  have hP : ((J ⊓ D).subgroupOf D).IsSubnormal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact hJ.subgroupOf
  let e : ↥(J ⊓ D) ≃* ↥((J ⊓ D).subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hL' : IsComponent (L.map e.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e hL
  have hL'' : IsComponent ((L.map e.toMonoidHom).map ((J ⊓ D).subgroupOf D).subtype) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L.map e.toMonoidHom).equivMapOfInjective _ (Subgroup.subtype_injective _)) hL'.1,
      hL'.2.trans' hP⟩
  have hle : (L.map e.toMonoidHom).map ((J ⊓ D).subgroupOf D).subtype ≤ layer ↥D :=
    le_sSup hL''
  rw [hD, le_bot_iff] at hle
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL''.1
  exact absurd hle ((Subgroup.nontrivial_iff_ne_bot _).mp hnt)

theorem layer_comp_inf_cent_eq_bot {G : Type} [Group G] [Finite G] {N : Subgroup G}
    {J : Subgroup ↥N} (hJ : IsComponent J) {W : Subgroup G} {v : G} (hvN : v ∈ N)
    (hJW : J.map N.subtype ≤ centralizer (W : Set G))
    (hEm : Em (N ⊓ centralizer ((W ⊔ Subgroup.zpowers v : Subgroup G) : Set G)) = ⊥) :
    layer ↥(J ⊓ centralizer ({(⟨v, hvN⟩ : ↥N)} : Set ↥N)) = ⊥ := by
  set C : Subgroup G := N ⊓ centralizer ((W ⊔ Subgroup.zpowers v : Subgroup G) : Set G) with hC
  have hCN : C ≤ N := inf_le_left
  have hLC : layer ↥C = ⊥ := by
    have h : (layer ↥C).map C.subtype = ⊥ := hEm
    exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h
  have hLD : layer ↥(C.subgroupOf N) = ⊥ :=
    layer_eq_bot_of_mulEquiv_of_layer_eq_bot (Subgroup.subgroupOfEquivOfLe hCN).symm hLC
  have hA : J ⊓ centralizer ({(⟨v, hvN⟩ : ↥N)} : Set ↥N) = J ⊓ C.subgroupOf N := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun hxJ => ?_
    have hxW : ∀ w ∈ W, w * (x : G) = (x : G) * w := fun w hw =>
      Subgroup.mem_centralizer_iff.mp (hJW ⟨x, hxJ, rfl⟩) w hw
    constructor
    · intro hxv
      have hvx : v * (x : G) = (x : G) * v := (congrArg Subtype.val hxv).symm
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have hle : W ⊔ Subgroup.zpowers v ≤ centralizer ({(x : G)} : Set G) := by
        refine sup_le (fun w hw => ?_) ((Subgroup.zpowers_le).mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxW w hw)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hvx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    · rintro ⟨-, hxC⟩
      have hv : v ∈ ((W ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
        (le_sup_right : Subgroup.zpowers v ≤ W ⊔ Subgroup.zpowers v) (Subgroup.mem_zpowers v)
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC v hv).symm
  rw [hA]
  exact layer_inf_eq_bot_of_isSubnormal hJ.2 hLD

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
