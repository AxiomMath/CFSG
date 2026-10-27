module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section Conj

variable {G : Type} [Group G]

private theorem mem_map_conj_iff {Y : Subgroup G} (c x : G) :
    x ∈ Y.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ Y := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem centralizer_map_conj_eq (V : Subgroup G) (c : G) :
    centralizer ((V.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (V : Set G)).map (MulAut.conj c).toMonoidHom :=
  Transport.centralizer_map_of_le_range (MulAut.conj c).injective (by
    intro y _
    exact ⟨c⁻¹ * y * c, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩)

theorem hasNormal2Compl_map_conj {X : Subgroup G} (c : G) (h : HasNormal2Compl X) :
    HasNormal2Compl (X.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨N, hNX, hNn, hNodd, a, ha⟩ := h
  refine ⟨N.map (MulAut.conj c).toMonoidHom, Subgroup.map_mono hNX, ?_, ?_, a, ?_⟩
  · refine ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : c⁻¹ * (n : G) * c ∈ N := (mem_map_conj_iff c _).1 hn
    have hy' : c⁻¹ * (y : G) * c ∈ X := (mem_map_conj_iff c _).1 y.2
    have := hNn.conj_mem (⟨c⁻¹ * (n : G) * c, hNX hn'⟩ : ↥X) (Subgroup.mem_subgroupOf.2 hn')
      ⟨_, hy'⟩
    have h2 := Subgroup.mem_subgroupOf.1 this
    rw [mem_map_conj_iff]
    have e : c⁻¹ * ((y : G) * (n : G) * (y : G)⁻¹) * c =
        (c⁻¹ * (y : G) * c) * (c⁻¹ * (n : G) * c) * (c⁻¹ * (y : G) * c)⁻¹ := by group
    rw [show ((y * n * y⁻¹ : ↥(X.map (MulAut.conj c).toMonoidHom)) : G) =
      (y : G) * (n : G) * (y : G)⁻¹ from rfl, e]
    exact h2
  · have h1 : Nat.card ↥(N.map (MulAut.conj c).toMonoidHom) = Nat.card ↥N :=
      Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [h1]
    exact hNodd
  · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj c).toMonoidHom) N X
      (MulAut.conj c).injective
    exact this.trans ha

theorem O2Of_map_conj [Finite G] (X : Subgroup G) (c : G) :
    O2Of (X.map (MulAut.conj c).toMonoidHom) = (O2Of X).map (MulAut.conj c).toMonoidHom := by
  have hs : Function.Surjective ((MulAut.conj c).toMonoidHom.subgroupMap X) :=
    MonoidHom.subgroupMap_surjective _ X
  have h := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual
    ((MulAut.conj c).toMonoidHom.subgroupMap X) hs (p := 2) Nat.prime_two
  unfold O2Of
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem dihedral_sylow_O2Of_of_eq [Finite G] {X X' : Subgroup G} (c : G)
    (hX : X' = X.map (MulAut.conj c).toMonoidHom)
    (h : ∀ P : Sylow 2 ↥(O2Of X), IsDihedral ↥P) :
    ∀ P : Sylow 2 ↥(O2Of X'), IsDihedral ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hX
  intro P'
  have hO := O2Of_map_conj X c
  let ψ : ↥(O2Of X) ≃* ↥(O2Of (X.map (MulAut.conj c).toMonoidHom)) :=
    ((MulAut.conj c).subgroupMap (O2Of X)).trans (MulEquiv.subgroupCongr hO.symm)
  let P : Sylow 2 ↥(O2Of X) := P'.mapSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  have hP : (P : Subgroup ↥(O2Of X)) =
      (P' : Subgroup ↥(O2Of (X.map (MulAut.conj c).toMonoidHom))).map ψ.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ P'
  obtain ⟨m, k, hm, hk, ⟨f⟩⟩ := h P
  exact ⟨m, k, hm, hk, ⟨((Subgroup.equivMapOfInjective
    (P' : Subgroup ↥(O2Of (X.map (MulAut.conj c).toMonoidHom))) ψ.symm.toMonoidHom
    ψ.symm.injective).trans (MulEquiv.subgroupCongr hP.symm)).trans f⟩⟩

end Conj

section Main

theorem lemma29Alt_map_conj {G : Type} [Group G] [Finite G] {z : G} {k : Kind} (V : Subgroup G)
    (c : G) (h : Lemma29Alt z k V) :
    Lemma29Alt z k (V.map (MulAut.conj c).toMonoidHom) := by
  rcases h with h | ⟨hk, hdih, hz⟩ | ⟨hk, hb⟩
  · left
    rw [centralizer_map_conj_eq]
    exact hasNormal2Compl_map_conj c h
  · right; left
    refine ⟨hk, dihedral_sylow_O2Of_of_eq c (centralizer_map_conj_eq V c) hdih, ?_⟩
    rcases hz with hz | ⟨t, g, hts, hg⟩
    · left
      intro u hu hzu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      refine hz v hv (hzu.trans (isConj_iff.mpr ⟨c⁻¹, ?_⟩))
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · right
      refine ⟨t, g * c⁻¹, hts, ?_⟩
      rw [← hg]
      unfold conjugate
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulAut.conj_apply]
      group
  · right; right
    exact ⟨hk, lemma29b_conj V c hb⟩

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
