module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem c3b_fixedSubgroup_conj {G : Type} [Group G] (t : G) :
    CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj t) =
      centralizer ({t} : Set G) := by
  ext x
  change t * x * t⁻¹ = x ↔ x ∈ centralizer ({t} : Set G)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h]
    group

theorem c3b_orderOf_conj {G : Type} [Group G] (hZ : center G = ⊥) {t : G} (ht : orderOf t = 2) :
    orderOf (MulAut.conj t) = 2 := by
  apply orderOf_eq_prime
  · have ht2 : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    rw [← map_pow, ht2, map_one]
  · intro h
    have htmem : t ∈ center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : t * g * t⁻¹ = g := by
        have := DFunLike.congr_fun h g
        rwa [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * t = t * g * t⁻¹ * t := by rw [hg]
        _ = t * g := by group
    have ht1 : t = 1 := by
      have : t ∈ (⊥ : Subgroup G) := hZ ▸ htmem
      simpa using this
    rw [ht1, orderOf_one] at ht
    omega

theorem c3b_lieModel_of_component
    (hCL1 : CFSG.ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    {G : Type} [Group G] (hZ : center G = ⊥) {τ : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible τ n p f) (hG : LieModel G τ n p f) {t : G}
    (ht : orderOf t = 2) {L : Subgroup G} (hL : IsComponentIn L (centralizer ({t} : Set G))) :
    (∃ (τ' : StatedLieTag) (n' f' : ℕ), StatedLieAdmissible τ' n' p f' ∧
      LieModel (L ⧸ center L) τ' n' p f') ∨ p = 3 := by
  let α : MulAut G := MulAut.conj t
  let C : Subgroup G := centralizer ({t} : Set G)
  have hfix : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α = C :=
    c3b_fixedSubgroup_conj t
  have hLC : L ≤ C := hL.1
  have hLcomp : IsComponent (L.subgroupOf C) := hL.2
  let e : ↥C ≃* ↥(CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α) :=
    MulEquiv.subgroupCongr hfix.symm
  let K : Subgroup (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α) :=
    (L.subgroupOf C).map e.toMonoidHom
  have hK : IsComponent K := CFSG.LocalCores.isComponent_map_mulEquiv e hLcomp
  rcases hCL1 G τ n p f hp hp2 hadm hG α (c3b_orderOf_conj hZ ht) K hK with
    ⟨τ', n', f', hadm', hm⟩ | hcase2
  · refine Or.inl ⟨τ', n', f', hadm', ?_⟩
    have eKL : ↥K ≃* ↥L :=
      ((L.subgroupOf C).equivMapOfInjective e.toMonoidHom e.injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe hLC)
    let ψ : ↥K ⧸ center ↥K ≃* ↥L ⧸ center ↥L :=
      QuotientGroup.congr (center ↥K) (center ↥L) eKL (Subgroup.map_center_eq eKL)
    exact LieModel.of_mulEquiv ψ hm
  · exact Or.inr hcase2.1

end CFSG.OddStandard.SmallF3.Omega
