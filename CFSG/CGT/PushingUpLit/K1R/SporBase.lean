module

public import CFSG.CGT.PushingUpLit.K1R.Defs
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem innerRoot_setup {D : Type} [Group D] [Finite D] (hD : IsSimpleGroup D) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    {α : MulAut D} (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    {S : Subgroup D} (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ t : D, orderOf t = 2 ∧ MulAut.conj t = α ∧
      CFSG.IsComponent (S.subgroupOf (centralizer ({t} : Set D))) ∧
      CFSG.Assembly.IsComponentOf S (centralizer ({t} : Set D)) ∧ IsSimpleGroup S ∧
      Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧ center S = ⊥ := by
  obtain ⟨φ⟩ := hSK
  have hSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimple hn hK
  have hSs : IsSimpleGroup S := φ.isSimpleGroup
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.sl2_exists_mul_ne (K := K)
  have hSnab : ∃ x y : S, x * y ≠ y * x :=
    ⟨φ.symm a, φ.symm b, fun h' => hab (by
      simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg φ h')⟩
  have hDnab : ∃ x y : D, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hSnab
    exact ⟨x, y, fun h' => hxy (Subtype.ext (by simpa only [coe_mul] using h'))⟩
  have hZD : center D = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hDnab).2
  obtain ⟨t, ht, rfl⟩ := exists_involution_of_mem_inner hZD hα hin
  have hC := Sporadic.eqLocus_conj t
  have hSt : S ≤ centralizer ({t} : Set D) := hC ▸ hSα
  have hSnt : (S.subgroupOf (centralizer ({t} : Set D))).Normal := by
    have := hSn
    rwa [hC] at this
  have e := Subgroup.subgroupOfEquivOfLe hSt
  have : IsSimpleGroup (S.subgroupOf (centralizer ({t} : Set D))) := e.isSimpleGroup
  have hnab : ∃ x y : S.subgroupOf (centralizer ({t} : Set D)), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hSnab
    refine ⟨e.symm x, e.symm y, fun h' => hxy ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'
  have hcomp : CFSG.IsComponent (S.subgroupOf (centralizer ({t} : Set D))) :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1, hSnt.isSubnormal⟩
  refine ⟨t, ht, rfl, hcomp,
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hSt).2 hcomp,
    hSs, by rw [Nat.card_congr φ.toEquiv, card_sl2 hK],
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).2⟩

theorem inner_false_of_comps {D : Type} [Group D] [Finite D] (hD : IsSimpleGroup D) {n : ℕ}
    (hn : 2 ≤ n) {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 2 ^ n)
    {α : MulAut D} (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    {S : Subgroup D} (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hQSL : ¬ Q (Matrix.SpecialLinearGroup (Fin 2) K))
    (hCQ : ∀ t : D, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set D)) Q) : False := by
  obtain ⟨φ⟩ := hSK
  obtain ⟨t, ht, rfl, hcomp, -, -, -, -⟩ := innerRoot_setup hD hn hK hα hin hSα hSn ⟨φ⟩
  have hSt : S ≤ centralizer ({t} : Set D) := (Sporadic.eqLocus_conj t) ▸ hSα
  exact hQSL (hQ _ _ (φ.symm.trans (Subgroup.subgroupOfEquivOfLe hSt).symm) (hCQ t ht _ hcomp))

theorem sporadicInner_of_comps {s : TauCeti.SporadicName} {Qi : (Y : Type) → [Group Y] → Prop}
    (hQi : IsoInvariant Qi)
    (hSLi : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Qi (Matrix.SpecialLinearGroup (Fin 2) K))
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set G)) Qi) :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D s :=
  InnerKernelSelector.of_false fun D _ _ hD hs n hn K _ _ hK _ hα hinn _ hSα hSn hSK _ =>
    inner_false_of_comps hD hn hK hα hinn hSα hSn hSK hQi (hSLi n hn K hK) (hin D hs)

end CFSG.CGT.PushingUpLit.K1R
