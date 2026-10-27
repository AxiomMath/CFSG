module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorRightOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorAction

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u v w x

variable {G : Type u} {F : Type v} {Ω : Type w} {Ξ : Type x}
variable [Group G] [Group F]

theorem stabilizer_map_of_equivariant
    [MulAction G Ω] [MulAction F Ξ]
    (e : G ≃* F) (f : Ω ≃ Ξ)
    (hequiv : ∀ (g : G) (z : Ω), f (g • z) = e g • f z) (a : Ω) :
    (MulAction.stabilizer G a).map e.toMonoidHom =
      MulAction.stabilizer F (f a) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    change e g • f a = f a
    rw [← hequiv]
    exact congrArg f (MulAction.mem_stabilizer_iff.mp hg)
  · intro hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply MulAction.mem_stabilizer_iff.mpr
    apply f.injective
    rw [hequiv, e.apply_symm_apply]
    exact MulAction.mem_stabilizer_iff.mp hy

theorem pair_stabilizer_map_of_equivariant
    [MulAction G Ω] [MulAction F Ξ]
    (e : G ≃* F) (f : Ω ≃ Ξ)
    (hequiv : ∀ (g : G) (z : Ω), f (g • z) = e g • f z) (a b : Ω) :
    (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).map e.toMonoidHom =
      MulAction.stabilizer F (f a) ⊓ MulAction.stabilizer F (f b) := by
  rw [Subgroup.map_inf _ _ _ e.injective,
    stabilizer_map_of_equivariant e f hequiv a,
    stabilizer_map_of_equivariant e f hequiv b]

theorem full_pair_data_of_equivariant_standard_pair
    [MulAction G Ω] [MulAction F Ξ]
    (e : G ≃* F) (f : Ω ≃ Ξ)
    (hequiv : ∀ (g : G) (z : Ω), f (g • z) = e g • f z)
    (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (a₀ b₀ : Ξ) (h₀ : a₀ ≠ b₀) (w₀ : F)
    (hwa : w₀ • a₀ = b₀) (hwb : w₀ • b₀ = a₀)
    (T₀ : Subgroup F)
    (hT₀ : (T₀ : Set F) = {y | y • a₀ = a₀ ∧ y • b₀ = b₀})
    (hcyclic : IsCyclic T₀)
    (hinv : ∀ y ∈ T₀, rightConjugateElem y w₀ = y⁻¹)
    (a b : Ω) (hab : a ≠ b) (t : G)
    (hta : t • a = b) (htb : t • b = a) :
    let T := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
    IsCyclic T ∧ Nat.card T = Nat.card T₀ ∧
      ∀ y ∈ T, rightConjugateElem y t = y⁻¹ := by
  let T := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
  let T₁ := MulAction.stabilizer F (f a) ⊓ MulAction.stabilizer F (f b)
  have hfa : e t • f a = f b := (hequiv t a).symm.trans (congrArg f hta)
  have hfb : e t • f b = f a := (hequiv t b).symm.trans (congrArg f htb)
  obtain ⟨hcyclic₁, hcard₁, hinv₁⟩ := full_pair_cyclic_card_and_inversion_of_standard_pair
    hdouble a₀ b₀ h₀ w₀ hwa hwb T₀ hT₀ hcyclic hinv
      (f a) (f b) (f.injective.ne hab) (e t) hfa hfb
  have hmap : T.map e.toMonoidHom = T₁ :=
    pair_stabilizer_map_of_equivariant e f hequiv a b
  let E : T ≃* T₁ :=
    (T.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine ⟨E.isCyclic.mpr hcyclic₁, (Nat.card_congr E.toEquiv).trans hcard₁, ?_⟩
  intro y hy
  have hey : e y ∈ T₁ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  apply e.injective
  simpa only [rightConjugateElem, map_mul, map_inv] using hinv₁ (e y) hey

theorem original_right_pair_intersection_data
    [MulAction F Ξ]
    (H L : Subgroup G) (a b : pointRightCosetSpace H)
    (hb : b ∈ numeratorRightOrbit H L a) (hab : a ≠ b)
    (t : G) (ht : orderOf t = 2) (htL : t ∈ L)
    (hflip : pointRightCosetMul H a t = b)
    (e : L ≃* F) (f : numeratorRightOrbit H L a ≃ Ξ)
    (hequiv : letI := numeratorRightOrbitAction H L a
      ∀ (l : L) (z : numeratorRightOrbit H L a), f (l • z) = e l • f z)
    (hdouble : MulAction.IsMultiplyPretransitive F Ξ 2)
    (a₀ b₀ : Ξ) (h₀ : a₀ ≠ b₀) (w₀ : F)
    (hwa : w₀ • a₀ = b₀) (hwb : w₀ • b₀ = a₀)
    (T₀ : Subgroup F)
    (hT₀ : (T₀ : Set F) = {y | y • a₀ = a₀ ∧ y • b₀ = b₀})
    (hcyclic : IsCyclic T₀)
    (hinv : ∀ y ∈ T₀, rightConjugateElem y w₀ = y⁻¹) :
    let T := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
    IsCyclic T ∧ Nat.card T = Nat.card T₀ ∧
      ∀ y ∈ T, rightConjugateElem y t = y⁻¹ := by
  let := numeratorRightOrbitAction H L a
  let aΓ : numeratorRightOrbit H L a := ⟨a, numeratorRightOrbit_base H L a⟩
  let bΓ : numeratorRightOrbit H L a := ⟨b, hb⟩
  let tL : L := ⟨t, htL⟩
  have habΓ : aΓ ≠ bΓ := fun h => hab (congrArg Subtype.val h)
  have htLorder : orderOf tL = 2 := (Subgroup.orderOf_coe tL).symm.trans ht
  have hta : tL • aΓ = bΓ := by
    apply Subtype.ext
    change pointRightCosetMul H a t⁻¹ = b
    rwa [inv_eq_self_of_orderOf_eq_two ht]
  have htb : tL • bΓ = aΓ := involution_flips_pair htLorder hta
  let T := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  have hpair : MulAction.stabilizer L aΓ ⊓ MulAction.stabilizer L bΓ =
      T.subgroupOf L := by
    rw [numeratorRightOrbitAction_stabilizer H L a aΓ,
      numeratorRightOrbitAction_stabilizer H L a bΓ]
    ext l
    change (l.val ∈ rightCosetStabilizer H a ∧ l.val ∈ rightCosetStabilizer H b) ↔
      l.val ∈ L ∧ (l.val ∈ rightCosetStabilizer H a ∧ l.val ∈ rightCosetStabilizer H b)
    exact ⟨fun h => ⟨l.property, h⟩, fun h => h.2⟩
  have hdata := full_pair_data_of_equivariant_standard_pair e f hequiv hdouble
    a₀ b₀ h₀ w₀ hwa hwb T₀ hT₀ hcyclic hinv aΓ bΓ habΓ tL hta htb
  change IsCyclic ↥(MulAction.stabilizer L aΓ ⊓ MulAction.stabilizer L bΓ) ∧ _ at hdata
  rw [hpair] at hdata
  let E : T.subgroupOf L ≃* T := Subgroup.subgroupOfEquivOfLe inf_le_left
  refine ⟨E.isCyclic.mp hdata.1, (Nat.card_congr E.toEquiv.symm).trans hdata.2.1, ?_⟩
  intro y hy
  let yL : L := ⟨y, hy.1⟩
  have hyT : yL ∈ T.subgroupOf L := hy
  have h := congrArg Subtype.val (hdata.2.2 yL hyT)
  exact h

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
