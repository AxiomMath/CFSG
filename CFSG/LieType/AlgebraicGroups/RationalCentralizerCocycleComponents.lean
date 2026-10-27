module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial (p_component_isomorphism_transport)

variable {G : Type*} [Group G]

theorem isPComponent_subgroupOf_subgroupOf_iff {A B L : Subgroup G} [Finite A] (hAB : A ≤ B)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    CFSG.IsPComponent ℓ ((L.subgroupOf B).subgroupOf (A.subgroupOf B)) ↔
      CFSG.IsPComponent ℓ (L.subgroupOf A) := by
  have : Finite (A.subgroupOf B) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hAB).symm.toEquiv
  rw [(p_component_isomorphism_transport ℓ hℓ (Subgroup.subgroupOfEquivOfLe hAB)).1]
  congr! 1
  ext ⟨x, hx⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : ((y : B) : G) = x := congrArg Subtype.val hyx
    rw [← this]
    exact hy
  · intro h
    exact ⟨⟨⟨x, hAB hx⟩, Subgroup.mem_subgroupOf.2 hx⟩, h, rfl⟩

theorem isPComponent_subgroupOf_iff_of_isSolvable {A B : Subgroup G} [Finite B] (hAB : A ≤ B)
    [(A.subgroupOf B).Normal] [Group.IsSolvable (B ⧸ A.subgroupOf B)] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L : Subgroup G) :
    (L ≤ B ∧ CFSG.IsPComponent ℓ (L.subgroupOf B)) ↔
      (L ≤ A ∧ CFSG.IsPComponent ℓ (L.subgroupOf A)) := by
  have : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAB)
  have hinv := p_components_solvable_quotient_invariance ℓ hℓ (A.subgroupOf B) (L.subgroupOf B)
  constructor
  · rintro ⟨hLB, hL⟩
    obtain ⟨hle, hL'⟩ := hinv.1 hL
    have hLA : L ≤ A := fun x hx => by
      have h := hle (show (⟨x, hLB hx⟩ : B) ∈ L.subgroupOf B from hx)
      exact h
    exact ⟨hLA, (isPComponent_subgroupOf_subgroupOf_iff hAB ℓ hℓ).1 hL'⟩
  · rintro ⟨hLA, hL⟩
    refine ⟨hLA.trans hAB, hinv.2 ⟨fun x hx => hLA hx,
      (isPComponent_subgroupOf_subgroupOf_iff hAB ℓ hℓ).2 hL⟩⟩

theorem isPComponent_subgroupOf_map_conj_iff {B B' : Subgroup G} [Finite B] (g : G)
    (hB : B.map (MulAut.conj g).toMonoidHom = B') (ℓ : ℕ) (hℓ : ℓ.Prime) (L : Subgroup G) :
    (L ≤ B ∧ CFSG.IsPComponent ℓ (L.subgroupOf B)) ↔
      (L.map (MulAut.conj g).toMonoidHom ≤ B' ∧
        CFSG.IsPComponent ℓ ((L.map (MulAut.conj g).toMonoidHom).subgroupOf B')) := by
  subst hB
  set f := (MulAut.conj g).subgroupMap B
  have : Finite (B.map (MulAut.conj g : G →* G)) := Finite.of_equiv _ f.toEquiv
  have : Finite (B.map (MulAut.conj g).toMonoidHom) := this
  have hmap : ∀ L : Subgroup G, L ≤ B → (L.subgroupOf B).map f.toMonoidHom =
      (L.map (MulAut.conj g).toMonoidHom).subgroupOf (B.map (MulAut.conj g).toMonoidHom) := by
    intro L hLB
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hLB hx⟩, hx, rfl⟩
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  constructor
  · rintro ⟨hLB, hL⟩
    refine ⟨Subgroup.map_mono hLB, ?_⟩
    rw [← hmap L hLB]
    exact ((p_component_isomorphism_transport ℓ hℓ f).1 _).1 hL
  · rintro ⟨hLB, hL⟩
    have hLB' : L ≤ B := (Subgroup.map_le_map_iff_of_injective hinj).1 hLB
    refine ⟨hLB', ((p_component_isomorphism_transport ℓ hℓ f).1 _).2 ?_⟩
    rw [hmap L hLB']
    exact hL

theorem normal_inf_subgroupOf {H B R : Subgroup G} (hBR : B ≤ R) [hN : (H.subgroupOf R).Normal] :
    ((H ⊓ B).subgroupOf B).Normal := by
  constructor
  rintro ⟨n, hnB⟩ hn ⟨b, hbB⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨?_, B.mul_mem (B.mul_mem hbB hnB) (B.inv_mem hbB)⟩
  have h := hN.conj_mem ⟨n, hBR hnB⟩ (Subgroup.mem_subgroupOf.2 hn.1) ⟨b, hBR hbB⟩
  rw [Subgroup.mem_subgroupOf] at h
  exact h

theorem isSolvable_quotient_inf_subgroupOf {H B R : Subgroup G} (hBR : B ≤ R)
    [(H.subgroupOf R).Normal] [Group.IsSolvable (R ⧸ H.subgroupOf R)]
    [((H ⊓ B).subgroupOf B).Normal] : Group.IsSolvable (B ⧸ (H ⊓ B).subgroupOf B) := by
  let f : B →* R ⧸ H.subgroupOf R := (QuotientGroup.mk' _).comp (Subgroup.inclusion hBR)
  have hker : f.ker = (H ⊓ B).subgroupOf B := by
    ext ⟨b, hb⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨h, hb⟩, fun h => h.1⟩
  have : Group.IsSolvable (B ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective f)
  exact Group.isSolvable_of_surjective (f := (QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom)
    (QuotientGroup.quotientMulEquivOfEq hker).surjective

end CFSG.LieType.AlgebraicGroups
