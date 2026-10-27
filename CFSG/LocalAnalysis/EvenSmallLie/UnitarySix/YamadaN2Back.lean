module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2R3b

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped MatrixGroups commutatorElement

noncomputable def slEquiv3 (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4) :
    SL(3, F) ≃* SL3 :=
  have : Fintype F := Fintype.ofFinite F
  let e : F ≃+* CFSG.Fischer.F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_F4])
  { toFun := SpecialLinearGroup.map e.toRingHom
    invFun := SpecialLinearGroup.map e.symm.toRingHom
    left_inv := fun g => Subtype.ext (by ext i j; simp)
    right_inv := fun g => Subtype.ext (by ext i j; simp)
    map_mul' := map_mul _ }

theorem mem_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (ha : e a ∈ center B) : a ∈ center A := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul, ha (e g)]

section Back

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}
variable [Fact (ElemSec D₂ (⊥ : Subgroup G))] [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal]
variable (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)

@[expose] noncomputable def preG2 (D₂ K₂ D₁ : Subgroup G)
    [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal]
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) : Subgroup G :=
  (X.comap (mk2 D₂ K₂ D₁)).map (nTwo D₂ K₂ D₁).subtype

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem mem_preG2 {X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))} {y : G} :
    y ∈ preG2 D₂ K₂ D₁ X ↔ ∃ hy : y ∈ nTwo D₂ K₂ D₁, mk2 D₂ K₂ D₁ ⟨y, hy⟩ ∈ X := by
  constructor
  · rintro ⟨⟨y, hy⟩, hX, rfl⟩
    exact ⟨hy, hX⟩
  · rintro ⟨hy, hX⟩
    exact ⟨⟨y, hy⟩, hX, rfl⟩

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem D₂_le_preG2 (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    D₂ ≤ preG2 D₂ K₂ D₁ X := by
  intro x hx
  rw [mem_preG2]
  refine ⟨D₂_le_nTwo hx, ?_⟩
  rw [Y14Hyp.mk2_eq_one _ hx]
  exact one_mem _

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem preG2_le (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    preG2 D₂ K₂ D₁ X ≤ nTwo D₂ K₂ D₁ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem preG2_sup (X Y : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    preG2 D₂ K₂ D₁ (X ⊔ Y) = preG2 D₂ K₂ D₁ X ⊔ preG2 D₂ K₂ D₁ Y := by
  have hs : Function.Surjective (mk2 D₂ K₂ D₁) := QuotientGroup.mk'_surjective _
  rw [preG2, preG2, preG2, ← Subgroup.comap_sup_eq (mk2 D₂ K₂ D₁) X Y hs, Subgroup.map_sup]

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem preG2_inf (X Y : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    preG2 D₂ K₂ D₁ (X ⊓ Y) = preG2 D₂ K₂ D₁ X ⊓ preG2 D₂ K₂ D₁ Y := by
  rw [preG2, preG2, preG2, Subgroup.comap_inf,
    Subgroup.map_inf_eq _ _ _ (Subgroup.subtype_injective _)]

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem preG2_top : preG2 D₂ K₂ D₁ ⊤ = nTwo D₂ K₂ D₁ := by
  rw [preG2, Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

include h in
omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.conjR_preG2
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR (preG2 D₂ K₂ D₁ X) t =
      preG2 D₂ K₂ D₁ (X.map (tauG2 h)) := by
  ext y
  rw [CFSG.EvenSmallLie.UnitarySix.YamadaEnd.mem_conjR, mem_preG2, mem_preG2]
  constructor
  · rintro ⟨hy, hX⟩
    have hy' : y ∈ nTwo D₂ K₂ D₁ := (mem_normalizer_iff.mp h.t_mem_normalizer y).mpr hy
    refine ⟨hy', ⟨_, hX, ?_⟩⟩
    rw [tauG2_mk]
    congr 1
    apply Subtype.ext
    simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [h.t_inv]
    have ht := h.t_sq
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group
  · rintro ⟨hy, ⟨m, hm, hmy⟩⟩
    have hty : t * y * t⁻¹ ∈ nTwo D₂ K₂ D₁ := (mem_normalizer_iff.mp h.t_mem_normalizer y).mp hy
    refine ⟨hty, ?_⟩
    have h1 : tauG2 h (mk2 D₂ K₂ D₁ ⟨y, hy⟩) = m := by rw [← hmy, h.pi_ττ]
    rw [tauG2_mk] at h1
    rw [← h1] at hm
    exact hm

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem mk2_mem_of_preG2 {X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))}
    (m : preG2 D₂ K₂ D₁ X) : mk2 D₂ K₂ D₁ ⟨m, preG2_le X m.2⟩ ∈ X := by
  obtain ⟨_, hmX⟩ := mem_preG2.mp m.2
  exact hmX

@[expose] noncomputable def phiG2
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    preG2 D₂ K₂ D₁ X →* X where
  toFun m := ⟨mk2 D₂ K₂ D₁ ⟨m, preG2_le X m.2⟩, mk2_mem_of_preG2 m⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (mk2 D₂ K₂ D₁) ⟨a, _⟩ ⟨b, _⟩)

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem phiG2_surjective
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    Function.Surjective (phiG2 X) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨⟨n, mem_preG2.mpr ⟨n.2, hx⟩⟩, rfl⟩

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
instance normal_preG2 (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    (D₂.subgroupOf (preG2 D₂ K₂ D₁ X)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ nTwo D₂ K₂ D₁ := preG2_le X g.2
    have := (inferInstance : (D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal).conj_mem
      ⟨n, preG2_le X n.2⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨g, hg⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem phiG2_ker (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    (phiG2 X).ker = D₂.subgroupOf (preG2 D₂ K₂ D₁ X) := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hm
    exact Y14Hyp.mem_D₂_of_mk2 _ (congrArg Subtype.val hm)
  · intro hm
    exact Subtype.ext (Y14Hyp.mk2_eq_one _ hm)

@[expose] noncomputable def quotEquivG2
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    ↥(preG2 D₂ K₂ D₁ X) ⧸ D₂.subgroupOf (preG2 D₂ K₂ D₁ X) ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq (phiG2_ker X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (phiG2 X) (phiG2_surjective X))

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem relIndex_preG2 (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) :
    D₂.relIndex (preG2 D₂ K₂ D₁ X) = Nat.card X := by
  rw [Subgroup.relIndex, Subgroup.index]
  exact Nat.card_congr (quotEquivG2 X).toEquiv

include h in
omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.type_back (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)
    (X : Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)))
    (h1 : X ⊔ X.map (tauG2 h) = ⊤) (h2 : ⁅X, X.map (tauG2 h)⁆ = ⊥)
    (h3 : Nat.card (X ⊓ X.map (tauG2 h) : Subgroup _) ∣ 3) (ψ : SL3 →* X)
    (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ center SL3) :
    ∃ M : Subgroup G, D₂ ≤ M ∧ M ≤ nTwo D₂ K₂ D₁ ∧
      nTwo D₂ K₂ D₁ = M ⊔ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t ∧
      ⁅M, CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t⁆ ≤ D₂ ∧
      D₂.relIndex (M ⊓ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t) ∣ 3 ∧
      ∃ _ : (D₂.subgroupOf M).Normal, ∃ ψ : SL(3, F) →* M ⧸ D₂.subgroupOf M,
        Function.Surjective ψ ∧ ψ.ker ≤ center SL(3, F) := by
  set M := preG2 D₂ K₂ D₁ X
  have hMt := h.conjR_preG2 X
  refine ⟨M, D₂_le_preG2 X, preG2_le X, ?_, ?_, ?_, ?_⟩
  · rw [hMt, ← preG2_sup, h1, preG2_top]
  · rw [hMt, Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_preG2] at ha hb
    obtain ⟨ha, haX⟩ := ha
    obtain ⟨hb, hbX⟩ := hb
    have hc : ⁅a, b⁆ ∈ nTwo D₂ K₂ D₁ := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine Y14Hyp.mem_D₂_of_mk2 hc ?_
    have hmk : mk2 D₂ K₂ D₁ ⟨⁅a, b⁆, hc⟩ = ⁅mk2 D₂ K₂ D₁ ⟨a, ha⟩, mk2 D₂ K₂ D₁ ⟨b, hb⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [hmk, ← Subgroup.mem_bot, ← h2]
    exact Subgroup.commutator_mem_commutator haX hbX
  · rw [hMt, ← preG2_inf, relIndex_preG2]
    exact h3
  · refine ⟨normal_preG2 X, ?_⟩
    let e := slEquiv3 F hF
    refine ⟨(quotEquivG2 X).symm.toMonoidHom.comp (ψ.comp e.toMonoidHom), ?_, ?_⟩
    · exact (quotEquivG2 X).symm.surjective.comp (hψ.comp e.surjective)
    · intro g hg
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hg
      exact mem_center_of_mulEquiv e (hk hg)

end Back

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
