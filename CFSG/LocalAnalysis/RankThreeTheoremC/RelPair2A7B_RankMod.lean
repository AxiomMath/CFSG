module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_RankCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Frattini

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.OrderReductions.FrattiniAutomorphisms
open scoped IsMulCommutative

noncomputable def subgroupSubmodule {Q : Type*} [Group Q] [IsElementaryAbelian 2 Q]
    (Y : Subgroup Q) : Submodule (ZMod 2) (Additive Q) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Y)

theorem mem_subgroupSubmodule {Q : Type*} [Group Q] [IsElementaryAbelian 2 Q]
    (Y : Subgroup Q) (v : Additive Q) : v ∈ subgroupSubmodule Y ↔ Additive.toMul v ∈ Y := Iff.rfl

@[expose] noncomputable def elementaryAction {A Q : Type*} [Group A] [Group Q]
    [IsElementaryAbelian 2 Q] (φ : A →* MulAut Q) :
    A →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q) where
  toFun a := LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((MulEquiv.toAdditive (φ a)).toLinearEquiv
      (fun c x => ZMod.map_smul (MulEquiv.toAdditive (φ a)).toAddMonoidHom c x))
  map_one' := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    simp
  map_mul' a b := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    change φ (a * b) (Additive.toMul x) = φ a (φ b (Additive.toMul x))
    rw [map_mul]
    rfl

theorem elementaryAction_apply {A Q : Type*} [Group A] [Group Q] [IsElementaryAbelian 2 Q]
    (φ : A →* MulAut Q) (a : A) (q : Q) :
    ((elementaryAction φ a : LinearMap.GeneralLinearGroup (ZMod 2) (Additive Q)) :
      Additive Q →ₗ[ZMod 2] Additive Q) (Additive.ofMul q) = Additive.ofMul (φ a q) := rfl

theorem rank_filtration_action {R A : Type*} [Group R] [Finite R] [Group A]
    [MulDistribMulAction A R] (hR : IsPGroup 2 R) {a b z : A}
    (hz : z = a * b * a⁻¹ * b⁻¹) (hz3 : z ^ 3 = 1) (hza : z * a = a * z) (hzb : z * b = b * z)
    (hz1 : ∃ r : R, z • r ≠ r) (R₁ R₂ : Subgroup R) (h12 : R₁ ≤ R₂)
    (hR₂ : ∀ r ∈ R₂, z • r ∈ R₂) (hz₂ : ∀ r ∈ R₂, (z • r) * r⁻¹ ∈ R₁)
    (hd₂ : R₂.index ≤ 4) (hd₁ : Nat.card R₁ ≤ 16) :
    R₂.index = 4 ∧ Nat.card R₁ = 16 ∧ R₁ ⊓ frattini R = ⊥ := by
  classical
  obtain ⟨-, -, -, hel, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) hR
  have : Finite (Additive (R ⧸ frattini R)) := inferInstanceAs (Finite (R ⧸ frattini R))
  have : FiniteDimensional (ZMod 2) (Additive (R ⧸ frattini R)) := Module.Finite.of_finite
  let π : R →* R ⧸ frattini R := QuotientGroup.mk' (frattini R)
  let φ : A →* MulAut (R ⧸ frattini R) :=
    (quotientAutomorphism (frattini R)).comp (MulDistribMulAction.toMulAut A R)
  let ρ : A →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R)) :=
    elementaryAction φ
  have hρ : ∀ (g : A) (r : R),
      (ρ g : Additive (R ⧸ frattini R) →ₗ[ZMod 2] Additive (R ⧸ frattini R))
        (Additive.ofMul (π r)) = Additive.ofMul (π (g • r)) := fun g r =>
    (elementaryAction_apply φ g (π r)).trans (congrArg Additive.ofMul
      (quotientAutomorphism_apply (frattini R) (MulDistribMulAction.toMulAut A R g) r))
  have hρ1 : ρ z ≠ 1 := by
    intro h1
    have hσ : quotientAutomorphism (frattini R) (MulDistribMulAction.toMulAut A R z) = 1 := by
      refine MulEquiv.ext fun v => ?_
      have h' := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (R ⧸ frattini R)) => (g : Additive (R ⧸ frattini R) →ₗ[ZMod 2]
          Additive (R ⧸ frattini R)) (Additive.ofMul v)) h1
      exact Additive.ofMul.injective h'
    obtain ⟨k, hk⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel (p := 2) hR).2
      ⟨_, MonoidHom.mem_ker.mpr hσ⟩
    have hσk : (MulDistribMulAction.toMulAut A R z) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hσ3 : (MulDistribMulAction.toMulAut A R z) ^ 3 = 1 := by
      rw [← map_pow, hz3, map_one]
    have hσ1 : MulDistribMulAction.toMulAut A R z = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
        (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσ3))
    obtain ⟨r, hr⟩ := hz1
    exact hr (congrArg (fun τ : MulAut R => τ r) hσ1)
  have hmem : ∀ (Y : Subgroup R) (v : Additive (R ⧸ frattini R)),
      v ∈ subgroupSubmodule (Y.map π) ↔ ∃ r ∈ Y, Additive.ofMul (π r) = v := by
    intro Y v
    rw [mem_subgroupSubmodule, Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, by rw [h]; rfl⟩
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, by rw [← h]; rfl⟩
  have hcard : ∀ W : Submodule (ZMod 2) (Additive (R ⧸ frattini R)),
      Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    intro W
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hcardq : ∀ W : Submodule (ZMod 2) (Additive (R ⧸ frattini R)),
      Nat.card (Additive (R ⧸ frattini R) ⧸ W) = 2 ^ Module.finrank (ZMod 2)
        (Additive (R ⧸ frattini R) ⧸ W) := by
    intro W
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hquot : Nat.card (Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π)) ≤
      R₂.index := by
    let f : R ⧸ R₂ → Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π) :=
      Quotient.lift (fun r : R => Submodule.Quotient.mk (Additive.ofMul (π r))) (by
        intro r₁ r₂ h
        have h' : r₁⁻¹ * r₂ ∈ R₂ := QuotientGroup.leftRel_apply.mp h
        rw [Submodule.Quotient.eq, hmem]
        refine ⟨r₂⁻¹ * r₁, ?_, ?_⟩
        · simpa using R₂.inv_mem h'
        · rw [map_mul, map_inv, ofMul_mul, ofMul_inv]
          exact neg_add_eq_sub _ _)
    have hsurj : Function.Surjective f := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (frattini R) (Additive.toMul v)
        refine ⟨(r : R ⧸ R₂), ?_⟩
        have hrv : Additive.ofMul (π r) = v := by
          rw [show π r = Additive.toMul v from hr]
          rfl
        change Submodule.Quotient.mk (Additive.ofMul (π r)) = _
        rw [hrv]
    exact Nat.card_le_card_of_surjective f hsurj
  let g : R₁ → subgroupSubmodule (R₁.map π) := fun r =>
    ⟨Additive.ofMul (π r), (hmem R₁ _).mpr ⟨r, r.2, rfl⟩⟩
  have hgsurj : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨r, hr, hrv⟩ := (hmem R₁ v).mp hv
    exact ⟨⟨r, hr⟩, Subtype.ext hrv⟩
  have hE₁card : Nat.card (subgroupSubmodule (R₁.map π)) ≤ Nat.card R₁ :=
    Nat.card_le_card_of_surjective g hgsurj
  have hd₂' : Module.finrank (ZMod 2)
      (Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π)) ≤ 2 := by
    have h2 : 2 ^ Module.finrank (ZMod 2)
        (Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π)) ≤ 2 ^ 2 := by
      calc _ = Nat.card (Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π)) :=
            (hcardq _).symm
        _ ≤ R₂.index := hquot
        _ ≤ 2 ^ 2 := by norm_num; exact hd₂
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have hd₁' : Module.finrank (ZMod 2) (subgroupSubmodule (R₁.map π)) ≤ 4 := by
    have h2 : 2 ^ Module.finrank (ZMod 2) (subgroupSubmodule (R₁.map π)) ≤ 2 ^ 4 := by
      calc _ = Nat.card (subgroupSubmodule (R₁.map π)) := (hcard _).symm
        _ ≤ Nat.card R₁ := hE₁card
        _ ≤ 2 ^ 4 := by norm_num; exact hd₁
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  have h12' : subgroupSubmodule (R₁.map π) ≤ subgroupSubmodule (R₂.map π) := by
    intro v hv
    obtain ⟨r, hr, h⟩ := (hmem R₁ v).mp hv
    exact (hmem R₂ v).mpr ⟨r, h12 hr, h⟩
  have hE₂ : ∀ v ∈ subgroupSubmodule (R₂.map π),
      ((ρ z : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R))) :
        Module.End (ZMod 2) (Additive (R ⧸ frattini R))) v ∈ subgroupSubmodule (R₂.map π) := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := (hmem R₂ v).mp hv
    rw [hρ z r]
    exact (hmem R₂ _).mpr ⟨z • r, hR₂ r hr, rfl⟩
  have hz₂' : ∀ v ∈ subgroupSubmodule (R₂.map π),
      ((ρ z : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (R ⧸ frattini R))) :
        Module.End (ZMod 2) (Additive (R ⧸ frattini R))) v - v ∈
          subgroupSubmodule (R₁.map π) := by
    intro v hv
    obtain ⟨r, hr, rfl⟩ := (hmem R₂ v).mp hv
    rw [hρ z r]
    refine (hmem R₁ _).mpr ⟨(z • r) * r⁻¹, hz₂ r hr, ?_⟩
    rw [map_mul, map_inv, ofMul_mul, ofMul_inv]
    exact (sub_eq_add_neg _ _).symm
  obtain ⟨hf2, hf4⟩ := rank_filtration_core (ρ a) (ρ b) (ρ z)
    (by rw [hz]; simp only [map_mul, map_inv]) (by rw [← map_pow, hz3, map_one])
    (by rw [← map_mul, ← map_mul, hza]) (by rw [← map_mul, ← map_mul, hzb]) hρ1
    (subgroupSubmodule (R₁.map π)) (subgroupSubmodule (R₂.map π)) h12' hE₂ hz₂' hd₂' hd₁'
  have h4 : Nat.card (Additive (R ⧸ frattini R) ⧸ subgroupSubmodule (R₂.map π)) = 4 := by
    rw [hcardq, hf2]
    norm_num
  have h16 : Nat.card (subgroupSubmodule (R₁.map π)) = 16 := by
    rw [hcard, hf4]
    norm_num
  have hidx : R₂.index = 4 := by
    have := h4 ▸ hquot
    omega
  have hR₁card : Nat.card R₁ = 16 := by
    have := h16 ▸ hE₁card
    omega
  refine ⟨hidx, hR₁card, ?_⟩
  have hgbij : Function.Bijective g := hgsurj.bijective_of_nat_card_le (by rw [h16, hR₁card])
  rw [eq_bot_iff]
  intro r hr
  have hπ : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr.2
  have : g ⟨r, hr.1⟩ = g 1 := by
    refine Subtype.ext ?_
    exact congrArg Additive.ofMul (hπ.trans (map_one π).symm)
  have h1 := hgbij.1 this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankThreeTheoremC
