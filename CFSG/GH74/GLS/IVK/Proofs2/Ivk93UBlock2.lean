module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg2
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
  CFSG.ComponentClassification.OddClassSelector
open scoped MatrixGroups

theorem Ivk93Cfg2.exists_unitary' {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {q₁ q₂ : ℕ}
    {L L' : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))}
    (h : Ivk93Cfg2 x q₁ q₂ L L') :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M₁ M₂ : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ ∧ Nonempty (↥L ≃* ↥M₁) ∧
          Nonempty (↥L' ≃* ↥M₂) := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  have hrange : φ.range = projSpecial hud (hypForm hud r ε) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hypModelEquiv hud (θ y)).2
    · intro hz
      obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
      refine ⟨θ.symm w, ?_⟩
      rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
      rfl
  have : φ.range.Normal := by
    rw [hrange]
    infer_instance
  have hK₁ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  have hK₂ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  have e₁ : Nonempty (↥L ≃* ↥((L.map φ).subgroupOf (centralizer ({φ x} : Set _)))) :=
    ⟨(L.equivMapOfInjective φ hφ).trans (Subgroup.subgroupOfEquivOfLe hK₁.1).symm⟩
  have e₂ : Nonempty (↥L' ≃* ↥((L'.map φ).subgroupOf (centralizer ({φ x} : Set _)))) :=
    ⟨(L'.equivMapOfInjective φ hφ).trans (Subgroup.subgroupOfEquivOfLe hK₂.1).symm⟩
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁ hK₂ e₁ e₂
  refine ⟨hud, A, ?_, _, _, hK₁.2, hK₂.2, fun k => h.ne ?_, e₁, e₂⟩
  · change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
    rw [hA, orderOf_injective φ hφ x, h.ord]
  · have h1 := subgroupOf_inj.mp k
    rw [inf_of_le_left hK₁.1, inf_of_le_left hK₂.1] at h1
    exact map_injective hφ h1

namespace Ivk93Cfg2

variable {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ} {L₁ L₂ : Subgroup J}

theorem false_of_quaternion (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {M : Type} [Group M] (e : ↥L₁ ≃* M)
    (hM : CFSG.IsQuasisimple M) (φ : QuaternionGroup 2 →* M ⧸ center M)
    (hφ : Function.Injective φ) : False := by
  classical
  have : Finite M := Finite.of_equiv _ e.toEquiv
  obtain ⟨F, _, _, hFq, ⟨eF⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
  have eS : SL(2, F) ≃* (M ⧸ pPrimeCore 2 M) :=
    eF.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)
  have hcard : Nat.card (M ⧸ pPrimeCore 2 M) = q₁ * (q₁ ^ 2 - 1) := by
    rw [← Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFq]
  have hker : pPrimeCore 2 M ≤ center M := by
    rcases LocalCores.quasisimple_normal_subgroups hM (inferInstance : (pPrimeCore 2 M).Normal) with
      htop | hle
    · exfalso
      have h1 : Nat.card (M ⧸ pPrimeCore 2 M) = 1 := by
        rw [htop]
        exact Subgroup.index_top
      have := h.sl2_card_ge
      omega
    · exact hle
  have hker' : (QuotientGroup.mk' (pPrimeCore 2 M)).ker ≤ center M := by
    rw [QuotientGroup.ker_mk']
    exact hker
  obtain ⟨eC⟩ := center_quotient_equiv_of_surjective hM (QuotientGroup.mk' (pPrimeCore 2 M))
    (QuotientGroup.mk'_surjective _) hker'
  let eQ : M ⧸ center M ≃* StatedProj (StatedSL 2 F) :=
    eC.trans ((QuotientGroup.congr (center (M ⧸ pPrimeCore 2 M)) (center SL(2, F)) eS.symm
      (Subgroup.map_center_eq eS.symm)).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F))
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  have hk : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hq5 := h.five₁
  have hodd := h.odd₁
  have hℓ2 : ringChar F ≠ 2 := by
    intro h2
    rw [h2] at hk
    have : 2 ∣ q₁ := by
      rw [← hFq, hk]
      exact dvd_pow_self 2 (PNat.ne_zero n)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hX : StatedClassicalModel (M ⧸ center M) .PSL 2 (ringChar F) n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eQ
      (OddSelector.statedClassicalModel_psl_two hℓ n.pos hk (by omega) (by omega))
  exact OddSelector.not_psl_two_odd_of_quaternion φ hφ hℓ2 hX

end Ivk93Cfg2

end CFSG.GH74.GLS.IVK.Proofs2
