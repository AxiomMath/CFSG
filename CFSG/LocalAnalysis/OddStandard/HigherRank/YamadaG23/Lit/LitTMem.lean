module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

private lemma conj_eq_commutator_mul (a b : Γ) : a * b * a⁻¹ = ⁅a, b⁆ * b := by
  simpa using (conj_eq_commutatorElement_mul (g₁ := a) (g₂ := b))

private lemma mem_normalizer_of_centralizes {Gh Zh : Subgroup Γ}
    (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x) {x : Γ} (hx : x ∈ Gh) :
    x ∈ normalizer (Zh : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro z
  constructor
  · intro hz
    have hconj : x * z * x⁻¹ = z := by
      rw [conj_eq_commutator_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr (hZc x hx z hz), one_mul]
    have : x⁻¹ * z * x = z := by
      calc x⁻¹ * z * x = x⁻¹ * (x * z * x⁻¹) * x := by rw [hconj]
        _ = z := by group
    rw [this]
    exact hz
  · intro hz
    have hconj : x * (x⁻¹ * z * x) * x⁻¹ = x⁻¹ * z * x := by
      rw [conj_eq_commutator_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr (hZc x hx (x⁻¹ * z * x) hz), one_mul]
    have : z = x⁻¹ * z * x := by
      calc z = x * (x⁻¹ * z * x) * x⁻¹ := by group
        _ = x⁻¹ * z * x := hconj
    rw [this]
    exact hz

theorem lit_mem_T_iff {Gh Zh : Subgroup Γ} {t : Γ} (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x)
    (hZG : Zh ≤ Gh) (htZ : t ∈ normalizer (Zh : Set Γ)) {x : Γ} (hx : x ∈ Gh) :
    x ∈ centralizerSection (Zh ⊔ zpowers t) Zh ↔ ⁅t, x⁆ ∈ Zh := by
  constructor
  · intro hxK
    exact hxK.2.2 t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  · intro ht
    have hxZ : x ∈ normalizer (Zh : Set Γ) := mem_normalizer_of_centralizes hZc hx
    let S : Subgroup Γ :=
      { carrier := {k | k ∈ normalizer (Zh : Set Γ) ∧ ⁅k, x⁆ ∈ Zh}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := by
          rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
          refine ⟨mul_mem haN hbN, ?_⟩
          rw [commutatorElement_mul_left_eq_conj_mul]
          exact Zh.mul_mem ((Subgroup.mem_normalizer_iff.mp haN (⁅b, x⁆)).mp hb) ha
        inv_mem' := by
          rintro a ⟨haN, ha⟩
          refine ⟨inv_mem haN, ?_⟩
          have hxa : ⁅x, a⁆ ∈ Zh := by simpa using Zh.inv_mem ha
          rw [commutatorElement_inv_left]
          simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem haN) (⁅x, a⁆)).mp hxa }
    have hZhS : Zh ≤ S := by
      intro z hz
      refine ⟨Subgroup.le_normalizer hz, ?_⟩
      have hz1 : ⁅z, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hZc x hx z hz).symm
      rw [hz1]
      exact Zh.one_mem
    have htS : t ∈ S := ⟨htZ, ht⟩
    have hKS : Zh ⊔ zpowers t ≤ S := sup_le hZhS (Subgroup.zpowers_le.mpr htS)
    have hxK : x ∈ normalizer ((Zh ⊔ zpowers t : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have hc : ⁅k, x⁆ ∈ Zh := (hKS hk).2
        have hkx : x * k * x⁻¹ = ⁅k, x⁆⁻¹ * k := by
          rw [commutatorElement_inv]
          exact conj_eq_commutator_mul x k
        rw [hkx]
        exact (Zh ⊔ zpowers t).mul_mem (Subgroup.mem_sup_left (Zh.inv_mem hc)) hk
      · intro hk
        have hyc : ⁅x * k * x⁻¹, x⁆ ∈ Zh := (hKS hk).2
        have hxinv : x⁻¹ ∈ normalizer (Zh : Set Γ) := inv_mem hxZ
        have hcinv : ⁅x⁻¹, x * k * x⁻¹⁆ ∈ Zh := by
          rw [commutatorElement_inv_left]
          simpa using (Subgroup.mem_normalizer_iff.mp hxinv (⁅x * k * x⁻¹, x⁆)).mp hyc
        have hk_eq : k = ⁅x⁻¹, x * k * x⁻¹⁆ * (x * k * x⁻¹) := by
          rw [← conj_eq_commutator_mul (x⁻¹) (x * k * x⁻¹)]
          group
        rw [hk_eq]
        exact (Zh ⊔ zpowers t).mul_mem (Subgroup.mem_sup_left hcinv) hk
    refine ⟨hxK, hxZ, fun k hk => (hKS hk).2⟩

theorem lit_mem_C_iff {Gh Zh Ah : Subgroup Γ} (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x)
    {x : Γ} (hx : x ∈ Gh) :
    x ∈ centralizerSection Ah Zh ↔ x ∈ normalizer (Ah : Set Γ) ∧ ∀ a ∈ Ah, ⁅a, x⁆ ∈ Zh := by
  constructor
  · rintro ⟨hA, -, hcomm⟩
    exact ⟨hA, hcomm⟩
  · rintro ⟨hA, hcomm⟩
    exact ⟨hA, mem_normalizer_of_centralizes hZc hx, hcomm⟩

end CFSG.OddStandard.HigherRank.YamadaG23
