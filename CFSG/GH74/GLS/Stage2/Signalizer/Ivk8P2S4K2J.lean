module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8K0Act
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Y

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K0
open scoped commutatorElement

variable {G : Type} [Group G]

theorem kaHyp_of_J [Finite G] {J : Subgroup G} (hq : IsQuasisimple ↥J) {z : G}
    (hz : z ∈ normalizer (J : Set G)) (hz2 : z * z = 1) (hJz : ⁅J, zpowers z⁆ = J) {p : ℕ}
    {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPN : P ≤ normalizer (J : Set G))
    (hnc : ¬ P ≤ centralizer (J : Set G)) (hPz : ∀ x ∈ P, z * x = x * z)
    (hPn : ∀ y ∈ J, y * z = z * y → y ∈ normalizer (P : Set G)) :
    alphaZ J hz * alphaZ J hz = 1 ∧ alphaZ J hz ≠ 1 ∧ KAHyp (alphaZ J hz) p (Pbar J P) := by
  have hperf : Group.IsPerfect ↥J := hq.1
  have hα2 : alphaZ J hz * alphaZ J hz = 1 := by
    rw [← map_mul]
    have : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥(normalizer (J : Set G))) = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hα1 : alphaZ J hz ≠ 1 := by
    intro h
    have hzC : z ∈ centralizer (J : Set G) := (YCfg.yAct_eq_one_iff J ⟨z, hz⟩).mp h
    have h1 : J ≤ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hzC)
    have h2 : ⁅J, zpowers z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [hJz] at h2
    have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot J).mp this h2
  refine ⟨hα2, hα1, isPGroup_Pbar hPp, Pbar_ne_bot hPN hnc,
    fun e he => comm_Pbar hz hPz he, ?_⟩
  intro c hcfix hodd
  obtain ⟨y, hyz, hyc⟩ := lift_fixed_odd J hz hz2 hcfix hodd
  have hy : (y : G) ∈ normalizer (P : Set G) := hPn (y : G) y.2 hyz
  rw [← hyc]
  exact conj_mem_normalizer_Pbar hy

theorem exists_of_yAct_inn {J : Subgroup G} [Group.IsPerfect ↥J] {n : G}
    (hn : n ∈ normalizer (J : Set G))
    (h : YCfg.yAct J ⟨n, hn⟩ ∈ innSub (↥J ⧸ center ↥J)) :
    ∃ a ∈ J, a⁻¹ * n ∈ centralizer (J : Set G) := by
  obtain ⟨yb, hyb⟩ := h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hyN : (y : G) ∈ normalizer (J : Set G) := le_normalizer y.2
  set η : ↥(normalizer (J : Set G)) := ⟨(y : G), hyN⟩ with hη
  have h1 : MulAut.conj (QuotientGroup.mk y : ↥J ⧸ center ↥J) = YCfg.yAct J η :=
    (YCfg.yAct_of_mem J y).symm
  have h2 : YCfg.yAct J (η⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [map_mul, map_inv, ← hyb, ← h1]
    exact inv_mul_cancel _
  have h4 : ((η⁻¹ * ⟨n, hn⟩ : ↥(normalizer (J : Set G))) : G) ∈ centralizer (J : Set G) :=
    (YCfg.yAct_eq_one_iff J _).mp h2
  exact ⟨(y : G), y.2, h4⟩

theorem jlevel_two [Finite G] {J : Subgroup G} (hq : IsQuasisimple ↥J)
    (hKA : KATwoY (↥J ⧸ center ↥J)) {z₁ z₂ : G} (hz₁ : z₁ ∈ normalizer (J : Set G))
    (hz₂ : z₂ ∈ normalizer (J : Set G)) (hz₁2 : z₁ * z₁ = 1) (hz₂2 : z₂ * z₂ = 1)
    (hJz₁ : ⁅J, zpowers z₁⁆ = J) (hJz₂ : ⁅J, zpowers z₂⁆ = J) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {P₁ P₂ : Subgroup G} (hP₁p : IsPGroup p ↥P₁) (hP₂p : IsPGroup p ↥P₂)
    (hP₁N : P₁ ≤ normalizer (J : Set G)) (hP₂N : P₂ ≤ normalizer (J : Set G))
    (hnc₁ : ¬ P₁ ≤ centralizer (J : Set G)) (hnc₂ : ¬ P₂ ≤ centralizer (J : Set G))
    (hP₁z : ∀ x ∈ P₁, z₁ * x = x * z₁) (hP₂z : ∀ x ∈ P₂, z₂ * x = x * z₂)
    (hP₁n : ∀ y ∈ J, y * z₁ = z₁ * y → y ∈ normalizer (P₁ : Set G))
    (hP₂n : ∀ y ∈ J, y * z₂ = z₂ * y → y ∈ normalizer (P₂ : Set G)) :
    ∃ a ∈ J, a⁻¹ * (z₁ * z₂) ∈ centralizer (J : Set G) := by
  have hperf : Group.IsPerfect ↥J := hq.1
  obtain ⟨h12, h11, hK₁⟩ := kaHyp_of_J hq hz₁ hz₁2 hJz₁ hP₁p hP₁N hnc₁ hP₁z hP₁n
  obtain ⟨h22, h21, hK₂⟩ := kaHyp_of_J hq hz₂ hz₂2 hJz₂ hP₂p hP₂N hnc₂ hP₂z hP₂n
  have hinn := hKA _ _ h12 h11 h22 h21 p hp hp2 _ _ hK₁ hK₂
  have hn : z₁ * z₂ ∈ normalizer (J : Set G) := Subgroup.mul_mem _ hz₁ hz₂
  have hmul : YCfg.yAct J ⟨z₁ * z₂, hn⟩ = alphaZ J hz₁ * alphaZ J hz₂ := by
    show YCfg.yAct J (⟨z₁, hz₁⟩ * ⟨z₂, hz₂⟩) = _
    rw [map_mul]
  exact exists_of_yAct_inn hn (by rw [hmul]; exact hinn)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
