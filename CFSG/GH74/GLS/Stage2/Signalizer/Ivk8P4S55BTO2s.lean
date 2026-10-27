module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTO2a
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG
open scoped commutatorElement

variable {M : Type*} [Group M]

theorem mem_normalizer_of_mem_centralizer {J : Subgroup M} {c : M}
    (hc : c ∈ centralizer (J : Set M)) : c ∈ normalizer (J : Set M) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← (mem_centralizer_iff.mp hc) x hx]
    simpa using hx
  · intro hx
    have e : c * x * c⁻¹ * c = c * (c * x * c⁻¹) := (mem_centralizer_iff.mp hc) _ hx
    have : x = c * x * c⁻¹ := by
      have e2 : c * x = c * (c * x * c⁻¹) := by rw [← e]; group
      exact mul_left_cancel e2
    rw [this]
    exact hx

theorem actJ_eq_one_of_mem_centralizer {J : Subgroup M} {c : M}
    (hc : c ∈ centralizer (J : Set M)) :
    actJ J ⟨c, mem_normalizer_of_mem_centralizer hc⟩ = 1 := by
  ext w
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
  rw [actJ_mk]
  congr 1
  apply Subtype.ext
  simp only [normalizerMonoidHom_apply_apply_coe]
  rw [← (mem_centralizer_iff.mp hc) j j.2]
  group

theorem actJ_mem_of_odd {J : Subgroup M} {O : Subgroup (MulAut (↥J ⧸ center ↥J))}
    (hO2 : ∀ y : MulAut (↥J ⧸ center ↥J), ∃ n : ℕ, y ^ 2 ^ n ∈ O) {y : M}
    (hy : y ∈ normalizer (J : Set M)) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    actJ J ⟨y, hy⟩ ∈ O := by
  obtain ⟨n, hn⟩ := hO2 (actJ J ⟨y, hy⟩)
  refine mem_of_pow_odd_of_pow_two hm ?_ hn
  have : (⟨y, hy⟩ : ↥(normalizer (J : Set M))) ^ m = 1 := Subtype.ext (by simp [hym])
  rw [← map_pow, this, map_one]
  exact O.one_mem

theorem mem_centralizer_layer {c : M}
    (h : ∀ J : Subgroup M, IsComponent J → c ∈ centralizer (J : Set M)) :
    c ∈ centralizer (layer M : Set M) := by
  have hle : layer M ≤ centralizer ({c} : Set M) := by
    refine sSup_le fun J hJ x hx => ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (h J hJ)) x hx
  rw [mem_centralizer_iff]
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hle hx)

theorem w_facts {J : Subgroup M}
    (h3 : ∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False)
    (hJ : IsComponent J) {O : Subgroup (MulAut (↥J ⧸ center ↥J))}
    (hO2 : ∀ y : MulAut (↥J ⧸ center ↥J), ∃ n : ℕ, y ^ 2 ^ n ∈ O) {g x : M} {m : ℕ}
    (hm : Odd m) (hgm : g ^ m = 1) :
    ∃ hw : x⁻¹ * (g * x * g⁻¹) ∈ normalizer (J : Set M), actJ J ⟨_, hw⟩ ∈ O := by
  have hu₁m : (x⁻¹ * g * x) ^ m = 1 := by
    have : x⁻¹ * g * x = x⁻¹ * g * x⁻¹⁻¹ := by group
    rw [this, conj_pow, hgm]
    group
  have hu₂m : g⁻¹ ^ m = 1 := by rw [inv_pow, hgm, inv_one]
  have hu₁ := mem_normalizer_of_odd h3 hJ hm hu₁m
  have hu₂ := mem_normalizer_of_odd h3 hJ hm hu₂m
  have he : x⁻¹ * (g * x * g⁻¹) = (x⁻¹ * g * x) * g⁻¹ := by group
  have hw : x⁻¹ * (g * x * g⁻¹) ∈ normalizer (J : Set M) := by
    rw [he]
    exact Subgroup.mul_mem _ hu₁ hu₂
  refine ⟨hw, ?_⟩
  have hsplit : (⟨_, hw⟩ : ↥(normalizer (J : Set M))) = ⟨_, hu₁⟩ * ⟨_, hu₂⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul]; exact he)
  rw [hsplit, map_mul]
  exact O.mul_mem (actJ_mem_of_odd hO2 hu₁ hm hu₁m) (actJ_mem_of_odd hO2 hu₂ hm hu₂m)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
