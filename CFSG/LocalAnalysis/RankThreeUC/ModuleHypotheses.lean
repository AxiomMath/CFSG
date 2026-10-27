module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

variable {G : Type} [Group G]

def centralizerOnQuotient (M V₀ V : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ M ∧ m ∈ normalizer (V : Set G) ∧ m ∈ normalizer (V₀ : Set G) ∧
    ∀ v ∈ V, m * v * m⁻¹ * v⁻¹ ∈ V₀}
  one_mem' := by
    refine ⟨one_mem _, one_mem _, one_mem _, fun v _ => ?_⟩
    simp [one_mem]
  mul_mem' := by
    rintro a b ⟨haM, haV, haV₀, ha⟩ ⟨hbM, hbV, hbV₀, hb⟩
    refine ⟨mul_mem haM hbM, mul_mem haV hbV, mul_mem haV₀ hbV₀, fun v hv => ?_⟩
    have h1 : a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ ∈ V₀ := by
      have := (mem_normalizer_iff.1 haV₀ (b * v * b⁻¹ * v⁻¹)).1 (hb v hv)
      simpa using this
    have h2 := mul_mem h1 (ha v hv)
    convert h2 using 1
    group
  inv_mem' := by
    rintro a ⟨haM, haV, haV₀, ha⟩
    refine ⟨inv_mem haM, inv_mem haV, inv_mem haV₀, fun v hv => ?_⟩
    have hu : a⁻¹ * v * a ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem haV) v).1 hv
      simpa using this
    have := ha _ hu
    have h3 : (a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹) = v * (a⁻¹ * v * a)⁻¹ := by group
    rw [h3] at this
    have h4 := inv_mem this
    convert h4 using 1
    group

def centralizerOnQuotientIn (M V₀ V : Subgroup G) : Subgroup M :=
  (centralizerOnQuotient M V₀ V).subgroupOf M

theorem centralizerOnQuotient_le (M V₀ V : Subgroup G) : centralizerOnQuotient M V₀ V ≤ M :=
  fun _ h => h.1

theorem centralizerOnQuotientIn_normal {M V₀ V : Subgroup G}
    (hV : M ≤ normalizer (V : Set G)) (hV₀ : M ≤ normalizer (V₀ : Set G)) :
    (centralizerOnQuotientIn M V₀ V).Normal := by
  refine ⟨fun n hn m => ?_⟩
  obtain ⟨hnM, hnV, hnV₀, hn⟩ := hn
  have hmM : (m : G) ∈ M := m.2
  refine ⟨mul_mem (mul_mem hmM hnM) (inv_mem hmM),
    ?_, ?_, fun v hv => ?_⟩
  · exact hV (mul_mem (mul_mem hmM hnM) (inv_mem hmM))
  · exact hV₀ (mul_mem (mul_mem hmM hnM) (inv_mem hmM))
  · have hu : (m : G)⁻¹ * v * m ∈ V := by
      have := (mem_normalizer_iff.1 (hV (inv_mem hmM)) v).1 hv
      simpa using this
    have h1 := (mem_normalizer_iff.1 (hV₀ hmM) _).1 (hn _ hu)
    convert h1 using 1
    show (m : G) * (n : G) * (m : G)⁻¹ * v * ((m : G) * (n : G) * (m : G)⁻¹)⁻¹ * v⁻¹ = _
    have e : M.subtype n = (n : G) := rfl
    rw [e]
    group

abbrev MBar (M V₀ V : Subgroup G) [(centralizerOnQuotientIn M V₀ V).Normal] : Type _ :=
  M ⧸ centralizerOnQuotientIn M V₀ V

end CFSG.LocalAnalysis.RankThreeUC
