module

public import CFSG.GH74.GLS.Stage4.T2NegRU3Basic
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Norm
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk41RDefs

public section

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3 CFSG.GH74.GLS.IVK.Proofs2.Ivk41R Matrix
open scoped commutatorElement

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3

variable {p n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p n K}

theorem hypUnitriangular_eq_map :
    hypUnitriangular h 1 1 = (⊤ : Subgroup (UHeis h)).map uSU := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := exists_uSU_of_mem hg
    exact ⟨x, Subgroup.mem_top _, hx⟩
  · rintro ⟨x, -, rfl⟩
    exact uSU_mem x

theorem commutator_hypUnitriangular :
    ⁅hypUnitriangular h 1 1, hypUnitriangular h 1 1⁆ = X0U h := by
  rw [hypUnitriangular_eq_map, ← Subgroup.map_commutator, UHeis.commutator_eq_center]
  rfl

theorem hypUnitriangular_le_centralizer :
    hypUnitriangular h 1 1 ≤ Subgroup.centralizer ((X0U h : Subgroup (hypSU h 1 1)) : Set (hypSU h 1 1)) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨y, hy, rfl⟩ := mem_X0U.mp hg
  obtain ⟨x, rfl⟩ := exists_uSU_of_mem hu
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (UHeis.mem_center.mpr hy) x]

theorem centralizer_X0U_le_normalizer :
    Subgroup.centralizer ((X0U h : Subgroup (hypSU h 1 1)) : Set (hypSU h 1 1)) ≤
      Subgroup.normalizer ((hypUnitriangular h 1 1 : Subgroup (hypSU h 1 1)) :
        Set (hypSU h 1 1)) := by
  intro g hg
  obtain ⟨c₀, hc₀, hc₀ne⟩ := h.exists_mem_traceZero_ne_zero
  have hc₀' : c₀ + h.bar c₀ + 0 * h.bar 0 = 0 := by
    have := (UnitaryFieldData.mem_traceZero h).mp hc₀
    simpa [UnitaryFieldData.trace] using this
  have hz₀ : uSU (⟨0, c₀, hc₀'⟩ : UHeis h) ∈ X0U h := mem_X0U.mpr ⟨_, rfl, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hg _ hz₀
  have hmat : ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *
      uMat (⟨0, c₀, hc₀'⟩ : UHeis h) =
      uMat (⟨0, c₀, hc₀'⟩ : UHeis h) * ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    have := congrArg (fun A : hypSU h 1 1 => ((A : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K)) hcomm
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_uSU] using this.symm
  obtain ⟨h10, h20, h21⟩ := lower_entries_zero (M := ((g : GL (HypIndex 1 1) K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K)) (x₀ := (⟨0, c₀, hc₀'⟩ : UHeis h))
    (x' := (⟨0, c₀, hc₀'⟩ : UHeis h)) rfl rfl hc₀ne hc₀ne hmat
  have hgB : g ∈ hypBorel h 1 1 := by
    refine mem_hypBorel_of_blockTriangular h ?_
    intro a b hab
    rcases a with i | i | i <;> rcases b with j | j | j <;> (obtain rfl := Subsingleton.elim i 0) <;>
      (obtain rfl := Subsingleton.elim j 0) <;>
      first | assumption | (exfalso; revert hab; simp)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hypUnitriangular_le_hypBorel (r := 1) (ε := 1) h)).mp
      (normal_hypUnitriangular (h := h) (r := 1) (ε := 1) le_rfl) hgB

theorem rstdU3 (h : UnitaryFieldData p n K) : p ≠ 2 → CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.RGood p n (tzU h) (X0U h) := by
  intro hp2
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite (hypSU h 1 1) := finite_hypSU h
  obtain ⟨hU, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hUp : IsPGroup p (hypUnitriangular h 1 1) := by
    rw [← hP]
    exact P.isPGroup'
  refine ⟨hypUnitriangular h 1 1, ?_, hUp, X0U_le_unitriangular, hypUnitriangular_le_centralizer, ?_,
    ?_, commutator_hypUnitriangular.ge, ?_, ?_⟩
  · exact (pCoreOf_eq_of_sylow P hP hypUnitriangular_le_centralizer
      centralizer_X0U_le_normalizer).symm
  · rw [hU]
  · intro r hr hc
    obtain ⟨y, rfl⟩ := exists_uSU_of_mem hr
    refine ⟨y, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    have := hc (uSU g) (uSU_mem g)
    rw [← map_mul, ← map_mul] at this
    exact (uSU_injective this).symm
  · intro r hr s hs
    rw [← commutator_hypUnitriangular]
    exact Subgroup.commutator_mem_commutator hr hs
  · intro r hr
    obtain ⟨y, rfl⟩ := exists_uSU_of_mem hr
    rw [tzU_conj_mul]
    exact ⟨_, negA_mul_mem_center y, rfl⟩

end CFSG.GH74.GLS.IVK.Proofs2.Ivk41RU3
