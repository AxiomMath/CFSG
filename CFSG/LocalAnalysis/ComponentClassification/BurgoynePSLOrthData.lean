module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrth
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLUnitary

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
    map_top_of_surjective _ e.surjective]

@[expose] def isoOrthGL (hK : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R) ≃*
      CatalogueBGraphForm.isometryGroup n K R :=
  (MulEquiv.subgroupCongr
    (CatalogueBLinearHigherB.orthogonalGroup_matrixQuadraticForm hK R hR)).trans
    (CatalogueBLinearHigherB.isometryGroupEquiv R)

section Transport

variable {G H : Type*} [Group G] [Group H] {I : Subgroup H} (e : G ≃* I)

abbrev transportGL (L : Subgroup G) : Subgroup H := (L.map e.toMonoidHom).map I.subtype

theorem trans_commutator : transportGL e (commutator G) = ⁅I, I⁆ := by
  rw [transportGL, map_commutator_mulEquiv, Subgroup.map_subtype_commutator]

theorem trans_iSup {ι : Type*} (L : ι → Subgroup G) :
    transportGL e (⨆ i, L i) = ⨆ i, transportGL e (L i) := by
  rw [transportGL, Subgroup.map_iSup, Subgroup.map_iSup]

theorem isQuasisimple_trans {L : Subgroup G} (hL : IsQuasisimple L) :
    IsQuasisimple (transportGL e L) :=
  LocalCores.isQuasisimple_of_mulEquiv ((L.equivMapOfInjective _ e.injective).trans
    ((L.map e.toMonoidHom).equivMapOfInjective _ I.subtype_injective)) hL

theorem trans_le_commutator {L : Subgroup G} (hL : L ≤ commutator G) :
    transportGL e L ≤ ⁅I, I⁆ := by
  rw [← trans_commutator e]
  exact map_mono (map_mono hL)

theorem conj_mem_trans {L : Subgroup G} (hLc : L ≤ commutator G)
    (hN : (L.subgroupOf (commutator G)).Normal) {x : H} (hx : x ∈ ⁅I, I⁆) {l : H}
    (hl : l ∈ transportGL e L) : x * l * x⁻¹ ∈ transportGL e L := by
  rw [← trans_commutator e] at hx
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨l₀, hl₀, rfl⟩, rfl⟩ := hl
  have hmem : x₀ * l₀ * x₀⁻¹ ∈ L := by
    have h1 := hN.conj_mem ⟨l₀, hLc hl₀⟩ (mem_subgroupOf.2 hl₀) ⟨x₀, hx₀⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  refine ⟨_, ⟨x₀ * l₀ * x₀⁻¹, hmem, rfl⟩, ?_⟩
  simp only [map_mul, map_inv]

include e in
theorem commutator_trans_of_isPerfect (hP : Group.IsPerfect (commutator G)) :
    ⁅⁅I, I⁆, ⁅I, I⁆⁆ = ⁅I, I⁆ := by
  have hiso : commutator G ≃* (⁅I, I⁆ : Subgroup H) :=
    ((commutator G).equivMapOfInjective _ e.injective).trans
      (((commutator G).map e.toMonoidHom).equivMapOfInjective _ I.subtype_injective) |>.trans
      (MulEquiv.subgroupCongr (trans_commutator e))
  have : Group.IsPerfect (⁅I, I⁆ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := hiso.toMonoidHom) hiso.surjective
  rw [← Subgroup.map_subtype_commutator, this.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end Transport

theorem orthComponentData [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) (hexc : ¬ (Nat.card K = 3 ∧ n ≤ 4)) :
    OrthComponentData n K R := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  set e := isoOrthGL hK R hR with he
  by_cases hT : ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    have hq := CatalogueBOrthogonal.derived_quasisimple Q h2 hQnd hT3.ge hTQ
    have hq' := isQuasisimple_trans e hq
    rw [trans_commutator] at hq'
    refine ⟨commutator_eq_self_of_isQuasisimple hq', 1,
      fun _ => ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆,
      by simp, fun _ => ⟨hq', le_rfl, ?_⟩⟩
    intro x hx l hl
    exact mul_mem (mul_mem hx hl) (inv_mem hx)
  · have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQnd
      (by rw [hdim]; exact hn) hT
    rw [hdim] at hcases
    have hcase : (Odd (Nat.card K) ∧ (Module.finrank K (Fin n → K) = 3 ∨
        Module.finrank K (Fin n → K) = 4 ∨ Module.finrank K (Fin n → K) = 5)) ∨
        (Odd (Nat.card K) ∧ Module.finrank K (Fin n → K) = 6 ∧
          ¬ ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
        (Module.finrank K (Fin n → K) = 4 ∧
          ∃ S : Submodule K (Fin n → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
      rw [hdim]
      rcases hcases with h | h | h | h
      · exact Or.inl ⟨hodd, Or.inl h⟩
      · exact Or.inl ⟨hodd, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨hodd, Or.inr (Or.inr h)⟩
      · exact Or.inr (Or.inl ⟨hodd, h, hT⟩)
    have hne : ¬ ((Module.finrank K (Fin n → K) = 3 ∧ Nat.card K = 3) ∨
        ((Module.finrank K (Fin n → K) = 4 ∧
          ∃ S : Submodule K (Fin n → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) ∧
          (Nat.card K = 2 ∨ Nat.card K = 3))) := by
      rw [hdim]
      rintro (⟨h3, hc⟩ | ⟨⟨h4, -⟩, hc | hc⟩)
      · exact hexc ⟨hc, by omega⟩
      · rw [hc] at hodd
        exact absurd hodd (by decide)
      · exact hexc ⟨hc, by omega⟩
    obtain ⟨hperf, -, ⟨m, L, -, -, hsup, hL, -⟩, -⟩ :=
      (LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
        Q hQnd hcase).2.1 hne
    refine ⟨commutator_trans_of_isPerfect e hperf, m, fun i => transportGL e (L i), ?_,
      fun i =>
      ⟨isQuasisimple_trans e (hL i).1, trans_le_commutator e (hL i).2.1, fun x hx l hl =>
        conj_mem_trans e (hL i).2.1 (hL i).2.2 hx hl⟩⟩
    rw [← trans_iSup, hsup, trans_commutator]

end CFSG.ComponentClassification.Burgoyne.PSL
