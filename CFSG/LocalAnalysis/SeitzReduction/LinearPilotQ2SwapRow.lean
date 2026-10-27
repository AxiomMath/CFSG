module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SwapParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)

section Overlaps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]
  [Finite K]

omit [Finite G] in
theorem isSimpleGroup_modelToG_blockSL_of_card_two (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {T : Finset (Fin n)} (hT : 3 ≤ T.card)
    (hTn : T.card < n) :
    IsSimpleGroup (modelToG e (blockSL (K := K) T)) ∧
      center (modelToG e (blockSL (K := K) T)) = ⊥ := by
  have hq := isQuasisimple_map_blockSL (K := K) e hTn (by omega) (Or.inl hT)
  obtain ⟨φ⟩ := blockSL_mulEquiv (K := K) hTn
  have hSL : center (SpecialLinearGroup (Fin T.card) K) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (eq_one_of_mem_center_specialLinearGroup_of_card_two hK hz)
  let ψ : modelToG e (blockSL (K := K) T) ≃* SpecialLinearGroup (Fin T.card) K :=
    ((((blockSL T).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((blockSL T).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective)).symm).trans φ
  have hZ : center (modelToG e (blockSL (K := K) T)) = ⊥ :=
    F4Pilot.center_eq_bot_congr ψ.symm hSL
  have : IsSimpleGroup (modelToG e (blockSL (K := K) T) ⧸
      center (modelToG e (blockSL (K := K) T))) := hq.2.1
  exact ⟨((QuotientGroup.quotientBot (G := modelToG e (blockSL (K := K) T))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup, hZ⟩

omit [Finite G] [Finite K] in
theorem symm_proj_transvection_ne_one (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {i j : Fin n} (hij : i ≠ j) :
    ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))) : L) : G) ≠ 1 := by
  intro h
  have h1 : e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))) = 1 :=
    Subtype.ext h
  have h2 : LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K)) =
      LinearFlag.proj n K 1 := by
    rw [map_one]
    exact e.symm.injective (h1.trans (map_one _).symm)
  have h3 := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i j)
    (eq_of_proj_eq_of_card_two hK h2)
  simp [SpecialLinearGroup.transvection_coe, one_apply, hij] at h3

omit [Finite G] [Finite K] in
theorem modelToG_sup_sup (e : L ≃* LinearFlag.projectiveSL n K)
    (A B C : Subgroup (LinearFlag.projectiveSL n K)) :
    modelToG e (A ⊔ B ⊔ C) = modelToG e A ⊔ modelToG e B ⊔ modelToG e C := by
  simp only [modelToG, Subgroup.map_sup]

end Overlaps

section Main

theorem mem_compl_pair_sdiff_pair_iff {n : ℕ} {x a b c d : Fin n} :
    x ∈ ({a, b} : Finset (Fin n))ᶜ \ {c, d} ↔
      (x : ℕ) ≠ a ∧ (x : ℕ) ≠ b ∧ (x : ℕ) ≠ c ∧ (x : ℕ) ≠ d := by
  simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or,
    ne_eq, Fin.ext_iff]
  tauto

end Main

end CFSG.SeitzReduction.LinearPilot
