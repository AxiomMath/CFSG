module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL219D
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46dTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSwap

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem exists_component_pump {Y : Type} [Group Y] [Finite Y] (hY : oddCore Y = ⊥) {s : Y}
    (hs : orderOf s = 2) {T : Subgroup Y}
    (hT : ComponentClassification.HarrisLit.IsTwoComponentIn T (centralizer ({s} : Set Y))) :
    ∃ M : Subgroup Y, IsComponent M ∧
      ((M.map (MulAut.conj s).toMonoidHom = M ∧ T ≤ M) ∨
        (M.map (MulAut.conj s).toMonoidHom ≠ M ∧
          ⁅M, M.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧
          ∃ φ : ↥M →* Y, (∀ m : ↥M, φ m = (m : Y) * (s * m * s⁻¹)) ∧ T = φ.range ∧
            φ.ker ≤ center ↥M)) := by
  have hOdd : pPrimeCore 2 Y = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hY
  obtain ⟨K, hK2, hcases, -⟩ :=
    (ComponentClassification.HarrisLit.harris82Lemma219Input_holds Y s hs).2 T hT
  have hKc : IsComponent K :=
    (ComponentClassification.HarrisLit.isTwoComponent_iff_isComponent hOdd K).mp hK2
  refine ⟨K, hKc, ?_⟩
  rcases hcases with ⟨hfix, hIn⟩ | ⟨hne, hTeq⟩
  ·
    exact Or.inl ⟨hfix, hIn.1.trans inf_le_left⟩
  ·
    have ht : s ^ 2 = 1 := by
      have h := pow_orderOf_eq_one s
      rwa [hs] at h
    have hc : K ≤ centralizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup Y) : Set Y) :=
      ComponentClassification.HarrisLit.le_centralizer_map_conj_of_isComponent hKc hne
    refine Or.inr ⟨hne, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc, ?_⟩
    refine ⟨ComponentClassification.HarrisLit.swapDiag K s hc, ?_, ?_, ?_⟩
    ·
      intro m
      rw [ComponentClassification.HarrisLit.swapDiag_apply, MulAut.conj_apply]
    ·
      rw [hTeq,
        ComponentClassification.HarrisLit.centralizerResidual_sup_eq_range K ht hc hKc.1.1]
    ·
      intro m hm
      rw [MonoidHom.mem_ker] at hm
      rw [ComponentClassification.HarrisLit.swapDiag_apply, MulAut.conj_apply] at hm
      have hm_eq : (m : Y) = MulAut.conj s ((m⁻¹ : ↥K) : Y) := by
        have hcoe : ((m⁻¹ : ↥K) : Y) = (m : Y)⁻¹ := rfl
        rw [hcoe, MulAut.conj_apply]
        calc (m : Y) = (s * (m : Y) * s⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hm
          _ = s * (m : Y)⁻¹ * s⁻¹ := by group
      have hmK : (m : Y) ∈ K.map (MulAut.conj s).toMonoidHom := by
        refine Subgroup.mem_map.mpr ⟨((m⁻¹ : ↥K) : Y), (m⁻¹ : ↥K).2, ?_⟩
        change MulAut.conj s ((m⁻¹ : ↥K) : Y) = (m : Y)
        exact hm_eq.symm
      rw [Subgroup.mem_center_iff]
      intro n
      exact Subtype.ext (mem_centralizer_iff.mp (hc n.2) (m : Y) hmK).symm

end CFSG.OddStandard.SmallF3.HypA2
