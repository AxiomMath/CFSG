module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U3CoreMaxMod

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

open CFSG.RankThree.PartTwo.Sec19 (descPSUHom descPSUHom_injective)

theorem card_le_27_su {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (E : Subgroup (MulAut (unitarySU 2 3 F 3))) (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  have hq : 2 < 2 ^ 3 := by norm_num
  by_cases hEr : E ≤ (suConj h).range
  · have hinf : E ⊓ (suConj h).range = E := inf_eq_left.2 hEr
    have h9 := KSU3Core.card_inf_range_suConj_le_nine h E hE
    rw [hinf] at h9
    omega
  · obtain ⟨φ, hφE, hφN⟩ : ∃ φ ∈ E, φ ∉ (suConj h).range := by
      by_contra hcon
      refine hEr fun x hx => ?_
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    obtain ⟨σ, hσ, H, hH⟩ :=
      CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.eq_conj_suField_of_not_mem (h := h) hq
        (hE.2 φ hφE) hφN
    have hE₁ : CFSG.Open.IsElemAbelian 3 (E.map (MulAut.conj (suConj h H)⁻¹).toMonoidHom) :=
      hE.map _
    have hf : suField h σ ∈ E.map (MulAut.conj (suConj h H)⁻¹).toMonoidHom :=
      KSU3Core.mem_map_conj_inv_of_eq_mul_inv (suConj h H) hφE hH
    have hcard : Nat.card (E.map (MulAut.conj (suConj h H)⁻¹).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj (suConj h H)⁻¹).injective
    have h1 := KSU3Core.card_le_three_mul_card_inf_range_suConj h hσ _ hE₁ hf
    have h9 := KSU3Core.card_inf_range_suConj_le_nine h _ hE₁
    omega

theorem card_le_27_psu {F : Type} [Field F] (h : UnitaryFieldData 2 3 F)
    (E : Subgroup (MulAut (unitaryPSU h 3))) (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  have hq : 2 < 2 ^ 3 := by norm_num
  have hDinj := descPSUHom_injective h hq
  have hDsurj := KSU3Core.descPSUHom_surjective_u3 h hq
  have hÃel : CFSG.Open.IsElemAbelian 3 (E.comap (descPSUHom h hq)) := hE.comap hDinj
  have hÃcard : Nat.card (E.comap (descPSUHom h hq)) = Nat.card E := by
    calc Nat.card (E.comap (descPSUHom h hq))
        = Nat.card ((E.comap (descPSUHom h hq)).map (descPSUHom h hq)) :=
          (Subgroup.card_map_of_injective hDinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self_of_surjective hDsurj E]
  have h27 := card_le_27_su h (E.comap (descPSUHom h hq)) hÃel
  omega

theorem exists_field_model {F : Type} [Field F] (h : UnitaryFieldData 2 3 F) {J : Type} [Group J]
    (ψ : unitarySU 2 3 F 3 ≃* J) (α : MulAut J) (hα3 : α ^ 3 = 1)
    (hα : MulAut.congr ψ.symm α ∉ (suConj h).range) :
    ∃ (ψ' : unitarySU 2 3 F 3 ≃* J) (σ : F ≃+* F), orderOf σ = 3 ∧
      ∀ s, α (ψ' s) = ψ' (suField h σ s) := by
  have hq : 2 < 2 ^ 3 := by norm_num
  have hφ3 : (MulAut.congr ψ.symm α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  obtain ⟨σ, hσ, H, hH⟩ :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.eq_conj_suField_of_not_mem (h := h) hq hφ3 hα
  refine ⟨(suConj h H : unitarySU 2 3 F 3 ≃* unitarySU 2 3 F 3).trans ψ, σ, hσ, fun s => ?_⟩
  have hαψ : ∀ u, α (ψ u) = ψ (MulAut.congr ψ.symm α u) := fun u => by
    simp [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]
  rw [hαψ, hH]
  simp [MulAut.mul_apply]

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
