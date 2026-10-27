module

public import CFSG.GH74.Generic.S1.Exo.HermOddStructure
public import CFSG.GH74.Generic.S1.Exo.LinMinus

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap CFSG.Open
open scoped Matrix

@[expose] def OmegaSplit (H : Type) [Group H] (z : H) (q : ℕ) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = q ^ 2 ∧
    ∃ Ω : Subgroup H, IsSimpleGroup ↥Ω ∧ Group.IsPerfect ↥Ω ∧
      Nat.card ↥Ω * 2 = q ^ 2 * (q ^ 4 - 1) ∧ Nonempty (↥Ω ≃* StatedProj (StatedSL 2 E)) ∧
      z ∉ Ω ∧ ∀ h : H, h ∈ Ω ∨ z * h ∈ Ω

theorem OmegaSplit.of_mulEquiv {H H' : Type} [Group H] [Group H'] (ψ : H ≃* H') {z : H} {z' : H'}
    (hz : ψ z = z') {q : ℕ} (h : OmegaSplit H z q) : OmegaSplit H' z' q := by
  obtain ⟨E, _, _, hE, Ω, hs, hp, hc, ⟨hi⟩, hzΩ, hall⟩ := h
  have e1 : ↥Ω ≃* ↥(Ω.map ψ.toMonoidHom) := ψ.subgroupMap Ω
  refine ⟨E, inferInstance, inferInstance, hE, Ω.map ψ.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact e1.symm.isSimpleGroup
  · exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  · rw [Nat.card_congr e1.symm.toEquiv]
    exact hc
  · exact ⟨e1.symm.trans hi⟩
  · rw [← hz]
    intro hmem
    exact hzΩ (by simpa using Subgroup.mem_map_equiv.1 hmem)
  · intro h'
    obtain ⟨h, rfl⟩ := ψ.surjective h'
    rcases hall h with h1 | h1
    · exact Or.inl ⟨h, h1, rfl⟩
    · refine Or.inr ⟨z * h, h1, ?_⟩
      rw [← hz]
      simp

theorem omegaSplit_soForm {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) {V : Type}
    [AddCommGroup V] [Module K V] (hdim : finrank K V = 4) (Q : QuadraticForm K V)
    (hnd : LinearMap.Nondegenerate (polarBilin Q))
    (hnp : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ hneg : LinearEquiv.neg K ∈ soForm Q,
      OmegaSplit ↥(soForm Q) ⟨LinearEquiv.neg K, hneg⟩ (Nat.card K) := by
  obtain ⟨E, _, _, hE, Ω, hle, hs, hp, hc, hi, hneg, hnegΩ, hall⟩ :=
    soForm_minus_four_structure h2 hdim Q hnd hnp
  refine ⟨hneg, E, inferInstance, inferInstance, hE, Ω.subgroupOf (soForm Q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.subgroupOfEquivOfLe hle).isSimpleGroup
  · exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hc
  · obtain ⟨e⟩ := hi
    exact ⟨(Subgroup.subgroupOfEquivOfLe hle).trans e⟩
  · exact hnegΩ
  · intro h
    exact hall h h.2

theorem omegaSplit_soMat {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (G : Matrix (Fin 4) (Fin 4) K) (hsymm : Gᵀ = G) (hdet : ¬ IsSquare G.det) :
    OmegaSplit ↥(soMat G) ⟨-1, neg_one_mem_soMat G⟩ (Nat.card K) := by
  obtain ⟨hnd, hnp⟩ := toQuadraticForm_minus_of_det_nonsquare h2 G hsymm hdet
  obtain ⟨hneg, hΩ⟩ := omegaSplit_soForm h2 (V := Fin 4 → K) (by simp)
    (Matrix.toQuadraticForm' G) hnd hnp
  obtain ⟨ψ, hψ⟩ := soMat_mulEquiv_soForm h2 G hsymm
  refine hΩ.of_mulEquiv ψ.symm ?_
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  exact (hψ ⟨-1, neg_one_mem_soMat G⟩ rfl).symm

end CFSG.GH74.Generic.S1.Exo
