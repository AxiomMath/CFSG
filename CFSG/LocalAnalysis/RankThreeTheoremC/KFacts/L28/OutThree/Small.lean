module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Reduction
public import CFSG.Blueprint.Catalog
import CFSG.Sporadic.Schreier.J1Outer
import CFSG.Sporadic.Bridge.J1
import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner autThreePowInner_alt)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs (autThreePowInner_of_mulEquiv)

theorem outCommInner_alternating_five : OutCommInner (alternatingGroup (Fin 5)) := by
  have hbij :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)
  intro α β
  obtain ⟨σ, rfl⟩ := hbij.2 α
  obtain ⟨τ, rfl⟩ := hbij.2 β
  have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ)]
    group
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  ext x
  simp [MulAut.conj_apply, MulAut.conjNormal_apply]

theorem outCommInner_of_alt_five {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group) : OutCommInner S :=
  OutCommInner.of_mulEquiv e outCommInner_alternating_five

theorem autThreePowInner_of_alt_five {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group) : AutThreePowInner S :=
  autThreePowInner_of_mulEquiv e (autThreePowInner_alt (by norm_num) (by norm_num))

section J1


theorem forall_inner_of_j1 {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) :
    ∀ φ : MulAut S, ∃ g : S, φ = MulAut.conj g := by
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  set e' : S ≃* CFSG.Blueprint.NativeSporadic.J1 := e.trans f.symm
  intro φ
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Schreier.at_j1_schreier.2.1 (MulAut.congr e' φ)
  refine ⟨e'.symm g, (MulAut.congr e').injective ?_⟩
  rw [hg, mulAut_congr_conj, MulEquiv.apply_symm_apply]

theorem outCommInner_of_j1 {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) : OutCommInner S :=
  outCommInner_of_forall_inner (forall_inner_of_j1 e)

theorem autThreePowInner_of_j1 {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) : AutThreePowInner S := by
  intro ψ _ _
  obtain ⟨g, hg⟩ := forall_inner_of_j1 e ψ
  exact ⟨g, fun x => by rw [hg]; rfl⟩

end J1

theorem outCommInner_of_suzukiModel {S : Type} [Group S]
    {p f : ℕ} (h : CFSG.Blueprint.SuzukiModel S p f) : OutCommInner S := fun α β =>
  CFSG.RankThree.PartTwo.KFacts.commutator_le_inner_of_suzukiModel h
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top α) (Subgroup.mem_top β))

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree
