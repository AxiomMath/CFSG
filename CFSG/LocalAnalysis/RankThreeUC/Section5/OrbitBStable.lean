module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaConjugationAction
public import CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors
public import CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitFixedVectorOrbitStable
public import CFSG.LocalAnalysis.RankThreeUC.Section5.IsInternalHyperplaneFixedSubmoduleOfBinaryRankCounterexample

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitBStable

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

theorem stable {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {D : Subgroup G} (hD : D ∈ Delta p P ρ) :
    ∀ b ∈ B, ∀ s ∈ twoCoreCommutator T B, ∃ t ∈ twoCoreCommutator T B,
      (D.map (MulAut.conj s).toMonoidHom).map (MulAut.conj b).toMonoidHom =
        D.map (MulAut.conj t).toMonoidHom := by
  classical
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  letI : MulAction G (Delta p P ρ) := MulAction.compHom _ (DeltaConjugationAction.act (p := p) hP ρ)
  have hsmul : ∀ (g : G) (i : Delta p P ρ), ((g • i : Delta p P ρ) : Subgroup G) =
      i.1.map (MulAut.conj g).toMonoidHom := fun g i => rfl
  have hperm : ∀ (g : G) (i : Delta p P ρ),
      (CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ i.1).map (ρ g) = CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (g • i).1 :=
    fun g i => DeltaConjugationAction.fixed_map hP ρ g i
  have hU : iSupIndep (fun D : Delta p P ρ => CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ D.1) :=
    (isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc).submodule_iSupIndep
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  let i : Delta p P ρ := ⟨D, hD⟩
  let Wsp : Submodule (ZMod 2) V := ⨆ s : S, CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (s.val • i).1
  let ρS : Representation (ZMod 2) S V := ρ.comp S.subtype
  have hWinv : ∀ g : S, Wsp ≤ Wsp.comap (ρS g) := by
    intro g
    refine iSup_le fun s => ?_
    intro v hv
    have hv' : ρ g.val v ∈ (CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (s.val • i).1).map (ρ g.val) :=
      Submodule.mem_map_of_mem hv
    rw [hperm] at hv'
    have : (g.val • (s.val • i)) = (g * s).val • i := by
      rw [← mul_smul]; rfl
    rw [this] at hv'
    exact Submodule.mem_iSup_of_mem (g * s) hv'
  have hWne : Wsp ≠ ⊥ := by
    intro h
    have h1 : CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (((1 : S).val • i : Delta p P ρ)).1 ≤ Wsp :=
      le_iSup (fun s : S => CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ (s.val • i).1) 1
    rw [h] at h1
    have : CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ D = ⊥ := by
      rw [eq_bot_iff]
      simpa using h1
    exact hD.2.2 this
  haveI : Finite S := inferInstance
  obtain ⟨w, hwW, hw0, hwfix⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors.exists_fixed (H := S) hS2 ρS Wsp hWinv hWne
  have hB : ∀ b : B, ρ b.val w = w := by
    intro b
    have hwS : w ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), B⁆ := by
      rw [CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule, Representation.mem_invariants]
      intro x
      exact hwfix ⟨x.1, x.2⟩
    have hchar : ∀ φ : ↥B ≃* ↥B,
        Subgroup.map φ.toMonoidHom (B.subgroupOf B) = B.subgroupOf B := by
      intro φ
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 φ.surjective
    exact (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction B le_rfl hchar).1 b.val b.2 w hwS
  have key := CFSG.GroupTheory.CoprimeActionSupport.IndependentOrbitFixedVectorOrbitStable.orbit_stable
    (fun D : Delta p P ρ => CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule ρ D.1) hU ρ hperm S B i w hw0 hwW
    (fun s => hwfix s) hB
  intro b hb s hs
  obtain ⟨t, ht⟩ := key ⟨b, hb⟩ ⟨s, hs⟩
  refine ⟨t.val, t.2, ?_⟩
  have := congrArg Subtype.val ht
  exact this

end CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitBStable
