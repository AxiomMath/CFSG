module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeBlocks
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective ne_succ')
open CFSG.SeitzReduction.LinearPilot (upperUnit diagUnit coe_diagUnit)
open scoped MatrixGroups

section Simple

variable {R : Type} [Field R] {S : Type} [Field S] {n : ℕ}

theorem spFieldMap_simpleRootHom (f : R →+* S) (j : Fin n) (A : SL(2, R)) :
    spFieldMap n f (simpleRootHom R j A) = simpleRootHom S j (SpecialLinearGroup.map f A) := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootHom_of_lt h, simpleRootHom_of_lt h, spFieldMap_shortBlock]
  · rw [simpleRootHom_of_not_lt h, simpleRootHom_of_not_lt h, spFieldMap_longBlock]

theorem simpleRootHom_diagUnit (j : Fin n) (κ : Rˣ) :
    ∃ t : Fin n → Rˣ, simpleRootHom R j (diagUnit κ) = diagSp R n t := by
  by_cases h : j.val + 1 < n
  · rw [simpleRootHom_of_lt h]
    exact ⟨_, shortBlock_diagUnit (ne_succ' h) κ⟩
  · rw [simpleRootHom_of_not_lt h]
    refine ⟨Pi.mulSingle j κ, ?_⟩
    rw [← rootTorusHom_apply, rootTorusHom_eq_longBlock]
    congr 1

end Simple

section Root

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {F : Type} [Field F] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} {ι : K →+* F} {σ : F ≃+* F} {k : Fin n}

theorem simpleRootHom_mem_spBlock {j : Fin n} (hkj : k ≠ j)
    (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) (A : SL(2, F)) :
    simpleRootHom F j A ∈ spBlock F ({k}ᶜ : Finset (Fin n)) :=
  simpleRootSL2_le_spBlock_compl hkj hk1 ⟨A, rfl⟩

@[expose] noncomputable def FieldNeighbourParam.rootHom (P : FieldNeighbourParam e t ι σ k)
    {j : Fin n} (hkj : k ≠ j) (hk1 : j.val + 1 < n → k.val ≠ j.val + 1) : SL(2, F) →* G :=
  P.Φ.comp ((simpleRootHom F j).codRestrict _ (simpleRootHom_mem_spBlock hkj hk1))

variable (P : FieldNeighbourParam e t ι σ k) {j : Fin n} (hkj : k ≠ j)
  (hk1 : j.val + 1 < n → k.val ≠ j.val + 1)

theorem FieldNeighbourParam.rootHom_apply (A : SL(2, F)) :
    P.rootHom hkj hk1 A = P.Φ ⟨simpleRootHom F j A, simpleRootHom_mem_spBlock hkj hk1 A⟩ :=
  rfl

theorem FieldNeighbourParam.rootHom_map (A : SL(2, K)) :
    P.rootHom hkj hk1 (SpecialLinearGroup.map ι A) = ((e.symm (simpleRootHom K j A) : L) : G) := by
  rw [← P.N1 _ (simpleRootHom_mem_spBlock hkj hk1 A), FieldNeighbourParam.rootHom_apply]
  congr 1
  exact Subtype.ext (spFieldMap_simpleRootHom ι j A).symm

theorem FieldNeighbourParam.conj_rootHom (A : SL(2, F)) :
    t * P.rootHom hkj hk1 A * t⁻¹ = P.rootHom hkj hk1 (SpecialLinearGroup.map σ.toRingHom A) := by
  rw [FieldNeighbourParam.rootHom_apply, P.N3, FieldNeighbourParam.rootHom_apply]
  congr 1
  apply Subtype.ext
  rw [coe_fieldBlockSp_apply]
  exact spFieldMap_simpleRootHom σ.toRingHom j A

theorem FieldNeighbourParam.commute_rootHom_diagUnit (α : Fˣ) (s : Fin n → Kˣ) :
    Commute (P.rootHom hkj hk1 (diagUnit α)) ((e.symm (diagSp K n s) : L) : G) := by
  obtain ⟨u, hu⟩ := simpleRootHom_diagUnit (R := F) j α
  set x : spBlock F ({k}ᶜ : Finset (Fin n)) :=
    ⟨simpleRootHom F j (diagUnit α), simpleRootHom_mem_spBlock hkj hk1 _⟩ with hx
  have hfix : conjDiagSp ({k}ᶜ : Finset (Fin n)) (liftParam ι s) x = x := by
    apply Subtype.ext
    rw [coe_conjDiagSp_apply, hx]
    simp only
    rw [hu, (commute_diagSp_diagSp (K := F) (liftParam ι s) u).eq, mul_inv_cancel_right]
  have h := P.N2 s (mem_top s) x
  rw [hfix] at h
  change P.Φ x * ((e.symm (diagSp K n s) : L) : G) = ((e.symm (diagSp K n s) : L) : G) * P.Φ x
  calc P.Φ x * ((e.symm (diagSp K n s) : L) : G) =
        (((e.symm (diagSp K n s) : L) : G) * P.Φ x * ((e.symm (diagSp K n s) : L) : G)⁻¹) *
          ((e.symm (diagSp K n s) : L) : G) := by rw [← h]
    _ = ((e.symm (diagSp K n s) : L) : G) * P.Φ x := by group

theorem FieldNeighbourParam.range_rootHom [Finite G] [Finite F] (hK : 4 ≤ Nat.card K) :
    (P.rootHom hkj hk1).range = pieceCore e ({j} : Finset (Fin n)) := by
  rw [P.pieceCore_singleton_eq_map hK hkj hk1]
  ext y
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨⟨simpleRootHom F j A, simpleRootHom_mem_spBlock hkj hk1 A⟩, mem_subgroupOf.2 ⟨A, rfl⟩,
      rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx
    refine ⟨A, ?_⟩
    rw [FieldNeighbourParam.rootHom_apply]
    congr 1
    exact Subtype.ext hA

end Root

end CFSG.SeitzReduction.SymplecticPilot
