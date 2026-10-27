module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Elts
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank.O7

open Matrix CFSG.Open

abbrev Idx : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

@[expose] def e7 : Fin 7 ≃ Idx where
  toFun i := ![.inl 0, .inl 1, .inl 2, .inr (.inl 0), .inr (.inl 1), .inr (.inl 2),
    .inr (.inr ())] i
  invFun
    | .inl i => ⟨i.1, by omega⟩
    | .inr (.inl i) => ⟨3 + i.1, by omega⟩
    | .inr (.inr _) => 6
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def Phi : GL (Fin 7) K ≃* GL Idx K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K e7).toRingEquiv.toMulEquiv

theorem coe_Phi (g : GL (Fin 7) K) : ((Phi g : GL Idx K) : Matrix Idx Idx K) =
    Matrix.reindex e7 e7 (g : M7) := rfl

theorem Qidx_eq (v : Idx → K) : StatedQuadOdd 3 K v = Q7 (fun i => v (e7 i)) := by
  simp [StatedQuadOdd, Q7, Fintype.sum_sum_type, Fin.sum_univ_three, e7]

theorem Phi_mulVec (g : GL (Fin 7) K) (v : Idx → K) :
    ((Phi g : GL Idx K) : Matrix Idx Idx K) *ᵥ v =
      fun i => ((g : M7) *ᵥ (fun j => v (e7 j))) (e7.symm i) := by
  rw [coe_Phi, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  rfl

theorem Phi_mem_iff (g : GL (Fin 7) K) :
    Phi g ∈ {A : GL Idx K | ∀ v, StatedQuadOdd 3 K ((A : Matrix Idx Idx K) *ᵥ v) =
      StatedQuadOdd 3 K v} ↔ g ∈ isoSet := by
  simp only [Set.mem_setOf_eq, isoSet]
  constructor
  · intro h w
    have := h (fun i => w (e7.symm i))
    rw [Phi_mulVec, Qidx_eq, Qidx_eq] at this
    simpa using this
  · intro h v
    rw [Phi_mulVec, Qidx_eq, Qidx_eq]
    simpa using h (fun j => v (e7 j))

theorem isoSet_image : {A : GL Idx K | ∀ v, StatedQuadOdd 3 K ((A : Matrix Idx Idx K) *ᵥ v) =
    StatedQuadOdd 3 K v} = Phi '' isoSet := by
  ext A
  constructor
  · intro hA
    refine ⟨Phi.symm A, (Phi_mem_iff _).1 ?_, by simp⟩
    simpa using hA
  · rintro ⟨g, hg, rfl⟩
    exact (Phi_mem_iff g).2 hg

theorem statedOmega_eq_map :
    StatedOmega (StatedQuadOdd 3 K) = Om7.map Phi.toMonoidHom := by
  unfold StatedOmega Om7
  rw [Subgroup.map_commutator, MonoidHom.map_closure]
  exact congrArg₂ _ (congrArg _ isoSet_image) (congrArg _ isoSet_image)

@[expose] noncomputable def Om7EquivOmega : Om7 ≃* StatedOmega (StatedQuadOdd 3 K) :=
  (Om7.equivMapOfInjective Phi.toMonoidHom Phi.injective).trans
    (MulEquiv.subgroupCongr statedOmega_eq_map.symm)

theorem det_eq_one_of_mem_Om7 {g : GL (Fin 7) K} (hg : g ∈ Om7) :
    Matrix.GeneralLinearGroup.det g = 1 := by
  have : Om7 ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 7) K →* Kˣ).ker := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  exact MonoidHom.mem_ker.1 (this hg)

theorem det_Phi (g : GL (Fin 7) K) :
    Matrix.GeneralLinearGroup.det (Phi g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, coe_Phi, Matrix.reindex_apply]
  exact Matrix.det_submatrix_equiv_self e7.symm _

theorem eq_one_of_scalar {g : GL (Fin 7) K} (hg : g ∈ Om7)
    (hs : Phi g ∈ StatedScalars Idx K) : g = 1 := by
  obtain ⟨c, hc⟩ := hs
  have h1 : Matrix.GeneralLinearGroup.det (Phi g) = 1 := by
    rw [det_Phi]; exact det_eq_one_of_mem_Om7 hg
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar] at h1
  have hc1 : c = 1 := by
    have : ∀ c : Kˣ, c ^ Fintype.card Idx = 1 → c = 1 := by decide
    exact this c h1
  subst hc1
  apply Phi.injective
  rw [← hc]
  simp

@[expose] noncomputable def ProjEquivOm7 :
    StatedProj (StatedOmega (StatedQuadOdd 3 K)) ≃* Om7 := by
  have hbot : (StatedScalars Idx K).subgroupOf (StatedOmega (StatedQuadOdd 3 K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : (x : GL Idx K) ∈ Om7.map Phi.toMonoidHom := by
      rw [← statedOmega_eq_map]; exact x.2
    obtain ⟨g, hg, hgx⟩ := hx'
    have : g = 1 := eq_one_of_scalar hg (by
      have : Phi g = (x : GL Idx K) := hgx
      rw [this]; exact hx)
    subst this
    apply Subtype.ext
    simpa using hgx.symm
  exact ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans
    Om7EquivOmega.symm

theorem card_Om7 : Nat.card Om7 = 4585351680 := by
  have h := CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC
    (K := K) (p := 3) (f := 1) Nat.prime_three (by norm_num) (by simp [ZMod.card]) (n := 3)
    (by norm_num)
  have h' : Nat.card (StatedProj (StatedOmega (StatedQuadOdd 3 K))) = ordBC 3 (3 ^ 1) := h
  rw [← Nat.card_congr ProjEquivOm7.toEquiv, h']
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LieRank.O7
