module

public import CFSG.ClassicalInvolution.Q3.Q3TJD4Lin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.Steinberg.SpinPlus
open scoped Matrix

variable {K : Type} [Field K]

theorem three_le_four : 3 ≤ 4 := by norm_num

theorem fin4_zero_ne_one : (0 : Fin 4) ≠ 1 := by decide

theorem fin4_one_ne_zero : (1 : Fin 4) ≠ 0 := by decide

theorem fin4_two_ne_three : (2 : Fin 4) ≠ 3 := by decide

variable (K) in
@[expose] noncomputable def d4Six : Bool ⊕ Bool × Bool → spinGroup (quadPlus 4 K)
  | .inl t => (plusFrame 4 K three_le_four).longRoot fin4_zero_ne_one true t (.ofAdd 1)
  | .inr (s, t) => (plusFrame 4 K three_le_four).longRoot fin4_two_ne_three s t (.ofAdd 1)

variable (K) in
@[expose] def d4SixMat : Bool ⊕ Bool × Bool → Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K
  | .inl t => longMat K plusIdx (0 : Fin 4) 1 true t
  | .inr (s, t) => longMat K plusIdx (2 : Fin 4) 3 s t

variable (K) in
@[expose] noncomputable def d4R0 : Subgroup (spinGroup (quadPlus 4 K)) :=
  plusRootGroup 4 K three_le_four (Pi.single 0 1) ⊔ plusRootGroup 4 K three_le_four (-Pi.single 0 1)

theorem coe_spinMatrix_d4Six (i : Bool ⊕ Bool × Bool) :
    (spinMatrix (quadPlus 4 K) (d4Six K i) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + d4SixMat K i := by
  rcases i with t | ⟨s, t⟩
  · change (spinMatrix (quadPlus 4 K) ((plusFrame 4 K three_le_four).longRoot fin4_zero_ne_one
      true t (.ofAdd 1)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + longMat K plusIdx (0 : Fin 4) 1 true t
    rw [coe_spinMatrix_longRoot (isCoordFrame_plusFrame three_le_four), one_smul]
  · change (spinMatrix (quadPlus 4 K) ((plusFrame 4 K three_le_four).longRoot fin4_two_ne_three
      s t (.ofAdd 1)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) =
      1 + longMat K plusIdx (2 : Fin 4) 3 s t
    rw [coe_spinMatrix_longRoot (isCoordFrame_plusFrame three_le_four), one_smul]

theorem d4SixMat_mulVec_e0 (i : Bool ⊕ Bool × Bool) :
    d4SixMat K i *ᵥ Pi.single (.inl 0) 1 = 0 := by
  rcases i with t | ⟨s, t⟩
  · exact longMat_zero_one_mulVec_e0 t
  · exact longMat_two_three_mulVec_e0 s t

theorem finrank_le_three_of_d4SixMat (W : Submodule K (Fin 4 ⊕ Fin 4 → K))
    (hW : ∀ w ∈ W, quadPlus 4 K w = 0) (h : ∀ i, ∀ w ∈ W, d4SixMat K i *ᵥ w ∈ W) :
    Module.finrank K W ≤ 3 :=
  finrank_le_three_of_invariant W hW (fun s t => h (.inr (s, t))) (fun t => h (.inl t))

theorem d4Six_inl_false_mem : d4Six K (.inl false) ∈ d4R0 K := by
  refine Subgroup.mem_sup_left ?_
  rw [plusRootGroup_single]
  exact ⟨.ofAdd 1, rfl⟩

theorem d4Six_commute_rootD (i : Bool ⊕ Bool × Bool) (hi : i ≠ .inl false) (c : K) :
    Commute (d4Six K i) (rootD K three_le_four 0 (.ofAdd c)) := by
  rcases i with t | ⟨s, t⟩
  · obtain rfl : t = true := by
      cases t
      · exact absurd rfl hi
      · rfl
    exact HypFrame.commute_longRoot_longRoot_left _ fin4_zero_ne_one fin4_zero_ne_one true true
      false 1 c
  · exact HypFrame.commute_longRoot_longRoot_of_disjoint _ fin4_two_ne_three fin4_zero_ne_one
      (by decide) (by decide) (by decide) (by decide) s t true false 1 c

theorem d4Six_commute_negRootD (i : Bool ⊕ Bool × Bool) (hi : i ≠ .inl false) (c : K) :
    Commute (d4Six K i) (negRootD K three_le_four 0 (.ofAdd c)) := by
  rcases i with t | ⟨s, t⟩
  · obtain rfl : t = true := by
      cases t
      · exact absurd rfl hi
      · rfl
    change Commute ((plusFrame 4 K three_le_four).longRoot fin4_zero_ne_one true true (.ofAdd 1))
      ((plusFrame 4 K three_le_four).longRoot fin4_one_ne_zero true false (.ofAdd c))
    rw [HypFrame.longRoot_swap]
    exact HypFrame.commute_longRoot_longRoot_left _ fin4_zero_ne_one.symm fin4_one_ne_zero true
      true false (-1) c
  · exact HypFrame.commute_longRoot_longRoot_of_disjoint _ fin4_two_ne_three fin4_one_ne_zero
      (by decide) (by decide) (by decide) (by decide) s t true false 1 c

theorem d4Six_commute (i : Bool ⊕ Bool × Bool) (hi : i ≠ .inl false) :
    ∀ r ∈ d4R0 K, Commute (d4Six K i) r := by
  have hle : d4R0 K ≤ Subgroup.centralizer {d4Six K i} := by
    refine sup_le ?_ ?_
    · rw [plusRootGroup_single]
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (d4Six_commute_rootD i hi (Multiplicative.toAdd c)).eq.symm
    · rw [plusRootGroup_neg_single]
      rintro _ ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (d4Six_commute_negRootD i hi (Multiplicative.toAdd c)).eq.symm
  intro r hr
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hr)).symm

end CFSG.ClassicalInvolution.Q3.Q3T
