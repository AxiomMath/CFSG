module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeI
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeII

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

theorem OmegaSetting.finrank_iSup_movedSpace_rhoE_eq_four (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) :
    finrank K ↥(⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) = 4 :=
  hs.finrank_iSup_movedSpace_rhoE_of_caseII hfix hK hF
    (hs.caseII_of_six_lt_finrank htop hF (by omega)) ha ha0

theorem OmegaSetting.qf_eq_zero_of_mem_iSup_movedSpace_rhoE (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) {x : V}
    (hx : x ∈ ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)) : Qf x = 0 :=
  hs.qf_eq_zero_of_mem_iSup_movedSpace_rhoE_of_caseII hfix hK hF
    (hs.caseII_of_six_lt_finrank htop hF (by omega)) ha ha0 hx

theorem OmegaSetting.movedSpace_rhoE_eq_iSup (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a w : N} (ha : QN a = 0) (ha0 : a ≠ 0) (haw : polar QN a w = 0)
    (hw : QN w ≠ 0) :
    movedSpace (rhoE ρ a w) = ⨆ (x : N) (_ : polar QN a x = 0), movedSpace (rhoE ρ a x) :=
  hs.movedSpace_rhoE_eq_iSup_of_caseII hfix hK hF
    (hs.caseII_of_six_lt_finrank htop hF (by omega)) ha ha0 haw hw

omit [CharP K 2] [Finite K] [FiniteDimensional K V] in
private theorem forall_apply_eq_iff_mem_orthogonal_iSup
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {ι : Type*} (p : ι → Prop)
    (g : ι → V ≃ₗ[K] V) (hg : ∀ i v, Qf (g i v) = Qf v) (x : V) :
    (∀ i, p i → g i x = x) ↔
      x ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf)
        (⨆ (i : ι) (_ : p i), movedSpace (g i)) := by
  have hker : ∀ i, x ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) (movedSpace (g i)) ↔
      g i x = x := fun i => by
    rw [← ker_sub_one_eq_orthogonal_movedSpace hnd (hg i), LinearMap.mem_ker]
    simp [sub_eq_zero]
  constructor
  · intro h
    have hle : (⨆ (i : ι) (_ : p i), movedSpace (g i)) ≤
        LinearMap.ker ((polarBilin Qf).flip x) := by
      refine iSup₂_le fun i hi y hy => ?_
      have hx := mem_orthogonal_iff_polar.mp ((hker i).mpr (h i hi)) y hy
      rw [LinearMap.mem_ker, LinearMap.flip_apply, polarBilin_apply_apply]
      exact hx
    refine mem_orthogonal_iff_polar.mpr fun y hy => ?_
    have hy' := hle hy
    rwa [LinearMap.mem_ker, LinearMap.flip_apply, polarBilin_apply_apply] at hy'
  · intro hx i hi
    have hle : movedSpace (g i) ≤ ⨆ (i : ι) (_ : p i), movedSpace (g i) :=
      le_iSup₂_of_le i hi le_rfl
    exact (hker i).mp (mem_orthogonal_iff_polar.mpr fun y hy =>
      mem_orthogonal_iff_polar.mp hx y (hle hy))

theorem OmegaSetting.forall_rhoE_apply_eq_iff_mem_iSup (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {a : N} (ha : QN a = 0) (ha0 : a ≠ 0) (x : V) :
    (∀ w : N, polar QN a w = 0 → rhoE ρ a w x = x) ↔
      x ∈ ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w) := by
  have hII := hs.caseII_of_six_lt_finrank htop hF (by omega)
  have hfin := hs.finrank_iSup_movedSpace_rhoE_of_caseII hfix hK hF hII ha ha0
  have hle := le_orthogonal_of_totallySingular fun y hy =>
    hs.qf_eq_zero_of_mem_iSup_movedSpace_rhoE_of_caseII hfix hK hF hII ha ha0 hy
  have hperp := finrank_orthogonal_polar hs.nd
    (⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w))
  rw [h8, hfin] at hperp
  have hEq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hperp, hfin])
  refine (forall_apply_eq_iff_mem_orthogonal_iSup hs.nd (fun w => polar QN a w = 0) (rhoE ρ a)
    (fun w v => hs.iso _ v) x).trans ?_
  rw [← hEq]

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
