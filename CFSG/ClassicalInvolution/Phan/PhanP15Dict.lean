module

public import CFSG.ClassicalInvolution.Phan.PhanP12Std
public import CFSG.ClassicalInvolution.Phan.PhanP14Minus
import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanG
open scoped MatrixGroups

variable {F : Type} [Field F] {ε : F} {hε : ε ≠ 0} {h4 : (4 : F) ≠ 0}

@[expose] def fixA (ε : F) (hε : ε ≠ 0) (h4 : (4 : F) ≠ 0) :
    Subgroup (spinGroup (quadPlus 4 F)) where
  carrier := {y | ∀ x ∈ planeA ε hε h4, spinAction (quadPlus 4 F) y x = x}
  mul_mem' {a b} ha hb x hx := by
    rw [map_mul, LinearEquiv.mul_apply, hb x hx, ha x hx]
  one_mem' x _ := by simp
  inv_mem' {a} ha x hx := by
    have := ha x hx
    calc spinAction (quadPlus 4 F) a⁻¹ x = spinAction (quadPlus 4 F) a⁻¹
          (spinAction (quadPlus 4 F) a x) := by rw [this]
      _ = x := by rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

section Card

variable {p e : ℕ} [Fact p.Prime]

theorem card_fixA_le (hp2 : p ≠ 2) (he : e ≠ 0) {ε : GaloisField p e} (hε : ε ≠ 0)
    (h4 : (4 : GaloisField p e) ≠ 0) (hε' : ¬IsSquare (-ε)) :
    Nat.card (fixA ε hε h4) ≤ Nat.card (Su (GaloisField p (2 * e)) p e 4) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_gf hp2 e
  have : Invertible (2 : GaloisField p e) := invertibleOfNonzero h2
  have hA := restrict_planeA_nondegenerate h2 hε h4
  have hQ : (quadPlus 4 (GaloisField p e)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 _)
  obtain ⟨eN⟩ := nonempty_isometry_planeA_perp_quadMinus h2 hε h4 hε'
  have hirr : ∀ s : GaloisField p e, s ^ 2 + 0 * s + ε ≠ 0 := fun s hs =>
    hε' ⟨s, by linear_combination -hs⟩
  obtain ⟨eSU, -⟩ := CFSG.ClassicalInvolution.WeakCT.SU4.su4SpinMinus_exists hp2 he hirr
  let eG := eN.spinGroupEquiv.trans eSU
  have : Finite (spinGroup ((quadPlus 4 (GaloisField p e)).restrict
      (LinearMap.BilinForm.orthogonal (quadPlus 4 (GaloisField p e)).polarBilin
        (planeA ε hε h4)))) := Finite.of_equiv _ eG.symm.toEquiv
  have : Nontrivial (LinearMap.BilinForm.orthogonal (quadPlus 4 (GaloisField p e)).polarBilin
      (planeA ε hε h4)) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField p e) (by
      rw [finrank_planeA_perp h2 hε h4]; norm_num)
  have hle : fixA ε hε h4 ≤ ((decompOrth hA).toIsometry.comp
      (QuadraticMap.Isometry.inl ((quadPlus 4 (GaloisField p e)).restrict
        (LinearMap.BilinForm.orthogonal (quadPlus 4 (GaloisField p e)).polarBilin
          (planeA ε hε h4))) ((quadPlus 4 (GaloisField p e)).restrict
            (planeA ε hε h4)))).spinGroupMap.range :=
    fun y hy => mem_range_spinGroupMap_of_fix hQ hA hy
  have hfin : Finite ((decompOrth hA).toIsometry.comp
      (QuadraticMap.Isometry.inl ((quadPlus 4 (GaloisField p e)).restrict
        (LinearMap.BilinForm.orthogonal (quadPlus 4 (GaloisField p e)).polarBilin
          (planeA ε hε h4))) ((quadPlus 4 (GaloisField p e)).restrict
            (planeA ε hε h4)))).spinGroupMap.range :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  calc Nat.card (fixA ε hε h4) ≤ _ := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (spinGroup ((quadPlus 4 (GaloisField p e)).restrict
      (LinearMap.BilinForm.orthogonal (quadPlus 4 (GaloisField p e)).polarBilin
        (planeA ε hε h4)))) :=
      Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    _ = Nat.card (Su (GaloisField p (2 * e)) p e 4) := Nat.card_congr eG.toEquiv

end Card

section Dict

variable {p e : ℕ} [Fact p.Prime]

theorem fixA_le_parab (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    fixA M.ε M.hε M.h4 ≤ parab M.S {1, 2, 3} := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hK := StdModel.card_K hq
  have h2 := two_ne_zero_gf hp2 e
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨ψ, hch⟩ := exists_chain_123 hK hq M.good
  have hinj : Function.Injective ψ := hch.injective hK M.good h2K
  have hgen := iSup_range_blockEmb2 hK (by omega : p ^ e ≠ 2) 3
  have hle_fix : ∀ j : Fin 3, ∀ A : Su (GaloisField p (2 * e)) p e 2,
      ψ (blockEmb2 (GaloisField p (2 * e)) p e 3 j A) ∈ fixA M.ε M.hε M.h4 := by
    intro j A
    have h1 := hch.le_range j A
    have hk : (![2, 1, 3] : Fin 3 → Fin 4) j ≠ 0 := by fin_cases j <;> decide
    exact spinAction_fix_planeA M.spec h2 hk h1
  have hle_par : ∀ j : Fin 3, ∀ A : Su (GaloisField p (2 * e)) p e 2,
      ψ (blockEmb2 (GaloisField p (2 * e)) p e 3 j A) ∈ parab M.S {1, 2, 3} := by
    intro j A
    have h1 := hch.le_range j A
    refine Lsup_le_parab (S := M.S) {1, 2, 3} ?_
    have : (![2, 1, 3] : Fin 3 → Fin 4) j ∈ ({1, 2, 3} : Set (Fin 4)) := by
      fin_cases j <;> simp
    exact (le_iSup₂ (f := fun (k : Fin 4) (_ : k ∈ ({1, 2, 3} : Set (Fin 4))) => (M.S.ι k).range)
      ((![2, 1, 3] : Fin 3 → Fin 4) j) this) h1
  have hrange : ∀ {P : Subgroup (spinGroup (quadPlus 4 (GaloisField p e)))},
      (∀ j : Fin 3, ∀ A : Su (GaloisField p (2 * e)) p e 2,
        ψ (blockEmb2 (GaloisField p (2 * e)) p e 3 j A) ∈ P) → ψ.range ≤ P := by
    intro P hP
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ ⨆ i : Fin 3, (blockEmb2 (GaloisField p (2 * e)) p e 3 i).range := by
      rw [hgen]; exact Subgroup.mem_top a
    refine Subgroup.iSup_induction _ (C := fun a => ψ a ∈ P) ha ?_ ?_ ?_
    · rintro i _ ⟨A, rfl⟩
      exact hP i A
    · rw [map_one]; exact one_mem _
    · intro a b ha hb
      rw [map_mul]; exact mul_mem ha hb
  have hrf := hrange hle_fix
  have hrp := hrange hle_par
  have hcard : Nat.card (fixA M.ε M.hε M.h4) ≤ Nat.card ψ.range := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact card_fixA_le hp2 he M.hε M.h4 M.nonsq
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hfinG : Finite (spinGroup (quadPlus 4 (GaloisField p e))) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hfin : Finite (fixA M.ε M.hε M.h4) := inferInstance
  have heq : ψ.range = fixA M.ε M.hε M.h4 := Subgroup.eq_of_le_of_card_ge hrf hcard
  rw [← heq]
  exact hrp

end Dict

section StabJ

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {S : PhanFamilyD4 K p f (spinGroup (quadPlus 4 F))}

theorem exists_tor_zero_mul_fix (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (hS : ModelSpec S ε hε h4) (hq : 5 ≤ p ^ f) (h2 : (2 : F) ≠ 0) (h2K : (2 : K) ≠ 0)
    {g : spinGroup (quadPlus 4 F)} (hgJ : g ∈ stabJ ε hε h4) :
    ∃ t ∈ (tor S 0).range, t⁻¹ * g ∈ fixA ε hε h4 := by
  obtain ⟨pr, hpr⟩ := exists_param_A h2 hgJ.1
  obtain ⟨t, ht, hta⟩ := exists_tor_zero_of_param hK hg hS hq h2 h2K pr
  have htR : t ∈ (S.ι 0).range := by
    obtain ⟨y, rfl⟩ := ht
    exact ⟨_, rfl⟩
  refine ⟨t, ht, fun x hx => ?_⟩
  obtain ⟨α, β, rfl⟩ := exists_comb_of_mem_planeA h2 hx
  have hinv : ∀ y, spinAction (quadPlus 4 F) t⁻¹ (spinAction (quadPlus 4 F) t y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hA1 : spinAction (quadPlus 4 F) g (vecA1 F) = spinAction (quadPlus 4 F) t (vecA1 F) := by
    rw [hpr, hta]
  have e1 : spinAction (quadPlus 4 F) (t⁻¹ * g) (vecA1 F) = vecA1 F := by
    rw [map_mul, LinearEquiv.mul_apply, hA1, hinv]
  have e2 : spinAction (quadPlus 4 F) (t⁻¹ * g) (jOp ε (vecA1 F)) = jOp ε (vecA1 F) := by
    rw [map_mul, LinearEquiv.mul_apply, hgJ.2 _ (vecA1_mem_planeA ε hε h4), hA1,
      ← spinAction_comm_jOp_of_mem_range_zero hS htR, hinv]
  rw [map_add, map_smul, map_smul, e1, e2]

end StabJ

section Stab

variable {p e : ℕ} [Fact p.Prime]

theorem stabJ_le_parab (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    stabJ M.ε M.hε M.h4 ≤ parab M.S {1, 2, 3} := by
  intro g hg
  have hK := StdModel.card_K hq
  have h2 := two_ne_zero_gf hp2 e
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨t, ht, hfix⟩ := exists_tor_zero_mul_fix hK M.good M.spec hq h2 h2K hg
  have hgt : g = t * (t⁻¹ * g) := by group
  rw [hgt]
  exact mul_mem (torusSub_le_parab (S := M.S) {1, 2, 3} (tor_range_le_torusSub 0 ht))
    (fixA_le_parab M hp2 hq hfix)

end Stab

end CFSG.ClassicalInvolution.PhanP
