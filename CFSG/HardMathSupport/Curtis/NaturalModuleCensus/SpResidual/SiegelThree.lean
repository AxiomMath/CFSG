module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelBlock
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.PerfectKer

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.SiegelThree

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K]

theorem exists_conj_eq_of_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hsq : ∀ x ∈ N, x * x = 1)
    {l m : G} (hm : m ∈ N) (h3 : l ^ 3 = 1) (hv : (l * m) ^ 3 = 1) :
    ∃ ρ ∈ N, ρ⁻¹ * (l * m) * ρ = l := by
  have hl : l⁻¹ = l * l := by
    rw [inv_eq_iff_mul_eq_one]
    calc l * (l * l) = l ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := h3
  have hll : l⁻¹ * l⁻¹ = l := by
    calc l⁻¹ * l⁻¹ = l⁻¹ * (l * l) := by rw [← hl]
      _ = l := by group
  have hm1 : l * m * l⁻¹ ∈ N := ‹N.Normal›.conj_mem m hm l
  have hm2 : l⁻¹ * m * l ∈ N := by
    have := ‹N.Normal›.conj_mem m hm l⁻¹
    simpa using this
  have hprod : (l * m * l⁻¹) * (l⁻¹ * m * l) * m = 1 := by
    calc (l * m * l⁻¹) * (l⁻¹ * m * l) * m = l * m * (l⁻¹ * l⁻¹) * m * l * m := by group
      _ = l * m * l * m * l * m := by rw [hll]
      _ = (l * m) ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := hv
  have hprod' : (l * m * l⁻¹) * m * (l⁻¹ * m * l) = 1 := by
    rw [mul_assoc (l * m * l⁻¹) m, hcomm m hm _ hm2, ← mul_assoc]
    exact hprod
  have hm2eq : l⁻¹ * m * l = (l * m * l⁻¹) * m := by
    have h1 := eq_inv_of_mul_eq_one_right hprod'
    rw [_root_.mul_inv_rev] at h1
    have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right (hsq m hm)
    have hm1i : (l * m * l⁻¹)⁻¹ = l * m * l⁻¹ := inv_eq_of_mul_eq_one_right (hsq _ hm1)
    rw [h1, hmi, hm1i]
    exact hcomm _ hm _ hm1
  have e : l * m * (l⁻¹ * m * l) = (l⁻¹ * m * l) * l := by
    calc l * m * (l⁻¹ * m * l) = (l * m * l⁻¹) * (m * l) := by group
      _ = ((l * m * l⁻¹) * m) * l := by group
      _ = (l⁻¹ * m * l) * l := by rw [hm2eq]
  refine ⟨l⁻¹ * m * l, hm2, ?_⟩
  calc (l⁻¹ * m * l)⁻¹ * (l * m) * (l⁻¹ * m * l)
      = (l⁻¹ * m * l)⁻¹ * (l * m * (l⁻¹ * m * l)) := by group
    _ = l := by rw [e]; group

theorem spMat_leviSp (B : GL (Fin 2) K) :
    spMat (SymplecticTorusWeyl.leviSp B) = fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0
      ((B⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
  SymplecticTorusWeyl.coe_leviSp B

theorem leviSp_mem (B : GL (Fin 2) K) :
    SymplecticTorusWeyl.leviSp B ∈ flagStabilizer 2 K {2} := by
  rw [SymplecticHigher.mem_flagStabilizer]
  intro i hi
  rw [Set.mem_singleton_iff.1 hi]
  have key : ∀ C : GL (Fin 2) K, ∀ x ∈ SymplecticFlag.flag 2 K 2,
      spMat (SymplecticTorusWeyl.leviSp C) *ᵥ x ∈ SymplecticFlag.flag 2 K 2 := by
    intro C x hx
    rw [SymplecticFlag.mem_flag_of_le le_rfl, SymplecticFlag.mem_isoFlag] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨fun j => ?_, fun j hj => absurd j.2 (by omega)⟩
    have hx0 : (x ∘ Sum.inr : Fin 2 → K) = 0 := funext hx1
    rw [spMat_leviSp, fromBlocks_mulVec]
    simp [hx0]
  refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (key B) fun v hv => ?_
  rw [← map_inv (SymplecticTorusWeyl.leviSp (r := 2) (k := K)) B]
  exact key _ v hv

theorem exists_unip {x : StatedSp 2 K} (hx : x ∈ flagStabilizer 2 K {2})
    (h1 : blockA (⟨x, hx⟩ : ↥(flagStabilizer 2 K {2})) = 1) :
    ∃ X : Matrix (Fin 2) (Fin 2) K, spMat x = fromBlocks 1 X 0 1 := by
  have hs := spMat_eq_fromBlocks_of_mem hx
  have h1' : (spMat x).toBlocks₁₁ = 1 := h1
  have hsymp : (spMat x)ᵀ * fromBlocks 0 1 (-1) 0 * spMat x = fromBlocks 0 1 (-1) 0 :=
    SymplecticTorusWeyl.mem_statedSp_iff.1 x.2
  have hD : (spMat x).toBlocks₂₂ = 1 := by
    rw [hs, h1'] at hsymp
    have := congrArg Matrix.toBlocks₁₂ hsymp
    rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at this
    simpa using this
  refine ⟨(spMat x).toBlocks₁₂, ?_⟩
  calc spMat x = fromBlocks (spMat x).toBlocks₁₁ (spMat x).toBlocks₁₂ 0 (spMat x).toBlocks₂₂ := hs
    _ = _ := by rw [h1', hD]

@[expose] def kerA : Subgroup ↥(flagStabilizer 2 K {2}) := (blockA (K := K)).toHomUnits.ker

theorem mem_kerA {x : ↥(flagStabilizer 2 K {2})} : x ∈ kerA ↔ blockA x = 1 := by
  rw [kerA, MonoidHom.mem_ker, Units.ext_iff]
  simp

instance : (kerA (K := K)).Normal := MonoidHom.normal_ker _

theorem kerA_comm {x y : ↥(flagStabilizer 2 K {2})} (hx : x ∈ kerA) (hy : y ∈ kerA) :
    x * y = y * x := by
  obtain ⟨X, hX⟩ := exists_unip x.2 (mem_kerA.1 hx)
  obtain ⟨Y, hY⟩ := exists_unip y.2 (mem_kerA.1 hy)
  apply Subtype.ext
  apply spMat_injective
  show spMat (x.1 * y.1) = spMat (y.1 * x.1)
  rw [spMat_mul, spMat_mul, hX, hY, fromBlocks_multiply, fromBlocks_multiply]
  simp [add_comm]

section CharTwo

variable [CharP K 2]

@[expose] def swap₀ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

omit [CharP K 2] in
theorem swap₀_mul_self : swap₀ * swap₀ = (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap₀, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 swap₀ swap₀ 0

omit [CharP K 2] in
theorem swapMat_mul_self : swapMat * swapMat = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  rw [swapMat, fromBlocks_multiply]
  simp [swap₀_mul_self]

omit [CharP K 2] in
theorem swap₀_transpose : (swap₀ : Matrix (Fin 2) (Fin 2) K)ᵀ = swap₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swap₀]

theorem swapMat_symplectic :
    (swapMat : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * fromBlocks 0 1 (-1) 0 * swapMat =
      fromBlocks 0 1 (-1) 0 := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  rw [swapMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [swap₀_transpose, swap₀_mul_self]
  have h1M : (-1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1]
  exact ⟨h1M, h1M.symm⟩

@[expose] def swapSp : StatedSp 2 K :=
  ⟨⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩,
    SymplecticTorusWeyl.mem_statedSp_iff.2 swapMat_symplectic⟩

theorem spMat_swapSp : spMat (swapSp : StatedSp 2 K) = swapMat := rfl

theorem swapSp_not_mem : (swapSp : StatedSp 2 K) ∉ flagStabilizer 2 K {2} := by
  intro h
  have := mulVec_inr_eq_zero_of_mem h (x := Pi.single (Sum.inl 0) 1) (fun j => by simp) 1
  rw [spMat_swapSp, mulVec_single_one, col_apply] at this
  simp [swapMat, swap₀] at this

theorem swapSp_commute (S : Matrix.SpecialLinearGroup (Fin 2) K) :
    swapSp * SymplecticTorusWeyl.leviSp (Matrix.SpecialLinearGroup.toGL S) =
      SymplecticTorusWeyl.leviSp (Matrix.SpecialLinearGroup.toGL S) * swapSp := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  apply spMat_injective
  rw [spMat_mul, spMat_mul, spMat_swapSp, spMat_leviSp, swapMat,
    fromBlocks_multiply, fromBlocks_multiply]
  have hinv : (((Matrix.SpecialLinearGroup.toGL S)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = adjugate (S : Matrix (Fin 2) (Fin 2) K) := by
    rw [← map_inv]
    exact Matrix.SpecialLinearGroup.coe_inv S
  rw [hinv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  have hneg : ∀ x : K, -x = x := fun x => CharTwo.neg_eq x
  have ha : swap₀ * (adjugate (S : Matrix (Fin 2) (Fin 2) K))ᵀ = (S : Matrix (Fin 2) (Fin 2) K) * swap₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap₀, Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, hneg]
  have hb : swap₀ * (S : Matrix (Fin 2) (Fin 2) K) = (adjugate (S : Matrix (Fin 2) (Fin 2) K))ᵀ * swap₀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap₀, Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, hneg]
  simp only [mul_zero, zero_mul, add_zero, zero_add, ha, hb]


theorem kerA_sq {x : ↥(flagStabilizer 2 K {2})} (hx : x ∈ kerA) : x * x = 1 := by
  obtain ⟨X, hX⟩ := exists_unip x.2 (mem_kerA.1 hx)
  apply Subtype.ext
  apply spMat_injective
  show spMat (x.1 * x.1) = spMat 1
  rw [spMat_mul, hX, spMat_one, fromBlocks_multiply]
  have : X + X = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  simp [this]

theorem false_of_siegel_three {v : StatedSp 2 K}
    (hv : v ∈ CFSG.AGLEmbedding.ParabPrime.perfectJoin (SymplecticHigher.flagStabilizer 2 K {2}))
    (hv3 : v ^ 3 = 1)
    (hfix : ∀ g : StatedSp 2 K, g * v = v * g → g ∈ SymplecticHigher.flagStabilizer 2 K {2}) :
    False := by
  obtain ⟨hvJ, hdet⟩ := exists_mem_ker_of_mem_perfectJoin _ (blockDet (K := K)) hv
  set vJ : ↥(flagStabilizer 2 K {2}) := ⟨v, hvJ⟩ with hvJdef
  set A : Matrix (Fin 2) (Fin 2) K := blockA vJ with hA
  have hdetA : A.det = 1 := by
    rw [← blockDet_apply, hdet]; rfl
  have hvJ3 : vJ ^ 3 = 1 := Subtype.ext hv3
  have hA3 : A ^ 3 = 1 := by
    have := congrArg (blockA (K := K)) hvJ3
    rwa [map_pow, map_one] at this
  let S : Matrix.SpecialLinearGroup (Fin 2) K := ⟨A, hdetA⟩
  have hS3 : S ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hA3
  set ℓ : StatedSp 2 K := SymplecticTorusWeyl.leviSp (Matrix.SpecialLinearGroup.toGL S) with hℓ
  have hℓJ : ℓ ∈ flagStabilizer 2 K {2} := leviSp_mem _
  set lJ : ↥(flagStabilizer 2 K {2}) := ⟨ℓ, hℓJ⟩ with hlJ
  have hblock : blockA lJ = A := by
    rw [blockA_apply]
    show (spMat ℓ).toBlocks₁₁ = A
    rw [hℓ, spMat_leviSp, toBlocks_fromBlocks₁₁]
    rfl
  have hl3 : lJ ^ 3 = 1 := by
    apply Subtype.ext
    show ℓ ^ 3 = 1
    rw [hℓ, ← map_pow, ← map_pow, hS3, map_one, map_one]
  have hinvblock : blockA lJ⁻¹ * blockA lJ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hm : lJ⁻¹ * vJ ∈ kerA := by
    rw [mem_kerA, map_mul, ← hA, ← hblock]
    exact hinvblock
  have hlm : lJ * (lJ⁻¹ * vJ) = vJ := mul_inv_cancel_left _ _
  obtain ⟨ρ, hρ, hconjJ⟩ := exists_conj_eq_of_normal (kerA (K := K)) (fun x hx y hy => kerA_comm hx hy)
    (fun x hx => kerA_sq hx) hm hl3 (by rw [hlm]; exact hvJ3)
  rw [hlm] at hconjJ
  have hconj : ρ.1⁻¹ * v * ρ.1 = ℓ := congrArg Subtype.val hconjJ
  have hvρ : v = ρ.1 * ℓ * ρ.1⁻¹ := by
    rw [← hconj]; group
  have hc : swapSp * ℓ = ℓ * swapSp := swapSp_commute S
  have hhv : (ρ.1 * swapSp * ρ.1⁻¹) * v = v * (ρ.1 * swapSp * ρ.1⁻¹) := by
    rw [hvρ]
    calc ρ.1 * swapSp * ρ.1⁻¹ * (ρ.1 * ℓ * ρ.1⁻¹) = ρ.1 * (swapSp * ℓ) * ρ.1⁻¹ := by group
      _ = ρ.1 * (ℓ * swapSp) * ρ.1⁻¹ := by rw [hc]
      _ = ρ.1 * ℓ * ρ.1⁻¹ * (ρ.1 * swapSp * ρ.1⁻¹) := by group
  have hhJ := hfix _ hhv
  apply swapSp_not_mem (K := K)
  have : (swapSp : StatedSp 2 K) = ρ.1⁻¹ * (ρ.1 * swapSp * ρ.1⁻¹) * ρ.1 := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ρ.2) hhJ) ρ.2

end CharTwo

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.SiegelThree
