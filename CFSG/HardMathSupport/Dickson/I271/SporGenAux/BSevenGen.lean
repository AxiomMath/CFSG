module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.BSevenGenKit
public import CFSG.Monster.Existence.BabyOrder
public import Certificates.Certificate17430

public section

namespace CFSG.HardMathSupport.Dickson.I271.BSevenGen

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
open scoped Matrix

local notation "sm" => CFSG.KC.BM.stripMat

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "SM" =>
  NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2

theorem conj_pow' {n : ℕ} {c ci g : Matrix (Fin n) (Fin n) (ZMod 2)} (h1 : c * ci = 1)
    (h2 : ci * c = 1) : ∀ k : ℕ, (ci * g * c) ^ k = ci * g ^ k * c
  | 0 => by rw [pow_zero, pow_zero, mul_one, h2]
  | k + 1 => by
    rw [pow_succ, conj_pow' h1 h2 k, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc c ci, h1, one_mul]

theorem pow_seventy {M : Type*} [Monoid M] {g y : M} (hy : y = g ^ 14) (hy5 : y ^ 5 = 1) :
    g ^ 70 = 1 := by
  have h70 : g ^ 70 = (g ^ 14) ^ 5 := pow_mul g 14 5
  rw [h70, ← hy, hy5]

theorem pow_seven_of {M : Type*} [Monoid M] {g x : M} (hx : x = g ^ 10) (hg : g ^ 70 = 1) :
    x ^ 7 = 1 := by
  have h70 : g ^ 70 = (g ^ 10) ^ 7 := pow_mul g 10 7
  rw [hx, ← h70, hg]

theorem vecMul_pow_of_fix {n : ℕ} {v : Fin n → ZMod 2} {X : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : v ᵥ* X = v) : ∀ k : ℕ, v ᵥ* X ^ k = v
  | 0 => by rw [pow_zero, Matrix.vecMul_one]
  | k + 1 => by rw [pow_succ, ← Matrix.vecMul_vecMul, vecMul_pow_of_fix h k, h]

section Elements


theorem fact17430 : CFSG.KC.BM.SevenGen.FactSevenGen := Certificates.certificate17430.1

theorem seedA1_eq : bMat bA₁ = sm CFSG.KC.BM.Seeds.A1 :=
  bMat_bA₁.trans Certificates.certificate17430.2.1

theorem seedA2_eq : bMat bA₂ = sm CFSG.KC.BM.Seeds.A2 :=
  bMat_bA₂.trans Certificates.certificate17430.2.2.1

theorem gens_mem : sm CFSG.KC.BM.Seven.g ∈ SM ∧ sm CFSG.KC.BM.SevenGen.gi ∈ SM ∧
    sm CFSG.KC.BM.SevenGen.s2 ∈ SM ∧ sm CFSG.KC.BM.SevenGen.s2i ∈ SM := by
  refine Certificates.certificate17430.2.2.2 _ ?_ ?_
  · rw [← seedA1_eq]
    exact genA₁_mem
  · rw [← seedA2_eq]
    exact genA₂_mem

theorem g_gi : sm CFSG.KC.BM.Seven.g * sm CFSG.KC.BM.SevenGen.gi = 1 := by
  obtain ⟨-, -, -, ⟨h, -⟩, -⟩ := fact17430
  exact h

theorem s2_s2i : sm CFSG.KC.BM.SevenGen.s2 * sm CFSG.KC.BM.SevenGen.s2i = 1 := by
  obtain ⟨-, -, -, ⟨-, h, -⟩, -⟩ := fact17430
  exact h

@[expose] noncomputable def sOne : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.Seven.g, gens_mem.1⟩
  inv := ⟨sm CFSG.KC.BM.SevenGen.gi, gens_mem.2.1⟩
  val_inv := Subtype.ext g_gi
  inv_val := Subtype.ext (mul_eq_one_symm g_gi)

@[expose] noncomputable def sTwo : NativeSporadic.B where
  val := ⟨sm CFSG.KC.BM.SevenGen.s2, gens_mem.2.2.1⟩
  inv := ⟨sm CFSG.KC.BM.SevenGen.s2i, gens_mem.2.2.2⟩
  val_inv := Subtype.ext s2_s2i
  inv_val := Subtype.ext (mul_eq_one_symm s2_s2i)

theorem bMat_sOne : bMat sOne = sm CFSG.KC.BM.Seven.g := rfl

theorem bMat_sOne_inv : bMat sOne⁻¹ = sm CFSG.KC.BM.SevenGen.gi := rfl

theorem bMat_sTwo : bMat sTwo = sm CFSG.KC.BM.SevenGen.s2 := rfl

theorem bMat_sTwo_inv : bMat sTwo⁻¹ = sm CFSG.KC.BM.SevenGen.s2i := rfl

theorem facts_of {s₁ s₂ : NativeSporadic.B} {G Gi S2 S2i X Y F C Ci Ap Bp H Hi A1 A2 : MatB}
    {v : Fin 4370 → ZMod 2} (hG : bMat s₁ = G) (hGi : bMat s₁⁻¹ = Gi) (hS2 : bMat s₂ = S2)
    (hS2i : bMat s₂⁻¹ = S2i) (hx : X = G ^ 10) (hy : Y = G ^ 14) (hy5 : Y ^ 5 = 1) (hx1 : X ≠ 1)
    (hcci : C * Ci = 1) (hs2 : S2 = Ci * G * C) (hf : F = Ci * X * C) (hxf : X * F = F * X)
    (hvx : v ᵥ* X = v) (hvf : v ᵥ* F ≠ v) (hap : Ap = (G ^ 2 * S2i * G * S2i * G) ^ 17)
    (hbp : Bp = (G * S2 * Gi * S2 ^ 2) ^ 13) (hHHi : H * Hi = 1) (hA1 : bMat bA₁ = A1)
    (hA2 : bMat bA₂ = A2) (hA1H : A1 * H = H * Ap) (hA2H : A2 * H = H * Bp) :
    (s₁ ^ 10) ^ 7 = 1 ∧ s₁ ^ 10 ≠ 1 ∧ (s₂ ^ 10) ^ 7 = 1 ∧
      s₁ ^ 10 * s₂ ^ 10 = s₂ ^ 10 * s₁ ^ 10 ∧ (∀ k < 7, s₂ ^ 10 ≠ (s₁ ^ 10) ^ k) ∧
      Subgroup.closure ({s₁, s₂} : Set NativeSporadic.B) = ⊤ := by
  have hcic : Ci * C = 1 := mul_eq_one_symm hcci
  have hx7 : X ^ 7 = 1 := pow_seven_of hx (pow_seventy hy hy5)
  have e1 : bMat (s₁ ^ 10) = X := by rw [map_pow, hG, hx]
  have e2 : bMat (s₂ ^ 10) = F := by rw [map_pow, hS2, hs2, conj_pow' hcci hcic, ← hx, hf]
  refine ⟨bMat_injective ?_, fun h => hx1 ?_, bMat_injective ?_, bMat_injective ?_,
    fun k _ h => hvf ?_, ?_⟩
  · rw [map_pow, e1, map_one]
    exact hx7
  · rw [← e1, h, map_one]
  · rw [map_pow, e2, map_one, hf, conj_pow' hcci hcic, hx7, Matrix.mul_one, hcic]
  · rw [map_mul, map_mul, e1, e2]
    exact hxf
  · rw [← e2, h, map_pow, e1]
    exact vecMul_pow_of_fix hvx k
  · have h1 : s₁ ∈ Subgroup.closure ({s₁, s₂} : Set NativeSporadic.B) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have h2 : s₂ ∈ Subgroup.closure ({s₁, s₂} : Set NativeSporadic.B) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have ea : bMat ((s₁ ^ 2 * s₂⁻¹ * s₁ * s₂⁻¹ * s₁) ^ 17) = Ap := by
      rw [hap, map_pow, map_mul, map_mul, map_mul, map_mul, map_pow, hG, hS2i]
    have eb : bMat ((s₁ * s₂ * s₁⁻¹ * s₂ ^ 2) ^ 13) = Bp := by
      rw [hbp, map_pow, map_mul, map_mul, map_mul, map_pow, hG, hS2, hGi]
    refine eq_top_of_intertwiner
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 2) (Subgroup.inv_mem _ h2)) h1)
        (Subgroup.inv_mem _ h2)) h1) 17)
      (Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2)
        (Subgroup.inv_mem _ h1)) (Subgroup.pow_mem _ h2 2)) 13) hHHi ?_ ?_
    · rw [hA1, ea]
      exact hA1H
    · rw [hA2, eb]
      exact hA2H

theorem bSevenGen_facts :
    (sOne ^ 10) ^ 7 = 1 ∧ sOne ^ 10 ≠ 1 ∧ (sTwo ^ 10) ^ 7 = 1 ∧
      sOne ^ 10 * sTwo ^ 10 = sTwo ^ 10 * sOne ^ 10 ∧ (∀ k < 7, sTwo ^ 10 ≠ (sOne ^ 10) ^ k) ∧
      Subgroup.closure ({sOne, sTwo} : Set NativeSporadic.B) = ⊤ := by
  obtain ⟨⟨hx, hy, hy5, hx1⟩, ⟨hcci, hs2, hf, hxf⟩, ⟨hvx, hvf⟩, ⟨-, -, hap, hbp⟩, hHHi, hA1H,
    hA2H⟩ := fact17430
  exact facts_of bMat_sOne bMat_sOne_inv bMat_sTwo bMat_sTwo_inv hx hy hy5 hx1 hcci hs2 hf hxf
    hvx hvf hap hbp hHHi seedA1_eq seedA2_eq hA1H hA2H

end Elements

section Pair


theorem card_B_factorization_seven : (Nat.card NativeSporadic.B).factorization 7 = 2 := by
  rw [CFSG.Monster.Existence.card_nativeB,
    show CFSG.Open.monsterBabyOrder = 7 ^ 2 * 84791458800539310024032256000000 by decide,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem centGen_B_seven : CentGen 7 NativeSporadic.B := by
  haveI : Finite NativeSporadic.B := finite_B
  obtain ⟨he, he1, hf, hef, hfe, htop⟩ := bSevenGen_facts
  exact centGen_of_data Nat.prime_seven card_B_factorization_seven htop he hf hef he1 hfe
    (Commute.self_pow sOne 10).eq (Commute.self_pow sTwo 10).eq
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem sporPair_B_seven
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers)
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) : SporPair .B 7 :=
  haveI : Finite NativeSporadic.B := finite_B
  sporPair_seven_of_model (M := NativeSporadic.B) hSpM hOut hBr (MulEquiv.refl _)
    card_B_factorization_seven centGen_B_seven

end Pair

end CFSG.HardMathSupport.Dickson.I271.BSevenGen
