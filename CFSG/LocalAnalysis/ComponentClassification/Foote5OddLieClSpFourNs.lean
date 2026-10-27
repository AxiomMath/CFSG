module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpFourLeg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewFour
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

abbrev uZ : Fin 3 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ![fromBlocks !![1, 1; -1, 1] (-!![1, 1; 1, -1]) !![1, 1; 1, -1] !![1, 1; -1, 1],
    fromBlocks !![1, -1; 1, 1] (-!![1, 1; 1, -1]) !![1, 1; 1, -1] !![1, -1; 1, 1],
    fromBlocks !![1, 1; -1, 1] (-!![-1, 1; 1, 1]) !![-1, 1; 1, 1] !![1, 1; -1, 1]]

theorem uZ_facts :
    (∀ k, uZ k * uZ k * uZ k = 1) ∧
    (∀ k, (uZ k)ᵀ * fromBlocks 0 1 (-1) 0 * uZ k = fromBlocks 0 1 (-1) 0) ∧
    (∀ k, uZ k * skewNs 2 (ZMod 3) (-1) = skewNs 2 (ZMod 3) (-1) * uZ k) ∧
    uZ 0 * uZ 1 = skewNs 2 (ZMod 3) (-1) * fromBlocks (fourMat (ZMod 3) 0) 0 0
      (fourMat (ZMod 3) 0) ∧
    uZ 0 * uZ 2 = skewNs 2 (ZMod 3) (-1) * fromBlocks (fourMat (ZMod 3) 1) 0 0
      (fourMat (ZMod 3) 1) ∧
    uZ 0 * uZ 1 * (uZ 0 * uZ 2) = -fromBlocks (fourMat (ZMod 3) 2) 0 0 (fourMat (ZMod 3) 2) ∧
    uZ 0 * uZ 1 * (uZ 0 * uZ 1) = -1 ∧ uZ 0 * uZ 2 * (uZ 0 * uZ 2) = -1 ∧
    uZ 0 * uZ 1 * (uZ 0 * uZ 2) * (uZ 0 * uZ 1 * (uZ 0 * uZ 2)) = -1 := by
  decide

section Map

variable (φ : ZMod 3 →+* K)

theorem mapMatrix_formJ : φ.mapMatrix (fromBlocks 0 1 (-1) 0 :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) = fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

theorem mapMatrix_skewNs : φ.mapMatrix (skewNs 2 (ZMod 3) (-1)) = skewNs 2 K (-1) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

theorem mapMatrix_fourMat (k : Fin 3) :
    φ.mapMatrix (fromBlocks (fourMat (ZMod 3) k) 0 0 (fourMat (ZMod 3) k)) =
      fromBlocks (fourMat K k) 0 0 (fourMat K k) := by
  fin_cases k <;> ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp

@[expose] def uSp (k : Fin 3) : StatedSp 2 K :=
  ⟨⟨φ.mapMatrix (uZ k), φ.mapMatrix (uZ k * uZ k), by
      rw [← map_mul, ← mul_assoc, uZ_facts.1 k, map_one], by
      rw [← map_mul, uZ_facts.1 k, map_one]⟩,
    mem_statedSp_iff.2 (by
      change (φ.mapMatrix (uZ k))ᵀ * fromBlocks 0 1 (-1) 0 * φ.mapMatrix (uZ k) = _
      have ht : (φ.mapMatrix (uZ k))ᵀ = φ.mapMatrix (uZ k)ᵀ := by
        rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map]
      rw [ht, ← mapMatrix_formJ φ, ← map_mul, ← map_mul, uZ_facts.2.1 k])⟩

theorem coe_uSp (k : Fin 3) :
    (((uSp φ k : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = φ.mapMatrix (uZ k) := rfl

end Map

theorem eq_one_skewNs_three [Finite K] (h3 : Nat.card K = 3) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hd0 : d ≠ 0) {R : Subgroup (MulAut (StatedProj (StatedSp 2 K)))} (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut 2 K (skewNsGsp 2 K hd0) = conjAut 2 K (skewNsGsp 2 K hd0) * y)
    (hRc : ∀ s, conjAut 2 K (skewNsGsp 2 K hd0) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ y ∈ R, y = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hdm : d = -1 := by
    rcases three_elements h3 d with h | h | h
    · exact absurd h hd0
    · exact absurd (by rw [h, one_pow]) (hd 1)
    · exact h
  subst hdm
  have hc : Fintype.card (ZMod 3) = Fintype.card K := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, h3]
  set φ : ZMod 3 →+* K := (FiniteField.ringEquivOfCardEq hc).toRingHom with hφ
  obtain ⟨hcube, -, hcomm, h01, h02, h0102, hsq01, hsq02, hsq0102⟩ := uZ_facts
  set A₁ := skewNs 2 K (-1) with hA₁
  have hAA : A₁ * A₁ = (-1 : K) • 1 := skewNs_mul_self (-1)
  have hfix : ∀ k, conjAut 2 K (skewNsGsp 2 K hd0) (proj 2 K (uSp φ k)) = proj 2 K (uSp φ k) := by
    intro k
    rw [conjAut_proj]
    refine congrArg (proj 2 K) (mem_spCent.2 ?_)
    rw [coe_skewNsGsp, coe_uSp, ← mapMatrix_skewNs φ, ← map_mul, ← map_mul, hcomm k]
  have hodd3 : ∀ k, Odd (orderOf (proj 2 K (uSp φ k))) := by
    intro k
    refine Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow]
    have e : uSp φ k ^ 3 = 1 := statedSp_ext (by
      rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_uSp, pow_three, ← map_mul,
        ← map_mul, ← mul_assoc, hcube k, map_one]
      rfl)
    rw [e, map_one]
  have hnorm : ∀ k, ∀ y ∈ R, conjProjH (StatedSp 2 K) (uSp φ k) * y *
      (conjProjH (StatedSp 2 K) (uSp φ k))⁻¹ ∈ R :=
    fun k y hy => hRc _ (hfix k) (hodd3 k) y hy
  have hnorm₂ : ∀ k k', ∀ y ∈ R, conjProjH (StatedSp 2 K) (uSp φ k * uSp φ k') * y *
      (conjProjH (StatedSp 2 K) (uSp φ k * uSp φ k'))⁻¹ ∈ R := by
    intro k k' y hy
    have h1 := hnorm k _ (hnorm k' y hy)
    rw [map_mul]
    have e : conjProjH (StatedSp 2 K) (uSp φ k) * conjProjH (StatedSp 2 K) (uSp φ k') * y *
        (conjProjH (StatedSp 2 K) (uSp φ k) * conjProjH (StatedSp 2 K) (uSp φ k'))⁻¹ =
        conjProjH (StatedSp 2 K) (uSp φ k) * (conjProjH (StatedSp 2 K) (uSp φ k') * y *
          (conjProjH (StatedSp 2 K) (uSp φ k'))⁻¹) * (conjProjH (StatedSp 2 K) (uSp φ k))⁻¹ := by
      group
    rw [e]
    exact h1
  have hm : ∀ k k', (((uSp φ k * uSp φ k' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = φ.mapMatrix (uZ k * uZ k') := fun k k' => by
    rw [Subgroup.coe_mul, Units.val_mul, coe_uSp, coe_uSp, map_mul]
  have hm₁ : (((uSp φ 0 * uSp φ 1 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = A₁ * fromBlocks (fourMat K 0) 0 0
        (fourMat K 0) := by
    rw [hm, h01, map_mul, mapMatrix_skewNs, mapMatrix_fourMat]
  have hm₂ : (((uSp φ 0 * uSp φ 2 : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = A₁ * fromBlocks (fourMat K 1) 0 0
        (fourMat K 1) := by
    rw [hm, h02, map_mul, mapMatrix_skewNs, mapMatrix_fourMat]
  have hm₃ : (((uSp φ 0 * uSp φ 1 * (uSp φ 0 * uSp φ 2) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        -fromBlocks (fourMat K 2) 0 0 (fourMat K 2) := by
    rw [Subgroup.coe_mul, Units.val_mul, hm, hm, ← map_mul, h0102, map_neg, mapMatrix_fourMat]
  have hsqM : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3), M * M = -1 →
      φ.mapMatrix M * φ.mapMatrix M = (-1 : K) • 1 := fun M hM => by
    rw [← map_mul, hM, map_neg, map_one, neg_one_smul]
  have hcancel : ∀ D S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, D * A₁ = A₁ * D →
      D * (A₁ * S) = (A₁ * S) * D → D * S = S * D := by
    intro D S hDA hDS
    have hAi : (-A₁) * A₁ = 1 := by rw [Matrix.neg_mul, hAA, neg_smul, one_smul, neg_neg]
    calc D * S = (-A₁) * A₁ * (D * S) := by rw [hAi, Matrix.one_mul]
      _ = (-A₁) * (D * (A₁ * S)) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁ D S, ← hDA, Matrix.mul_assoc D A₁ S]
      _ = (-A₁) * ((A₁ * S) * D) := by rw [hDS]
      _ = S * D := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAi, Matrix.one_mul]
  have hAA' : ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((skewNsGsp 2 K hd0 : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (-1 : K) • 1 := hAA
  have hleg : ∀ (S : StatedSp 2 K), ((S : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((S : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (-1 : K) • 1 →
      (∀ D : gsp 2 K, ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        A₁ = A₁ * ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
        ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          ((S : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((D : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) →
        ∃ m : ℕ, conjAut 2 K (D ^ 2 ^ m) = 1) →
      ∀ x ∈ R, conjProjH (StatedSp 2 K) S * x = x * conjProjH (StatedSp 2 K) S → x = 1 :=
    fun S hSS hS x hx hc => eq_one_of_commute_leg_of_odd h3 le_rfl hd0 hAA'
      (neg_ne_zero.2 one_ne_zero) hSS hS (odd_orderOf_of_mem hRodd hx) (hRi x hx) hc.symm
  have hfpf₁ := hleg _ (by rw [hm]; exact hsqM _ hsq01) fun D hDA hDS =>
    ⟨3, conjAut_pow_eight_of_commute_skewNs h3 0 hDA (hcancel _ _ hDA (by rwa [hm₁] at hDS))⟩
  have hfpf₂ := hleg _ (by rw [hm]; exact hsqM _ hsq02) fun D hDA hDS =>
    ⟨3, conjAut_pow_eight_of_commute_skewNs h3 1 hDA (hcancel _ _ hDA (by rwa [hm₂] at hDS))⟩
  have hfpf₃ := hleg (uSp φ 0 * uSp φ 1 * (uSp φ 0 * uSp φ 2)) (by
      rw [Subgroup.coe_mul, Units.val_mul, hm, hm, ← map_mul]
      exact hsqM _ hsq0102) fun D hDA hDS =>
    ⟨3, conjAut_pow_eight_of_commute_skewNs h3 2 hDA (by
      rw [hm₃, Matrix.mul_neg, Matrix.neg_mul] at hDS
      exact neg_inj.1 hDS)⟩
  have hsq : ∀ S : StatedSp 2 K, ((S : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((S : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (-1 : K) • 1 →
      conjProjH (StatedSp 2 K) S * conjProjH (StatedSp 2 K) S = 1 := fun S hS => by
    rw [← map_mul]
    exact conjProjH_eq_one_of_smul (by norm_num) (neg_ne_zero.2 one_ne_zero)
      (by rw [Subgroup.coe_mul, Units.val_mul]; exact hS)
  have hRb : R = ⊥ := eq_bot_of_four_group
    (s₁ := conjProjH (StatedSp 2 K) (uSp φ 0 * uSp φ 1))
    (s₂ := conjProjH (StatedSp 2 K) (uSp φ 0 * uSp φ 2))
    (hsq _ (by rw [hm]; exact hsqM _ hsq01)) (hsq _ (by rw [hm]; exact hsqM _ hsq02))
    (hnorm₂ 0 1) (hnorm₂ 0 2) hfpf₁ hfpf₂ (by
      rw [← map_mul]
      exact hfpf₃)
  intro y hy
  rw [hRb] at hy
  exact mem_bot.1 hy

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
