module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166F2Blocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamA8Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.Open CFSG.RankThree.PartTwo.Census CFSG.Assembly.LowTwoRank
open scoped commutatorElement

local notation "𝔽₂" => ZMod 2

namespace SLNineTwo

open F2Block

private abbrev SIdx := Fin 2 ⊕ (Fin 2 ⊕ Fin 2)

private def sVecW (v : SIdx → 𝔽₂) : W7 → 𝔽₂
  | Sum.inl i => v (Sum.inl i)
  | Sum.inr (Sum.inl i) => v (Sum.inr (Sum.inl i))
  | Sum.inr (Sum.inr (Sum.inl i)) => v (Sum.inr (Sum.inr i))
  | Sum.inr (Sum.inr (Sum.inr _)) => 0

private def sPhiW : W7 → 𝔽₂
  | Sum.inr (Sum.inr (Sum.inr _)) => 1
  | _ => 0

private def sEmb : SIdx → W7
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr i) => Sum.inr (Sum.inr (Sum.inl i))

private theorem sVecW_add (v w : SIdx → 𝔽₂) : sVecW (v + w) = sVecW v + sVecW w := by
  funext i
  rcases i with a | a | a | a
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sVecW_zero : sVecW (0 : SIdx → 𝔽₂) = 0 := by
  funext i
  rcases i with a | a | a | a <;> rfl

private theorem sEmb_sVecW (v : SIdx → 𝔽₂) (i : SIdx) : sVecW v (sEmb i) = v i := by
  rcases i with a | a | a <;> rfl

private theorem sPhiW_dot_sVecW (v : SIdx → 𝔽₂) : sPhiW ⬝ᵥ sVecW v = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with a | a | a | a <;> simp [sPhiW, sVecW]

private def sNW (v : SIdx → 𝔽₂) : Matrix W7 W7 𝔽₂ :=
  Matrix.vecMulVec (sVecW v) sPhiW

private theorem sNW_add (v w : SIdx → 𝔽₂) : sNW (v + w) = sNW v + sNW w := by
  rw [sNW, sNW, sNW, sVecW_add]
  ext i j
  simp [Matrix.vecMulVec, Pi.add_apply, add_mul]

private theorem sNW_mul (v w : SIdx → 𝔽₂) : sNW v * sNW w = 0 := by
  rw [sNW, sNW, Matrix.vecMulVec_mul_vecMulVec, sPhiW_dot_sVecW, zero_smul,
    Matrix.vecMulVec_zero]

private def sMatW (v : SIdx → 𝔽₂) : Matrix W7 W7 𝔽₂ :=
  1 + sNW v

private theorem sMatW_add (v w : SIdx → 𝔽₂) : sMatW (v + w) = sMatW v * sMatW w := by
  rw [sMatW, sMatW, sMatW, sNW_add, add_mul, mul_add, mul_add, one_mul, mul_one,
    one_mul, sNW_mul]
  abel

private theorem sMatW_zero : sMatW (0 : SIdx → 𝔽₂) = 1 := by
  rw [sMatW, sNW, sVecW_zero]
  ext i j
  simp [Matrix.vecMulVec]

private theorem sMatW_mul_self (v : SIdx → 𝔽₂) : sMatW v * sMatW v = 1 := by
  rw [← sMatW_add]
  have hv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  rw [hv, sMatW_zero]

private theorem det_sMatW (v : SIdx → 𝔽₂) : (sMatW v).det = 1 := by
  have hself : sMatW v * sMatW v = 1 := sMatW_mul_self v
  have hdet : (sMatW v).det * (sMatW v).det = 1 := by
    rw [← Matrix.det_mul, hself, Matrix.det_one]
  have h2 : ∀ x : 𝔽₂, x = 0 ∨ x = 1 := by decide
  rcases h2 (sMatW v).det with h | h <;> simp_all

private def sHomW : Multiplicative (SIdx → 𝔽₂) →* Matrix.SpecialLinearGroup W7 𝔽₂ where
  toFun v := ⟨sMatW v.toAdd, det_sMatW v.toAdd⟩
  map_one' := by
    apply Subtype.ext
    change sMatW 0 = 1
    rw [sMatW_zero]
  map_mul' v w := by
    apply Subtype.ext
    change sMatW (v.toAdd + w.toAdd) = sMatW v.toAdd * sMatW w.toAdd
    rw [sMatW_add]

def SJW : Subgroup (Matrix.SpecialLinearGroup W7 𝔽₂) := sHomW.range

private theorem sHomW_injective : Function.Injective sHomW := by
  intro v w hvw
  have hmat : sMatW v.toAdd = sMatW w.toAdd := congrArg Subtype.val hvw
  have hN : sNW v.toAdd = sNW w.toAdd := by
    have h1 : sMatW v.toAdd - 1 = sMatW w.toAdd - 1 := by rw [hmat]
    simpa [sMatW] using h1
  have hveq : v.toAdd = w.toAdd := by
    funext i
    have h := congrFun (congrFun hN (sEmb i)) (Sum.inr (Sum.inr (Sum.inr (0 : Fin 1))))
    simpa [sNW, Matrix.vecMulVec_apply, sPhiW, sEmb_sVecW] using h
  exact Multiplicative.toAdd.injective hveq

private theorem card_SJW : Nat.card SJW = 2 ^ 6 := by
  rw [SJW, ← Nat.card_congr (MonoidHom.ofInjective sHomW_injective).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem pow_three_multiplicative_pi3 (u : Multiplicative (Fin 3 → ZMod 3)) : u ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext k
  show (3 : ℕ) • u.toAdd k = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem bHomW_injective : Function.Injective bHomW := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  have h1 : bMatW a.toAdd = bMatW b.toAdd := congrArg Subtype.val hab
  have hk : ∀ k : Fin 3, a.toAdd k = b.toAdd k := by
    intro k
    apply threeCycleMat_pow_val_injective
    fin_cases k
    · ext i j
      have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl j)
      simpa [bMatW, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inl j))
      simpa [bMatW, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
    · ext i j
      have := congrFun (congrFun h1 (Sum.inr (Sum.inr (Sum.inl i))))
        (Sum.inr (Sum.inr (Sum.inl j)))
      simpa [bMatW, fromBlocks_apply₂₂, fromBlocks_apply₁₁] using this
  exact funext hk

def BJW : Subgroup (Matrix.SpecialLinearGroup W7 𝔽₂) := bHomW.range

theorem isElemAbelian_BJW : IsElemAbelian 3 BJW :=
  isElemAbelian_range (p := 3) pow_three_multiplicative_pi3 bHomW

theorem card_BJW : Nat.card BJW = 3 ^ 3 := by
  rw [BJW, ← Nat.card_congr (MonoidHom.ofInjective bHomW_injective).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

@[expose] def extend23 (a : Fin 2 → ZMod 3) : Fin 3 → ZMod 3 :=
  fun i => if i = 0 then a 0 else if i = 1 then a 1 else 0

private theorem extend23_add (a b : Fin 2 → ZMod 3) : extend23 (a + b) = extend23 a + extend23 b := by
  funext i
  fin_cases i <;> simp [extend23]

@[expose] def eHom23 : Multiplicative (Fin 2 → ZMod 3) →* Multiplicative (Fin 3 → ZMod 3) where
  toFun a := Multiplicative.ofAdd (extend23 a.toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp [extend23]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change extend23 (a.toAdd + b.toAdd) = extend23 a.toAdd + extend23 b.toAdd
    exact extend23_add _ _

private theorem eHom23_injective : Function.Injective eHom23 := by
  intro a b hab
  have h : extend23 a.toAdd = extend23 b.toAdd := Multiplicative.toAdd.injective hab
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · have := congrFun h 0
    simpa [extend23] using this
  · have := congrFun h 1
    simpa [extend23] using this

@[expose] def EJW : Subgroup (Matrix.SpecialLinearGroup W7 𝔽₂) := (bHomW.comp eHom23).range

theorem EJW_le_BJW : EJW ≤ BJW := by
  rintro _ ⟨a, rfl⟩
  exact ⟨eHom23 a, rfl⟩

theorem card_EJW : Nat.card EJW = 3 ^ 2 := by
  have hinj : Function.Injective (bHomW.comp eHom23) := bHomW_injective.comp eHom23_injective
  rw [EJW, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  simp [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem isPGroup_two_SJW : IsPGroup 2 SJW :=
  IsPGroup.of_card (n := 6) (by rw [card_SJW])

private def V5idx : W7 := Sum.inr (Sum.inr (Sum.inr (0 : Fin 1)))

private theorem sPhiW_eq_single : sPhiW = Pi.single V5idx (1 : 𝔽₂) := by
  funext i
  rcases i with a | a | a | a
  · simp [sPhiW, V5idx, Pi.single_apply]
  · simp [sPhiW, V5idx, Pi.single_apply]
  · simp [sPhiW, V5idx, Pi.single_apply]
  · fin_cases a
    simp [sPhiW, V5idx, Pi.single_apply]

private theorem bMatW_V5 (a : Fin 3 → ZMod 3) (j : W7) : bMatW a V5idx j = sPhiW j := by
  rcases j with i | i | i | i
  · simp [bMatW, V5idx, sPhiW, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  · simp [bMatW, V5idx, sPhiW, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  · simp [bMatW, V5idx, sPhiW, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂]
  · fin_cases i
    simp [bMatW, V5idx, sPhiW, Matrix.one_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂]

private theorem sPhiW_mul_bMatW_inv (a : Fin 3 → ZMod 3) :
    sPhiW ᵥ* bMatW (-a) = sPhiW := by
  funext j
  rw [sPhiW_eq_single, Matrix.vecMul, single_dotProduct, bMatW_V5, one_mul, sPhiW_eq_single]

private def actVec (a : Fin 3 → ZMod 3) (v : SIdx → 𝔽₂) : SIdx → 𝔽₂ :=
  fun i => (bMatW a *ᵥ sVecW v) (sEmb i)

private theorem bMatW_mulVec_sVecW (a : Fin 3 → ZMod 3) (v : SIdx → 𝔽₂) :
    bMatW a *ᵥ sVecW v = sVecW (actVec a v) := by
  funext j
  rcases j with i | i | i | i
  · rfl
  · rfl
  · rfl
  · have h0 : (bMatW a *ᵥ sVecW v) V5idx = 0 := by
      have h : (bMatW a *ᵥ sVecW v) V5idx = sPhiW ⬝ᵥ sVecW v := by
        simp [Matrix.mulVec, dotProduct, bMatW_V5]
      rw [h, sPhiW_dot_sVecW]
    fin_cases i
    simpa [sVecW, V5idx] using h0

private theorem bHomW_inv_eq (a : Fin 3 → ZMod 3) :
    (bHomW (Multiplicative.ofAdd a))⁻¹ = bHomW (Multiplicative.ofAdd (-a)) := by
  have h : (Multiplicative.ofAdd a)⁻¹ = Multiplicative.ofAdd (-a) := by
    apply Multiplicative.toAdd.injective
    simp
  rw [← MonoidHom.map_inv, h]

private theorem conj_of_mul_eq_one (A B : Matrix W7 W7 𝔽₂) (hAB : A * B = 1)
    (u v : W7 → 𝔽₂) :
    A * (1 + Matrix.vecMulVec u v) * B =
      1 + Matrix.vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAB]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]

private theorem bMatW_add (a b : Fin 3 → ZMod 3) : bMatW (a + b) = bMatW a * bMatW b := by
  have h : bHomW (Multiplicative.ofAdd (a + b)) =
      bHomW (Multiplicative.ofAdd a) * bHomW (Multiplicative.ofAdd b) := by
    rw [ofAdd_add, map_mul]
  exact congrArg Subtype.val h

private theorem bMatW_mul_bMatW_neg (a : Fin 3 → ZMod 3) :
    bMatW a * bMatW (-a) = 1 := by
  rw [← bMatW_add, add_neg_cancel]
  simp [bMatW]

private theorem bMatW_conj_sMatW (a : Fin 3 → ZMod 3) (v : SIdx → 𝔽₂) :
    bMatW a * sMatW v * bMatW (-a) = sMatW (actVec a v) := by
  rw [show sMatW v = 1 + Matrix.vecMulVec (sVecW v) sPhiW from rfl]
  rw [show sMatW (actVec a v) = 1 + Matrix.vecMulVec (sVecW (actVec a v)) sPhiW from rfl]
  rw [conj_of_mul_eq_one (bMatW a) (bMatW (-a)) (bMatW_mul_bMatW_neg a),
    bMatW_mulVec_sVecW, sPhiW_mul_bMatW_inv]

private theorem bHomW_conj_sHomW (a : Fin 3 → ZMod 3) (v : SIdx → 𝔽₂) :
    bHomW (Multiplicative.ofAdd a) * sHomW (Multiplicative.ofAdd v) *
        (bHomW (Multiplicative.ofAdd a))⁻¹ =
      sHomW (Multiplicative.ofAdd (actVec a v)) := by
  apply Subtype.ext
  rw [bHomW_inv_eq]
  exact bMatW_conj_sMatW a v

theorem BJW_le_normalizer_SJW : BJW ≤ Subgroup.normalizer (SJW : Set _) := by
  refine CFSG.subgroup_le_normalizer_of_conj_mem SJW BJW ?_
  rintro ⟨b, hb⟩ h hh
  obtain ⟨a, rfl⟩ := hb
  obtain ⟨v, rfl⟩ := hh
  refine ⟨Multiplicative.ofAdd (actVec a.toAdd v.toAdd), ?_⟩
  simpa only [ofAdd_toAdd] using (bHomW_conj_sHomW a.toAdd v.toAdd).symm

theorem BJW_inf_centralizer_SJW_eq_bot :
    BJW ⊓ Subgroup.centralizer (SJW : Set _) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro b ⟨hbB, hbC⟩
  obtain ⟨a, rfl⟩ := hbB
  have hact : ∀ v : SIdx → 𝔽₂, actVec a.toAdd v = v := by
    intro v
    have hcomm : bHomW (Multiplicative.ofAdd a.toAdd) * sHomW (Multiplicative.ofAdd v) =
        sHomW (Multiplicative.ofAdd v) * bHomW (Multiplicative.ofAdd a.toAdd) := by
      have h := Subgroup.mem_centralizer_iff.1 hbC _ ⟨Multiplicative.ofAdd v, rfl⟩
      simpa only [ofAdd_toAdd] using h.symm
    have hconj : bHomW (Multiplicative.ofAdd a.toAdd) * sHomW (Multiplicative.ofAdd v) *
        (bHomW (Multiplicative.ofAdd a.toAdd))⁻¹ = sHomW (Multiplicative.ofAdd v) := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [bHomW_conj_sHomW] at hconj
    exact Multiplicative.toAdd.injective (sHomW_injective hconj)
  have h0 : a.toAdd 0 = 0 := by
    have h := congrFun (hact (Pi.single (Sum.inl (1 : Fin 2) : SIdx) 1))
      (Sum.inl (0 : Fin 2) : SIdx)
    have h01 : (cMat ^ (a.toAdd 0).val) 0 1 = 0 := by
      simpa [actVec, sVecW, sEmb, bMatW, Matrix.mulVec, dotProduct, Pi.single_apply,
        fromBlocks_apply₁₁] using h
    exact threeCycleMat_pow_val_zero_one h01
  have h1 : a.toAdd 1 = 0 := by
    have h := congrFun (hact (Pi.single (Sum.inr (Sum.inl (1 : Fin 2)) : SIdx) 1))
      (Sum.inr (Sum.inl (0 : Fin 2)) : SIdx)
    have h01 : (cMat ^ (a.toAdd 1).val) 0 1 = 0 := by
      simpa [actVec, sVecW, sEmb, bMatW, Matrix.mulVec, dotProduct, Pi.single_apply,
        fromBlocks_apply₂₂, fromBlocks_apply₁₁] using h
    exact threeCycleMat_pow_val_zero_one h01
  have h2 : a.toAdd 2 = 0 := by
    have h := congrFun (hact (Pi.single (Sum.inr (Sum.inr (1 : Fin 2)) : SIdx) 1))
      (Sum.inr (Sum.inr (0 : Fin 2)) : SIdx)
    have h01 : (cMat ^ (a.toAdd 2).val) 0 1 = 0 := by
      simpa [actVec, sVecW, sEmb, bMatW, Matrix.mulVec, dotProduct, Pi.single_apply,
        fromBlocks_apply₂₂, fromBlocks_apply₁₁] using h
    exact threeCycleMat_pow_val_zero_one h01
  have ha : a.toAdd = 0 := by
    funext k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  have : a = 1 := Multiplicative.toAdd.injective ha
  rw [this, map_one]
  exact Subgroup.one_mem _

end SLNineTwo

end CFSG.LocalAnalysis.GLTheoremA.Y10F
