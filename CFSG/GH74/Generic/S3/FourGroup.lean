module

public import CFSG.GH74.Generic.S3.Prop21Leaves
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.GH74.Generic.S3

open Subgroup
open scoped MatrixGroups Matrix

@[expose] def CycFour (X : Type*) [Group X] : Prop :=
  ∀ a b : X, a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b →
    ∃ g : X, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a

theorem CycFour.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : CycFour X) :
    CycFour Y := by
  intro a b ha hb hab ha1 hb1 hne
  have hX : e.symm a * e.symm a = 1 := by rw [← map_mul, ha, map_one]
  have hY : e.symm b * e.symm b = 1 := by rw [← map_mul, hb, map_one]
  have hXY : e.symm a * e.symm b = e.symm b * e.symm a := by rw [← map_mul, ← map_mul, hab]
  obtain ⟨g, hg1, hg2⟩ := h (e.symm a) (e.symm b) hX hY hXY
    (fun h' => ha1 (by simpa using congrArg e h'))
    (fun h' => hb1 (by simpa using congrArg e h'))
    (fun h' => hne (by simpa using congrArg e h'))
  refine ⟨e g, ?_, ?_⟩
  · have := congrArg e hg1
    simpa using this
  · have := congrArg e hg2
    simpa using this

theorem exists_involution_lift_of_central_cube {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hcen : ∀ z ∈ π.ker, z ∈ center X)
    (hcube : ∀ z ∈ π.ker, z ^ 3 = 1) {y : Y} (hy : y * y = 1) :
    ∃ x : X, x * x = 1 ∧ π x = y := by
  obtain ⟨x₀, rfl⟩ := hπ y
  have hz : x₀ * x₀ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul]; exact hy
  set z := x₀ * x₀ with hzdef
  have hw : z ^ 2 ∈ π.ker := (π.ker).pow_mem hz 2
  have hwc : (z ^ 2)⁻¹ ∈ center X := (center X).inv_mem (hcen _ hw)
  set W := (z ^ 2)⁻¹ with hW
  have hc : x₀ * W = W * x₀ := mem_center_iff.mp hwc x₀
  have h3 : z ^ 3 = 1 := hcube z hz
  have hWW : W * W = z⁻¹ := by
    rw [hW, ← mul_inv_rev, ← pow_add]
    have : z ^ (2 + 2) = z := by
      calc z ^ (2 + 2) = z ^ 3 * z := by rw [← pow_succ]
        _ = z := by rw [h3, one_mul]
    rw [this]
  refine ⟨x₀ * W, ?_, ?_⟩
  · calc x₀ * W * (x₀ * W) = x₀ * (W * x₀) * W := by simp only [mul_assoc]
      _ = x₀ * (x₀ * W) * W := by rw [hc]
      _ = (x₀ * x₀) * (W * W) := by simp only [mul_assoc]
      _ = 1 := by rw [hWW, ← hzdef, mul_inv_cancel]
  · have : π W = 1 := by
      rw [hW, map_inv, map_pow, MonoidHom.mem_ker.mp hz, one_pow, inv_one]
    rw [map_mul, this, mul_one]

theorem CycFour.of_central_cube {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hcen : ∀ z ∈ π.ker, z ∈ center X)
    (hcube : ∀ z ∈ π.ker, z ^ 3 = 1) (hX : CycFour X) : CycFour Y := by
  intro a b ha hb hab ha1 hb1 hne
  obtain ⟨a', ha'2, rfl⟩ := exists_involution_lift_of_central_cube π hπ hcen hcube ha
  obtain ⟨b', hb'2, rfl⟩ := exists_involution_lift_of_central_cube π hπ hcen hcube hb
  have ha3 : ∀ x, a' * (a' * x) = x := fun x => by rw [← mul_assoc, ha'2, one_mul]
  have hb3 : ∀ x, b' * (b' * x) = x := fun x => by rw [← mul_assoc, hb'2, one_mul]
  have hu : (a' * b') * (a' * b') ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul]
    calc π a' * π b' * (π a' * π b') = π a' * (π b' * π a') * π b' := by simp only [mul_assoc]
      _ = π a' * (π a' * π b') * π b' := by rw [hab]
      _ = (π a' * π a') * (π b' * π b') := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have hcomm : a' * b' = b' * a' := by
    set u := (a' * b') * (a' * b') with hudef
    have hucen : a' * u = u * a' := mem_center_iff.mp (hcen u hu) a'
    have h1 : u = b' * a' * b' * a' := by
      calc u = u * (a' * a') := by rw [ha'2, mul_one]
        _ = a' * u * a' := by rw [← mul_assoc, ← hucen]
        _ = b' * a' * b' * a' := by rw [hudef]; simp only [mul_assoc, ha3]
    have huu : u * u = 1 := by
      calc u * u = u * (b' * a' * b' * a') := by rw [← h1]
        _ = 1 := by rw [hudef]; simp only [mul_assoc, ha3, hb3, ha'2]
    have hu3 := hcube u hu
    have hu1 : u = 1 := by
      calc u = u * (u * u) := by rw [huu, mul_one]
        _ = u ^ 3 := by rw [pow_three]
        _ = 1 := hu3
    have h4 : a' * b' = (a' * b')⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hudef]; exact hu1
    rw [h4, mul_inv_rev, inv_eq_of_mul_eq_one_right ha'2, inv_eq_of_mul_eq_one_right hb'2]
  have ha1' : a' ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hb1' : b' ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hne' : a' ≠ b' := fun h => hne (by rw [h])
  obtain ⟨g, hg1, hg2⟩ := hX a' b' ha'2 hb'2 hcomm ha1' hb1' hne'
  refine ⟨π g, ?_, ?_⟩
  · have := congrArg π hg1
    simpa using this
  · have := congrArg π hg2
    simpa using this

theorem CycFour.of_surjective_central {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hcen : ∀ z ∈ π.ker, z ∈ center X)
    (hinv : ∀ z ∈ π.ker, z * z = 1 → z = 1) (hY : CycFour Y) : CycFour X := by
  have key : ∀ (t s : X), t * t = 1 → s * s = 1 → π t = π s → t = s := by
    intro t s ht hs hts
    have hz : t * s⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hts, mul_inv_cancel]
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    set z := t * s⁻¹ with hzdef
    have hcomm : s * z = z * s := mem_center_iff.mp (hcen _ hz) s
    have hzs : z * s = t := by rw [hzdef, inv_mul_cancel_right]
    have hzz : z * z = 1 := by
      calc z * z = z * z * (s * s) := by rw [hs, mul_one]
        _ = z * (z * s) * s := by simp only [mul_assoc]
        _ = z * (s * z) * s := by rw [hcomm]
        _ = (z * s) * (z * s) := by simp only [mul_assoc]
        _ = t * t := by rw [hzs]
        _ = 1 := ht
    have h1 := hinv z hz hzz
    rw [hzdef, hs'] at h1
    exact mul_inv_eq_one.mp (by rw [hs']; exact h1)
  intro a b ha hb hab ha1 hb1 hne
  have ha3 : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hπa : π a ≠ 1 := fun h => ha1 (hinv a (MonoidHom.mem_ker.mpr h) ha)
  have hπb : π b ≠ 1 := fun h => hb1 (hinv b (MonoidHom.mem_ker.mpr h) hb)
  have hsq : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by simp only [ha3, hb]
  have hπab : π a ≠ π b := by
    intro h
    apply hne
    have hmem : a * b ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, ← h, ← map_mul, ha, map_one]
    have h1 := hinv _ hmem hsq
    calc a = a * (b * b) := by rw [hb, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h1, one_mul]
  obtain ⟨gb, hg1, hg2⟩ := hY (π a) (π b) (by rw [← map_mul, ha, map_one])
    (by rw [← map_mul, hb, map_one]) (by rw [← map_mul, ← map_mul, hab]) hπa hπb hπab
  obtain ⟨g, rfl⟩ := hπ gb
  have hconj : ∀ x : X, x * x = 1 → (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := fun x hx => by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx]; group
  refine ⟨g, key _ _ (hconj a ha) hsq ?_, key _ _ (hconj b hb) ha ?_⟩
  · simpa using hg1
  · simpa using hg2

theorem exists_cyc_of_frame {X M : Type*} [Group X] [Monoid M] (m : X →* M)
    (hm : Function.Injective m) {a b g c : X} {D₁ D₂ : M}
    (h1 : m a * m g = m g * D₁) (h2 : m b * m g = m g * D₂)
    (hc1 : m c * D₁ = D₁ * D₂ * m c) (hc2 : m c * D₂ = D₁ * m c) :
    ∃ h : X, h * a * h⁻¹ = a * b ∧ h * b * h⁻¹ = a := by
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : X, a₁ = g⁻¹ * a * g := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁⟩ : ∃ b₁ : X, b₁ = g⁻¹ * b * g := ⟨_, rfl⟩
  have e1 : m a₁ = D₁ := by
    calc m a₁ = m g⁻¹ * (m a * m g) := by rw [ha₁]; simp only [map_mul, mul_assoc]
      _ = m g⁻¹ * (m g * D₁) := by rw [h1]
      _ = D₁ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have e2 : m b₁ = D₂ := by
    calc m b₁ = m g⁻¹ * (m b * m g) := by rw [hb₁]; simp only [map_mul, mul_assoc]
      _ = m g⁻¹ * (m g * D₂) := by rw [h2]
      _ = D₂ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have ca : c * a₁ = a₁ * b₁ * c := by
    apply hm
    rw [map_mul, map_mul, map_mul, e1, e2]
    exact hc1
  have cb : c * b₁ = a₁ * c := by
    apply hm
    rw [map_mul, map_mul, e1, e2]
    exact hc2
  refine ⟨g * c * g⁻¹, ?_, ?_⟩
  · have hA : (g * c * g⁻¹) * a = a * b * (g * c * g⁻¹) := by
      calc (g * c * g⁻¹) * a = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * (c * a₁) * g⁻¹ := by rw [← ha₁]
        _ = g * (a₁ * b₁ * c) * g⁻¹ := by rw [ca]
        _ = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g) * c) * g⁻¹ := by rw [ha₁, hb₁]
        _ = a * b * (g * c * g⁻¹) := by group
    exact mul_inv_eq_iff_eq_mul.mpr hA
  · have hB : (g * c * g⁻¹) * b = a * (g * c * g⁻¹) := by
      calc (g * c * g⁻¹) * b = g * (c * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * (c * b₁) * g⁻¹ := by rw [← hb₁]
        _ = g * (a₁ * c) * g⁻¹ := by rw [cb]
        _ = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by rw [ha₁]
        _ = a * (g * c * g⁻¹) := by group
    exact mul_inv_eq_iff_eq_mul.mpr hB

section Linear

variable {K : Type} [Field K]

@[expose] def cycMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem negBlock_three_zero : CFSG.ClassicalInvolution.Models.negBlock K 3 0 =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [CFSG.ClassicalInvolution.Models.negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem negBlock_three_one : CFSG.ClassicalInvolution.Models.negBlock K 3 1 =
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  rw [CFSG.ClassicalInvolution.Models.negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem cycMat_mul_negBlock_zero : cycMat K * CFSG.ClassicalInvolution.Models.negBlock K 3 0 =
    CFSG.ClassicalInvolution.Models.negBlock K 3 0 * CFSG.ClassicalInvolution.Models.negBlock K 3 1 *
      cycMat K := by
  rw [negBlock_three_zero, negBlock_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycMat_mul_negBlock_one : cycMat K * CFSG.ClassicalInvolution.Models.negBlock K 3 1 =
    CFSG.ClassicalInvolution.Models.negBlock K 3 0 * cycMat K := by
  rw [negBlock_three_zero, negBlock_three_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycMat_mul_transpose : cycMat K * (cycMat K)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem transpose_cycMat_mul : (cycMat K)ᵀ * cycMat K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_cycMat : (cycMat K).det = 1 := by
  simp [cycMat, Matrix.det_fin_three]

@[expose] def slCoe (K : Type) [Field K] : SL(3, K) →* Matrix (Fin 3) (Fin 3) K where
  toFun g := g
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' g h := Matrix.SpecialLinearGroup.coe_mul g h

theorem slCoe_injective : Function.Injective (slCoe K) := fun _ _ h => Subtype.ext h

theorem cycFour_sl3 (h2 : (2 : K) ≠ 0) : CycFour SL(3, K) := by
  intro a b ha hb hab ha1 hb1 hne
  have hA : (a : Matrix (Fin 3) (Fin 3) K) * a = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ha, Matrix.SpecialLinearGroup.coe_one]
  have hB : (b : Matrix (Fin 3) (Fin 3) K) * b = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hb, Matrix.SpecialLinearGroup.coe_one]
  have hc : (a : Matrix (Fin 3) (Fin 3) K) * b = b * a := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hab]
  have hd₁ := CFSG.GH74.GLS.LU.finrank_eigSpace_neg_one_eq_two h2 ha ha1
  have hd₂ := CFSG.GH74.GLS.LU.finrank_eigSpace_neg_one_eq_two h2 hb hb1
  have hne' : (a : Matrix (Fin 3) (Fin 3) K) ≠ b := fun h => hne (Subtype.ext h)
  rcases CFSG.ClassicalInvolution.Models.inf_eq_bot_or_exists_frame h2 (le_refl 3) hA hB hc hd₁ hd₂
    hne' with hV | ⟨P, hP1, hP2⟩
  · exfalso
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (CFSG.ClassicalInvolution.Models.eigSpace (a : Matrix (Fin 3) (Fin 3) K) (-1))
      (CFSG.ClassicalInvolution.Models.eigSpace (b : Matrix (Fin 3) (Fin 3) K) (-1))
    rw [hV, finrank_bot, hd₁, hd₂] at hsum
    have : Module.finrank K ↥(CFSG.ClassicalInvolution.Models.eigSpace
        (a : Matrix (Fin 3) (Fin 3) K) (-1) ⊔
        CFSG.ClassicalInvolution.Models.eigSpace (b : Matrix (Fin 3) (Fin 3) K) (-1)) ≤ 3 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  · exact exists_cyc_of_frame (slCoe K) slCoe_injective (g := P)
      (c := (⟨cycMat K, det_cycMat⟩ : SL(3, K))) (D₁ := CFSG.ClassicalInvolution.Models.negBlock K 3 0)
      (D₂ := CFSG.ClassicalInvolution.Models.negBlock K 3 1) hP1 hP2 cycMat_mul_negBlock_zero
      cycMat_mul_negBlock_one

end Linear

section Unitary

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def suCoe (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] :
    Su K p f 3 →* Matrix (Fin 3) (Fin 3) K where
  toFun := suMat
  map_one' := suMat_one
  map_mul' := suMat_mul

@[expose] def cycGL (K : Type) [Field K] : GL (Fin 3) K :=
  ⟨cycMat K, (cycMat K)ᵀ, cycMat_mul_transpose, transpose_cycMat_mul⟩

theorem cycGL_mem : cycGL K ∈ SUid (unitaryInvolution K p f) 3 := by
  rw [mem_SUid]
  refine ⟨det_cycMat, ?_⟩
  show conjTr (unitaryInvolution K p f) (cycMat K) * cycMat K = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycFour_su3 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) : CycFour (Su K p f 3) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  intro a b ha hb hab ha1 hb1 hne
  have hA : suMat a * suMat a = 1 := by rw [← suMat_mul, ha, suMat_one]
  have hB : suMat b * suMat b = 1 := by rw [← suMat_mul, hb, suMat_one]
  have hc : suMat a * suMat b = suMat b * suMat a := by
    rw [← suMat_mul, ← suMat_mul, hab]
  have hd₁ : Module.finrank K (eigSpace (suMat a) (-1)) = 2 :=
    CFSG.GH74.GLS.LU.finrank_eigSpace_neg_one_eq_two_of_det h2 hA (det_suMat a)
      (fun h => ha1 (suMat_injective (by rw [h, suMat_one])))
  have hd₂ : Module.finrank K (eigSpace (suMat b) (-1)) = 2 :=
    CFSG.GH74.GLS.LU.finrank_eigSpace_neg_one_eq_two_of_det h2 hB (det_suMat b)
      (fun h => hb1 (suMat_injective (by rw [h, suMat_one])))
  rcases inf_eq_bot_or_exists_su_frame hK h2 (le_refl 3) hA hB hc hd₁ hd₂ hne with
    hV | ⟨g, hg1, hg2⟩
  · exfalso
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (eigSpace (suMat a) (-1))
      (eigSpace (suMat b) (-1))
    rw [hV, finrank_bot, hd₁, hd₂] at hsum
    have : Module.finrank K ↥(eigSpace (suMat a) (-1) ⊔ eigSpace (suMat b) (-1)) ≤ 3 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  · exact exists_cyc_of_frame (suCoe K p f) suMat_injective (g := g)
      (c := (⟨cycGL K, cycGL_mem⟩ : Su K p f 3)) (D₁ := negBlock K 3 0) (D₂ := negBlock K 3 1)
      hg1 hg2 cycMat_mul_negBlock_zero cycMat_mul_negBlock_one

end Unitary

theorem cycFour_psl {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    CycFour (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  refine CycFour.of_mulEquiv
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K) ?_
  refine CycFour.of_central_cube (QuotientGroup.mk' (center SL(3, K))) (QuotientGroup.mk'_surjective _)
    (fun z hz => by rwa [QuotientGroup.ker_mk'] at hz)
    (fun z hz => CFSG.GH74.GLS.LU.center_pow_three z (by rwa [QuotientGroup.ker_mk'] at hz))
    (cycFour_sl3 h2)

theorem cycFour_psu {K : Type} [Field K] {p f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) (hp : p ≠ 2) :
    CycFour (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) := by
  have : Fact p.Prime := ⟨hU.prime⟩
  have : Finite K := hU.finite
  have : CharP K p := hU.charP
  have hX := cycFour_su3 (K := K) (p := p) (f := f) hU.card_eq_sq hp
  let e : CFSG.ClassicalInvolution.Phan.Su K p f 3 ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hU.card_eq_sq 3)
  have hX' := CycFour.of_mulEquiv e hX
  have hY : CycFour (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3) := by
    refine CycFour.of_central_cube (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj hU 3)
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryProj_surjective hU 3) ?_ ?_ hX'
    · intro z hz
      rw [CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj] at hz
      exact CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_le_center hU 3 hz
    · intro z hz
      rw [CFSG.ClassicalGroups.UnitaryFlag.ker_unitaryProj] at hz
      obtain ⟨c, -, hc3, hzc⟩ := CFSG.ClassicalGroups.UnitaryFlag.mem_unitaryScalars.mp hz
      apply Subtype.ext
      rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
      rfl
  exact CycFour.of_mulEquiv
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3) (by norm_num)) hY

theorem eq_one_of_odd_center {L : Type*} [Group L] (hodd : Odd (Nat.card (center L))) {z : L}
    (hz : z ∈ center L) (hzz : z * z = 1) : z = 1 := by
  have h1 : orderOf z ∣ Nat.card (center L) := Subgroup.orderOf_dvd_natCard (center L) hz
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at h1
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := h1
    omega

theorem b_L3_fourgroup : B_L3_fourgroup := by
  intro G _ _ t p f ht hp hp2 hq5 L hL hodd hmod a b haL hbL ha hb hab ha1 hb1 hne
  have hcyc : CycFour ↥L := by
    refine CycFour.of_surjective_central (QuotientGroup.mk' (center ↥L))
      (QuotientGroup.mk'_surjective _) (fun z hz => by rwa [QuotientGroup.ker_mk'] at hz)
      (fun z hz hzz => eq_one_of_odd_center hodd (by rwa [QuotientGroup.ker_mk'] at hz) hzz) ?_
    rcases ht with rfl | rfl
    · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hmod
      exact CycFour.of_mulEquiv e.symm
        (cycFour_psl (Ring.two_ne_zero (ringChar_ne_two_of_card_pow hp hp2 hF)))
    · obtain ⟨-, hf, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data hmod
      have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
        ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
      exact CycFour.of_mulEquiv e.symm (cycFour_psu hU hp2)
  obtain ⟨g, hg1, hg2⟩ := hcyc ⟨a, haL⟩ ⟨b, hbL⟩ (Subtype.ext ha) (Subtype.ext hb) (Subtype.ext hab)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hne (congrArg Subtype.val h))
  exact ⟨g, g.2, congrArg Subtype.val hg1, congrArg Subtype.val hg2⟩

end CFSG.GH74.Generic.S3
