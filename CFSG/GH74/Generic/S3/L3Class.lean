module

public import CFSG.GH74.Generic.S3.FourGroup
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public section

namespace CFSG.GH74.Generic.S3

open Subgroup CFSG.ClassicalInvolution.Models
open scoped MatrixGroups Matrix

@[expose] def SingleInv (X : Type*) [Group X] : Prop :=
  ∀ a b : X, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ g : X, g * a * g⁻¹ = b

theorem SingleInv.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : SingleInv X) :
    SingleInv Y := by
  intro a b ha ha1 hb hb1
  obtain ⟨g, hg⟩ := h (e.symm a) (e.symm b) (by rw [← map_mul, ha, map_one])
    (fun h' => ha1 (by simpa using congrArg e h')) (by rw [← map_mul, hb, map_one])
    (fun h' => hb1 (by simpa using congrArg e h'))
  refine ⟨e g, ?_⟩
  have := congrArg e hg
  simpa using this

theorem SingleInv.of_central_cube {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hcen : ∀ z ∈ π.ker, z ∈ center X)
    (hcube : ∀ z ∈ π.ker, z ^ 3 = 1) (hX : SingleInv X) : SingleInv Y := by
  intro a b ha ha1 hb hb1
  obtain ⟨a', ha'2, rfl⟩ := exists_involution_lift_of_central_cube π hπ hcen hcube ha
  obtain ⟨b', hb'2, rfl⟩ := exists_involution_lift_of_central_cube π hπ hcen hcube hb
  obtain ⟨g, hg⟩ := hX a' b' ha'2 (fun h => ha1 (by rw [h, map_one]))
    hb'2 (fun h => hb1 (by rw [h, map_one]))
  refine ⟨π g, ?_⟩
  have := congrArg π hg
  simpa using this

theorem eq_of_involutions_of_map_eq {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hcen : ∀ z ∈ π.ker, z ∈ center X) (hinv : ∀ z ∈ π.ker, z * z = 1 → z = 1) {t s : X}
    (ht : t * t = 1) (hs : s * s = 1) (hts : π t = π s) : t = s := by
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

theorem SingleInv.of_surjective_central {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hcen : ∀ z ∈ π.ker, z ∈ center X)
    (hinv : ∀ z ∈ π.ker, z * z = 1 → z = 1) (hY : SingleInv Y) : SingleInv X := by
  intro a b ha ha1 hb hb1
  have hπa : π a ≠ 1 := fun h => ha1 (hinv a (MonoidHom.mem_ker.mpr h) ha)
  have hπb : π b ≠ 1 := fun h => hb1 (hinv b (MonoidHom.mem_ker.mpr h) hb)
  obtain ⟨gb, hg⟩ := hY (π a) (π b) (by rw [← map_mul, ha, map_one]) hπa
    (by rw [← map_mul, hb, map_one]) hπb
  obtain ⟨g, rfl⟩ := hπ gb
  have hconj : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; group
  exact ⟨g, eq_of_involutions_of_map_eq π hcen hinv hconj hb (by simpa using hg)⟩

theorem exists_conj_of_frame {X M : Type*} [Group X] [Monoid M] (m : X →* M)
    (hm : Function.Injective m) {a b g g' : X} {Δ : M}
    (h1 : m a * m g = m g * Δ) (h2 : m b * m g' = m g' * Δ) :
    ∃ h : X, h * a * h⁻¹ = b := by
  have e1 : m (g⁻¹ * a * g) = Δ := by
    calc m (g⁻¹ * a * g) = m g⁻¹ * (m a * m g) := by simp only [map_mul, mul_assoc]
      _ = m g⁻¹ * (m g * Δ) := by rw [h1]
      _ = Δ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have e2 : m (g'⁻¹ * b * g') = Δ := by
    calc m (g'⁻¹ * b * g') = m g'⁻¹ * (m b * m g') := by simp only [map_mul, mul_assoc]
      _ = m g'⁻¹ * (m g' * Δ) := by rw [h2]
      _ = Δ := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have e : g⁻¹ * a * g = g'⁻¹ * b * g' := hm (e1.trans e2.symm)
  refine ⟨g' * g⁻¹, ?_⟩
  calc g' * g⁻¹ * a * (g' * g⁻¹)⁻¹ = g' * (g⁻¹ * a * g) * g'⁻¹ := by group
    _ = g' * (g'⁻¹ * b * g') * g'⁻¹ := by rw [e]
    _ = b := by group

section Linear

variable {K : Type} [Field K]

theorem exists_sl3_frame (h2 : (2 : K) ≠ 0) {D : Matrix (Fin 3) (Fin 3) K} (hD : D * D = 1)
    (hdim : Module.finrank K (eigSpace D (-1)) = 2) :
    ∃ P : SL(3, K), D * (P : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) *
      Matrix.diagonal (fun j : Fin 3 => if j.val < 2 then (-1 : K) else 1) := by
  have hcompl := isCompl_eigSpace h2 hD
  set V := eigSpace D (-1) with hV
  set W := eigSpace D 1 with hW'
  have hW : Module.finrank K W = 1 := CFSG.GH74.GLS.LU.finrank_eigSpace_one_of_finrank_neg_one h2 hD hdim
  let E : Bool → Submodule K (Fin 3 → K) := fun b => cond b W V
  have hint : DirectSum.IsInternal E := by
    rw [DirectSum.isInternal_submodule_iff_isCompl E (i := false) (j := true) (by simp)
      (by ext b; cases b <;> simp)]
    exact hcompl
  let ε : Fin 3 → Bool := fun j => decide (2 ≤ j.val)
  have hε : ∀ b, Nat.card {j // ε j = b} = Module.finrank K (E b) := by
    intro b
    cases b
    · change _ = Module.finrank K V
      rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin 3 => j.val < 2)
        (fun j => by simp only [ε, decide_eq_false_iff_not, not_le]))]
      rw [hdim]
      exact card_fin_val_lt (by norm_num)
    · change _ = Module.finrank K W
      rw [hW, Nat.card_congr (Equiv.subtypeEquivRight (q := fun j : Fin 3 => 2 ≤ j.val)
        (fun j => by simp only [ε, decide_eq_true_eq]))]
      exact card_fin_val_ge (by norm_num)
  obtain ⟨P, hP⟩ := exists_sl_adapted (by norm_num : 0 < 3) E hint ε hε
  refine ⟨P, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have hcol := hP j
  by_cases hj : j.val < 2
  · have hmem : (fun k => (P : Matrix (Fin 3) (Fin 3) K) k j) ∈ V := by
      simpa [E, ε, not_le.mpr hj] using hcol
    have := congr_fun (mem_eigSpace_neg_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at this
    simp only [Matrix.mul_apply, hj, ite_true]
    rw [this]
    ring
  · have hmem : (fun k => (P : Matrix (Fin 3) (Fin 3) K) k j) ∈ W := by
      simpa [E, ε, not_lt.mp hj] using hcol
    have := congr_fun (mem_eigSpace_one.mp hmem) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, hj, ite_false]
    rw [this]
    ring

theorem singleInv_sl3 (h2 : (2 : K) ≠ 0) : SingleInv SL(3, K) := by
  have frame : ∀ A : SL(3, K), A * A = 1 → A ≠ 1 → ∃ P : SL(3, K),
      (A : Matrix (Fin 3) (Fin 3) K) * P = P *
        Matrix.diagonal (fun j : Fin 3 => if j.val < 2 then (-1 : K) else 1) := by
    intro A hA hA1
    have hI : (A : Matrix (Fin 3) (Fin 3) K) * A = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_one]
    exact exists_sl3_frame h2 hI (CFSG.GH74.GLS.LU.finrank_eigSpace_neg_one_eq_two h2 hA hA1)
  intro a b ha ha1 hb hb1
  obtain ⟨P, hP⟩ := frame a ha ha1
  obtain ⟨P', hP'⟩ := frame b hb hb1
  exact exists_conj_of_frame (slCoe K) slCoe_injective hP hP'

end Linear

theorem singleInv_psl {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    SingleInv (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) := by
  refine SingleInv.of_mulEquiv
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K) ?_
  exact SingleInv.of_central_cube (QuotientGroup.mk' (center SL(3, K))) (QuotientGroup.mk'_surjective _)
    (fun z hz => by rwa [QuotientGroup.ker_mk'] at hz)
    (fun z hz => CFSG.GH74.GLS.LU.center_pow_three z (by rwa [QuotientGroup.ker_mk'] at hz))
    (singleInv_sl3 h2)

theorem singleInv_psu {K : Type} [Field K] {p f : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K) (hp : p ≠ 2) :
    SingleInv (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) := by
  refine SingleInv.of_mulEquiv
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3) (by norm_num)) ?_
  intro a b ha ha1 hb hb1
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hb) hb1
  have h1 := CFSG.RankThree.Classical.isConj_unitaryProj_unitaryInvT hU hp ha2
  have h2 := CFSG.RankThree.Classical.isConj_unitaryProj_unitaryInvT hU hp hb2
  obtain ⟨g, hg⟩ := isConj_iff.mp (h1.trans h2.symm)
  exact ⟨g, hg⟩

theorem b_L3_class : B_L3_class := by
  intro G _ _ t p f ht hp hp2 hq5 L hL hodd hmod a haL b hbL ha ha1 hb hb1
  have hS : SingleInv ↥L := by
    refine SingleInv.of_surjective_central (QuotientGroup.mk' (center ↥L))
      (QuotientGroup.mk'_surjective _) (fun z hz => by rwa [QuotientGroup.ker_mk'] at hz)
      (fun z hz hzz => eq_one_of_odd_center hodd (by rwa [QuotientGroup.ker_mk'] at hz) hzz) ?_
    rcases ht with rfl | rfl
    · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hmod
      exact SingleInv.of_mulEquiv e.symm
        (singleInv_psl (Ring.two_ne_zero (ringChar_ne_two_of_card_pow hp hp2 hF)))
    · obtain ⟨-, hf, F, _, _, hF, ⟨e⟩⟩ := lieModel_psu_data hmod
      have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
        ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
      exact SingleInv.of_mulEquiv e.symm (singleInv_psu hU hp2)
  obtain ⟨g, hg⟩ := hS ⟨a, haL⟩ ⟨b, hbL⟩ (Subtype.ext ha) (fun h => ha1 (congrArg Subtype.val h))
    (Subtype.ext hb) (fun h => hb1 (congrArg Subtype.val h))
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

end CFSG.GH74.Generic.S3
