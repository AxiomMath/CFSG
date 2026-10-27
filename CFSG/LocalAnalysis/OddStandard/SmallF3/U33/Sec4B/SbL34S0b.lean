module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


section Model

theorem ut3_comm {R : Type} [CommRing R] (x y : UT3 R) :
    x * y * x⁻¹ * y⁻¹ = ⟨0, 0, x.a * y.b - y.a * x.b⟩ := by
  ext <;> simp only [UT3.mul_def, UT3.inv_def] <;> ring

theorem ut3_central_ab {x : UT3 F4} (hx : ∀ y : UT3 F4, x * y = y * x) : x.a = 0 ∧ x.b = 0 := by
  have h1 := congrArg UT3.c (hx ⟨1, 0, 0⟩)
  have h2 := congrArg UT3.c (hx ⟨0, 1, 0⟩)
  simp only [UT3.mul_def] at h1 h2
  constructor
  · have h := h2
    simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at h
    exact add_left_cancel (h.trans (add_zero x.c).symm)
  · have h := h1
    simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero x.c).symm)

theorem ut3_card_center_le :
    Nat.card {x : UT3 F4 // ∀ y : UT3 F4, x * y = y * x} ≤ 4 := by
  have hK : Nat.card F4 = 4 := by
    have := GaloisField.card 2 2 (by norm_num)
    simpa using this
  rw [← hK]
  refine Nat.card_le_card_of_injective
    (fun x : {x : UT3 F4 // ∀ y : UT3 F4, x * y = y * x} => x.1.c) ?_
  intro x y h
  apply Subtype.ext
  obtain ⟨ha, hb⟩ := ut3_central_ab x.2
  obtain ⟨ha', hb'⟩ := ut3_central_ab y.2
  ext
  · rw [ha, ha']
  · rw [hb, hb']
  · exact h

theorem ut3_nonabelian : ∃ a b : UT3 F4, a * b ≠ b * a := by
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ?_⟩
  intro h
  have hc := congrArg UT3.c h
  simp only [UT3.mul_def, mul_zero, mul_one, one_mul, zero_mul, add_zero, zero_add] at hc
  exact one_ne_zero hc

theorem ut3_exists_comm {a : UT3 F4} (ha : ∃ w : UT3 F4, a * w ≠ w * a) {c : UT3 F4}
    (hc : ∀ y : UT3 F4, c * y = y * c) : ∃ w : UT3 F4, a * w * a⁻¹ * w⁻¹ = c := by
  obtain ⟨hca, hcb⟩ := ut3_central_ab hc
  have ha' : a.a ≠ 0 ∨ a.b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h, hh⟩ := ha
    apply hh
    ext <;> simp only [UT3.mul_def, hcon.1, hcon.2] <;> ring
  by_cases haa : a.a = 0
  · have hab : a.b ≠ 0 := by tauto
    refine ⟨⟨-(c.c / a.b), 0, 0⟩, ?_⟩
    rw [ut3_comm]
    ext
    · simp [hca]
    · simp [hcb]
    · simp [haa]
      field_simp [hab] <;> ring
  · refine ⟨⟨0, c.c / a.a, 0⟩, ?_⟩
    rw [ut3_comm]
    ext
    · simp [hca]
    · simp [hcb]
    · simp
      field_simp [haa] <;> ring

end Model

section Basic

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem V_le_ZQ : fourGrp x₁ x₂ ≤
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  intro a ha
  refine ⟨hc.V_le_Q ha, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro h hh
  have hhV : h ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hO : h ∈ ctxO t tau x₁ x₂ := hc.Q_le_O hh
    have : h ∈ ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← hc.O_eq_CV]
      exact hO
    exact this.2
  exact (Subgroup.mem_centralizer_iff.mp hhV a ha).symm

end Basic

section Transfer

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem Q_nonab : ∃ a ∈ ctxQ t tau x₁ x₂ rho, ∃ b ∈ ctxQ t tau x₁ x₂ rho, a * b ≠ b * a := by
  obtain ⟨φ⟩ := hs
  obtain ⟨a, b, hab⟩ := ut3_nonabelian
  refine ⟨((φ.symm a : ↥(ctxQ t tau x₁ x₂ rho)) : G), (φ.symm a).2,
    ((φ.symm b : ↥(ctxQ t tau x₁ x₂ rho)) : G), (φ.symm b).2, ?_⟩
  intro h
  apply hab
  have h' : (φ.symm a : ↥(ctxQ t tau x₁ x₂ rho)) * φ.symm b =
      φ.symm b * φ.symm a := by
    apply Subtype.ext
    exact h
  calc a * b = φ (φ.symm a * φ.symm b) := by simp
    _ = φ (φ.symm b * φ.symm a) := by rw [h']
    _ = b * a := by simp

theorem card_ZQ_le :
    Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) ≤
      4 := by
  obtain ⟨φ⟩ := hs
  haveI : Finite (UT3 F4) :=
    Finite.of_injective (fun x : UT3 F4 => (x.a, x.b, x.c)) (by
      intro x y h
      simp only [Prod.mk.injEq] at h
      exact UT3.ext h.1 h.2.1 h.2.2)
  let F : ↥(ctxQ t tau x₁ x₂ rho ⊓
      centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) →
      {x : UT3 F4 // ∀ y : UT3 F4, x * y = y * x} := fun z =>
    ⟨φ ⟨z.1, z.2.1⟩, by
      intro y
      have hq : (φ.symm y : ↥(ctxQ t tau x₁ x₂ rho)) * ⟨z.1, z.2.1⟩ =
          ⟨z.1, z.2.1⟩ * φ.symm y := by
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp z.2.2 (φ.symm y) (φ.symm y).2
      calc φ ⟨z.1, z.2.1⟩ * y = φ (⟨z.1, z.2.1⟩ * φ.symm y) := by simp
        _ = φ (φ.symm y * ⟨z.1, z.2.1⟩) := by rw [hq]
        _ = y * φ ⟨z.1, z.2.1⟩ := by simp⟩
  have hinj : Function.Injective F := by
    intro z w h
    have h1 : φ ⟨z.1, z.2.1⟩ = φ ⟨w.1, w.2.1⟩ := congrArg Subtype.val h
    have h2 : (⟨z.1, z.2.1⟩ : ↥(ctxQ t tau x₁ x₂ rho)) = ⟨w.1, w.2.1⟩ := φ.injective h1
    exact Subtype.ext (congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) h2)
  exact (Nat.card_le_card_of_injective F hinj).trans ut3_card_center_le

theorem Z_Q : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) =
    fourGrp x₁ x₂ := by
  have hle : fourGrp x₁ x₂ ≤
      ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    V_le_ZQ hc
  have hcard : Nat.card ↥(ctxQ t tau x₁ x₂ rho ⊓
      centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)) ≤ Nat.card (fourGrp x₁ x₂) := by
    rw [card_fourGrp hc]
    exact card_ZQ_le hc hs
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem pairing_Q {a : G} (haQ : a ∈ ctxQ t tau x₁ x₂ rho) (ha : a ∉ fourGrp x₁ x₂) {c : G}
    (hcV : c ∈ fourGrp x₁ x₂) : ∃ w ∈ ctxQ t tau x₁ x₂ rho, a * w * a⁻¹ * w⁻¹ = c := by
  have hs_syl : IsSylSL34 (ctxQ t tau x₁ x₂ rho) := hs
  obtain ⟨φ⟩ := hs_syl
  have hZ : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) =
      fourGrp x₁ x₂ := Z_Q hc hs
  have hnc : a ∉ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro h
    exact ha (by rw [← hZ]; exact ⟨haQ, h⟩)
  have hnc' : ¬ ∀ h ∈ ↑(ctxQ t tau x₁ x₂ rho), h * a = a * h :=
    fun hall => hnc (Subgroup.mem_centralizer_iff.mpr hall)
  push_neg at hnc'
  obtain ⟨h, hhQ, hcomm⟩ := hnc'
  let A : ↥(ctxQ t tau x₁ x₂ rho) := ⟨a, haQ⟩
  let H : ↥(ctxQ t tau x₁ x₂ rho) := ⟨h, hhQ⟩
  let C : ↥(ctxQ t tau x₁ x₂ rho) := ⟨c, hc.V_le_Q hcV⟩
  have hneq : ∃ w : UT3 F4, φ A * w ≠ w * φ A := by
    refine ⟨φ H, ?_⟩
    intro heq
    apply hcomm
    have hh : A * H = H * A := by
      apply φ.injective
      simp only [map_mul]
      exact heq
    exact (congrArg (fun x : ↥(ctxQ t tau x₁ x₂ rho) => (x : G)) hh).symm
  have hcent : ∀ y : UT3 F4, φ C * y = y * φ C := by
    intro y
    have hcZ : c ∈ ctxQ t tau x₁ x₂ rho ⊓
        centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) := V_le_ZQ hc hcV
    have hq : (φ.symm y : ↥(ctxQ t tau x₁ x₂ rho)) * C = C * φ.symm y := by
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcZ.2 (φ.symm y) (φ.symm y).2
    calc φ C * y = φ (C * φ.symm y) := by simp
      _ = φ (φ.symm y * C) := by rw [hq]
      _ = y * φ C := by simp
  obtain ⟨w', hw'⟩ := ut3_exists_comm (a := φ A) (c := φ C) hneq hcent
  refine ⟨((φ.symm w' : ↥(ctxQ t tau x₁ x₂ rho)) : G), (φ.symm w').2, ?_⟩
  have hQeq : A * φ.symm w' * A⁻¹ * (φ.symm w')⁻¹ = C := by
    apply φ.injective
    simp only [map_mul, map_inv]
    simpa using hw'
  exact congrArg Subtype.val hQeq

end Transfer

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
