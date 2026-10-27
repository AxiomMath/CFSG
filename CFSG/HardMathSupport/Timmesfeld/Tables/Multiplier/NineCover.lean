module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.LieType.Multipliers.U43Action
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 Matrix
open CFSG.RankThree.PartTwo.Sec4.Census

namespace U43Six

@[expose] def n1 : Matrix (Fin 4) (Fin 4) F9 :=
  !![⟨0, 1⟩, ⟨1, 1⟩, 0, 0;
    ⟨2, 1⟩, ⟨0, 2⟩, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

@[expose] def n2 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, ⟨0, 1⟩, ⟨1, 1⟩;
    0, 0, ⟨2, 1⟩, ⟨0, 2⟩]

@[expose] def n3 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 1, ⟨1, 2⟩;
    0, 0, ⟨1, 1⟩, ⟨2, 0⟩;
    ⟨2, 0⟩, ⟨2, 1⟩, 0, 0;
    ⟨2, 2⟩, 1, 0, 0]

@[expose] def n4 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, ⟨0, 1⟩, ⟨1, 1⟩;
    0, 0, ⟨2, 1⟩, ⟨0, 2⟩;
    ⟨0, 1⟩, ⟨1, 1⟩, 0, 0;
    ⟨2, 1⟩, ⟨0, 2⟩, 0, 0]

@[expose] def fc (a : ZMod 3) : F9 := ⟨a, 0⟩

theorem fc_add : ∀ a b : ZMod 3, fc (a + b) = fc a + fc b := by decide

@[expose] def nn (a b c d : ZMod 3) : Matrix (Fin 4) (Fin 4) F9 :=
  fc a • n1 + fc b • n2 + fc c • n3 + fc d • n4

@[expose] def rmat (a b c d : ZMod 3) : Matrix (Fin 4) (Fin 4) F9 := 1 + nn a b c d

theorem n_mul_n : n1 * n1 = 0 ∧ n1 * n2 = 0 ∧ n1 * n3 = 0 ∧ n1 * n4 = 0 ∧
    n2 * n1 = 0 ∧ n2 * n2 = 0 ∧ n2 * n3 = 0 ∧ n2 * n4 = 0 ∧
    n3 * n1 = 0 ∧ n3 * n2 = 0 ∧ n3 * n3 = 0 ∧ n3 * n4 = 0 ∧
    n4 * n1 = 0 ∧ n4 * n2 = 0 ∧ n4 * n3 = 0 ∧ n4 * n4 = 0 := by decide +kernel

theorem nn_mul_nn (a b c d a' b' c' d' : ZMod 3) :
    nn a b c d * nn a' b' c' d' = 0 := by
  obtain ⟨h11, h12, h13, h14, h21, h22, h23, h24, h31, h32, h33, h34, h41, h42, h43, h44⟩ :=
    n_mul_n
  simp only [nn, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h11, h12, h13, h14, h21, h22,
    h23, h24, h31, h32, h33, h34, h41, h42, h43, h44, smul_zero, add_zero]

theorem nn_add (a b c d a' b' c' d' : ZMod 3) :
    nn (a + a') (b + b') (c + c') (d + d') = nn a b c d + nn a' b' c' d' := by
  simp only [nn, fc_add, add_smul]
  abel

theorem rmat_mul (a b c d a' b' c' d' : ZMod 3) :
    rmat a b c d * rmat a' b' c' d' = rmat (a + a') (b + b') (c + c') (d + d') := by
  have h : ∀ A B : Matrix (Fin 4) (Fin 4) F9, (1 + A) * (1 + B) = 1 + A + B + A * B := by
    intro A B
    noncomm_ring
  rw [rmat, rmat, rmat, h, nn_mul_nn, add_zero, nn_add, add_assoc]

theorem rmat_zero : rmat 0 0 0 0 = 1 := by decide +kernel

theorem det_rmat : ∀ a b c d : ZMod 3, (rmat a b c d).det = 1 := by decide +kernel

theorem rmat_unitary : ∀ a b c d : ZMod 3,
    ((rmat a b c d).map (· ^ 3))ᵀ * rmat a b c d = 1 := by decide +kernel

theorem rmat_entries : ∀ a b c d : ZMod 3,
    rmat a b c d 0 1 = 0 → rmat a b c d 2 3 = 0 → rmat a b c d 0 2 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by decide +kernel

@[expose] def pmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 1, 0;
    0, 0, 0, 1;
    1, 0, 0, 0;
    0, 1, 0, 0]

@[expose] def nmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, ⟨0, 1⟩, 0, 0;
    1, 0, 0, 0;
    0, 0, 0, 1;
    0, 0, ⟨0, 2⟩, 0]

@[expose] def gmat : Matrix (Fin 4) (Fin 4) F9 :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, ⟨2, 0⟩, 0;
    0, 0, 0, ⟨2, 0⟩]

theorem det_pmat : pmat.det = 1 := by decide +kernel
theorem det_nmat : nmat.det = 1 := by decide +kernel
theorem det_gmat : gmat.det = 1 := by decide +kernel
theorem pmat_unitary : (pmat.map (· ^ 3))ᵀ * pmat = 1 := by decide +kernel
theorem nmat_unitary : (nmat.map (· ^ 3))ᵀ * nmat = 1 := by decide +kernel
theorem gmat_unitary : (gmat.map (· ^ 3))ᵀ * gmat = 1 := by decide +kernel

theorem pmat_mul_rmat : ∀ a b c d : ZMod 3,
    pmat * rmat a b c d = rmat b a (-c) d * pmat := by decide +kernel

theorem gmat_mul_rmat : ∀ a b c d : ZMod 3,
    gmat * rmat a b c d = rmat a b (-c) (-d) * gmat := by decide +kernel

theorem nmat_mul_rmat : ∀ a b : ZMod 3,
    nmat * rmat a b 0 0 = rmat (-a) (-b) 0 0 * nmat := by decide +kernel

@[expose] noncomputable def toSU (A : Matrix (Fin 4) (Fin 4) F9) (hdet : A.det = 1)
    (hu : (A.map (· ^ 3))ᵀ * A = 1) : StatedSU 4 3 F9 :=
  ⟨GeneralLinearGroup.mk'' A (by rw [hdet]; exact isUnit_one),
    Subgroup.subset_closure ⟨hdet, hu⟩⟩

theorem ext_matrix {x y : StatedSU 4 3 F9}
    (h : ((x : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      ((y : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9)) : x = y :=
  Subtype.ext (Units.ext h)

@[expose] noncomputable def theta4 :
    Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) →* StatedSU 4 3 F9 where
  toFun x := toSU (rmat x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2.1 x.toAdd.2.2.2) (det_rmat _ _ _ _)
    (rmat_unitary _ _ _ _)
  map_one' := ext_matrix rmat_zero
  map_mul' _ _ := ext_matrix (rmat_mul _ _ _ _ _ _ _ _).symm

theorem coe_theta4 (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) :
    (((theta4 x : StatedSU 4 3 F9) : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) =
      rmat x.toAdd.1 x.toAdd.2.1 x.toAdd.2.2.1 x.toAdd.2.2.2 :=
  rfl

@[expose] noncomputable def thetaBar :
    Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) →* X₀ :=
  (QuotientGroup.mk' _).comp theta4

theorem thetaBar_injective : Function.Injective thetaBar := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [thetaBar, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have h01 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 0 1) hc
  have h23 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 2 3) hc
  have h02 := congrArg (fun A : GL (Fin 4) F9 => (A : Matrix (Fin 4) (Fin 4) F9) 0 2) hc
  simp only [GeneralLinearGroup.coe_scalar, coe_theta4, Matrix.scalar_apply,
    Matrix.diagonal_apply_ne _ (show (0 : Fin 4) ≠ 1 by decide),
    Matrix.diagonal_apply_ne _ (show (2 : Fin 4) ≠ 3 by decide),
    Matrix.diagonal_apply_ne _ (show (0 : Fin 4) ≠ 2 by decide)] at h01 h23 h02
  obtain ⟨ha, hb, hc', hd⟩ := rmat_entries _ _ _ _ h01.symm h23.symm h02.symm
  apply Multiplicative.toAdd.injective
  exact Prod.ext ha (Prod.ext hb (Prod.ext hc' hd))

theorem card_range_thetaBar : Nat.card thetaBar.range = 3 ^ 4 := by
  rw [Nat.card_congr (MonoidHom.ofInjective thetaBar_injective).toEquiv.symm,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]
  norm_num

@[expose] noncomputable def pSU : StatedSU 4 3 F9 := toSU pmat det_pmat pmat_unitary

@[expose] noncomputable def nSU : StatedSU 4 3 F9 := toSU nmat det_nmat nmat_unitary

@[expose] noncomputable def gSU : StatedSU 4 3 F9 := toSU gmat det_gmat gmat_unitary

@[expose] noncomputable def pBar : X₀ := QuotientGroup.mk pSU

@[expose] noncomputable def nBar : X₀ := QuotientGroup.mk nSU

@[expose] noncomputable def gBar : X₀ := QuotientGroup.mk gSU

@[expose] noncomputable def w1 : X₀ := thetaBar (Multiplicative.ofAdd (1, 0, 0, 0))

@[expose] noncomputable def w2 : X₀ := thetaBar (Multiplicative.ofAdd (0, 1, 0, 0))

@[expose] noncomputable def w3 : X₀ := thetaBar (Multiplicative.ofAdd (0, 0, 1, 0))

@[expose] noncomputable def w4 : X₀ := thetaBar (Multiplicative.ofAdd (0, 0, 0, 1))

theorem pBar_conj (a b c d : ZMod 3) :
    pBar * thetaBar (Multiplicative.ofAdd (a, b, c, d)) * pBar⁻¹ =
      thetaBar (Multiplicative.ofAdd (b, a, -c, d)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg QuotientGroup.mk (ext_matrix (pmat_mul_rmat a b c d))

theorem gBar_conj (a b c d : ZMod 3) :
    gBar * thetaBar (Multiplicative.ofAdd (a, b, c, d)) * gBar⁻¹ =
      thetaBar (Multiplicative.ofAdd (a, b, -c, -d)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg QuotientGroup.mk (ext_matrix (gmat_mul_rmat a b c d))

theorem nBar_conj (a b : ZMod 3) :
    nBar * thetaBar (Multiplicative.ofAdd (a, b, 0, 0)) * nBar⁻¹ =
      thetaBar (Multiplicative.ofAdd (-a, -b, 0, 0)) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg QuotientGroup.mk (ext_matrix (nmat_mul_rmat a b))

theorem thetaBar_inv (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) :
    (thetaBar x)⁻¹ = thetaBar x⁻¹ := (map_inv thetaBar x).symm

theorem pow_three_eq_one_gen : ∀ x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3),
    x ^ 3 = 1 := by decide

theorem thetaBar_pow_three (x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) :
    thetaBar x ^ 3 = 1 := by
  rw [← map_pow, pow_three_eq_one_gen, map_one]

theorem w1_pow_three : w1 ^ 3 = 1 := thetaBar_pow_three _
theorem w2_pow_three : w2 ^ 3 = 1 := thetaBar_pow_three _
theorem w3_pow_three : w3 ^ 3 = 1 := thetaBar_pow_three _
theorem w4_pow_three : w4 ^ 3 = 1 := thetaBar_pow_three _

theorem pBar_w1 : pBar * w1 * pBar⁻¹ = w2 := pBar_conj 1 0 0 0
theorem pBar_w2 : pBar * w2 * pBar⁻¹ = w1 := pBar_conj 0 1 0 0
theorem pBar_w4 : pBar * w4 * pBar⁻¹ = w4 := pBar_conj 0 0 0 1

theorem pBar_w3 : pBar * w3 * pBar⁻¹ = w3⁻¹ := by
  rw [w3, thetaBar_inv, pBar_conj]
  congr 1

theorem gBar_w1 : gBar * w1 * gBar⁻¹ = w1 := gBar_conj 1 0 0 0
theorem gBar_w2 : gBar * w2 * gBar⁻¹ = w2 := gBar_conj 0 1 0 0

theorem gBar_w3 : gBar * w3 * gBar⁻¹ = w3⁻¹ := by
  rw [w3, thetaBar_inv, gBar_conj]
  congr 1

theorem gBar_w4 : gBar * w4 * gBar⁻¹ = w4⁻¹ := by
  rw [w4, thetaBar_inv, gBar_conj]
  congr 1

theorem nBar_w1 : nBar * w1 * nBar⁻¹ = w1⁻¹ := by
  rw [w1, thetaBar_inv, nBar_conj]
  congr 1

theorem nBar_w2 : nBar * w2 * nBar⁻¹ = w2⁻¹ := by
  rw [w2, thetaBar_inv, nBar_conj]
  congr 1

theorem eq_gen_mul : ∀ x : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3),
    x = Multiplicative.ofAdd (1, 0, 0, 0) ^ (Multiplicative.toAdd x).1.val *
      Multiplicative.ofAdd (0, 1, 0, 0) ^ (Multiplicative.toAdd x).2.1.val *
      Multiplicative.ofAdd (0, 0, 1, 0) ^ (Multiplicative.toAdd x).2.2.1.val *
      Multiplicative.ofAdd (0, 0, 0, 1) ^ (Multiplicative.toAdd x).2.2.2.val := by decide

theorem range_thetaBar_le : thetaBar.range ≤ Subgroup.closure {w1, w2, w3, w4} := by
  rintro _ ⟨x, rfl⟩
  have h1 : w1 ∈ Subgroup.closure ({w1, w2, w3, w4} : Set X₀) :=
    Subgroup.subset_closure (by simp)
  have h2 : w2 ∈ Subgroup.closure ({w1, w2, w3, w4} : Set X₀) :=
    Subgroup.subset_closure (by simp)
  have h3 : w3 ∈ Subgroup.closure ({w1, w2, w3, w4} : Set X₀) :=
    Subgroup.subset_closure (by simp)
  have h4 : w4 ∈ Subgroup.closure ({w1, w2, w3, w4} : Set X₀) :=
    Subgroup.subset_closure (by simp)
  have e : thetaBar x = w1 ^ (Multiplicative.toAdd x).1.val *
      w2 ^ (Multiplicative.toAdd x).2.1.val *
      w3 ^ (Multiplicative.toAdd x).2.2.1.val * w4 ^ (Multiplicative.toAdd x).2.2.2.val := by
    rw [w1, w2, w3, w4, ← map_pow thetaBar, ← map_pow thetaBar, ← map_pow thetaBar,
      ← map_pow thetaBar, ← map_mul thetaBar, ← map_mul thetaBar, ← map_mul thetaBar,
      ← eq_gen_mul x]
  rw [e]
  exact mul_mem (mul_mem (mul_mem (pow_mem h1 _) (pow_mem h2 _)) (pow_mem h3 _)) (pow_mem h4 _)

theorem gens_subset_range : ({w1, w2, w3, w4} : Set X₀) ⊆ thetaBar.range := by
  rintro _ (rfl | rfl | rfl | rfl) <;> exact ⟨_, rfl⟩

section Lifts

variable {G : Type} [Group G] {φ : G →* X₀}

theorem commute_of_gen4 (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (x y : G) (hx : φ x ∈ ({w1, w2, w3, w4} : Set X₀)) (hy : φ y ∈ ({w1, w2, w3, w4} : Set X₀))
    (hxy : φ x ≠ φ y) : x * y = y * x := by
  have hcomm : ∀ i j : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3),
      Commute (thetaBar i) (thetaBar j) := fun i j => (Commute.all i j).map thetaBar
  have hc : ∀ {u v : X₀}, u ∈ ({w1, w2, w3, w4} : Set X₀) → v ∈ ({w1, w2, w3, w4} : Set X₀) →
      Commute u v := by
    rintro u v (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> exact hcomm _ _
  have h3 : ∀ {v : X₀}, v ∈ ({w1, w2, w3, w4} : Set X₀) → v ^ 3 = 1 := by
    rintro v (rfl | rfl | rfl | rfl)
    exacts [w1_pow_three, w2_pow_three, w3_pow_three, w4_pow_three]
  have key : ∀ (n : X₀) (a b : G), φ a ∈ ({w1, w2, w3, w4} : Set X₀) →
      φ b ∈ ({w1, w2, w3, w4} : Set X₀) →
      ((n * φ a * n⁻¹ = φ a ∧ n * φ b * n⁻¹ = (φ b)⁻¹) ∨
        (n * φ a * n⁻¹ = φ b ∧ n * φ b * n⁻¹ = φ a)) → a * b = b * a := by
    intro n a b ha hb hn
    exact TripleCoverLift.commute_of_conj hφ hker (p := 3) (by decide) (x := a) (y := b)
      (hc ha hb) (h3 hb) hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
  · exact absurd (hx.trans hy.symm) hxy
  · exact key pBar x y (by simp [hx]) (by simp [hy])
      (Or.inr ⟨by rw [hx, hy]; exact pBar_w1, by rw [hx, hy]; exact pBar_w2⟩)
  · exact key gBar x y (by simp [hx]) (by simp [hy])
      (Or.inl ⟨by rw [hx]; exact gBar_w1, by rw [hy]; exact gBar_w3⟩)
  · exact key gBar x y (by simp [hx]) (by simp [hy])
      (Or.inl ⟨by rw [hx]; exact gBar_w1, by rw [hy]; exact gBar_w4⟩)
  · exact key pBar x y (by simp [hx]) (by simp [hy])
      (Or.inr ⟨by rw [hx, hy]; exact pBar_w2, by rw [hx, hy]; exact pBar_w1⟩)
  · exact absurd (hx.trans hy.symm) hxy
  · exact key gBar x y (by simp [hx]) (by simp [hy])
      (Or.inl ⟨by rw [hx]; exact gBar_w2, by rw [hy]; exact gBar_w3⟩)
  · exact key gBar x y (by simp [hx]) (by simp [hy])
      (Or.inl ⟨by rw [hx]; exact gBar_w2, by rw [hy]; exact gBar_w4⟩)
  · exact (key gBar y x (by simp [hy]) (by simp [hx])
      (Or.inl ⟨by rw [hy]; exact gBar_w1, by rw [hx]; exact gBar_w3⟩)).symm
  · exact (key gBar y x (by simp [hy]) (by simp [hx])
      (Or.inl ⟨by rw [hy]; exact gBar_w2, by rw [hx]; exact gBar_w3⟩)).symm
  · exact absurd (hx.trans hy.symm) hxy
  · exact (key pBar y x (by simp [hy]) (by simp [hx])
      (Or.inl ⟨by rw [hy]; exact pBar_w4, by rw [hx]; exact pBar_w3⟩)).symm
  · exact (key gBar y x (by simp [hy]) (by simp [hx])
      (Or.inl ⟨by rw [hy]; exact gBar_w1, by rw [hx]; exact gBar_w4⟩)).symm
  · exact (key gBar y x (by simp [hy]) (by simp [hx])
      (Or.inl ⟨by rw [hy]; exact gBar_w2, by rw [hx]; exact gBar_w4⟩)).symm
  · exact key pBar x y (by simp [hx]) (by simp [hy])
      (Or.inl ⟨by rw [hx]; exact pBar_w4, by rw [hy]; exact pBar_w3⟩)
  · exact absurd (hx.trans hy.symm) hxy

theorem commute_of_mem_range (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {x y : G} (hx : φ x ∈ thetaBar.range) (hy : φ y ∈ thetaBar.range) : x * y = y * x :=
  TripleCoverLift.commute_of_mem_closure hφ hker (commute_of_gen4 hφ hker)
    (range_thetaBar_le hx) (range_thetaBar_le hy)

theorem exists_lift_of_mem_range (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {e : X₀} (he : e ∈ thetaBar.range) : ∃ y : G, φ y = e ∧ y ^ 3 = 1 := by
  refine TripleCoverLift.exists_lift_pow_eq_one_of_mem_closure (E := thetaBar.range)
    (fun x hx y hy => commute_of_mem_range hφ hker hx hy) (S := {w1, w2, w3, w4})
    gens_subset_range ?_ (range_thetaBar_le he)
  rintro _ (rfl | rfl | rfl | rfl)
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      w1_pow_three nBar_w1
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      w2_pow_three nBar_w2
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      w3_pow_three gBar_w3
  · exact TripleCoverLift.exists_lift_pow_eq_one_of_conj_eq_inv hφ hker (by decide)
      w4_pow_three gBar_w4

end Lifts

end U43Six

open U43Six in
theorem six_le_pRank_of_cover {G : Type} [Group G] [Finite G] (φ : G →* X₀)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ 3 = 1) (hZ : 9 ≤ Nat.card Z) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x ∈ thetaBar.range.comap φ, ∀ y ∈ thetaBar.range.comap φ, x * y = y * x :=
    fun x hx y hy => commute_of_mem_range hφ hker hx hy
  set U := TripleCoverLift.powOneSubgroup φ thetaBar.range 3 hcomm with hUdef
  have hUab : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (TripleCoverLift.mem_powOneSubgroup.mp a.2).1 _
      (TripleCoverLift.mem_powOneSubgroup.mp b.2).1)⟩⟩,
      fun x hx => (TripleCoverLift.mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup 3 U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X₀ := φ.comp U.subtype
  have hψr : ψ.range = thetaBar.range := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (TripleCoverLift.mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := exists_lift_of_mem_range hφ hker he
      exact ⟨⟨y, TripleCoverLift.mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => TripleCoverLift.mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact thetaBar.range.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : 9 ≤ Nat.card ψ.ker := by
    calc 9 ≤ Nat.card Z := hZ
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have h729 : 3 ^ 6 ≤ 3 ^ k := by
    rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, card_range_thetaBar]
    calc 3 ^ 6 = 9 * 3 ^ 4 := by norm_num
      _ ≤ Nat.card ψ.ker * 3 ^ 4 := Nat.mul_le_mul hψk le_rfl
  have hk6 : 6 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp h729
  exact hk6.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hUab hk)

end CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
