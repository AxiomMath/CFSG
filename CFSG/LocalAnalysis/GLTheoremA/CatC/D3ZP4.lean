module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZP3

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even

section Factor

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem rho_mem_normalizer_iff_k (hK2 : ringChar K ≠ 2) (k : Fin Tag.D4.rank) (X : SL2 K) :
    ρ k X ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) ↔
      (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  constructor
  · intro h
    have h1 : ρ k X * xUnit Tag.D4 K k 1 * (ρ k X)⁻¹ ∈ Uk K k :=
      (Subgroup.mem_normalizer_iff.1 h _).1 (xUnit_mem_Uk k 1)
    obtain ⟨c, hc⟩ := mem_Uk.1 h1
    have h2 : ρ k (uSL c) = ρ k (X * uSL 1 * X⁻¹) := by
      rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL, simpleRootSL2_uSL]; exact hc
    have h3 := simpleRootSL2_injective hK2 k h2
    have h4 : uSL c * X = X * uSL 1 := by
      rw [h3, inv_mul_cancel_right]
    have h5 := congrArg (fun Z : SL2 K => (Z : Matrix (Fin 2) (Fin 2) K) 1 1) h4
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two] using h5
  · intro h
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    have e : ρ k X * xUnit Tag.D4 K k c * (ρ k X)⁻¹ = ρ k (X * uSL c * X⁻¹) := by
      rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL]
    rw [e, sl2_upper_conj h c, simpleRootSL2_uSL]
    exact xUnit_mem_Uk _ _

theorem normalizes_X10_k (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank)
    (A e : SL2 K) (R : ModGL Tag.D4 K) (hR : ∀ Y : SL2 K, Commute R (ρ k Y)) :
    (ρ k e)⁻¹ * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k e ∈
        Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) ↔
      ((dconj ((b k)⁻¹) e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  have hn : (ρ k e)⁻¹ * (h * (ρ k A * R)) * ρ k e =
      h * ρ k (dconj ((b k)⁻¹) e⁻¹ * A * e) * R := by
    have e2 : (ρ k e)⁻¹ * h = h * ρ k (dconj ((b k)⁻¹) e⁻¹) := by
      have := conj_inv_rho b k e⁻¹
      rw [map_inv] at this
      calc (ρ k e)⁻¹ * h = h * (h⁻¹ * (ρ k e)⁻¹ * h) := by group
        _ = h * ρ k (dconj ((b k)⁻¹) e⁻¹) := by rw [hh, this]
    rw [map_mul, map_mul]
    calc (ρ k e)⁻¹ * (h * (ρ k A * R)) * ρ k e
        = ((ρ k e)⁻¹ * h) * ρ k A * (R * ρ k e) := by group
      _ = ((ρ k e)⁻¹ * h) * ρ k A * (ρ k e * R) := by rw [(hR e).eq]
      _ = h * ρ k (dconj ((b k)⁻¹) e⁻¹) * ρ k A * ρ k e * R := by rw [e2]; group
      _ = _ := by group
  rw [hn]
  have hT : h ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) :=
    rootDiagUnit_mem_normalizer_Uk (K := K) b k
  have hRN : R ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
    refine mem_normalizer_of_forall_conj_mem _ fun u hu => ?_
    obtain ⟨c, rfl⟩ := mem_Uk.1 hu
    have e1 : R * xUnit Tag.D4 K k c * R⁻¹ = xUnit Tag.D4 K k c := by
      have := (hR (uSL c)).eq
      rw [simpleRootSL2_uSL] at this
      rw [this, mul_inv_cancel_right]
    rw [e1]; exact xUnit_mem_Uk k c
  constructor
  · intro hmem
    have h1 : ρ k (dconj ((b k)⁻¹) e⁻¹ * A * e) =
        h⁻¹ * (h * ρ k (dconj ((b k)⁻¹) e⁻¹ * A * e) * R) * R⁻¹ := by group
    have h2 : ρ k (dconj ((b k)⁻¹) e⁻¹ * A * e) ∈
        Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
      rw [h1]; exact mul_mem (mul_mem (inv_mem hT) hmem) (inv_mem hRN)
    exact (rho_mem_normalizer_iff_k hK2 k _).1 h2
  · intro hX
    exact mul_mem (mul_mem hT ((rho_mem_normalizer_iff_k hK2 k _).2 hX)) hRN

theorem eq_one_or_neg_of_central (hK2 : ringChar K ≠ 2) (Y : SL2 K)
    (hY : ∀ Z : SL2 K, Y * Z = Z * Y) : Y = 1 ∨ Y = HSL (-1) := by
  have hu := congrArg (fun Z : SL2 K => (Z : Matrix (Fin 2) (Fin 2) K)) (hY (uSL 1))
  have hv := congrArg (fun Z : SL2 K => (Z : Matrix (Fin 2) (Fin 2) K)) (hY (vSL 1))
  have hu00 := congrFun (congrFun hu 0) 0
  have hu01 := congrFun (congrFun hu 0) 1
  have hv00 := congrFun (congrFun hv 0) 0
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons] at hu00 hu01 hv00
  have h10 : (Y : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination -hu00
  have h01 : (Y : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by linear_combination hv00
  have h11 : (Y : Matrix (Fin 2) (Fin 2) K) 1 1 = (Y : Matrix (Fin 2) (Fin 2) K) 0 0 := by
    linear_combination -hu01
  have hdet := det_SL2 Y
  have hsq : ((Y : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * ((Y : Matrix (Fin 2) (Fin 2) K) 0 0 + 1) = 0 := by
    rw [h11, h01] at hdet
    linear_combination hdet
  rcases mul_eq_zero.1 hsq with h | h
  · left
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [h10, h01, h11, sub_eq_zero.1 h]
  · right
    have hm : (Y : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := by linear_combination h
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL, h10, h01, h11, hm]

theorem factor_sign (hK2 : ringChar K ≠ 2) (k : Fin Tag.D4.rank) (X X' : SL2 K) (R R' : ModGL Tag.D4 K)
    (hR : ∀ Y : SL2 K, Commute R (ρ k Y)) (hR' : ∀ Y : SL2 K, Commute R' (ρ k Y))
    (h : ρ k X * R = ρ k X' * R') : X'⁻¹ * X = 1 ∨ X'⁻¹ * X = HSL (-1) := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : SL2 K, Y = X'⁻¹ * X := ⟨_, rfl⟩
  have h1 : ρ k Y = R' * R⁻¹ := by
    rw [hYdef]
    calc ρ k (X'⁻¹ * X) = (ρ k X')⁻¹ * (ρ k X * R) * R⁻¹ := by rw [map_mul, map_inv]; group
      _ = (ρ k X')⁻¹ * (ρ k X' * R') * R⁻¹ := by rw [h]
      _ = R' * R⁻¹ := by group
  rw [← hYdef]
  refine eq_one_or_neg_of_central hK2 Y fun Z => ?_
  apply simpleRootSL2_injective hK2 k
  rw [map_mul, map_mul, h1]
  exact ((hR' Z).mul_left (hR Z).inv_left).eq

theorem prod_mul (b b' : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ A₀' A₁' A₃' : SL2 K) :
    (rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) *
        (rootDiagUnit Tag.D4 b' * (ρ 0 A₀' * (ρ 1 A₁' * ρ 3 A₃'))) =
      rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b' *
        (ρ 0 (dconj ((b' 0)⁻¹) A₀ * A₀') * (ρ 1 (dconj ((b' 1)⁻¹) A₁ * A₁') *
          ρ 3 (dconj ((b' 3)⁻¹) A₃ * A₃'))) := by
  set h' : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b' with hh'
  have hconj : ∀ (k : Fin Tag.D4.rank) (X : SL2 K), ρ k X * h' = h' * ρ k (dconj ((b' k)⁻¹) X) :=
    fun k X => by rw [← conj_inv_rho b' k X, ← hh']; group
  have e1 : (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h' = h' * (ρ 0 (dconj ((b' 0)⁻¹) A₀) *
      (ρ 1 (dconj ((b' 1)⁻¹) A₁) * ρ 3 (dconj ((b' 3)⁻¹) A₃))) := by
    calc (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h' = ρ 0 A₀ * (ρ 1 A₁ * (ρ 3 A₃ * h')) := by group
      _ = ρ 0 A₀ * (ρ 1 A₁ * (h' * ρ 3 (dconj ((b' 3)⁻¹) A₃))) := by rw [hconj 3]
      _ = ρ 0 A₀ * ((ρ 1 A₁ * h') * ρ 3 (dconj ((b' 3)⁻¹) A₃)) := by group
      _ = ρ 0 A₀ * ((h' * ρ 1 (dconj ((b' 1)⁻¹) A₁)) * ρ 3 (dconj ((b' 3)⁻¹) A₃)) := by
          rw [hconj 1]
      _ = (ρ 0 A₀ * h') * (ρ 1 (dconj ((b' 1)⁻¹) A₁) * ρ 3 (dconj ((b' 3)⁻¹) A₃)) := by group
      _ = (h' * ρ 0 (dconj ((b' 0)⁻¹) A₀)) * (ρ 1 (dconj ((b' 1)⁻¹) A₁) *
          ρ 3 (dconj ((b' 3)⁻¹) A₃)) := by rw [hconj 0]
      _ = _ := by group
  calc (rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) *
        (h' * (ρ 0 A₀' * (ρ 1 A₁' * ρ 3 A₃')))
      = rootDiagUnit Tag.D4 b * ((ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h') *
          (ρ 0 A₀' * (ρ 1 A₁' * ρ 3 A₃')) := by group
    _ = rootDiagUnit Tag.D4 b * (h' * (ρ 0 (dconj ((b' 0)⁻¹) A₀) *
          (ρ 1 (dconj ((b' 1)⁻¹) A₁) * ρ 3 (dconj ((b' 3)⁻¹) A₃)))) *
          (ρ 0 A₀' * (ρ 1 A₁' * ρ 3 A₃')) := by rw [e1]
    _ = rootDiagUnit Tag.D4 b * h' * ((ρ 0 (dconj ((b' 0)⁻¹) A₀) *
          (ρ 1 (dconj ((b' 1)⁻¹) A₁) * ρ 3 (dconj ((b' 3)⁻¹) A₃))) *
          (ρ 0 A₀' * (ρ 1 A₁' * ρ 3 A₃'))) := by group
    _ = rootDiagUnit Tag.D4 b * h' * ((ρ 0 (dconj ((b' 0)⁻¹) A₀) * ρ 0 A₀') *
          ((ρ 1 (dconj ((b' 1)⁻¹) A₁) * ρ 1 A₁') * (ρ 3 (dconj ((b' 3)⁻¹) A₃) * ρ 3 A₃'))) := by
          rw [mul_three_comm (comm01 _ _).symm (comm03 _ _).symm (comm13 _ _).symm]
    _ = _ := by rw [← map_mul, ← map_mul, ← map_mul]

theorem HSL_negOne_sq : HSL (-1 : Kˣ) * HSL (-1) = (1 : SL2 K) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem rho_negOne_eq {k : Fin Tag.D4.rank} (hk : k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    ρ k (HSL (-1)) = ρ 0 (HSL (-1)) := by
  have hc : ∀ j, ((-1 : Kˣ)) ^ Tag.D4.cartan k j = ((-1 : Kˣ)) ^ Tag.D4.cartan 0 j := by
    intro j
    have key : ∀ k : Fin Tag.D4.rank, k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) →
        ∀ j : Fin Tag.D4.rank, Even (Tag.D4.cartan k j - Tag.D4.cartan 0 j) := by decide
    obtain ⟨c, hc⟩ := key k hk j
    have : Tag.D4.cartan k j = Tag.D4.cartan 0 j + (c + c) := by omega
    rw [this, _root_.zpow_add, (Even.neg_one_zpow ⟨c, rfl⟩), mul_one]
  rw [simpleRootSL2_HSL, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  exact hc j

theorem HSL_negOne_ne_one (hK2 : ringChar K ≠ 2) : HSL (-1 : Kˣ) ≠ (1 : SL2 K) := by
  intro h
  have h00 := congrArg (fun Z : SL2 K => (Z : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_neg, Units.val_one,
    Matrix.one_apply_eq] at h00
  exact Ring.two_ne_zero hK2 (by linear_combination -h00)

theorem three_center {G : Type*} [Group G] {a b c ζ : G} (hb : Commute ζ b) (hc : Commute ζ c) :
    (a * ζ) * ((b * ζ) * (c * ζ)) = (a * (b * c)) * (ζ * ζ * ζ) := by
  calc (a * ζ) * ((b * ζ) * (c * ζ)) = a * ((ζ * b) * (ζ * c)) * ζ := by group
    _ = a * ((b * ζ) * (c * ζ)) * ζ := by rw [hb.eq, hc.eq]
    _ = a * (b * (ζ * c) * ζ) * ζ := by group
    _ = a * (b * (c * ζ) * ζ) * ζ := by rw [hc.eq]
    _ = (a * (b * c)) * (ζ * ζ * ζ) := by group

theorem exists_factor_eq (hK2 : ringChar K ≠ 2) (X₀ X₁ X₃ X₀' X₁' X₃' : SL2 K)
    (h : ρ 0 X₀ * (ρ 1 X₁ * ρ 3 X₃) = ρ 0 X₀' * (ρ 1 X₁' * ρ 3 X₃')) :
    X₀ = X₀' ∨ X₁ = X₁' ∨ X₃ = X₃' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h0, h1, h3⟩ := hcon
  have hperm1 : ∀ a b c : SL2 K, ρ 0 a * (ρ 1 b * ρ 3 c) = ρ 1 b * (ρ 0 a * ρ 3 c) := by
    intro a b c
    calc ρ 0 a * (ρ 1 b * ρ 3 c) = (ρ 0 a * ρ 1 b) * ρ 3 c := by group
      _ = (ρ 1 b * ρ 0 a) * ρ 3 c := by rw [(comm01 a b).eq]
      _ = _ := by group
  have hperm3 : ∀ a b c : SL2 K, ρ 0 a * (ρ 1 b * ρ 3 c) = ρ 3 c * (ρ 0 a * ρ 1 b) := by
    intro a b c
    calc ρ 0 a * (ρ 1 b * ρ 3 c) = ρ 0 a * (ρ 3 c * ρ 1 b) := by rw [(comm13 b c).eq]
      _ = (ρ 0 a * ρ 3 c) * ρ 1 b := by group
      _ = (ρ 3 c * ρ 0 a) * ρ 1 b := by rw [(comm03 a c).eq]
      _ = _ := by group
  have s0 : X₀'⁻¹ * X₀ = HSL (-1) := by
    rcases factor_sign hK2 0 X₀ X₀' (ρ 1 X₁ * ρ 3 X₃) (ρ 1 X₁' * ρ 3 X₃')
      (fun Y => (comm01 Y X₁).symm.mul_left (comm03 Y X₃).symm)
      (fun Y => (comm01 Y X₁').symm.mul_left (comm03 Y X₃').symm) h with e | e
    · exact absurd (inv_mul_eq_one.1 e).symm h0
    · exact e
  have s1 : X₁'⁻¹ * X₁ = HSL (-1) := by
    rw [hperm1, hperm1] at h
    rcases factor_sign hK2 1 X₁ X₁' (ρ 0 X₀ * ρ 3 X₃) (ρ 0 X₀' * ρ 3 X₃')
      (fun Y => (comm01 X₀ Y).mul_left (comm13 Y X₃).symm)
      (fun Y => (comm01 X₀' Y).mul_left (comm13 Y X₃').symm) h with e | e
    · exact absurd (inv_mul_eq_one.1 e).symm h1
    · exact e
  have s3 : X₃'⁻¹ * X₃ = HSL (-1) := by
    rw [hperm3, hperm3] at h
    rcases factor_sign hK2 3 X₃ X₃' (ρ 0 X₀ * ρ 1 X₁) (ρ 0 X₀' * ρ 1 X₁')
      (fun Y => (comm03 X₀ Y).mul_left (comm13 X₁ Y))
      (fun Y => (comm03 X₀' Y).mul_left (comm13 X₁' Y)) h with e | e
    · exact absurd (inv_mul_eq_one.1 e).symm h3
    · exact e
  have hX0 : X₀ = X₀' * HSL (-1) := by rw [← s0, mul_inv_cancel_left]
  have hX1 : X₁ = X₁' * HSL (-1) := by rw [← s1, mul_inv_cancel_left]
  have hX3 : X₃ = X₃' * HSL (-1) := by rw [← s3, mul_inv_cancel_left]
  rw [hX0, hX1, hX3, map_mul, map_mul, map_mul, rho_negOne_eq mem_outer1, rho_negOne_eq mem_outer3,
    three_center (comm01 _ _) (comm03 _ _)] at h
  have hζ3 : ρ 0 (HSL (-1)) * ρ 0 (HSL (-1)) * ρ 0 (HSL (-1)) = 1 :=
    mul_left_cancel (h.trans (mul_one _).symm)
  have hζ2 : ρ 0 (HSL (-1)) * ρ 0 (HSL (-1)) = 1 := by
    rw [← map_mul, HSL_negOne_sq, map_one]
  rw [hζ2, one_mul] at hζ3
  exact HSL_negOne_ne_one hK2 (simpleRootSL2_injective hK2 0 (hζ3.trans (map_one _).symm))

end Factor

end CFSG.LocalAnalysis.GLTheoremA
