module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL1

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even


section Two

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem exists_unit_of_diag {W : SL2 K} (w01 : (W : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (w10 : (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ u : Kˣ, W = HSL u ∧ ((u : Kˣ) : K) = (W : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  have hdetW := det_SL2 W
  rw [w01, w10] at hdetW
  have hW00 : (W : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h0; rw [h0] at hdetW; simp at hdetW
  refine ⟨Units.mk0 _ hW00, ?_, by simp⟩
  refine SL2_ext ?_ ?_ ?_ ?_
  · rfl
  · simp [coe_HSL, w01]
  · simp [coe_HSL, w10]
  · have : (W : Matrix (Fin 2) (Fin 2) K) 0 0 * (W : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
      linear_combination hdetW
    simp only [coe_HSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right this

theorem split_two (hK2 : ringChar K ≠ 2) {m : ModGL Tag.D4 K}
    (hm : m ∈ parabolicLevi Tag.D4 K ({2} : Set (Fin Tag.D4.rank))) (hm2 : m * m = 1) :
    ∃ e : SL2 K, ∀ c : K, ∃ c' : K,
      ((ρ 2 e)⁻¹ * m * ρ 2 e) * xUnit Tag.D4 K 2 c * ((ρ 2 e)⁻¹ * m * ρ 2 e)⁻¹ =
        xUnit Tag.D4 K 2 c' := by
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm
  have hl' : l ∈ (ρ 2).range := by
    rw [range_simpleRootSL2, ← leviRoot_singleton]; exact hl
  obtain ⟨A, rfl⟩ := hl'
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  have hmm : (h * ρ 2 A) * (h * ρ 2 A) = h ^ 2 * ρ 2 (dconj ((b 2)⁻¹) A * A) := by
    have e1 : ρ 2 A * h = h * ρ 2 (dconj ((b 2)⁻¹) A) := by
      rw [← conj_inv_rho b 2 A, ← hh]; group
    calc (h * ρ 2 A) * (h * ρ 2 A) = h * (ρ 2 A * h) * ρ 2 A := by group
      _ = h * (h * ρ 2 (dconj ((b 2)⁻¹) A)) * ρ 2 A := by rw [e1]
      _ = h ^ 2 * (ρ 2 (dconj ((b 2)⁻¹) A) * ρ 2 A) := by rw [pow_two]; group
      _ = h ^ 2 * ρ 2 (dconj ((b 2)⁻¹) A * A) := by rw [map_mul]
  have hhW : h ^ 2 * ρ 2 (dconj ((b 2)⁻¹) A * A) = 1 := by rw [← hmm]; exact hm2
  obtain ⟨w01, w10, w11⟩ := factor_diag hK2 b 2 (dconj ((b 2)⁻¹) A * A) 1
    (fun X => Commute.one_left _) (by rw [mul_one]; exact hhW)
  obtain ⟨u, hWu, hu⟩ := exists_unit_of_diag w01 w10
  have hρW : ρ 2 (dconj ((b 2)⁻¹) A * A) = torusElt Tag.D4 K 2 u := by rw [hWu, simpleRootSL2_HSL]
  have hrel : rootDiagUnit Tag.D4 (b * b * fun i => u ^ Tag.D4.cartan 2 i) = 1 := by
    rw [rootDiagUnit_mul, rootDiagUnit_mul, ← torusElt_eq_rootDiagUnit, ← hρW, ← pow_two]
    exact hhW
  have hu0 := rootDiagUnit_eq_one_apply hrel 0
  have hcart : Tag.D4.cartan 2 0 = -1 := by decide
  simp only [Pi.mul_apply, hcart, _root_.zpow_neg, _root_.zpow_one] at hu0
  have hub : u = b 0 * b 0 := (eq_of_mul_inv_eq_one (show (b 0 * b 0) * u⁻¹ = 1 from hu0)).symm
  have hW00b : ((dconj ((b 2)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((b 0 : Kˣ) : K) ^ 2 := by
    rw [← hu, hub]; simp [sq]
  obtain ⟨e, he⟩ := exists_upper (b 2) A w01 w10 w11 ((b 0 : Kˣ) : K) hW00b
  refine ⟨e, fun c => ?_⟩
  simpa only [mul_one] using normalizes_of_upper b 2 A e 1 (fun Y => Commute.one_left _) he c

end Two

section Three

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem levi_outer_decomp {m : ModGL Tag.D4 K}
    (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank))) :
    ∃ (b : Fin Tag.D4.rank → Kˣ) (A₀ A₁ A₃ : SL2 K),
      m = rootDiagUnit Tag.D4 b * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) := by
  obtain ⟨b, l, hl, rfl⟩ := exists_eq_rootDiagUnit_mul hm
  have hl' : l ∈ (outerHom K).range := leviRoot_outer_le_range K hl
  obtain ⟨⟨A₀, A₁, A₃⟩, rfl⟩ := hl'
  exact ⟨b, A₀, A₁, A₃, by rw [outerHom_apply]; rfl⟩


theorem mem_outer0 : (0 : Fin Tag.D4.rank) ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) := Set.mem_insert _ _
theorem mem_outer1 : (1 : Fin Tag.D4.rank) ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) :=
  Set.mem_insert_of_mem _ (Set.mem_insert _ _)
theorem mem_outer3 : (3 : Fin Tag.D4.rank) ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) :=
  Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

theorem comm01 (X Y : SL2 K) : Commute (ρ 0 X) (ρ 1 Y) :=
  commute_rho_outer mem_outer0 mem_outer1 (by decide) X Y
theorem comm03 (X Y : SL2 K) : Commute (ρ 0 X) (ρ 3 Y) :=
  commute_rho_outer mem_outer0 mem_outer3 (by decide) X Y
theorem comm13 (X Y : SL2 K) : Commute (ρ 1 X) (ρ 3 Y) :=
  commute_rho_outer mem_outer1 mem_outer3 (by decide) X Y

theorem mul_three_comm {G : Type*} [Group G] {a₀ a₁ a₃ b₀ b₁ b₃ : G}
    (h10 : Commute a₁ b₀) (h30 : Commute a₃ b₀) (h31 : Commute a₃ b₁) :
    (a₀ * (a₁ * a₃)) * (b₀ * (b₁ * b₃)) = (a₀ * b₀) * ((a₁ * b₁) * (a₃ * b₃)) := by
  calc (a₀ * (a₁ * a₃)) * (b₀ * (b₁ * b₃)) = a₀ * (a₁ * (a₃ * b₀) * (b₁ * b₃)) := by group
    _ = a₀ * (a₁ * (b₀ * a₃) * (b₁ * b₃)) := by rw [h30.eq]
    _ = a₀ * ((a₁ * b₀) * (a₃ * b₁ * b₃)) := by group
    _ = a₀ * ((b₀ * a₁) * (b₁ * a₃ * b₃)) := by rw [h10.eq, h31.eq]
    _ = _ := by group

theorem factor_unit (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank)
    (A : SL2 K) (R' : ModGL Tag.D4 K) (hR' : ∀ Y : SL2 K, Commute R' (ρ k Y))
    (h : rootDiagUnit Tag.D4 b ^ 2 * (ρ k (dconj ((b k)⁻¹) A * A) * R') = 1) :
    (((dconj ((b k)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      ((dconj ((b k)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      ((dconj ((b k)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
        ((b k : Kˣ) : K) ^ 2 * ((dconj ((b k)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0) ∧
    ∃ u : Kˣ, ρ k (dconj ((b k)⁻¹) A * A) = torusElt Tag.D4 K k u ∧
      ((u : Kˣ) : K) = ((dconj ((b k)⁻¹) A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  obtain ⟨w01, w10, w11⟩ := factor_diag hK2 b k _ R' hR' h
  obtain ⟨u, hWu, hu⟩ := exists_unit_of_diag w01 w10
  exact ⟨⟨w01, w10, w11⟩, u, by rw [hWu, simpleRootSL2_HSL], hu⟩

theorem isSquare_of_three (hK2 : ringChar K ≠ 2) {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : IsSquare (x * y * z)) : IsSquare x ∨ IsSquare y ∨ IsSquare z := by
  classical
  haveI := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  obtain ⟨hx', hy', hz'⟩ := hcon
  have hxy := (quadraticChar_neg_one_iff_not_isSquare (F := K)).2 hx'
  have hyy := (quadraticChar_neg_one_iff_not_isSquare (F := K)).2 hy'
  have hzz := (quadraticChar_neg_one_iff_not_isSquare (F := K)).2 hz'
  have hxyz : x * y * z ≠ 0 := mul_ne_zero (mul_ne_zero hx hy) hz
  have hone := (quadraticChar_one_iff_isSquare hxyz).2 h
  rw [map_mul, map_mul, hxy, hyy, hzz] at hone
  norm_num at hone

theorem split_three (hK2 : ringChar K ≠ 2) {m : ModGL Tag.D4 K}
    (hm : m ∈ parabolicLevi Tag.D4 K ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hm2 : m * m = 1) :
    ∃ k : Fin Tag.D4.rank, k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∧ ∃ e : SL2 K, ∀ c : K, ∃ c' : K,
      ((ρ k e)⁻¹ * m * ρ k e) * xUnit Tag.D4 K k c * ((ρ k e)⁻¹ * m * ρ k e)⁻¹ =
        xUnit Tag.D4 K k c' := by
  obtain ⟨b, A₀, A₁, A₃, rfl⟩ := levi_outer_decomp hm
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  have hconj : ∀ (k : Fin Tag.D4.rank) (X : SL2 K), ρ k X * h = h * ρ k (dconj ((b k)⁻¹) X) :=
    fun k X => by rw [← conj_inv_rho b k X, ← hh]; group
  set W₀ : SL2 K := dconj ((b 0)⁻¹) A₀ * A₀ with hW₀
  set W₁ : SL2 K := dconj ((b 1)⁻¹) A₁ * A₁ with hW₁
  set W₃ : SL2 K := dconj ((b 3)⁻¹) A₃ * A₃ with hW₃
  have hmm : (h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) * (h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) =
      h ^ 2 * (ρ 0 W₀ * (ρ 1 W₁ * ρ 3 W₃)) := by
    have e1 : (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h = h * (ρ 0 (dconj ((b 0)⁻¹) A₀) *
        (ρ 1 (dconj ((b 1)⁻¹) A₁) * ρ 3 (dconj ((b 3)⁻¹) A₃))) := by
      calc (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h = ρ 0 A₀ * (ρ 1 A₁ * (ρ 3 A₃ * h)) := by group
        _ = ρ 0 A₀ * (ρ 1 A₁ * (h * ρ 3 (dconj ((b 3)⁻¹) A₃))) := by rw [hconj 3]
        _ = ρ 0 A₀ * ((ρ 1 A₁ * h) * ρ 3 (dconj ((b 3)⁻¹) A₃)) := by group
        _ = ρ 0 A₀ * ((h * ρ 1 (dconj ((b 1)⁻¹) A₁)) * ρ 3 (dconj ((b 3)⁻¹) A₃)) := by
            rw [hconj 1]
        _ = (ρ 0 A₀ * h) * (ρ 1 (dconj ((b 1)⁻¹) A₁) * ρ 3 (dconj ((b 3)⁻¹) A₃)) := by group
        _ = (h * ρ 0 (dconj ((b 0)⁻¹) A₀)) * (ρ 1 (dconj ((b 1)⁻¹) A₁) *
            ρ 3 (dconj ((b 3)⁻¹) A₃)) := by rw [hconj 0]
        _ = _ := by group
    calc (h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) * (h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)))
        = h * ((ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) * h) * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) := by group
      _ = h * (h * (ρ 0 (dconj ((b 0)⁻¹) A₀) * (ρ 1 (dconj ((b 1)⁻¹) A₁) *
          ρ 3 (dconj ((b 3)⁻¹) A₃)))) * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) := by rw [e1]
      _ = h ^ 2 * ((ρ 0 (dconj ((b 0)⁻¹) A₀) * (ρ 1 (dconj ((b 1)⁻¹) A₁) *
          ρ 3 (dconj ((b 3)⁻¹) A₃))) * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃))) := by rw [pow_two]; group
      _ = h ^ 2 * ((ρ 0 (dconj ((b 0)⁻¹) A₀) * ρ 0 A₀) * ((ρ 1 (dconj ((b 1)⁻¹) A₁) * ρ 1 A₁) *
          (ρ 3 (dconj ((b 3)⁻¹) A₃) * ρ 3 A₃))) := by
          rw [mul_three_comm (comm01 _ _).symm (comm03 _ _).symm (comm13 _ _).symm]
      _ = h ^ 2 * (ρ 0 W₀ * (ρ 1 W₁ * ρ 3 W₃)) := by rw [hW₀, hW₁, hW₃, map_mul, map_mul, map_mul]
  have hW : h ^ 2 * (ρ 0 W₀ * (ρ 1 W₁ * ρ 3 W₃)) = 1 := by rw [← hmm]; exact hm2
  have hR0 : ∀ Y : SL2 K, Commute (ρ 1 W₁ * ρ 3 W₃) (ρ 0 Y) := fun Y =>
    (comm01 Y W₁).symm.mul_left (comm03 Y W₃).symm
  have hR1 : ∀ Y : SL2 K, Commute (ρ 0 W₀ * ρ 3 W₃) (ρ 1 Y) := fun Y =>
    (comm01 W₀ Y).mul_left (comm13 Y W₃).symm
  have hR3 : ∀ Y : SL2 K, Commute (ρ 0 W₀ * ρ 1 W₁) (ρ 3 Y) := fun Y =>
    (comm03 W₀ Y).mul_left (comm13 W₁ Y)
  have hW1 : h ^ 2 * (ρ 1 W₁ * (ρ 0 W₀ * ρ 3 W₃)) = 1 := by
    rw [← hW]
    congr 1
    calc ρ 1 W₁ * (ρ 0 W₀ * ρ 3 W₃) = (ρ 1 W₁ * ρ 0 W₀) * ρ 3 W₃ := by group
      _ = (ρ 0 W₀ * ρ 1 W₁) * ρ 3 W₃ := by rw [(comm01 W₀ W₁).eq]
      _ = _ := by group
  have hW3 : h ^ 2 * (ρ 3 W₃ * (ρ 0 W₀ * ρ 1 W₁)) = 1 := by
    rw [← hW]
    congr 1
    calc ρ 3 W₃ * (ρ 0 W₀ * ρ 1 W₁) = (ρ 3 W₃ * ρ 0 W₀) * ρ 1 W₁ := by group
      _ = (ρ 0 W₀ * ρ 3 W₃) * ρ 1 W₁ := by rw [(comm03 W₀ W₃).eq]
      _ = ρ 0 W₀ * (ρ 3 W₃ * ρ 1 W₁) := by group
      _ = ρ 0 W₀ * (ρ 1 W₁ * ρ 3 W₃) := by rw [(comm13 W₁ W₃).eq]
  obtain ⟨⟨w0₀₁, w0₁₀, w0₁₁⟩, u₀, hρ₀, hu₀⟩ := factor_unit hK2 b 0 A₀ _ hR0 hW
  obtain ⟨⟨w1₀₁, w1₁₀, w1₁₁⟩, u₁, hρ₁, hu₁⟩ := factor_unit hK2 b 1 A₁ _ hR1 hW1
  obtain ⟨⟨w3₀₁, w3₁₀, w3₁₁⟩, u₃, hρ₃, hu₃⟩ := factor_unit hK2 b 3 A₃ _ hR3 hW3
  have hrel : rootDiagUnit Tag.D4 (b * b * ((fun i => u₀ ^ Tag.D4.cartan 0 i) *
      ((fun i => u₁ ^ Tag.D4.cartan 1 i) * (fun i => u₃ ^ Tag.D4.cartan 3 i)))) = 1 := by
    simp only [rootDiagUnit_mul]
    rw [← torusElt_eq_rootDiagUnit, ← torusElt_eq_rootDiagUnit, ← torusElt_eq_rootDiagUnit,
      ← hρ₀, ← hρ₁, ← hρ₃, ← pow_two]
    exact hW
  have hu2 := rootDiagUnit_eq_one_apply hrel 2
  have hc0 : Tag.D4.cartan 0 2 = -1 := by decide
  have hc1 : Tag.D4.cartan 1 2 = -1 := by decide
  have hc3 : Tag.D4.cartan 3 2 = -1 := by decide
  simp only [Pi.mul_apply, hc0, hc1, hc3, _root_.zpow_neg, _root_.zpow_one] at hu2
  have hprod : ((u₀ : Kˣ) : K) * ((u₁ : Kˣ) : K) * ((u₃ : Kˣ) : K) = ((b 2 : Kˣ) : K) ^ 2 := by
    have : u₀ * u₁ * u₃ = b 2 * b 2 := by
      have h' : (b 2 * b 2) * (u₀⁻¹ * (u₁⁻¹ * u₃⁻¹)) = 1 := hu2
      have h'' : (b 2 * b 2) * (u₀ * u₁ * u₃)⁻¹ = 1 := by
        rw [← h']; congr 1; simp [mul_comm, mul_left_comm, mul_assoc]
      exact (eq_of_mul_inv_eq_one h'').symm
    have := congrArg (fun x : Kˣ => (x : K)) this
    simpa [sq] using this
  rcases isSquare_of_three hK2 (Units.ne_zero u₀) (Units.ne_zero u₁) (Units.ne_zero u₃)
    ⟨((b 2 : Kˣ) : K), by rw [hprod]; ring⟩ with ⟨ω, hω⟩ | ⟨ω, hω⟩ | ⟨ω, hω⟩
  · obtain ⟨e, he⟩ := exists_upper (b 0) A₀ w0₀₁ w0₁₀ w0₁₁ ω (by rw [← hu₀, hω]; ring)
    exact ⟨0, mem_outer0, e, fun c => normalizes_of_upper b 0 A₀ e (ρ 1 A₁ * ρ 3 A₃)
      (fun Y => (comm01 Y A₁).symm.mul_left (comm03 Y A₃).symm) he c⟩
  · obtain ⟨e, he⟩ := exists_upper (b 1) A₁ w1₀₁ w1₁₀ w1₁₁ ω (by rw [← hu₁, hω]; ring)
    refine ⟨1, mem_outer1, e, fun c => ?_⟩
    have hm1 : h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) = h * (ρ 1 A₁ * (ρ 0 A₀ * ρ 3 A₃)) := by
      congr 1
      calc ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃) = (ρ 0 A₀ * ρ 1 A₁) * ρ 3 A₃ := by group
        _ = (ρ 1 A₁ * ρ 0 A₀) * ρ 3 A₃ := by rw [(comm01 A₀ A₁).eq]
        _ = _ := by group
    rw [hm1]
    exact normalizes_of_upper b 1 A₁ e (ρ 0 A₀ * ρ 3 A₃)
      (fun Y => (comm01 A₀ Y).mul_left (comm13 Y A₃).symm) he c
  · obtain ⟨e, he⟩ := exists_upper (b 3) A₃ w3₀₁ w3₁₀ w3₁₁ ω (by rw [← hu₃, hω]; ring)
    refine ⟨3, mem_outer3, e, fun c => ?_⟩
    have hm3 : h * (ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃)) = h * (ρ 3 A₃ * (ρ 0 A₀ * ρ 1 A₁)) := by
      congr 1
      calc ρ 0 A₀ * (ρ 1 A₁ * ρ 3 A₃) = ρ 0 A₀ * (ρ 3 A₃ * ρ 1 A₁) := by rw [(comm13 A₁ A₃).eq]
        _ = (ρ 0 A₀ * ρ 3 A₃) * ρ 1 A₁ := by group
        _ = (ρ 3 A₃ * ρ 0 A₀) * ρ 1 A₁ := by rw [(comm03 A₀ A₃).eq]
        _ = _ := by group
    rw [hm3]
    exact normalizes_of_upper b 3 A₃ e (ρ 0 A₀ * ρ 1 A₁)
      (fun Y => (comm03 A₀ Y).mul_left (comm13 A₁ Y)) he c

end Three



end CFSG.LocalAnalysis.GLTheoremA
