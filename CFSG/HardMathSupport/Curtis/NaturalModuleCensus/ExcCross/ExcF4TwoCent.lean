module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwNFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcF4TwoData
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTitsLift
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4Cent
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.F4Two

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Curtis.UnitaryLevi (SM wordW wordW_append laF lbF wa wb QF4 QF4_comm
  QF4_cube QF4_pGroup nine_dvd_QF4 wa_mem_QF4 wb_mem_QF4 exists_conj_mem_QF4 mem_QF4 wa_cube
  wb_cube wa_wb_comm inv_eq_sq_of_cube inv_wa_wb inv_wa_wb_wb pair_nine card_centralizer_conj
  wordW_cube_of wordW_comm_of pair_comm_of_closure solve_int_fpf)

section Abstract

variable {G : Type} [Group G] {W : Type} [Group W] {r : ℕ} {C : Type} [CommGroup C] [IsCyclic C]
variable (ι : (Fin r → C) →* G) (π : G →* W) (A : W → Matrix (Fin r) (Fin r) ℤ)
variable (hι : Function.Injective ι)
  (hker : ∀ g : G, π g = 1 → g ∈ ι.range) (hιπ : ∀ t, π (ι t) = 1)
  (hconj : ∀ (g : G) (t : Fin r → C), g * ι t * g⁻¹ = ι (mactC (A (π g)) t))

include hker hιπ hconj in
theorem exists_fixed_point (x y₁ y₂ : W) (gx g₁ gx' g₂ : G) (hgx : π gx = x) (hg₁ : π g₁ = y₁)
    (hc₁ : g₁ * gx = gx * g₁) (hgx' : π gx' = x) (hg₂ : π g₂ = y₂) (hc₂ : g₂ * gx' = gx' * g₂)
    (hpoint : ∀ κ : Fin r → ℤ, ∃ c d₁ d₂ : Fin r → ℤ,
      (1 - A x).mulVec d₁ = (1 - A y₁).mulVec c ∧
      (1 - A x).mulVec d₂ = (1 - A y₂).mulVec (c - κ)) :
    ∃ sp : G, π sp = x ∧ ∀ y ∈ Subgroup.closure ({y₁, y₂} : Set W),
      ∃ c ∈ Subgroup.centralizer ({sp} : Set G), π c = y := by
  obtain ⟨k, hk⟩ := exists_decomp_ab ι π hker (hgx'.trans hgx.symm)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hkc : ∀ j, ∃ m : ℤ, g ^ m = k j := fun j => Subgroup.mem_zpowers_iff.1 (hg (k j))
  choose κ hκ using hkc
  have hkk : k = vecTC κ g := funext fun j => (hκ j).symm
  obtain ⟨c, d₁, d₂, h₁, h₂⟩ := hpoint κ
  have vsub : ∀ u v : Fin r → ℤ, vecTC u g * (vecTC v g)⁻¹ = vecTC (u - v) g := by
    intro u v
    ext j
    simp [vecTC, zpow_sub]
  have key : ∀ (d c' : Fin r → ℤ) (Y : Matrix (Fin r) (Fin r) ℤ),
      (1 - A x).mulVec d = (1 - Y).mulVec c' →
      vecTC d g * (mactC (A x) (vecTC d g))⁻¹ = vecTC c' g * (mactC Y (vecTC c' g))⁻¹ := by
    intro d c' Y h
    rw [← mactC_one_sub, ← mactC_one_sub, mactC_vecTC, mactC_vecTC, h]
  obtain ⟨sp, hsp⟩ : ∃ sp : G, sp = ι (vecTC c g) * gx := ⟨_, rfl⟩
  have hπsp : π sp = x := by rw [hsp, map_mul, hιπ, one_mul, hgx]
  obtain ⟨hm1, hp1⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj (vecTC c g) 1 (vecTC d₁ g)
    (s := sp) (gx := gx) (gy := g₁) hsp
    (by rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hc₁])
    (by rw [hgx, hg₁, inv_one, mul_one]; exact key d₁ c (A y₁) h₁)
  obtain ⟨hm2, hp2⟩ := lift_centralizer_of_solve_ab ι π A hιπ hconj (vecTC c g * k⁻¹) 1
    (vecTC d₂ g) (s := sp) (gx := gx') (gy := g₂)
    (by rw [hsp, hk, ← mul_assoc, ← map_mul, inv_mul_cancel_right])
    (by rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hc₂])
    (by rw [hgx', hg₂, inv_one, mul_one, hkk, vsub]; exact key d₂ (c - κ) (A y₂) h₂)
  refine ⟨sp, hπsp, fun y hy => ?_⟩
  have hle : Subgroup.closure ({y₁, y₂} : Set W) ≤
      (Subgroup.centralizer ({sp} : Set G)).map π := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hm1, hp1.trans hg₁⟩
    · exact ⟨_, hm2, hp2.trans hg₂⟩
  obtain ⟨c', hc', hπ⟩ := hle hy
  exact ⟨c', hc', hπ⟩

include hι hker hιπ hconj in
theorem caseB_pair {n : ℕ} (x y₁ y₂ : W) (ys : Fin n → W)
    (hys : ∀ i, ys i ∈ Subgroup.closure ({y₁, y₂} : Set W)) (s gx g₁ gx' g₂ : G)
    (hs : π s = x) (hgx : π gx = x) (hg₁ : π g₁ = y₁) (hc₁ : g₁ * gx = gx * g₁)
    (hgx' : π gx' = x) (hg₂ : π g₂ = y₂) (hc₂ : g₂ * gx' = gx' * g₂)
    (hpoint : ∀ κ : Fin r → ℤ, ∃ c d₁ d₂ : Fin r → ℤ,
      (1 - A x).mulVec d₁ = (1 - A y₁).mulVec c ∧
      (1 - A x).mulVec d₂ = (1 - A y₂).mulVec (c - κ))
    (Ξ : Matrix (Fin r) (Fin r) ℤ) (hΞ : (1 - A x) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin r → ℤ, ∃ i : Fin n, ∃ d : Fin r → ℤ,
      (1 - A x).mulVec d = (1 - A (ys i)).mulVec c)
    (ω : C) (hω : orderOf ω = 3) (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((A x).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure ({x, ys i} : Set W))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) := by
  obtain ⟨sp, hsp, hlift⟩ := exists_fixed_point ι π A hker hιπ hconj x y₁ y₂ gx g₁ gx' g₂ hgx hg₁
    hc₁ hgx' hg₂ hc₂ hpoint
  choose cc hcc hcπ using fun i => hlift (ys i) (hys i)
  exact caseB_ab ι π A hι hker hιπ hconj x ys s sp hs hsp
    (fun i => ⟨cc i, hcπ i, Subgroup.mem_centralizer_singleton_iff.1 (hcc i)⟩) Ξ hΞ hsolve ω hω
    c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12 h21 h22 hQ

end Abstract

section PointInt

theorem pair_point_int (X Y₁ Y₂ Θ : Matrix (Fin 4) (Fin 4) ℤ) (e₂ e₃ l₂ l₃ : Fin 4 → ℤ)
    (D1 : (1 - X) * Θ + Matrix.vecMulVec e₂ l₂ + Matrix.vecMulVec e₃ l₃ = 1)
    (hY₂ : X * Y₂ = Y₂ * X) (d₁ d₃ : Fin 4 → ℤ)
    (h₁ : (1 - X).mulVec d₁ = (1 - Y₁).mulVec e₂)
    (h₃ : (1 - X).mulVec d₃ = (1 - Y₂).mulVec e₃) (κ : Fin 4 → ℤ) :
    ∃ c d₁' d₂' : Fin 4 → ℤ, (1 - X).mulVec d₁' = (1 - Y₁).mulVec c ∧
      (1 - X).mulVec d₂' = (1 - Y₂).mulVec (c - κ) := by
  obtain ⟨m₂, hm₂⟩ : ∃ m, m = l₂ ⬝ᵥ κ := ⟨_, rfl⟩
  obtain ⟨m₃, hm₃⟩ : ∃ m, m = l₃ ⬝ᵥ κ := ⟨_, rfl⟩
  have hκ : κ = (1 - X).mulVec (Θ.mulVec κ) + m₂ • e₂ + m₃ • e₃ := by
    have h1 : κ = ((1 - X) * Θ + Matrix.vecMulVec e₂ l₂ + Matrix.vecMulVec e₃ l₃).mulVec κ := by
      rw [D1, Matrix.one_mulVec]
    have h2 : ((1 - X) * Θ + Matrix.vecMulVec e₂ l₂ + Matrix.vecMulVec e₃ l₃).mulVec κ =
        (1 - X).mulVec (Θ.mulVec κ) + m₂ • e₂ + m₃ • e₃ := by
      rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.vecMulVec_mulVec,
        Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul, hm₂, hm₃]
    exact h1.trans h2
  have hcomm : (1 - X) * (1 - Y₂) = (1 - Y₂) * (1 - X) := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hY₂]
    abel
  have e : m₂ • e₂ - κ = -((1 - X).mulVec (Θ.mulVec κ)) - m₃ • e₃ := by
    calc m₂ • e₂ - κ = m₂ • e₂ - ((1 - X).mulVec (Θ.mulVec κ) + m₂ • e₂ + m₃ • e₃) := by
          rw [← hκ]
      _ = _ := by abel
  have hP : (1 - X).mulVec ((1 - Y₂).mulVec (Θ.mulVec κ)) =
      (1 - Y₂).mulVec ((1 - X).mulVec (Θ.mulVec κ)) := by
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  refine ⟨m₂ • e₂, m₂ • d₁, -((1 - Y₂).mulVec (Θ.mulVec κ)) - m₃ • d₃, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h₁]
  · rw [e, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_neg,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hP, h₃]

end PointInt

section WeylFacts


theorem isPGroup_closure_pair {a b : WeylGroup Tag.F4} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) : IsPGroup 3 (Subgroup.closure ({a, b} : Set (WeylGroup Tag.F4))) := by
  have hcomm := pair_comm_of_closure a b hab
  have hcube : ∀ x ∈ Subgroup.closure ({a, b} : Set (WeylGroup Tag.F4)), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => rcases hy with rfl | rfl; exact ha; exact hb
    | one => simp
    | mul u v hu hv hu3 hv3 =>
      rw [(show Commute u v from hcomm u hu v hv).mul_pow, hu3, hv3, one_mul]
    | inv u hu hu3 => simp [inv_pow, hu3]
  exact fun x => ⟨1, by
    ext
    simpa using hcube x x.2⟩

@[expose] def twL2AB : List (Fin Tag.F4.rank) :=
  ([0, 1, 0, 2, 1, 0, 2, 3, 2, 1] : List (Fin 4))

@[expose] def twL2AB2 : List (Fin Tag.F4.rank) := ([0, 1, 2, 1, 0, 2, 3, 2] : List (Fin 4))

@[expose] def twZsAB : Fin 4 → List (Fin Tag.F4.rank) :=
  ![laF, twL2AB, laF ++ twL2AB ++ laF ++ laF, laF ++ laF ++ twL2AB ++ laF]

@[expose] def twZsAB2 : Fin 4 → List (Fin Tag.F4.rank) :=
  ![laF, twL2AB2, laF ++ laF ++ twL2AB2 ++ laF, laF ++ twL2AB2 ++ laF ++ laF]

theorem twZsAB_W :
    (SM (twLAB ++ twLAB ++ twLAB) = SM [] ∧ SM twLAB ≠ SM []) ∧ ∀ i : Fin 4,
      SM (twZsAB i ++ twZsAB i ++ twZsAB i) = SM [] ∧ SM (twZsAB i) ≠ SM twLAB ∧
      SM (twZsAB i) ≠ SM [] ∧ SM (twZsAB i) ≠ SM (twLAB ++ twLAB) ∧
      SM (twLAB ++ twZsAB i) = SM (twZsAB i ++ twLAB) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

theorem twZsAB2_W :
    (SM (twLAB2 ++ twLAB2 ++ twLAB2) = SM [] ∧ SM twLAB2 ≠ SM []) ∧ ∀ i : Fin 4,
      SM (twZsAB2 i ++ twZsAB2 i ++ twZsAB2 i) = SM [] ∧ SM (twZsAB2 i) ≠ SM twLAB2 ∧
      SM (twZsAB2 i) ≠ SM [] ∧ SM (twZsAB2 i) ≠ SM (twLAB2 ++ twLAB2) ∧
      SM (twLAB2 ++ twZsAB2 i) = SM (twZsAB2 i ++ twLAB2) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

theorem twZsAB_mem (i : Fin 4) : wordW Tag.F4 (twZsAB i) ∈
    Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB} : Set (WeylGroup Tag.F4)) := by
  have h1 : wordW Tag.F4 laF ∈
      Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB} : Set (WeylGroup Tag.F4)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : wordW Tag.F4 twL2AB ∈
      Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB} : Set (WeylGroup Tag.F4)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases i
  · exact h1
  · exact h2
  · show wordW Tag.F4 (laF ++ twL2AB ++ laF ++ laF) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h2) h1) h1
  · show wordW Tag.F4 (laF ++ laF ++ twL2AB ++ laF) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h1) h2) h1

theorem twZsAB2_mem (i : Fin 4) : wordW Tag.F4 (twZsAB2 i) ∈
    Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB2} : Set (WeylGroup Tag.F4)) := by
  have h1 : wordW Tag.F4 laF ∈
      Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB2} : Set (WeylGroup Tag.F4)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : wordW Tag.F4 twL2AB2 ∈
      Subgroup.closure ({wordW Tag.F4 laF, wordW Tag.F4 twL2AB2} : Set (WeylGroup Tag.F4)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  fin_cases i
  · exact h1
  · exact h2
  · show wordW Tag.F4 (laF ++ laF ++ twL2AB2 ++ laF) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h1) h2) h1
  · show wordW Tag.F4 (laF ++ twL2AB2 ++ laF ++ laF) ∈ _
    rw [wordW_append, wordW_append, wordW_append]
    exact mul_mem (mul_mem (mul_mem h1 h2) h1) h1

end WeylFacts

section Data

theorem twZ_ab_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - ATw twLAB).mulVec d = (1 - ATw (twZsAB i)).mulVec
      (((a : ℕ) : ℤ) • ![-1, -1, -1, 0] + ((b : ℕ) : ℤ) • ![-1, 0, -1, -1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![0, -4, 2, 0], by decide +kernel⟩
  · exact ⟨1, ![0, -8, 4, 0], by decide +kernel⟩
  · exact ⟨0, ![-1, -1, 1, 0], by decide +kernel⟩
  · exact ⟨2, ![6, 0, -3, 0], by decide +kernel⟩
  · exact ⟨3, ![-14, 10, -3, -2], by decide +kernel⟩
  · exact ⟨0, ![-2, -2, 2, 0], by decide +kernel⟩
  · exact ⟨3, ![-14, 10, -3, -2], by decide +kernel⟩
  · exact ⟨2, ![12, 0, -6, 0], by decide +kernel⟩

theorem twZ_ab_data :
    (∀ i : Fin 4, ATw twLAB * ATw (twZsAB i) = ATw (twZsAB i) * ATw twLAB) ∧
    ((1 - ATw twLAB).mulVec ![-1, -1, 1, 0] = (1 - ATw laF).mulVec ![-1, -1, -1, 0]) ∧
    ((1 - ATw twLAB).mulVec ![0, -4, 2, 0] = (1 - ATw twL2AB).mulVec ![-1, 0, -1, -1]) ∧
    (ATw twLAB * ATw twL2AB = ATw twL2AB * ATw twLAB) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem twZ_ab_solve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - ATw twLAB).mulVec d = (1 - ATw (twZsAB i)).mulVec c := by
  obtain ⟨D1, D2, D3, -, -, -, -⟩ := twB_ab_data
  exact solve_int_fpf (ATw twLAB) (fun i => ATw (twZsAB i)) twZ_ab_data.1 _ _ _ _ _ _ _ D1 D2 D3
    twZ_ab_tab

theorem twZ_ab_point : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
    (1 - ATw twLAB).mulVec d₁ = (1 - ATw laF).mulVec c ∧
    (1 - ATw twLAB).mulVec d₂ = (1 - ATw twL2AB).mulVec (c - κ) := by
  obtain ⟨D1, -, -, -, -, -, -⟩ := twB_ab_data
  obtain ⟨-, h₁, h₃, hY⟩ := twZ_ab_data
  exact pair_point_int _ _ _ _ _ _ _ _ D1 hY _ _ h₁ h₃

theorem twZ_ab2_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - ATw twLAB2).mulVec d = (1 - ATw (twZsAB2 i)).mulVec
      (((a : ℕ) : ℤ) • ![-1, -1, -1, -1] + ((b : ℕ) : ℤ) • ![-1, 0, -1, -1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![-4, 0, 0, 2], by decide +kernel⟩
  · exact ⟨1, ![-8, 0, 0, 4], by decide +kernel⟩
  · exact ⟨0, ![-1, -1, 1, 0], by decide +kernel⟩
  · exact ⟨2, ![2, 6, -7, 3], by decide +kernel⟩
  · exact ⟨3, ![12, -16, 2, 6], by decide +kernel⟩
  · exact ⟨0, ![-2, -2, 2, 0], by decide +kernel⟩
  · exact ⟨3, ![14, -18, 2, 7], by decide +kernel⟩
  · exact ⟨2, ![4, 12, -14, 6], by decide +kernel⟩

theorem twZ_ab2_data :
    (∀ i : Fin 4, ATw twLAB2 * ATw (twZsAB2 i) = ATw (twZsAB2 i) * ATw twLAB2) ∧
    ((1 - ATw twLAB2).mulVec ![-1, -1, 1, 0] = (1 - ATw laF).mulVec ![-1, -1, -1, -1]) ∧
    ((1 - ATw twLAB2).mulVec ![-4, 0, 0, 2] = (1 - ATw twL2AB2).mulVec ![-1, 0, -1, -1]) ∧
    (ATw twLAB2 * ATw twL2AB2 = ATw twL2AB2 * ATw twLAB2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem twZ_ab2_solve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - ATw twLAB2).mulVec d = (1 - ATw (twZsAB2 i)).mulVec c := by
  obtain ⟨D1, D2, D3, -, -, -, -⟩ := twB_ab2_data
  exact solve_int_fpf (ATw twLAB2) (fun i => ATw (twZsAB2 i)) twZ_ab2_data.1 _ _ _ _ _ _ _ D1 D2 D3
    twZ_ab2_tab

theorem twZ_ab2_point : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
    (1 - ATw twLAB2).mulVec d₁ = (1 - ATw laF).mulVec c ∧
    (1 - ATw twLAB2).mulVec d₂ = (1 - ATw twL2AB2).mulVec (c - κ) := by
  obtain ⟨D1, -, -, -, -, -, -⟩ := twB_ab2_data
  obtain ⟨-, h₁, h₃, hY⟩ := twZ_ab2_data
  exact pair_point_int _ _ _ _ _ _ _ _ D1 hY _ _ h₁ h₃

end Data

section Main


@[expose] def BdTw {L : Type} [Field L] (Fr : L →+* L) (w0 : WeylGroup Tag.F4)
    (x : WeylGroup Tag.F4) : Prop :=
  ∀ s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr,
    NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = x → s ^ 3 = 1 →
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)))

theorem BdTw.inv {L : Type} [Field L] {Fr : L →+* L} {w0 : WeylGroup Tag.F4}
    {x : WeylGroup Tag.F4} (h : BdTw Fr w0 x) : BdTw Fr w0 x⁻¹ := by
  intro s hs hs3
  have h1 := h s⁻¹ (by rw [map_inv, hs, inv_inv]) (by rw [inv_pow, hs3, inv_one])
  have : Subgroup.centralizer
      ({s⁻¹} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)) =
      Subgroup.centralizer ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)) := by
    ext c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  rwa [this] at h1

variable {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L]
  (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
  {w0 : WeylGroup Tag.F4} (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u)

include hFr hw0 in
theorem boundTwA_core (h3 : 3 ∣ Nat.card F + 1) (lx ly : List (Fin Tag.F4.rank))
    (hx : wordW Tag.F4 lx ∈ QF4) (hy : wordW Tag.F4 ly ∈ QF4) (Φ Ψ : Matrix (Fin 4) (Fin 4) ℤ)
    (hid : 1 - ATw ly = (1 - ATw lx) * Φ + Ψ * (1 + ATw lx + ATw lx * ATw lx))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 ly} :
      Set (WeylGroup Tag.F4))))
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = wordW Tag.F4 lx)
    (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  obtain ⟨ω, hω⟩ := exists_orderOf_three_μC (F := F) (L := L) h3
  obtain ⟨C, hCinj, hCsurj, hCmem⟩ := exists_nfix_lift Fr hFr w0 QF4 QF4_pGroup
    (fun q _ => Subgroup.mem_centralizer_singleton_iff.2 (weylGroup_mul_comm_of_neg hw0 q).symm)
  obtain ⟨gx, hgxC, hgx⟩ := hCsurj _ hx
  obtain ⟨gy, hgyC, hgy⟩ := hCsurj _ hy
  have hcomm : gy * gx = gx * gy := hCinj _ (mul_mem hgyC hgxC) _ (mul_mem hgxC hgyC) (by
    rw [map_mul, map_mul, hgx, hgy]; exact QF4_comm _ hy _ hx)
  have hgx3 : gx ^ 3 = 1 := hCinj _ (pow_mem hgxC 3) _ (one_mem C) (by
    rw [map_pow, map_one, hgx]; exact QF4_cube _ hx)
  refine caseA_ab (ιT Fr hFr w0 hw0) (NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    Atw (ιT_injective Fr hFr w0 hw0) (NFixToWeyl_eq_one_mem_range Fr hFr w0 hw0)
    (NFixToWeyl_ιT Fr hFr w0 hw0) (NFix_conj_ιT Fr hFr w0 hw0) _ _ s gx gy hs hgx hgy hcomm hgx3
    hs3 Φ Ψ ?_ ω hω c₁ c₂ p₁ p₂ ?_ ?_ h11 h12 h21 h22 hQ
  · rw [Atw_wordW, Atw_wordW]; exact hid
  · rw [Atw_wordW]; exact hf₁
  · rw [Atw_wordW]; exact hf₂

include hFr hw0 in
theorem boundTwA_a (h3 : 3 ∣ Nat.card F + 1)
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = wordW Tag.F4 laF)
    (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  obtain ⟨hid, hf₁, hf₂⟩ := twA_a_data
  exact boundTwA_core Fr hFr hw0 h3 laF lbF wa_mem_QF4 wb_mem_QF4 _ _ hid _ _ 2 3 hf₁ hf₂
    (by decide) (by decide) (by decide) (by decide) nine_dvd_QF4 s hs hs3

include hFr hw0 in
theorem boundTwA_b (h3 : 3 ∣ Nat.card F + 1)
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = wordW Tag.F4 lbF)
    (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  obtain ⟨hid, hf₁, hf₂⟩ := twA_b_data
  refine boundTwA_core Fr hFr hw0 h3 lbF laF wb_mem_QF4 wa_mem_QF4 _ _ hid _ _ 0 2 hf₁ hf₂
    (by decide) (by decide) (by decide) (by decide) ?_ s hs hs3
  have : ({wordW Tag.F4 lbF, wordW Tag.F4 laF} : Set (WeylGroup Tag.F4)) = {wa, wb} := by
    rw [Set.pair_comm]; rfl
  rw [this]
  exact nine_dvd_QF4

include hFr hw0 in
theorem boundTwB_core (h3 : 3 ∣ Nat.card F + 1) (lx l₁ l₂ : List (Fin Tag.F4.rank))
    (ys : Fin 4 → List (Fin Tag.F4.rank)) (Ξ : Matrix (Fin 4) (Fin 4) ℤ)
    (hΞ : (1 - ATw lx) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin 4 → ℤ, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
      (1 - ATw lx).mulVec d = (1 - ATw (ys i)).mulVec c)
    (hpt : ∀ κ : Fin 4 → ℤ, ∃ c d₁ d₂ : Fin 4 → ℤ,
      (1 - ATw lx).mulVec d₁ = (1 - ATw l₁).mulVec c ∧
      (1 - ATw lx).mulVec d₂ = (1 - ATw l₂).mulVec (c - κ))
    (c₁ c₂ : Fin 4 → ℤ) (p₁ p₂ : Fin 4)
    (hf₁ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lx).mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hx : wordW Tag.F4 lx ∈ QF4) (hy₁ : wordW Tag.F4 l₁ ∈ QF4)
    (hx3 : wordW Tag.F4 lx ^ 3 = 1) (hy3 : wordW Tag.F4 l₂ ^ 3 = 1)
    (hxy : wordW Tag.F4 lx * wordW Tag.F4 l₂ = wordW Tag.F4 l₂ * wordW Tag.F4 lx)
    (hys : ∀ i, wordW Tag.F4 (ys i) ∈ Subgroup.closure
      ({wordW Tag.F4 l₁, wordW Tag.F4 l₂} : Set (WeylGroup Tag.F4)))
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure
      ({wordW Tag.F4 lx, wordW Tag.F4 (ys i)} : Set (WeylGroup Tag.F4))))
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = wordW Tag.F4 lx) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  obtain ⟨ω, hω⟩ := exists_orderOf_three_μC (F := F) (L := L) h3
  have hcen : ∀ Q : Subgroup (WeylGroup Tag.F4),
      Q ≤ Subgroup.centralizer ({w0} : Set (WeylGroup Tag.F4)) := fun Q q _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (weylGroup_mul_comm_of_neg hw0 q).symm
  obtain ⟨C, hCinj, hCsurj, -⟩ := exists_nfix_lift Fr hFr w0 QF4 QF4_pGroup (hcen _)
  obtain ⟨gx, hgxC, hgx⟩ := hCsurj _ hx
  obtain ⟨g₁, hg₁C, hg₁⟩ := hCsurj _ hy₁
  have hc₁ : g₁ * gx = gx * g₁ := hCinj _ (mul_mem hg₁C hgxC) _ (mul_mem hgxC hg₁C) (by
    rw [map_mul, map_mul, hgx, hg₁]; exact QF4_comm _ hy₁ _ hx)
  obtain ⟨C₂, hC₂inj, hC₂surj, -⟩ := exists_nfix_lift Fr hFr w0
    (Subgroup.closure ({wordW Tag.F4 lx, wordW Tag.F4 l₂} : Set (WeylGroup Tag.F4)))
    (isPGroup_closure_pair hxy hx3 hy3) (hcen _)
  obtain ⟨gx', hgx'C, hgx'⟩ := hC₂surj _ (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨g₂, hg₂C, hg₂⟩ := hC₂surj _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hc₂ : g₂ * gx' = gx' * g₂ := hC₂inj _ (mul_mem hg₂C hgx'C) _ (mul_mem hgx'C hg₂C) (by
    rw [map_mul, map_mul, hgx', hg₂]; exact hxy.symm)
  refine caseB_pair (ιT Fr hFr w0 hw0) (NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    Atw (ιT_injective Fr hFr w0 hw0) (NFixToWeyl_eq_one_mem_range Fr hFr w0 hw0)
    (NFixToWeyl_ιT Fr hFr w0 hw0) (NFix_conj_ιT Fr hFr w0 hw0) _ _ _
    (fun i => wordW Tag.F4 (ys i)) hys s gx g₁ gx' g₂ hs hgx hg₁ hc₁ hgx' hg₂ hc₂ ?_ Ξ ?_ ?_ ω hω
    c₁ c₂ p₁ p₂ ?_ ?_ h11 h12 h21 h22 hQ
  · intro κ
    obtain ⟨c, d₁, d₂, e₁, e₂⟩ := hpt κ
    exact ⟨c, d₁, d₂, by rw [Atw_wordW, Atw_wordW]; exact e₁,
      by rw [Atw_wordW, Atw_wordW]; exact e₂⟩
  · rw [Atw_wordW]; exact hΞ
  · intro c
    obtain ⟨i, d, hd⟩ := hsolve c
    exact ⟨i, d, by rw [Atw_wordW, Atw_wordW]; exact hd⟩
  · rw [Atw_wordW]; exact hf₁
  · rw [Atw_wordW]; exact hf₂

end Main

section Main2


variable {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L]
  (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
  {w0 : WeylGroup Tag.F4} (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u)

theorem twLAB_mem_QF4 : wordW Tag.F4 twLAB ∈ QF4 := by
  rw [twLAB, wordW_append]
  exact mul_mem wa_mem_QF4 wb_mem_QF4

theorem twLAB2_mem_QF4 : wordW Tag.F4 twLAB2 ∈ QF4 := by
  rw [twLAB2, wordW_append, wordW_append]
  exact mul_mem (mul_mem wa_mem_QF4 wb_mem_QF4) wb_mem_QF4

include hFr hw0 in
theorem bdTw_wa (h3 : 3 ∣ Nat.card F + 1) : BdTw Fr w0 wa := fun s hs hs3 =>
  boundTwA_a Fr hFr hw0 h3 s hs hs3

include hFr hw0 in
theorem bdTw_wb (h3 : 3 ∣ Nat.card F + 1) : BdTw Fr w0 wb := fun s hs hs3 =>
  boundTwA_b Fr hFr hw0 h3 s hs hs3

include hFr hw0 in
theorem bdTw_ab (h3 : 3 ∣ Nat.card F + 1) : BdTw Fr w0 (wa * wb) := by
  intro s hs _
  obtain ⟨-, -, -, hΞ, -, hf₁, hf₂⟩ := twB_ab_data
  obtain ⟨⟨hW1, hW2⟩, hWy⟩ := twZsAB_W
  refine boundTwB_core Fr hFr hw0 h3 twLAB laF twL2AB twZsAB _ hΞ twZ_ab_solve twZ_ab_point _ _ 0
    2 hf₁ hf₂ (by decide) (by decide) (by decide) (by decide) twLAB_mem_QF4 wa_mem_QF4
    (wordW_cube_of twLAB hW1) (wordW_cube_of twL2AB (twZsAB_W.2 1).1)
    (wordW_comm_of twLAB twL2AB (twZsAB_W.2 1).2.2.2.2) twZsAB_mem
    (fun i => pair_nine twLAB (twZsAB i) hW1 (hWy i).1 hW2 (hWy i).2.1 (hWy i).2.2.1
      (hWy i).2.2.2.1 (hWy i).2.2.2.2) s ?_
  rw [hs, twLAB, wordW_append]; rfl

include hFr hw0 in
theorem bdTw_ab2 (h3 : 3 ∣ Nat.card F + 1) : BdTw Fr w0 (wa * wb * wb) := by
  intro s hs _
  obtain ⟨-, -, -, hΞ, -, hf₁, hf₂⟩ := twB_ab2_data
  obtain ⟨⟨hW1, hW2⟩, hWy⟩ := twZsAB2_W
  refine boundTwB_core Fr hFr hw0 h3 twLAB2 laF twL2AB2 twZsAB2 _ hΞ twZ_ab2_solve twZ_ab2_point
    _ _ 0 2 hf₁ hf₂ (by decide) (by decide) (by decide) (by decide) twLAB2_mem_QF4 wa_mem_QF4
    (wordW_cube_of twLAB2 hW1) (wordW_cube_of twL2AB2 (twZsAB2_W.2 1).1)
    (wordW_comm_of twLAB2 twL2AB2 (twZsAB2_W.2 1).2.2.2.2) twZsAB2_mem
    (fun i => pair_nine twLAB2 (twZsAB2 i) hW1 (hWy i).1 hW2 (hWy i).2.1 (hWy i).2.2.1
      (hWy i).2.2.2.1 (hWy i).2.2.2.2) s ?_
  rw [hs, twLAB2, wordW_append, wordW_append]; rfl

include hFr hw0 in
theorem bdTw_of_QF4 (h3 : 3 ∣ Nat.card F + 1) {x : WeylGroup Tag.F4} (hx : x ∈ QF4)
    (hx1 : x ≠ 1) : BdTw Fr w0 x := by
  obtain ⟨i, j, rfl⟩ := mem_QF4 hx
  rw [pow_eq_pow_mod i wa_cube, pow_eq_pow_mod j wb_cube] at hx1 ⊢
  have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize i % 3 = a at hi hx1 ⊢
  generalize j % 3 = b at hj hx1 ⊢
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hx1
  · simpa using bdTw_wb Fr hFr hw0 h3
  · have := (bdTw_wb Fr hFr hw0 h3).inv
    rwa [inv_eq_sq_of_cube wb_cube, ← one_mul (wb ^ 2), ← pow_zero wa] at this
  · simpa using bdTw_wa Fr hFr hw0 h3
  · simpa using bdTw_ab Fr hFr hw0 h3
  · have := bdTw_ab2 Fr hFr hw0 h3
    simpa [pow_two, mul_assoc] using this
  · have := (bdTw_wa Fr hFr hw0 h3).inv
    rwa [inv_eq_sq_of_cube wa_cube, ← mul_one (wa ^ 2), ← pow_zero wb] at this
  · have := (bdTw_ab2 Fr hFr hw0 h3).inv
    rwa [inv_wa_wb_wb] at this
  · have := (bdTw_ab Fr hFr hw0 h3).inv
    rwa [inv_wa_wb] at this

include hFr hw0 in
theorem bdTw_torus
    (s : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)
    (hs : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = 1)
    (h3 : 3 ∣ Nat.card F + 1) :
    81 ∣ Nat.card (Subgroup.centralizer
      ({s} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr))) := by
  obtain ⟨t, rfl⟩ := NFixToWeyl_eq_one_mem_range Fr hFr w0 hw0 s hs
  have hle : (ιT Fr hFr w0 hw0).range ≤ Subgroup.centralizer
      ({ιT Fr hFr w0 hw0 t} : Set (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)) := by
    rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mul_comm]
  have hcard : Nat.card (ιT Fr hFr w0 hw0).range = (Nat.card F + 1) ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (ιT_injective Fr hFr w0 hw0)).toEquiv,
      Nat.card_pi]
    simp [natCard_μC]
    rfl
  have h81 : 81 ∣ (Nat.card F + 1) ^ 4 := by
    have : (3 : ℕ) ^ 4 ∣ (Nat.card F + 1) ^ 4 := pow_dvd_pow_of_dvd h3 4
    simpa using this
  exact (hcard ▸ h81).trans (Subgroup.card_dvd_of_le hle)

end Main2

section Final


theorem nfixF4NLevel : CFSG.HardMathSupport.Malle.E27Lie.ExcCross.NFixF4NLevel := by
  intro F _ _ L _ _ _ Fr hFr h3 w0 hw0 s hs3 _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  by_cases hz1 : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s = 1
  · exact bdTw_torus Fr hFr hw0 s hz1 h3
  · have hz3 : (NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s) ^ 3 = 1 := by
      rw [← map_pow, hs3, map_one]
    obtain ⟨w, hw⟩ := exists_conj_mem_QF4 _ hz3
    obtain ⟨g, hg⟩ := NFixToWeyl_surjective Fr hw0 hFr w
    have hconj : NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr (g * s * g⁻¹) =
        w * NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg]
    have hne : w * NFixToWeyl (canonicalRep (coxeterSystem Tag.F4) L w0) Fr s * w⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have h' := mul_inv_eq_one.1 h
      exact mul_left_cancel (h'.trans (mul_one w).symm)
    have hQ := bdTw_of_QF4 Fr hFr hw0 h3 hw hne (g * s * g⁻¹) hconj
      (by rw [conj_pow, hs3]; simp)
    rwa [card_centralizer_conj] at hQ

end Final

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
