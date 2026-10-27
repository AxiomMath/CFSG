module

public import CFSG.LieType.SeitzGeneration.DiagWeights
public import CFSG.RankThree.PartOne.KF.UnitaryModel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

@[expose] def HasThreeIndep (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∃ e₁ e₂ e₃ : G, Commute e₁ e₂ ∧ Commute e₁ e₃ ∧ Commute e₂ e₃ ∧ e₁ ^ p = 1 ∧ e₂ ^ p = 1 ∧
    e₃ ^ p = 1 ∧ ∀ i j k : ℤ, e₁ ^ i * e₂ ^ j * e₃ ^ k = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k

theorem HasThreeIndep.of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {p : ℕ}
    (h : HasThreeIndep G p) : HasThreeIndep H p := by
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc, hi⟩ := h
  refine ⟨e a, e b, e c, hab.map e, hac.map e, hbc.map e, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ha, map_one]
  · rw [← map_pow, hb, map_one]
  · rw [← map_pow, hc, map_one]
  · intro i j k h
    refine hi i j k (e.injective ?_)
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_one]
    exact h

theorem HasThreeIndep.of_hom {G Q : Type*} [Group G] [Group Q] (π : G →* Q) {p : ℕ}
    {x₁ x₂ x₃ : G} (h12 : Commute x₁ x₂) (h13 : Commute x₁ x₃) (h23 : Commute x₂ x₃)
    (hp₁ : x₁ ^ p = 1) (hp₂ : x₂ ^ p = 1) (hp₃ : x₃ ^ p = 1)
    (hi : ∀ i j k : ℤ, π (x₁ ^ i * x₂ ^ j * x₃ ^ k) = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k) : HasThreeIndep Q p :=
  ⟨π x₁, π x₂, π x₃, h12.map π, h13.map π, h23.map π, by rw [← map_pow, hp₁, map_one],
    by rw [← map_pow, hp₂, map_one], by rw [← map_pow, hp₃, map_one], fun i j k h =>
      hi i j k (by simpa only [map_mul, map_zpow] using h)⟩

section Linear

variable {F : Type} [Field F] {n : ℕ}

@[expose] def diagSLn (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) : Matrix.SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal fun i => (w i : F), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hw, Units.val_one]⟩

theorem toGL_diagSLn (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) :
    Matrix.SpecialLinearGroup.toGL (diagSLn w hw) = diagU w := Units.ext rfl

end Linear

section LinearModel

variable {F : Type} [Field F] [Finite F] {n p : ℕ}

omit [Finite F] in
theorem toGL_injective' :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) F →
      GL (Fin n) F) := fun a b h => by
  apply Subtype.ext
  have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h
  exact this

theorem hasThreeIndep_psl (hn : 5 ≤ n) (hp : p.Prime) (hpq : p ∣ Nat.card F - 1) :
    HasThreeIndep (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hx : ∀ k : Fin 3, Matrix.SpecialLinearGroup.toGL
      (diagSLn (F := F) (wt ζ hn k) (prod_wt ζ hn k)) = diagU (wt ζ hn k) := fun k =>
    toGL_diagSLn _ _
  have hcomm : ∀ a b : Fin 3, Commute (diagSLn (F := F) (wt ζ hn a) (prod_wt ζ hn a))
      (diagSLn (F := F) (wt ζ hn b) (prod_wt ζ hn b)) := fun a b => by
    apply toGL_injective'
    rw [map_mul, map_mul, hx, hx, diagU_mul, diagU_mul, mul_comm]
  have hpow : ∀ a : Fin 3, diagSLn (F := F) (wt ζ hn a) (prod_wt ζ hn a) ^ p = 1 := fun a => by
    apply toGL_injective'
    rw [map_pow, map_one, hx, diagU_pow, wt_pow hζp hn a, diagU_one]
  refine HasThreeIndep.of_hom (QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))) (hcomm 0 1) (hcomm 0 2) (hcomm 1 2)
    (hpow 0) (hpow 1) (hpow 2) fun i j k h => ?_
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
  have e : ∀ (d : Fin n → Fˣ) (m : ℤ), (diagU d : GL (Fin n) F) ^ m = diagU (d ^ m) :=
    fun d m => (map_zpow diagUHom d m).symm
  have hg : Matrix.SpecialLinearGroup.toGL (diagSLn (F := F) (wt ζ hn 0) (prod_wt ζ hn 0) ^ i *
      diagSLn (F := F) (wt ζ hn 1) (prod_wt ζ hn 1) ^ j *
      diagSLn (F := F) (wt ζ hn 2) (prod_wt ζ hn 2) ^ k) =
      diagU (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) := by
    rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, hx, hx, hx, e, e, e, diagU_mul, diagU_mul]
  refine scalar_wt hζ hn fun l l' => Units.ext ?_
  have hl : ∀ l : Fin n, ((wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l : F) = r := fun l => by
    have h1 := congrArg
      (fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) l l) hg
    have h2 := congrArg (fun A : Matrix (Fin n) (Fin n) F => A l l) hr
    simp only [diagU_apply_same] at h1
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
    exact h1.symm.trans h2.symm
  exact (hl l).trans (hl l').symm

end LinearModel

section UnitaryModel

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem hasThreeIndep_psu (hU : UnitaryFieldData ℓ f K) (hn : 5 ≤ n) (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) : HasThreeIndep (StatedProj (StatedSU n (ℓ ^ f) K)) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin := hU.finite
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card_eq_sq]
    have h1 : (ℓ ^ f) ^ 2 - 1 ^ 2 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := Nat.sq_sub_sq _ _
    rw [one_pow] at h1
    rw [h1]
    exact hpq.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let x : Fin 3 → unitarySU ℓ f K n := fun k =>
    ⟨diagU (wt ζ hn k), torusSU_le_unitarySU hU hpq
      (mem_torusSU_iff.2 ⟨wt ζ hn k, fun i => congrFun (wt_pow hζp hn k) i, prod_wt ζ hn k,
        rfl⟩)⟩
  have hcomm : ∀ a b : Fin 3, Commute (x a) (x b) := fun a b => by
    apply Subtype.ext
    change diagU (wt ζ hn a) * diagU (wt ζ hn b) = diagU (wt ζ hn b) * diagU (wt ζ hn a)
    rw [diagU_mul, diagU_mul, mul_comm]
  have hpow : ∀ a : Fin 3, x a ^ p = 1 := fun a => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (diagU (wt ζ hn a)) ^ p = 1
    rw [diagU_pow, wt_pow hζp hn a, diagU_one]
  refine HasThreeIndep.of_hom (QuotientGroup.mk'
    ((StatedScalars (Fin n) K).subgroupOf (unitarySU ℓ f K n))) (hcomm 0 1) (hcomm 0 2)
    (hcomm 1 2) (hpow 0) (hpow 1) (hpow 2) fun i j k h => ?_
  have hmem := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨c, hc⟩ := hmem
  have e : ∀ (d : Fin n → Kˣ) (m : ℤ), (diagU d : GL (Fin n) K) ^ m = diagU (d ^ m) :=
    fun d m => (map_zpow diagUHom d m).symm
  have hg : (((x 0 ^ i * x 1 ^ j * x 2 ^ k : unitarySU ℓ f K n)) : GL (Fin n) K) =
      diagU (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_zpow,
      Subgroup.coe_zpow]
    change (diagU (wt ζ hn 0)) ^ i * (diagU (wt ζ hn 1)) ^ j * (diagU (wt ζ hn 2)) ^ k = _
    rw [e, e, e, diagU_mul, diagU_mul]
  refine scalar_wt hζ hn fun l l' => Units.ext ?_
  have hl : ∀ l : Fin n, ((wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l : K) = c := fun l => by
    have h1 := congrArg
      (fun g : GL (Fin n) K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) l l) (hc.trans hg)
    simp only [diagU_apply_same, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h1
    exact h1.symm
  exact (hl l).trans (hl l').symm

end UnitaryModel

end CFSG.LieType.SeitzGeneration
