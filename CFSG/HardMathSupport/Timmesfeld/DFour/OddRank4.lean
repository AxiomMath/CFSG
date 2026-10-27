module

public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open scoped MatrixGroups

theorem four_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y z w : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hxw : Commute x w)
    (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z)
    (hw1 : ∀ n m l : ℕ, x ^ n * y ^ m * z ^ l ≠ w) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ :=
    CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀ B₀.subtype Subtype.val_injective (y := x) hx
      (by
        rintro ⟨b, hb⟩
        exact hx1 (hb ▸ h₀ b))
      (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ :=
    CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y) hy
      (by
        rintro ⟨a, ha⟩
        obtain ⟨n, hn⟩ := hr₁' a
        exact hy1 n (hn ▸ ha))
      (fun a => by
        obtain ⟨n, hn⟩ := hr₁' a
        rw [hn]
        exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, hr₃⟩ :=
    CFSG.SectionRank.exists_extend hc₂ hp₂ hcard₂ F₂ hF₂ (y := z) hz
      (by
        rintro ⟨a, ha⟩
        obtain ⟨n, m, hnm⟩ := hr₂' a
        exact hz1 n m (hnm ▸ ha))
      (fun a => by
        obtain ⟨n, m, hnm⟩ := hr₂' a
        rw [hnm]
        exact (hxz.pow_left n).mul_left (hyz.pow_left m))
  have hr₃' : ∀ a, ∃ n m l : ℕ, F₃ a = x ^ n * y ^ m * z ^ l := fun a => by
    obtain ⟨b, l, hb⟩ := hr₃ a
    obtain ⟨n, m, hnm⟩ := hr₂' b
    exact ⟨n, m, l, by rw [hb, hnm]⟩
  obtain ⟨F₄, hF₄, hc₄, hp₄, hcard₄, -⟩ :=
    CFSG.SectionRank.exists_extend hc₃ hp₃ hcard₃ F₃ hF₃ (y := w) hw
      (by
        rintro ⟨a, ha⟩
        obtain ⟨n, m, l, hnml⟩ := hr₃' a
        exact hw1 n m l (hnml ▸ ha))
      (fun a => by
        obtain ⟨n, m, l, hnml⟩ := hr₃' a
        rw [hnml]
        exact ((hxw.pow_left n).mul_left (hyw.pow_left m)).mul_left (hzw.pow_left l))
  exact CFSG.SectionRank.le_pRank_of_injective hp.out.one_lt hc₄ hp₄ hcard₄ F₄ hF₄ le_top

theorem four_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y z w : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H) (hwH : w ∈ H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hz : z ^ p = 1) (hw : w ^ p = 1) (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) (hxw : Commute x w) (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y)
    (hz1 : ∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * c ≠ z)
    (hw1 : ∀ n m l : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * z ^ l * c ≠ w) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  refine four_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) (hpow z hzH hz) (hpow w hwH hw)
    (hcomm _ _ _ _ hxy) (hcomm _ _ _ _ hxz) (hcomm _ _ _ _ hyz) (hcomm _ _ _ _ hxw)
    (hcomm _ _ _ _ hyw) (hcomm _ _ _ _ hzw) (fun h => hx1 ?_) (fun n h => ?_)
    (fun n m h => ?_) (fun n m l h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hz1 n m _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hw1 n m l _ this (mul_inv_cancel_left _ _)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem blk4_mulVec_of_vanish (f : Fin 4 → ι) (hf : Function.Injective f)
    (N : Matrix (Fin 4) (Fin 4) K) {v : ι → K} (hv : ∀ k, v (f k) = 0) :
    blk4 f hf N *ᵥ v = v := by
  funext a
  by_cases ha : a ∈ Set.range f
  · obtain ⟨k, rfl⟩ := ha
    rw [blk4_mulVec_f, hv k]
    simp [hv]
  · exact blk4_mulVec_of_not f hf N v ha

theorem four_le_pRank_plus_of_char {n : ℕ} (hn : 4 ≤ n) [Finite K] {c : K} (hc : c ≠ 0)
    (hcsq : c ^ 2 ≠ 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set i3 : Fin n := ⟨3, by omega⟩
  have hab : ∀ i j : Fin n, (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j := fun _ _ => Sum.inl_ne_inr
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  set f₁ := frame4 (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr i0 i1 with hf₁def
  set f₂ := frame4 (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr i2 i3 with hf₂def
  have hf₁ : Function.Injective f₁ :=
    frame4_injective _ _ Sum.inl_injective Sum.inr_injective hab i0 i1 h01
  have hf₂ : Function.Injective f₂ :=
    frame4_injective _ _ Sum.inl_injective Sum.inr_injective hab i2 i3 h23
  have hdisj : ∀ k l, f₁ k ≠ f₂ l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [hf₁def, hf₂def, frame4, i0, i1, i2, i3, Fin.ext_iff]
  have hQ : ∀ v, StatedQuadPlus n K v = ∑ i, v (Sum.inl i) * v (Sum.inr i) + (fun _ => 0) v :=
    fun v => by simp [StatedQuadPlus]
  have HQ₁ := hq_of_sum (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective hab i0 i1 h01 (StatedQuadPlus n K) (fun _ => 0) (fun _ _ _ => rfl) hQ
  have HQ₂ := hq_of_sum (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective hab i2 i3 h23 (StatedQuadPlus n K) (fun _ => 0) (fun _ _ _ => rfl) hQ
  set x : GL (Fin n ⊕ Fin n) K := gen f₁ hf₁ lmat lmat_one lmat_mul c3 with hxdef
  set y : GL (Fin n ⊕ Fin n) K := gen f₁ hf₁ rmat rmat_one rmat_mul c3 with hydef
  set z : GL (Fin n ⊕ Fin n) K := gen f₂ hf₂ lmat lmat_one lmat_mul c3 with hzdef
  set w : GL (Fin n ⊕ Fin n) K := gen f₂ hf₂ rmat rmat_one rmat_mul c3 with hwdef
  have hxO : x ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hyO : y ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hzO : z ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₂ hf₂ HQ₂ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hwO : w ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₂ hf₂ HQ₂ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, c3_pow_three, map_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← map_pow, c3_pow_three, map_one]
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, c3_pow_three, map_one]
  have hw3 : w ^ 3 = 1 := by rw [hwdef, ← map_pow, c3_pow_three, map_one]
  have hxy : Commute x y := by
    ext1
    simp only [Units.val_mul, hxdef, hydef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hzw : Commute z w := by
    ext1
    simp only [Units.val_mul, hzdef, hwdef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hdc : ∀ (a b : GL (Fin n ⊕ Fin n) K) (N M : Matrix (Fin 4) (Fin 4) K),
      (a : Matrix _ _ K) = blk4 f₁ hf₁ N → (b : Matrix _ _ K) = blk4 f₂ hf₂ M → Commute a b := by
    intro a b N M ha hb
    ext1
    simp only [Units.val_mul, ha, hb]
    exact blk4_commute f₁ f₂ hf₁ hf₂ hdisj _ _
  have hxz : Commute x z := hdc x z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyz : Commute y z := hdc y z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hxw : Commute x w := hdc x w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyw : Commute y w := hdc y w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hx1 : x ∉ StatedScalars (Fin n ⊕ Fin n) K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ 0) (f₁ 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf₁.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hlr : ∀ (m : ℕ) (u : K), ¬ ∀ k l, lmat (((c3 : SL(2, K)) ^ m : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) k l * u =
        rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l := by
    intro m u key
    have hm : (c3 : SL(2, K)) ^ m = c3 ^ (m % 3) := by
      conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
    rw [hm] at key
    have h3 : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : m % 3
    · have e := key 0 1
      simp [lmat, rmat, c3] at e
    · have e := key 0 0
      rw [pow_one] at e
      simp [lmat, rmat, c3] at e
    · have e := key 0 1
      rw [coe_c3_sq] at e
      simp [lmat, rmat, c3] at e
  have hy1 : ∀ m : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K, x ^ m * s ≠ y := by
    rintro m _ ⟨u, rfl⟩ hmc
    refine hlr m u fun k l => ?_
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ k) (f₁ l)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
      Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
    exact h1
  have hz1 : ∀ m l : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K, x ^ m * y ^ l * s ≠ z := by
    intro m l s hs
    have hn1 : f₂ 1 ∉ Set.range f₁ := fun ⟨k, hk⟩ => hdisj k 1 hk
    have hfix : ((x ^ m * y ^ l : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₂ 1) 1 =
        Pi.single (f₂ 1) 1 := by
      rw [hxdef, hydef, ← map_pow, ← map_pow, Units.val_mul, coe_gen, coe_gen, blk4_mul]
      exact blk4_mulVec_single_of_not f₁ hf₁ _ hn1
    have hzv : ((z : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₂ 1) 1 =
        Pi.single (f₂ 2) 1 := by
      rw [hzdef, coe_gen]
      funext b
      by_cases hb : b ∈ Set.range f₂
      · obtain ⟨k, rfl⟩ := hb
        rw [blk4_mulVec_f]
        fin_cases k <;> simp [Pi.single_apply, hf₂.eq_iff, lmat, c3]
      · rw [blk4_mulVec_of_not f₂ hf₂ _ _ hb]
        have h1 : b ≠ f₂ 1 := fun h => hb ⟨1, h.symm⟩
        have h2 : b ≠ f₂ 2 := fun h => hb ⟨2, h.symm⟩
        simp [h1, h2]
    exact CFSG.SectionRank.ClassicalEven.mul_scalar_ne (hf₂.ne (by decide)) hfix hzv hs
  have hw1 : ∀ m l r : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K,
      x ^ m * y ^ l * z ^ r * s ≠ w := by
    rintro m l r _ ⟨u, rfl⟩ hmc
    refine hlr r u fun k j => ?_
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      ((g : Matrix _ _ K) *ᵥ Pi.single (f₂ j) 1) (f₂ k)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, hzdef, hwdef,
      ← map_pow, coe_gen, ← Matrix.mulVec_mulVec, Matrix.scalar_apply,
      Matrix.diagonal_mulVec_single] at h1
    have hvan : ∀ k', (blk4 f₂ hf₂ (lmat (((c3 : SL(2, K)) ^ r : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K)) *ᵥ Pi.single (f₂ j) ((u : K) * 1)) (f₁ k') = 0 := by
      intro k'
      have hn : f₁ k' ∉ Set.range f₂ := fun ⟨k'', hk''⟩ => hdisj k' k'' hk''.symm
      rw [blk4_mulVec_of_not f₂ hf₂ _ _ hn]
      simp [hdisj k' j]
    rw [blk4_mulVec_of_vanish f₁ hf₁ _ hvan, blk4_mulVec_of_vanish f₁ hf₁ _ hvan,
      blk4_mulVec_f, blk4_mulVec_f] at h1
    simpa [Pi.single_apply, hf₂.eq_iff] using h1
  exact four_le_pRank_statedProj hxO hyO hzO hwO hx3 hy3 hz3 hw3 hxy hxz hyz hxw hyw hzw hx1 hy1
    hz1 hw1

end CFSG.HardMathSupport.Timmesfeld.DFour
