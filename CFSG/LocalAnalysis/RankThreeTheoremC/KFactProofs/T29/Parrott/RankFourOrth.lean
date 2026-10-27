module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.PLElem.RankFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open CFSG.HardMathSupport.Timmesfeld.DFour
open scoped MatrixGroups

section Pairs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem four_le_pRank_omega_of_pairs {m : ℕ} (hm : 4 ≤ m) (a b : Fin m → ι)
    (ha : Function.Injective a) (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j)
    (Q R : (ι → K) → K)
    (hR : ∀ v w : ι → K, (∀ x, (∀ i, a i ≠ x) → (∀ i, b i ≠ x) → v x = w x) → R v = R w)
    (hQ : ∀ v, Q v = ∑ i, v (a i) * v (b i) + R v) {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega Q))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set i0 : Fin m := ⟨0, by omega⟩
  set i1 : Fin m := ⟨1, by omega⟩
  set i2 : Fin m := ⟨2, by omega⟩
  set i3 : Fin m := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  set f₁ := frame4 a b i0 i1 with hf₁def
  set f₂ := frame4 a b i2 i3 with hf₂def
  have hf₁ : Function.Injective f₁ := frame4_injective a b ha hb hab i0 i1 h01
  have hf₂ : Function.Injective f₂ := frame4_injective a b ha hb hab i2 i3 h23
  have hdisj : ∀ k l, f₁ k ≠ f₂ l := by
    intro k l
    fin_cases k <;> fin_cases l <;>
      simp [hf₁def, hf₂def, frame4, i0, i1, i2, i3, ha.eq_iff, hb.eq_iff, hab, (hab _ _).symm,
        Fin.ext_iff]
  have hRf : ∀ j0 j1 : Fin m, ∀ v w : ι → K,
      (∀ x, x ∉ Set.range (frame4 a b j0 j1) → v x = w x) → R v = R w := by
    intro j0 j1 v w h
    refine hR v w fun x hxa hxb => h x ?_
    rintro ⟨k, hk⟩
    fin_cases k <;> simp only [frame4] at hk <;>
      first
      | exact hxa _ (by simpa using hk)
      | exact hxb _ (by simpa using hk)
  have HQ₁ := hq_of_sum a b ha hb hab i0 i1 h01 Q R (hRf i0 i1) hQ
  have HQ₂ := hq_of_sum a b ha hb hab i2 i3 h23 Q R (hRf i2 i3) hQ
  set x : GL ι K := gen f₁ hf₁ lmat lmat_one lmat_mul c3 with hxdef
  set y : GL ι K := gen f₁ hf₁ rmat rmat_one rmat_mul c3 with hydef
  set z : GL ι K := gen f₂ hf₂ lmat lmat_one lmat_mul c3 with hzdef
  set w : GL ι K := gen f₂ hf₂ rmat rmat_one rmat_mul c3 with hwdef
  have hxO : x ∈ StatedOmega Q :=
    gen_mem_omega _ f₁ hf₁ HQ₁ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hyO : y ∈ StatedOmega Q :=
    gen_mem_omega _ f₁ hf₁ HQ₁ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hzO : z ∈ StatedOmega Q :=
    gen_mem_omega _ f₂ hf₂ HQ₂ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hwO : w ∈ StatedOmega Q :=
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
  have hdc : ∀ (g h : GL ι K) (N M : Matrix (Fin 4) (Fin 4) K),
      (g : Matrix ι ι K) = blk4 f₁ hf₁ N → (h : Matrix ι ι K) = blk4 f₂ hf₂ M → Commute g h := by
    intro g h N M hg hh
    ext1
    simp only [Units.val_mul, hg, hh]
    exact blk4_commute f₁ f₂ hf₁ hf₂ hdisj _ _
  have hxz : Commute x z := hdc x z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyz : Commute y z := hdc y z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hxw : Commute x w := hdc x w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyw : Commute y w := hdc y w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hx1 : x ∉ StatedScalars ι K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (f₁ 0) (f₁ 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf₁.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hlr : ∀ (k : ℕ) (u : K), ¬ ∀ i j, lmat (((c3 : SL(2, K)) ^ k : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) i j * u =
        rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) i j := by
    intro k u key
    have hk : (c3 : SL(2, K)) ^ k = c3 ^ (k % 3) := by
      conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
    rw [hk] at key
    have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : k % 3
    · have e := key 0 1
      simp [lmat, rmat, c3] at e
    · have e := key 0 0
      rw [pow_one] at e
      simp [lmat, rmat, c3] at e
    · have e := key 0 1
      rw [coe_c3_sq] at e
      simp [lmat, rmat, c3] at e
  have hy1 : ∀ k : ℕ, ∀ s ∈ StatedScalars ι K, x ^ k * s ≠ y := by
    rintro k _ ⟨u, rfl⟩ hmc
    refine hlr k u fun i j => ?_
    have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (f₁ i) (f₁ j)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
      Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
    exact h1
  have hz1 : ∀ k l : ℕ, ∀ s ∈ StatedScalars ι K, x ^ k * y ^ l * s ≠ z := by
    intro k l s hs
    have hn1 : f₂ 1 ∉ Set.range f₁ := fun ⟨j, hj⟩ => hdisj j 1 hj
    have hfix : ((x ^ k * y ^ l : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (f₂ 1) 1 =
        Pi.single (f₂ 1) 1 := by
      rw [hxdef, hydef, ← map_pow, ← map_pow, Units.val_mul, coe_gen, coe_gen, blk4_mul]
      exact blk4_mulVec_single_of_not f₁ hf₁ _ hn1
    have hzv : ((z : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (f₂ 1) 1 = Pi.single (f₂ 2) 1 := by
      rw [hzdef, coe_gen]
      funext e
      by_cases he : e ∈ Set.range f₂
      · obtain ⟨j, rfl⟩ := he
        rw [blk4_mulVec_f]
        fin_cases j <;> simp [Pi.single_apply, hf₂.eq_iff, lmat, c3]
      · rw [blk4_mulVec_of_not f₂ hf₂ _ _ he]
        have h1 : e ≠ f₂ 1 := fun h => he ⟨1, h.symm⟩
        have h2 : e ≠ f₂ 2 := fun h => he ⟨2, h.symm⟩
        simp [h1, h2]
    exact CFSG.SectionRank.ClassicalEven.mul_scalar_ne (hf₂.ne (by decide)) hfix hzv hs
  have hw1 : ∀ k l r : ℕ, ∀ s ∈ StatedScalars ι K, x ^ k * y ^ l * z ^ r * s ≠ w := by
    rintro k l r _ ⟨u, rfl⟩ hmc
    refine hlr r u fun i j => ?_
    have h1 := congrArg (fun g : GL ι K =>
      ((g : Matrix ι ι K) *ᵥ Pi.single (f₂ j) 1) (f₂ i)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, hzdef, hwdef,
      ← map_pow, coe_gen, ← Matrix.mulVec_mulVec, Matrix.scalar_apply,
      Matrix.diagonal_mulVec_single] at h1
    have hvan : ∀ i', (blk4 f₂ hf₂ (lmat (((c3 : SL(2, K)) ^ r : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K)) *ᵥ Pi.single (f₂ j) ((u : K) * 1)) (f₁ i') = 0 := by
      intro i'
      have hn : f₁ i' ∉ Set.range f₂ := fun ⟨i'', hi''⟩ => hdisj i' i'' hi''.symm
      rw [blk4_mulVec_of_not f₂ hf₂ _ _ hn]
      simp [hdisj i' j]
    rw [blk4_mulVec_of_vanish f₁ hf₁ _ hvan, blk4_mulVec_of_vanish f₁ hf₁ _ hvan,
      blk4_mulVec_f, blk4_mulVec_f] at h1
    simpa [Pi.single_apply, hf₂.eq_iff] using h1
  exact four_le_pRank_statedProj hxO hyO hzO hwO hx3 hy3 hz3 hw3 hxy hxz hyz hxw hyw hzw hx1 hy1
    hz1 hw1

theorem four_le_pRank_omegaOdd {n : ℕ} (hn : 4 ≤ n) {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K)))) := by
  refine four_le_pRank_omega_of_pairs hn (Sum.inl : Fin n → Fin n ⊕ Fin n ⊕ Unit)
    (fun i => Sum.inr (Sum.inl i)) Sum.inl_injective (fun i j h => by simpa using h)
    (fun i j => by simp) _ (fun v => v (Sum.inr (Sum.inr ())) ^ 2) ?_
    (fun v => by simp [StatedQuadOdd]) hc hcsq
  intro v w h
  rw [h _ (fun i => by simp) (fun i => by simp)]

theorem four_le_pRank_omegaMinus {n : ℕ} (hn : 5 ≤ n) (b c' : K) {c : K} (hc : c ≠ 0)
    (hcsq : c ^ 2 ≠ 1) :
    4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c')))) := by
  refine four_le_pRank_omega_of_pairs (m := n - 1) (by omega)
    (Sum.inl : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
    (fun i => Sum.inr (Sum.inl i)) Sum.inl_injective (fun i j h => by simpa using h)
    (fun i j => by simp) _ (fun v => v (Sum.inr (Sum.inr 0)) ^ 2 +
      b * v (Sum.inr (Sum.inr 0)) * v (Sum.inr (Sum.inr 1)) + c' * v (Sum.inr (Sum.inr 1)) ^ 2)
    ?_ (fun v => by simp [StatedQuadMinus, add_assoc]) hc hcsq
  intro v w h
  rw [h _ (fun i => by simp) (fun i => by simp), h _ (fun i => by simp) (fun i => by simp)]

end Pairs

theorem four_le_pRank_three_orth {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n p f : ℕ}
    (hC : StatedClassicalModel X t n p f)
    (ht : (t = .POmegaOdd ∧ 4 ≤ n) ∨ (t = .POmegaPlus ∧ 4 ≤ n) ∨ (t = .POmegaMinus ∧ 5 ≤ n))
    (h3 : p ≠ 3) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · obtain ⟨⟨hp, hf, -, h2⟩, K, _, _, hK, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact four_le_pRank_omegaOdd hn c2 c4
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    by_cases h2 : p = 2
    · subst h2
      exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaPlus_four_le_pRank_three hn
    · obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
      exact four_le_pRank_plus_of_char hn c2 c4
  · obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := hC
    have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    by_cases h2 : p = 2
    · subst h2
      exact CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.PLElem.omegaMinus_four_le_pRank_three hn b c
    · obtain ⟨c2, c4⟩ := char_facts (K := K) hp h2 h3
      exact four_le_pRank_omegaMinus hn b c c2 c4

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
