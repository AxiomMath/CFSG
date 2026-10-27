module

public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank
public import CFSG.LocalAnalysis.GLTheoremB.PGroupBasics
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.OrthWit

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem three_le_localRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y z u : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z)
    (hu : orderOf u = 2) (hux : Commute x u) (huy : Commute y u) (huz : Commute z u) :
    3 ≤ localRank p G := by
  set Y : Subgroup G := Subgroup.centralizer ({u} : Set G) with hY
  have hmem : ∀ {g : G}, Commute g u → g ∈ Y := fun h =>
    Subgroup.mem_centralizer_singleton_iff.2 h.eq
  let x' : Y := ⟨x, hmem hux⟩
  let y' : Y := ⟨y, hmem huy⟩
  let z' : Y := ⟨z, hmem huz⟩
  have hval : ∀ {a b : Y}, (a : G) = b → a = b := fun h => Subtype.ext h
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) :=
    CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (x := x') (y := y') (z := z')
      (hval (by simpa using hx)) (hval (by simpa using hy)) (hval (by simpa using hz))
      (Subtype.ext hxy.eq) (Subtype.ext hxz.eq) (Subtype.ext hyz.eq)
      (fun h => hx1 (congrArg Subtype.val h))
      (fun n h => hy1 n (by simpa using congrArg Subtype.val h))
      (fun n m h => hz1 n m (by simpa using congrArg Subtype.val h))
  obtain ⟨E₀, -, hE₀, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt (⊤ : Subgroup Y)
  obtain ⟨E, -, hE, hEc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE₀ (n := 3)
    (by rw [hcard]; exact pow_dvd_pow p h3)
  refine CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp.out hu
    (V := E.map Y.subtype) (Subgroup.map_subtype_le E) (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hEc]

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

open Classical in
@[expose] noncomputable def eFr3 (g : Fin 3 → ι) (hg : Function.Injective g) :
    ι ≃ Fin 3 ⊕ ↥(Set.range g)ᶜ :=
  (Equiv.Set.sumCompl (Set.range g)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective g hg).symm (Equiv.refl _))

theorem eFr3_apply_g (g : Fin 3 → ι) (hg : Function.Injective g) (k : Fin 3) :
    eFr3 g hg (g k) = Sum.inl k := by
  classical
  simp [eFr3, Equiv.Set.sumCompl_symm_apply_of_mem]

theorem eFr3_apply_of_not (g : Fin 3 → ι) (hg : Function.Injective g) {a : ι}
    (ha : a ∉ Set.range g) : ∃ h : a ∈ (Set.range g)ᶜ, eFr3 g hg a = Sum.inr ⟨a, h⟩ := by
  classical
  refine ⟨ha, ?_⟩
  simp [eFr3, Equiv.Set.sumCompl_symm_apply_of_notMem, ha]

theorem eFr3_symm_inl (g : Fin 3 → ι) (hg : Function.Injective g) (k : Fin 3) :
    (eFr3 g hg).symm (Sum.inl k) = g k := by
  rw [Equiv.symm_apply_eq, eFr3_apply_g]

@[expose] noncomputable def blk3 (g : Fin 3 → ι) (hg : Function.Injective g)
    (N : Matrix (Fin 3) (Fin 3) K) : Matrix ι ι K :=
  (fromBlocks N 0 0 1 : Matrix (Fin 3 ⊕ ↥(Set.range g)ᶜ) (Fin 3 ⊕ ↥(Set.range g)ᶜ) K).submatrix
    (eFr3 g hg) (eFr3 g hg)

theorem blk3_mul (g : Fin 3 → ι) (hg : Function.Injective g) (N N' : Matrix (Fin 3) (Fin 3) K) :
    blk3 g hg N * blk3 g hg N' = blk3 g hg (N * N') := by
  unfold blk3
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]

theorem blk3_one (g : Fin 3 → ι) (hg : Function.Injective g) :
    blk3 g hg (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold blk3
  rw [fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blk3_mulVec_g (g : Fin 3 → ι) (hg : Function.Injective g) (N : Matrix (Fin 3) (Fin 3) K)
    (v : ι → K) (k : Fin 3) : (blk3 g hg N *ᵥ v) (g k) = ∑ l, N k l * v (g l) := by
  unfold blk3 Matrix.mulVec dotProduct
  rw [← (eFr3 g hg).symm.sum_comp, Fintype.sum_sum_type]
  simp [eFr3_apply_g, eFr3_symm_inl]

theorem blk3_mulVec_of_not (g : Fin 3 → ι) (hg : Function.Injective g)
    (N : Matrix (Fin 3) (Fin 3) K) (v : ι → K) {a : ι} (ha : a ∉ Set.range g) :
    (blk3 g hg N *ᵥ v) a = v a := by
  obtain ⟨h, hea⟩ := eFr3_apply_of_not g hg ha
  unfold blk3 Matrix.mulVec dotProduct
  rw [← (eFr3 g hg).symm.sum_comp, Fintype.sum_sum_type]
  have h1 : (eFr3 g hg).symm (Sum.inr ⟨a, h⟩) = a := by
    rw [Equiv.symm_apply_eq]; exact hea.symm
  simp [hea, Matrix.one_apply, h1]

theorem blk4_blk3_commute (f : Fin 4 → ι) (g : Fin 3 → ι) (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ k l, f k ≠ g l) (N : Matrix (Fin 4) (Fin 4) K)
    (M : Matrix (Fin 3) (Fin 3) K) :
    blk4 f hf N * blk3 g hg M = blk3 g hg M * blk4 f hf N := by
  have hnf : ∀ k, g k ∉ Set.range f := fun k ⟨l, h⟩ => hfg l k h
  have hng : ∀ k, f k ∉ Set.range g := fun k ⟨l, h⟩ => hfg k l h.symm
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  funext a
  by_cases ha : a ∈ Set.range f
  · obtain ⟨k, rfl⟩ := ha
    rw [blk4_mulVec_f, blk3_mulVec_of_not g hg M _ (hng k), blk4_mulVec_f]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [blk3_mulVec_of_not g hg M _ (hng l)]
  · by_cases hb : a ∈ Set.range g
    · obtain ⟨k, rfl⟩ := hb
      rw [blk4_mulVec_of_not f hf N _ (hnf k), blk3_mulVec_g, blk3_mulVec_g]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [blk4_mulVec_of_not f hf N _ (hnf l)]
    · rw [blk4_mulVec_of_not f hf N _ ha, blk3_mulVec_of_not g hg M _ hb,
        blk3_mulVec_of_not g hg M _ hb, blk4_mulVec_of_not f hf N _ ha]

@[expose] def adjmat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0 ^ 2, -(A 0 1 ^ 2), -(2 * A 0 0 * A 0 1);
    -(A 1 0 ^ 2), A 1 1 ^ 2, 2 * A 1 0 * A 1 1;
    -(A 0 0 * A 1 0), A 0 1 * A 1 1, A 0 0 * A 1 1 + A 0 1 * A 1 0]

theorem adjmat_mul (A B : Matrix (Fin 2) (Fin 2) K) : adjmat (A * B) = adjmat A * adjmat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two] <;> ring

theorem adjmat_one : adjmat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjmat]

@[expose] def q3 (u : Fin 3 → K) : K := u 0 * u 1 + u 2 ^ 2

theorem q3_adjmat (A : Matrix (Fin 2) (Fin 2) K) (hA : A.det = 1) (u : Fin 3 → K) :
    q3 (adjmat A *ᵥ u) = q3 u := by
  rw [Matrix.det_fin_two] at hA
  simp only [q3, adjmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (u 0 * u 1 + u 2 ^ 2) * (A 0 0 * A 1 1 - A 0 1 * A 1 0 + 1) * hA

@[expose] noncomputable def adjGen (g : Fin 3 → ι) (hg : Function.Injective g) :
    SL(2, K) →* GL ι K :=
  MonoidHom.toHomUnits
    { toFun := fun A => blk3 g hg (adjmat (A : Matrix (Fin 2) (Fin 2) K))
      map_one' := by simp [adjmat_one, blk3_one]
      map_mul' := fun A B => by
        rw [Matrix.SpecialLinearGroup.coe_mul, adjmat_mul, ← blk3_mul] }

theorem coe_adjGen (g : Fin 3 → ι) (hg : Function.Injective g) (A : SL(2, K)) :
    ((adjGen g hg A : GL ι K) : Matrix ι ι K) = blk3 g hg (adjmat (A : Matrix (Fin 2) (Fin 2) K)) :=
  rfl

theorem adjGen_mem_omega (Q : (ι → K) → K) (g : Fin 3 → ι) (hg : Function.Injective g)
    (HQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range g → v a = w a) →
      Q v - Q w = q3 (v ∘ g) - q3 (w ∘ g))
    {a : K} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) (A : SL(2, K)) :
    adjGen g hg A ∈ StatedOmega Q := by
  have hperf : ⁅(⊤ : Subgroup SL(2, K)), ⊤⁆ = ⊤ := Matrix.SL2.commutator_eq_top ha hasq
  have hQb : ∀ (N : Matrix (Fin 3) (Fin 3) K), (∀ u, q3 (N *ᵥ u) = q3 u) →
      ∀ v : ι → K, Q (blk3 g hg N *ᵥ v) = Q v := by
    intro N hN v
    have h := HQ (blk3 g hg N *ᵥ v) v (fun a ha => blk3_mulVec_of_not g hg N v ha)
    have h2 : (blk3 g hg N *ᵥ v) ∘ g = N *ᵥ (v ∘ g) := by
      funext k
      rw [Function.comp_apply, blk3_mulVec_g]
      rfl
    rw [h2, hN] at h
    linear_combination h
  have hle : (⊤ : Subgroup SL(2, K)).map (adjGen g hg) ≤
      Subgroup.closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} := by
    rintro _ ⟨B, -, rfl⟩
    refine Subgroup.subset_closure ?_
    intro v
    rw [coe_adjGen]
    exact hQb _ (q3_adjmat _ B.2) v
  have hA : A ∈ ⁅(⊤ : Subgroup SL(2, K)), (⊤ : Subgroup SL(2, K))⁆ := by rw [hperf]; trivial
  have := Subgroup.mem_map_of_mem (adjGen g hg) hA
  rw [Subgroup.map_commutator] at this
  exact Subgroup.commutator_mono hle hle this

end Block

section Witness

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def negSL : SL(2, K) := ⟨-1, by simp [Matrix.det_neg]⟩

theorem negSL_mul_comm (A : SL(2, K)) : negSL * A = A * negSL := by
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) K) * A = A * (-1)
  simp

theorem negSL_sq : (negSL : SL(2, K)) ^ 2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change (-1 : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1
  simp [pow_two]

theorem mul_scalar_ne_of_coord {g h c : GL ι K} {a b : ι} (hab : a ≠ b)
    (hg : (g : Matrix ι ι K) *ᵥ Pi.single a 1 = Pi.single a 1)
    (hh : ((h : Matrix ι ι K) *ᵥ Pi.single a 1) b ≠ 0) (hc : c ∈ StatedScalars ι K) :
    g * c ≠ h := by
  obtain ⟨u, rfl⟩ := hc
  intro he
  have := congrFun (congrArg (fun k : GL ι K => (k : Matrix ι ι K) *ᵥ Pi.single a 1) he) b
  simp only [Units.val_mul, ← mulVec_mulVec, GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_one_eq_diagonal, smul_mulVec, one_mulVec, mulVec_smul, hg] at this
  apply hh
  rw [← this]
  simp [Pi.single_apply, hab.symm]

theorem three_le_localRank_omega [Finite K] (Q : (ι → K) → K) (f : Fin 4 → ι)
    (hf : Function.Injective f) (g : Fin 3 → ι) (hg : Function.Injective g)
    (hfg : ∀ k l, f k ≠ g l)
    (HQ : ∀ v w : ι → K, (∀ a, a ∉ Set.range f → v a = w a) →
      Q v - Q w = q4 (v ∘ f) - q4 (w ∘ f))
    (HQ3 : ∀ v w : ι → K, (∀ a, a ∉ Set.range g → v a = w a) →
      Q v - Q w = q3 (v ∘ g) - q3 (w ∘ g))
    (h2 : (2 : K) ≠ 0) (h4 : (2 : K) ^ 2 ≠ 1) :
    3 ≤ localRank 3 (StatedProj (StatedOmega Q)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup (GL ι K) := StatedOmega Q with hH
  set x : GL ι K := gen f hf lmat lmat_one lmat_mul c3 with hxdef
  set y : GL ι K := gen f hf rmat rmat_one rmat_mul c3 with hydef
  set z : GL ι K := adjGen g hg c3 with hzdef
  set t : GL ι K := gen f hf lmat lmat_one lmat_mul negSL with htdef
  have hxO : x ∈ H :=
    gen_mem_omega Q f hf HQ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) h2 h4 c3
  have hyO : y ∈ H :=
    gen_mem_omega Q f hf HQ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) h2 h4 c3
  have hzO : z ∈ H := adjGen_mem_omega Q g hg HQ3 h2 h4 c3
  have htO : t ∈ H :=
    gen_mem_omega Q f hf HQ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) h2 h4 negSL
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, c3_pow_three, map_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← map_pow, c3_pow_three, map_one]
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, c3_pow_three, map_one]
  have ht2 : t ^ 2 = 1 := by rw [htdef, ← map_pow, negSL_sq, map_one]
  have hxy : Commute x y := by
    ext1
    simp only [Units.val_mul, hxdef, hydef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hxz : Commute x z := by
    ext1
    simp only [Units.val_mul, hxdef, hzdef, coe_gen, coe_adjGen]
    exact blk4_blk3_commute f g hf hg hfg _ _
  have hyz : Commute y z := by
    ext1
    simp only [Units.val_mul, hydef, hzdef, coe_gen, coe_adjGen]
    exact blk4_blk3_commute f g hf hg hfg _ _
  have hxt : Commute x t := by
    rw [hxdef, htdef]
    exact Commute.map (negSL_mul_comm c3).symm _
  have hyt : Commute y t := by
    ext1
    simp only [Units.val_mul, hydef, htdef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hzt : Commute z t := by
    ext1
    simp only [Units.val_mul, hzdef, htdef, coe_gen, coe_adjGen]
    exact (blk4_blk3_commute f g hf hg hfg _ _).symm
  have hx1 : x ∉ StatedScalars ι K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g' : GL ι K => (g' : Matrix ι ι K) (f 0) (f 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hy1 : ∀ n : ℕ, ∀ s ∈ StatedScalars ι K, x ^ n * s ≠ y := by
    rintro n _ ⟨u, rfl⟩ hmc
    have key : ∀ k l, lmat (((c3 : SL(2, K)) ^ n : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l *
        (u : K) = rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l := by
      intro k l
      have h1 := congrArg (fun g' : GL ι K => (g' : Matrix ι ι K) (f k) (f l)) hmc
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
        Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
      exact h1
    have hn : (c3 : SL(2, K)) ^ n = c3 ^ (n % 3) := by
      conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
    rw [hn] at key
    have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : n % 3
    · have e := key 0 1
      simp [lmat, rmat, c3] at e
    · have e := key 0 0
      rw [pow_one] at e
      simp [lmat, rmat, c3] at e
    · have e := key 0 1
      rw [coe_c3_sq] at e
      simp [lmat, rmat, c3] at e
  have hn0 : g 0 ∉ Set.range f := fun ⟨k, hk⟩ => hfg k 0 hk
  have hz1 : ∀ n m : ℕ, ∀ s ∈ StatedScalars ι K, x ^ n * y ^ m * s ≠ z := by
    intro n m s hs
    have hfix : ((x ^ n * y ^ m : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (g 0) 1 =
        Pi.single (g 0) 1 := by
      rw [hxdef, hydef, ← map_pow, ← map_pow, Units.val_mul, coe_gen, coe_gen, blk4_mul]
      exact CFSG.HardMathSupport.Timmesfeld.DFour.blk4_mulVec_single_of_not f hf _ hn0
    have hzv : (((z : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (g 0) 1) (g 1) ≠ 0 := by
      rw [hzdef, coe_adjGen, blk3_mulVec_g]
      simp [Fin.sum_univ_three, Pi.single_apply, hg.eq_iff, adjmat, c3]
    exact mul_scalar_ne_of_coord (hg.ne (by decide)) hfix hzv hs
  have ht1 : t ∉ StatedScalars ι K := by
    rintro ⟨u, hu⟩
    have e1 : (u : K) = 1 := by
      have := congrFun (congrArg (fun g' : GL ι K => (g' : Matrix ι ι K) *ᵥ
        Pi.single (g 0) 1) hu) (g 0)
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
        smul_mulVec, one_mulVec] at this
      rw [htdef, coe_gen, blk4_mulVec_of_not f hf _ _ hn0] at this
      simpa using this
    have e2 : (u : K) = -1 := by
      have := congrFun (congrArg (fun g' : GL ι K => (g' : Matrix ι ι K) *ᵥ
        Pi.single (f 0) 1) hu) (f 0)
      simp only [GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal,
        smul_mulVec, one_mulVec] at this
      rw [htdef, coe_gen, blk4_mulVec_f] at this
      simpa [Fin.sum_univ_four, Pi.single_apply, hf.eq_iff, lmat, negSL] using this
    apply h2
    linear_combination e2 - e1
  set N : Subgroup H := (StatedScalars ι K).subgroupOf H with hN
  set π : H →* StatedProj H := QuotientGroup.mk' N with hπ
  have hmem : ∀ a b : H, π a = π b → ((a : GL ι K)⁻¹ * b) ∈ StatedScalars ι K :=
    fun a b h => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        hN, Subgroup.mem_subgroupOf] at h
      simpa using h
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H) (k : ℕ), a ^ k = 1 → π ⟨a, ha⟩ ^ k = 1 :=
    fun a ha k h => by
      rw [← map_pow]
      have : (⟨a, ha⟩ : H) ^ k = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
      rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hu1 : π ⟨t, htO⟩ ≠ 1 := fun h => ht1 (by
    have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this)
  have hu : orderOf (π ⟨t, htO⟩) = 2 :=
    orderOf_eq_prime (hpow t htO 2 ht2) hu1
  refine three_le_localRank_of_gens (hpow x hxO 3 hx3) (hpow y hyO 3 hy3) (hpow z hzO 3 hz3)
    (hcomm _ _ _ _ hxy) (hcomm _ _ _ _ hxz) (hcomm _ _ _ _ hyz) (fun h => hx1 ?_)
    (fun n h => ?_) (fun n m h => ?_) hu (hcomm _ _ _ _ hxt) (hcomm _ _ _ _ hyt)
    (hcomm _ _ _ _ hzt)
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

end Witness

section Forms

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {m : ℕ}

@[expose] def frame3 (a b : Fin m → ι) (i₀ : Fin m) (c : ι) : Fin 3 → ι := ![a i₀, b i₀, c]

theorem frame3_injective (a b : Fin m → ι) (hab : ∀ i j, a i ≠ b j) (i₀ : Fin m) {c : ι}
    (hca : ∀ i, a i ≠ c) (hcb : ∀ i, b i ≠ c) : Function.Injective (frame3 a b i₀ c) := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;>
    simp [frame3, hab, (hab _ _).symm, hca, hcb, (hca _).symm, (hcb _).symm] at hkl ⊢

theorem notMem_range_frame3 (a b : Fin m → ι) (ha : Function.Injective a)
    (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) (i₀ i : Fin m) {c : ι}
    (hca : ∀ i, a i ≠ c) (hcb : ∀ i, b i ≠ c) (h : i ≠ i₀) :
    a i ∉ Set.range (frame3 a b i₀ c) ∧ b i ∉ Set.range (frame3 a b i₀ c) := by
  constructor <;>
  · rintro ⟨k, hk⟩
    fin_cases k <;>
      simp [frame3, ha.eq_iff, hb.eq_iff, hab, (hab _ _).symm, hca, hcb, (hca _).symm,
        (hcb _).symm, h, h.symm] at hk

theorem frame4_frame3_disjoint (a b : Fin m → ι) (ha : Function.Injective a)
    (hb : Function.Injective b) (hab : ∀ i j, a i ≠ b j) {i0 i1 i₀ : Fin m} {c : ι}
    (hca : ∀ i, a i ≠ c) (hcb : ∀ i, b i ≠ c) (h0 : i₀ ≠ i0) (h1 : i₀ ≠ i1) :
    ∀ k l, frame4 a b i0 i1 k ≠ frame3 a b i₀ c l := by
  intro k l
  fin_cases k <;> fin_cases l <;>
    simp [frame4, frame3, ha.eq_iff, hb.eq_iff, hab, (hab _ _).symm, hca, hcb, h0, h1,
      h0.symm, h1.symm]

theorem hq3_of_sum (a b : Fin m → ι) (ha : Function.Injective a) (hb : Function.Injective b)
    (hab : ∀ i j, a i ≠ b j) (i₀ : Fin m) {c : ι} (hca : ∀ i, a i ≠ c) (hcb : ∀ i, b i ≠ c)
    (Q R : (ι → K) → K)
    (hR : ∀ v w : ι → K, (∀ x, x ∉ Set.range (frame3 a b i₀ c) → v x = w x) →
      R v - R w = v c ^ 2 - w c ^ 2)
    (hQ : ∀ v, Q v = ∑ i, v (a i) * v (b i) + R v) :
    ∀ v w : ι → K, (∀ x, x ∉ Set.range (frame3 a b i₀ c) → v x = w x) →
      Q v - Q w = q3 (v ∘ frame3 a b i₀ c) - q3 (w ∘ frame3 a b i₀ c) := by
  intro v w hvw
  have hs : ∑ i, v (a i) * v (b i) - ∑ i, w (a i) * w (b i) =
      v (a i₀) * v (b i₀) - w (a i₀) * w (b i₀) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i₀]
    · intro i _ hi
      obtain ⟨h1, h2⟩ := notMem_range_frame3 a b ha hb hab i₀ i hca hcb hi
      rw [hvw _ h1, hvw _ h2, sub_self]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hRv := hR v w hvw
  rw [hQ v, hQ w]
  simp only [q3, frame3, Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination hs + hRv

theorem three_le_localRank_odd [Finite K] {n : ℕ} (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0)
    (h4 : (2 : K) ^ 2 ≠ 1) :
    3 ≤ localRank 3 (StatedProj (StatedOmega (StatedQuadOdd n K))) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set a : Fin n → Fin n ⊕ Fin n ⊕ Unit := Sum.inl
  set b : Fin n → Fin n ⊕ Fin n ⊕ Unit := fun i => Sum.inr (Sum.inl i)
  set c : Fin n ⊕ Fin n ⊕ Unit := Sum.inr (Sum.inr ())
  have ha : Function.Injective a := Sum.inl_injective
  have hb : Function.Injective b := fun i j h => by simpa [b] using h
  have hab : ∀ i j, a i ≠ b j := fun i j => by simp [a, b]
  have hca : ∀ i, a i ≠ c := fun i => by simp [a, c]
  have hcb : ∀ i, b i ≠ c := fun i => by simp [b, c]
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [i0, i2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
  have hQ : ∀ v, StatedQuadOdd n K v = ∑ i, v (a i) * v (b i) + v c ^ 2 :=
    fun v => by simp [StatedQuadOdd, a, b, c]
  have HQ : ∀ v w : (Fin n ⊕ Fin n ⊕ Unit) → K,
      (∀ x, x ∉ Set.range (frame4 a b i0 i1) → v x = w x) →
      StatedQuadOdd n K v - StatedQuadOdd n K w =
        q4 (v ∘ frame4 a b i0 i1) - q4 (w ∘ frame4 a b i0 i1) := by
    refine hq_of_sum a b ha hb hab i0 i1 h01 _ (fun v => v c ^ 2) ?_ hQ
    intro v w h
    have hc : c ∉ Set.range (frame4 a b i0 i1) := by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [frame4, a, b, c] at hk
    simp only [h _ hc]
  have HQ3 := hq3_of_sum a b ha hb hab i2 hca hcb _ (fun v => v c ^ 2)
    (fun v w _ => rfl) hQ
  exact three_le_localRank_omega _ (frame4 a b i0 i1) (frame4_injective a b ha hb hab i0 i1 h01)
    (frame3 a b i2 c) (frame3_injective a b hab i2 hca hcb)
    (frame4_frame3_disjoint a b ha hb hab hca hcb h20 h21) HQ HQ3 h2 h4

theorem three_le_localRank_minus [Finite K] {n : ℕ} (hn : 4 ≤ n) (h2 : (2 : K) ≠ 0)
    (h4 : (2 : K) ^ 2 ≠ 1) (c' : K) :
    3 ≤ localRank 3 (StatedProj (StatedOmega (StatedQuadMinus n K 0 c'))) := by
  set i0 : Fin (n - 1) := ⟨0, by omega⟩
  set i1 : Fin (n - 1) := ⟨1, by omega⟩
  set i2 : Fin (n - 1) := ⟨2, by omega⟩
  set a : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := Sum.inl
  set b : Fin (n - 1) → Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := fun i => Sum.inr (Sum.inl i)
  set c : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := Sum.inr (Sum.inr 0)
  set d : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 := Sum.inr (Sum.inr 1)
  have ha : Function.Injective a := Sum.inl_injective
  have hb : Function.Injective b := fun i j h => by simpa [b] using h
  have hab : ∀ i j, a i ≠ b j := fun i j => by simp [a, b]
  have hca : ∀ i, a i ≠ c := fun i => by simp [a, c]
  have hcb : ∀ i, b i ≠ c := fun i => by simp [b, c]
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h20 : i2 ≠ i0 := by simp [i0, i2, Fin.ext_iff]
  have h21 : i2 ≠ i1 := by simp [i1, i2, Fin.ext_iff]
  have hQ : ∀ v, StatedQuadMinus n K 0 c' v =
      ∑ i, v (a i) * v (b i) + (v c ^ 2 + 0 * v c * v d + c' * v d ^ 2) :=
    fun v => by simp [StatedQuadMinus, a, b, c, d, add_assoc]
  have hd4 : d ∉ Set.range (frame4 a b i0 i1) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame4, a, b, d] at hk
  have hc4 : c ∉ Set.range (frame4 a b i0 i1) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame4, a, b, c] at hk
  have hd3 : d ∉ Set.range (frame3 a b i2 c) := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [frame3, a, b, c, d] at hk
  have HQ : ∀ v w : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) → K,
      (∀ x, x ∉ Set.range (frame4 a b i0 i1) → v x = w x) →
      StatedQuadMinus n K 0 c' v - StatedQuadMinus n K 0 c' w =
        q4 (v ∘ frame4 a b i0 i1) - q4 (w ∘ frame4 a b i0 i1) := by
    refine hq_of_sum a b ha hb hab i0 i1 h01 _
      (fun v => v c ^ 2 + 0 * v c * v d + c' * v d ^ 2) ?_ hQ
    intro v w h
    simp only [h _ hc4, h _ hd4]
  have HQ3 := hq3_of_sum a b ha hb hab i2 hca hcb _
    (fun v => v c ^ 2 + 0 * v c * v d + c' * v d ^ 2)
    (fun v w h => by simp only [h _ hd3]; ring) hQ
  exact three_le_localRank_omega _ (frame4 a b i0 i1) (frame4_injective a b ha hb hab i0 i1 h01)
    (frame3 a b i2 c) (frame3_injective a b hab i2 hca hcb)
    (frame4_frame3_disjoint a b ha hb hab hca hcb h20 h21) HQ HQ3 h2 h4

end Forms

section Models

theorem three_le_twoLocalRank_of_odd {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaOdd n ℓ f) (hℓ3 : ℓ ≠ 3) : 3 ≤ GLATwoLocalRank 3 G := by
  obtain ⟨⟨hℓ, hf, hn, hℓ2⟩, K, _, _, hK, ⟨e⟩⟩ := h
  haveI := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨c2, c4⟩ := char_facts (K := K) hℓ hℓ2 hℓ3
  haveI : Finite (StatedProj (StatedOmega (StatedQuadOdd n K))) := Finite.of_equiv G e.toEquiv
  change 3 ≤ localRank 3 G
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  exact three_le_localRank_odd hn c2 c4

theorem three_le_twoLocalRank_of_minus {G : Type} [Group G] [Finite G] {n ℓ f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n ℓ f) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) :
    3 ≤ GLATwoLocalRank 3 G := by
  obtain ⟨⟨hℓ, hf, hn⟩, K, _, _, hK, -, -, -, -⟩ := id h
  haveI := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  haveI := Fintype.ofFinite K
  obtain ⟨c2, c4⟩ := char_facts (K := K) hℓ hℓ2 hℓ3
  have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  obtain ⟨δ, hδ⟩ := FiniteField.exists_nonsquare (F := K) hrc
  have hirr : ∀ s : K, s ^ 2 + 0 * s + -δ ≠ 0 := fun s hs =>
    hδ ⟨s, by linear_combination -hs⟩
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K 0 (-δ))))
      .POmegaMinus n ℓ f :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, 0, -δ, hirr, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h hM
  haveI : Finite (StatedProj (StatedOmega (StatedQuadMinus n K 0 (-δ)))) :=
    Finite.of_equiv G e.toEquiv
  change 3 ≤ localRank 3 G
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  exact three_le_localRank_minus hn c2 c4 (-δ)

end Models

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.OrthWit

end
