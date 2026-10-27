module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerOTwo
import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

variable {K : Type*} [Field K]

theorem proj_transvection_ne_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) {c : K} (hc : c ≠ 0) :
    LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hij c) ≠ 1 := by
  rw [Ne, LinearFlag.proj_eq_one_iff]
  rintro ⟨d, -, hd⟩
  have h := congrFun (congrFun hd i) j
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne hij,
    single_apply, ite_eq_left ⟨rfl, rfl⟩, scalar_apply, diagonal_apply_ne _ hij, zero_add] at h
  exact hc h

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k)

theorem mat_mem_radical : P.mat K ∈ P.radical K := by
  intro i j hij
  rw [coe_mat, Matrix.add_apply, P.nil_apply_of_le hij, add_zero]

theorem elt_mem_radicalP : P.elt K ∈ P.radicalP K :=
  Subgroup.mem_map_of_mem _ P.mat_mem_radical

theorem commutator_radicalP_ne_bot (hk : 0 < k) (hJ : P.free.Nonempty) :
    ⁅P.radicalP K, P.radicalP K⁆ ≠ ⊥ := by
  intro h
  set a : Fin k := ⟨0, hk⟩
  have hmem : LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection (P.u_ne_w a a) (1 : K)) ∈
      ⁅P.radicalP K, P.radicalP K⁆ := by
    rw [radicalP, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ (P.transvection_u_w_mem_commutator hJ a a 1)
  rw [h, Subgroup.mem_bot] at hmem
  exact proj_transvection_ne_one (P.u_ne_w a a) one_ne_zero hmem

theorem commutator_radical_apply_eq {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ ⁅P.radical K, P.radical K⁆) {i j : Fin n} (hij : ¬ (P.level i = 0 ∧ P.level j = 2)) :
    (x : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  have hxR : x ∈ P.radical K :=
    (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)) hx
  by_cases hle : P.level j ≤ P.level i
  · exact hxR i j hle
  · refine P.commutator_radical_le hx i j ?_
    by_contra h
    push Not at h
    obtain ⟨s, hs⟩ := P.mem_outer.1 h.1
    obtain ⟨t, ht⟩ := P.mem_outer.1 h.2
    rcases s with a | a <;> rcases t with b | b
    · simp only [supp, Sum.elim_inl] at hs ht
      subst hs ht
      rw [level_u, level_u] at hle
      exact hle le_rfl
    · simp only [supp, Sum.elim_inl, Sum.elim_inr] at hs ht
      subst hs ht
      exact hij ⟨P.level_u a, P.level_w b⟩
    · simp only [supp, Sum.elim_inl, Sum.elim_inr] at hs ht
      subst hs ht
      rw [level_w, level_u] at hle
      exact hle (by norm_num)
    · simp only [supp, Sum.elim_inr] at hs ht
      subst hs ht
      rw [level_w, level_w] at hle
      exact hle le_rfl

theorem commute_of_mem_commutator_radical {x r : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ ⁅P.radical K, P.radical K⁆) (hr : r ∈ P.radical K) : Commute x r := by
  set X := (x : Matrix (Fin n) (Fin n) K) - 1 with hXdef
  set Y := (r : Matrix (Fin n) (Fin n) K) - 1 with hYdef
  have hX : ∀ i j, ¬ (P.level i = 0 ∧ P.level j = 2) → X i j = 0 := fun i j h => by
    rw [hXdef, Matrix.sub_apply, P.commutator_radical_apply_eq hx h, sub_self]
  have hY : ∀ i j, P.level j ≤ P.level i → Y i j = 0 := fun i j h => by
    rw [hYdef, Matrix.sub_apply, hr i j h, sub_self]
  have hXY : X * Y = 0 := by
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : P.level i = 0 ∧ P.level l = 2
    · rw [hY l j (by have := P.level_le_two j; omega), mul_zero]
    · rw [hX i l h, zero_mul]
  have hYX : Y * X = 0 := by
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h : P.level l = 0 ∧ P.level j = 2
    · rw [hY i l (by omega), zero_mul]
    · rw [hX l j h, mul_zero]
  have hx' : (x : Matrix (Fin n) (Fin n) K) = 1 + X := by rw [hXdef]; abel
  have hr' : (r : Matrix (Fin n) (Fin n) K) = 1 + Y := by rw [hYdef]; abel
  apply Subtype.ext
  change (x : Matrix (Fin n) (Fin n) K) * (r : Matrix (Fin n) (Fin n) K) =
    (r : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
  have e1 : (1 + X) * (1 + Y) = 1 + X + Y + X * Y := by noncomm_ring
  have e2 : (1 + Y) * (1 + X) = 1 + Y + X + Y * X := by noncomm_ring
  rw [hx', hr', e1, e2, hXY, hYX]
  abel

theorem radicalP_le_centralizer_commutator :
    P.radicalP K ≤ Subgroup.centralizer
      ((⁅P.radicalP K, P.radicalP K⁆ : Subgroup (LinearFlag.projectiveSL n K)) :
        Set (LinearFlag.projectiveSL n K)) := by
  rintro _ ⟨r, hr, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [radicalP, ← Subgroup.map_commutator] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [← map_mul, ← map_mul, (P.commute_of_mem_commutator_radical hx hr).eq]

theorem commutator_radical_eq_bot_of_free_eq_empty (hJ : P.free = ∅) :
    ⁅P.radical K, P.radical K⁆ = ⊥ := by
  have hlev : ∀ i, P.level i ≠ 1 := fun i h => by
    have : i ∈ P.free := P.mem_free.2 h
    rw [hJ] at this
    exact Finset.notMem_empty i this
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx r hr
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  set X := (x : Matrix (Fin n) (Fin n) K) - 1 with hXdef
  set Y := (r : Matrix (Fin n) (Fin n) K) - 1 with hYdef
  have hX : ∀ i j, P.level j ≤ P.level i → X i j = 0 := fun i j h => by
    rw [hXdef, Matrix.sub_apply, hx i j h, sub_self]
  have hY : ∀ i j, P.level j ≤ P.level i → Y i j = 0 := fun i j h => by
    rw [hYdef, Matrix.sub_apply, hr i j h, sub_self]
  have hprod : ∀ A B : Matrix (Fin n) (Fin n) K, (∀ i j, P.level j ≤ P.level i → A i j = 0) →
      (∀ i j, P.level j ≤ P.level i → B i j = 0) → A * B = 0 := by
    intro A B hA hB
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : P.level l ≤ P.level i
    · rw [hA i l h1, zero_mul]
    · have hl1 := hlev l
      have hi2 := P.level_le_two i
      have hj2 := P.level_le_two j
      rw [hB l j (by omega), mul_zero]
  have hx' : (x : Matrix (Fin n) (Fin n) K) = 1 + X := by rw [hXdef]; abel
  have hr' : (r : Matrix (Fin n) (Fin n) K) = 1 + Y := by rw [hYdef]; abel
  apply Subtype.ext
  change (x : Matrix (Fin n) (Fin n) K) * (r : Matrix (Fin n) (Fin n) K) =
    (r : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
  have e1 : (1 + X) * (1 + Y) = 1 + X + Y + X * Y := by noncomm_ring
  have e2 : (1 + Y) * (1 + X) = 1 + Y + X + Y * X := by noncomm_ring
  rw [hx', hr', e1, e2, hprod X Y hX hY, hprod Y X hY hX]
  abel

theorem commutator_radicalP_eq_bot_of_free_eq_empty (hJ : P.free = ∅) :
    ⁅P.radicalP K, P.radicalP K⁆ = ⊥ := by
  rw [radicalP, ← Subgroup.map_commutator, P.commutator_radical_eq_bot_of_free_eq_empty hJ,
    Subgroup.map_bot]

theorem le_radicalP_of_isPGroup_of_free_eq_empty [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hk : 0 < k) (hJ : P.free = ∅) {T : Subgroup (LinearFlag.projectiveSL n K)}
    (hT : IsPGroup 2 T) (hTΛ : T ≤ (P.core K).map (LinearFlag.proj n K))
    (hN : (P.core K).map (LinearFlag.proj n K) ≤
      Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K))) :
    T ≤ P.radicalP K := by
  set T' : Subgroup (P.core K) := T.comap ((LinearFlag.proj n K).comp (P.core K).subtype)
    with hT'
  have hT'n : T'.Normal := by
    constructor
    intro x hx c
    have hc : LinearFlag.proj n K c ∈ Subgroup.normalizer (T : Set _) := hN ⟨c, c.2, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hc
    have := (hc (LinearFlag.proj n K x)).1 hx
    show LinearFlag.proj n K ((c * x * c⁻¹ : P.core K) : SpecialLinearGroup (Fin n) K) ∈ T
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
  have h2pow : ∀ x ∈ T', ∃ e : ℕ,
      ((x : SpecialLinearGroup (Fin n) K) ^ 2 ^ e) ∈ LinearFlag.scalars n K := by
    intro x hx
    obtain ⟨e, he⟩ := hT ⟨LinearFlag.proj n K x, hx⟩
    refine ⟨e, ?_⟩
    rw [← LinearFlag.proj_eq_one_iff, map_pow]
    exact congrArg Subtype.val he
  have hscalU : ∀ x : P.core K, (x : SpecialLinearGroup (Fin n) K) ∈ LinearFlag.scalars n K →
      P.coreU K x ∈ Subgroup.center (SpecialLinearGroup (Fin k) K) := by
    intro x hx
    obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have : ((P.coreU K x : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        scalar (Fin k) (c : K) := by
      show ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = _
      rw [hc]
      ext a b
      simp [scalar_apply, diagonal_apply, P.u_injective.eq_iff]
    rw [this]
    exact (scalar_commute (c : K) (fun _ => Commute.all _ _) _).symm
  have hU : ∀ x ∈ T', P.coreU K x ∈ Subgroup.center (SpecialLinearGroup (Fin k) K) := by
    have : (T'.map (P.coreU K)).Normal := hT'n.map _ P.coreU_surjective
    have hle := le_center_of_normal_of_two_pow hq (T'.map (P.coreU K)) (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨e, he⟩ := h2pow x hx
      exact ⟨e, by rw [← map_pow]; exact hscalU _ he⟩)
    exact fun x hx => hle ⟨x, hx, rfl⟩
  intro t ht
  obtain ⟨B, hB, rfl⟩ := hTΛ ht
  set x : P.core K := ⟨B, hB⟩
  have hx : x ∈ T' := ht
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hU x hx)
  have hBu : ∀ a b, (B : Matrix (Fin n) (Fin n) K) (P.u a) (P.u b) = if a = b then r else 0 := by
    intro a b
    have := congrFun (congrFun hr a) b
    rw [scalar_apply, diagonal_apply] at this
    exact this.symm
  obtain ⟨e, he⟩ := h2pow x hx
  obtain ⟨c, hcn, hc⟩ := LinearFlag.mem_scalars.1 he
  set a₀ : Fin k := ⟨0, hk⟩
  have hcr : (c : K) = r ^ 2 ^ e := by
    have h1 := congrArg (fun X : SpecialLinearGroup (Fin k) K =>
      (X : Matrix (Fin k) (Fin k) K) a₀ a₀) (map_pow (P.coreU K) x (2 ^ e))
    have hd : ((P.coreU K x : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        scalar (Fin k) r := by
      ext i j
      show (B : Matrix (Fin n) (Fin n) K) (P.u i) (P.u j) = _
      rw [hBu i j, scalar_apply, diagonal_apply]
    rw [Matrix.SpecialLinearGroup.coe_pow, hd, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
    have h2 : ((x ^ 2 ^ e : P.core K) : SpecialLinearGroup (Fin n) K) (P.u a₀) (P.u a₀) = c := by
      rw [Subgroup.coe_pow, hc, scalar_apply, diagonal_apply_eq]
    rw [← h2]
    exact h1
  have hrn : r ^ n = 1 := by
    refine eq_of_pow_two_pow_eq (e := e) ?_
    rw [← pow_mul, mul_comm, pow_mul, ← hcr, one_pow, ← Units.val_pow_eq_pow_val, hcn,
      Units.val_one]
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (P.u a₀).elim0
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hrn
    exact zero_ne_one hrn
  set z := LinearFlag.scalarElement (n := n) (Units.mk0 r hr0)⁻¹ (by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hrn, inv_one,
      Units.val_one])
  have hz : z ∈ LinearFlag.scalars n K := LinearFlag.scalarElement_mem_scalars _ _
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    LinearFlag.scalars_le_center n K hz
  have hcoe : ((B * z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * scalar (Fin n) r⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_scalarElement, Units.val_inv_eq_inv_val,
      Units.val_mk0]
  have hBz : B * z ∈ P.radical K := by
    refine P.mem_radical_of_blocks (mul_mem (P.core_le_centralizer hB) ?_) (fun a b => ?_)
      (fun i j hi _ => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact (Subgroup.mem_center_iff.1 hzc h)
    · rw [hcoe, scalar_apply, mul_diagonal, hBu a b, one_apply_of_injective P.u_injective,
        one_apply]
      split_ifs with hab
      · exact mul_inv_cancel₀ hr0
      · exact zero_mul _
    · rw [hJ] at hi
      exact absurd hi (Finset.notMem_empty i)
  have hπz : LinearFlag.proj n K z = 1 := LinearFlag.proj_eq_one_iff.2 hz
  refine ⟨B * z, hBz, ?_⟩
  rw [map_mul, hπz, mul_one]

theorem leviOneHom_transvection {a b : Fin k} (hab : a ≠ b) (c : K) :
    P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hab c) =
      Matrix.SpecialLinearGroup.transvection (P.u_injective.ne hab) c *
        Matrix.SpecialLinearGroup.transvection (P.w_injective.ne hab) c := by
  have hwu : ∀ x y, P.w x ≠ P.u y := fun x y => (P.u_ne_w y x).symm
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe]
  have hprod : (1 + single (P.u a) (P.u b) c) * (1 + single (P.w a) (P.w b) c) =
      1 + single (P.u a) (P.u b) c + single (P.w a) (P.w b) c := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, single_mul_single_of_ne _ _ _ _ (P.u_ne_w b a), add_zero]
    abel
  rw [hprod]
  by_cases h : i ∈ P.outer ∧ j ∈ P.outer
  · obtain ⟨s, rfl⟩ := P.mem_outer.1 h.1
    obtain ⟨t, rfl⟩ := P.mem_outer.1 h.2
    rw [leviOneHom_apply_supp, Matrix.SpecialLinearGroup.transvection_coe]
    rcases s with x | x <;> rcases t with y | y <;>
      simp [supp, single_apply, one_apply, P.u_injective.eq_iff, P.w_injective.eq_iff,
        P.u_ne_w, hwu]
  · rw [P.leviOneHom_apply_of_not_mem_outer _ (not_and_or.1 h), Matrix.add_apply,
      Matrix.add_apply, single_apply, single_apply, ite_eq_right, ite_eq_right, add_zero,
      add_zero]
    · rintro ⟨rfl, rfl⟩
      exact h ⟨P.w_mem_outer a, P.w_mem_outer b⟩
    · rintro ⟨rfl, rfl⟩
      exact h ⟨P.u_mem_outer a, P.u_mem_outer b⟩

theorem commutatorElement_mul_left_of_commute {G : Type*} [Group G] {x y z : G}
    (h : Commute y z) : ⁅x * y, z⁆ = ⁅x, z⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z) * y⁻¹ * x⁻¹ * z⁻¹ := by group
    _ = x * (z * y) * y⁻¹ * x⁻¹ * z⁻¹ := by rw [h.eq]
    _ = x * z * x⁻¹ * z⁻¹ := by group

theorem commutatorElement_mul_right_of_commute {G : Type*} [Group G] {x y z : G}
    (h : Commute x z) : ⁅z, x * y⁆ = x * ⁅z, y⁆ * x⁻¹ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * (x * y) * z⁻¹ * (x * y)⁻¹ = (z * x) * y * z⁻¹ * y⁻¹ * x⁻¹ := by group
    _ = (x * z) * y * z⁻¹ * y⁻¹ * x⁻¹ := by rw [h.symm.eq]
    _ = x * (z * y * z⁻¹ * y⁻¹) * x⁻¹ := by group

theorem u_ne_of_mem_free {l : Fin n} (hl : l ∈ P.free) (a : Fin k) : P.u a ≠ l :=
  fun h => P.u_not_mem_free a (h ▸ hl)

theorem ne_w_of_mem_free {l : Fin n} (hl : l ∈ P.free) (a : Fin k) : l ≠ P.w a :=
  fun h => P.w_not_mem_free a (h ▸ hl)

theorem transvection_u_free_mem_commutator (hk : 2 ≤ k) {l : Fin n} (hl : l ∈ P.free)
    (a : Fin k) (c : K) :
    Matrix.SpecialLinearGroup.transvection (P.u_ne_of_mem_free hl a) c ∈
      ⁅P.leviOne K, P.radical K⁆ := by
  obtain ⟨b, hba⟩ : ∃ b : Fin k, b ≠ a := by
    by_cases h : a = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [h, Fin.ext_iff] at h'; simp at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  have hab : a ≠ b := hba.symm
  have hr : Matrix.SpecialLinearGroup.transvection (P.u_ne_of_mem_free hl b) c ∈ P.radical K :=
    P.transvection_mem_radical _ (by rw [level_u, P.mem_free.1 hl]; omega) c
  have hm : P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hab 1) ∈ P.leviOne K :=
    ⟨_, rfl⟩
  have key : ⁅P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hab 1),
      Matrix.SpecialLinearGroup.transvection (P.u_ne_of_mem_free hl b) c⁆ =
      Matrix.SpecialLinearGroup.transvection (P.u_ne_of_mem_free hl a) c := by
    rw [leviOneHom_transvection, commutatorElement_mul_left_of_commute
      (Matrix.SpecialLinearGroup.commute_transvection _ _ (P.u_ne_w b b).symm
        (P.ne_w_of_mem_free hl a) 1 c),
      Matrix.SpecialLinearGroup.commutatorElement_transvection _ _ (P.u_ne_of_mem_free hl a) 1 c,
      one_mul]
  rw [← key]
  exact Subgroup.commutator_mem_commutator hm hr

theorem transvection_free_w_mem_commutator (hk : 2 ≤ k) {l : Fin n} (hl : l ∈ P.free)
    (a : Fin k) (c : K) :
    Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl a) c ∈
      ⁅P.leviOne K, P.radical K⁆ := by
  obtain ⟨b, hba⟩ : ∃ b : Fin k, b ≠ a := by
    by_cases h : a = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [h, Fin.ext_iff] at h'; simp at h'⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h h'.symm⟩
  have hr : Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl b) c ∈ P.radical K :=
    P.transvection_mem_radical _ (by rw [level_w, P.mem_free.1 hl]; omega) c
  have hm : P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hba 1) ∈ P.leviOne K :=
    ⟨_, rfl⟩
  have hT₁ : Commute (Matrix.SpecialLinearGroup.transvection (P.u_injective.ne hba) (1 : K))
      (Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl b) c) :=
    Matrix.SpecialLinearGroup.commute_transvection _ _ (P.u_ne_of_mem_free hl a)
      (P.u_ne_w b b).symm 1 c
  have hT₁' : Commute (Matrix.SpecialLinearGroup.transvection (P.u_injective.ne hba) (1 : K))
      (Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl a) c) :=
    Matrix.SpecialLinearGroup.commute_transvection _ _ (P.u_ne_of_mem_free hl a)
      (P.u_ne_w b a).symm 1 c
  have key : ⁅Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl b) c,
      P.leviOneHom K (Matrix.SpecialLinearGroup.transvection hba 1)⁆ =
      Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hl a) c := by
    rw [leviOneHom_transvection, commutatorElement_mul_right_of_commute hT₁,
      Matrix.SpecialLinearGroup.commutatorElement_transvection _ _ (P.ne_w_of_mem_free hl a) c 1,
      mul_one, hT₁'.eq,
      mul_inv_cancel_right]
  rw [← key, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator hr hm

variable (K) in
@[expose] noncomputable def blockFree : P.parabolic K →* Matrix P.free P.free K where
  toFun B := ((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
    (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n)
  map_one' := by
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ Subtype.val_injective]
  map_mul' B B' := by
    show (((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n) = _
    rw [Matrix.SpecialLinearGroup.coe_mul,
      P.submatrix_mul_free (P.mem_parabolic.1 B.2) (P.mem_parabolic.1 B'.2)]

theorem submatrix_u_mem_range_scalar_of_commute {m : SpecialLinearGroup (Fin n) K}
    (hm : ∀ a b, m * Matrix.SpecialLinearGroup.transvection (P.u_ne_w a b) 1 =
      Matrix.SpecialLinearGroup.transvection (P.u_ne_w a b) 1 * m) :
    (m : Matrix (Fin n) (Fin n) K).submatrix P.u P.u ∈ Set.range (scalar (Fin k)) :=
  mem_range_scalar_of_commute_single fun _ _ _ =>
    (P.commute_submatrix_u_of_commute hm _).symm

theorem commutatorElement_mem_radical_of_free_card_eq_one (hJ : P.free.card = 1)
    {B B' : SpecialLinearGroup (Fin n) K} (hB : B ∈ Subgroup.centralizer {P.mat K})
    (hB' : B' ∈ Subgroup.centralizer {P.mat K})
    (hBs : (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u ∈ Set.range (scalar (Fin k)))
    (hB's : (B' : Matrix (Fin n) (Fin n) K).submatrix P.u P.u ∈ Set.range (scalar (Fin k))) :
    ⁅B, B'⁆ ∈ P.radical K := by
  have hsub : Subsingleton P.free := by
    obtain ⟨l, hl⟩ := Finset.card_eq_one.1 hJ
    refine ⟨fun x y => Subtype.ext ?_⟩
    have hx : (x : Fin n) ∈ ({l} : Finset (Fin n)) := hl ▸ x.2
    have hy : (y : Fin n) ∈ ({l} : Finset (Fin n)) := hl ▸ y.2
    rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]
  have hcommF : ∀ X Y : Matrix P.free P.free K, Commute X Y := by
    intro X Y
    ext i j
    rw [mul_apply, mul_apply, Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i,
      Subsingleton.elim j i, mul_comm]
  set p : P.parabolic K := ⟨B, P.centralizer_le_parabolic hB⟩
  set p' : P.parabolic K := ⟨B', P.centralizer_le_parabolic hB'⟩
  have hc : ((⁅p, p'⁆ : P.parabolic K) : SpecialLinearGroup (Fin n) K) = ⁅B, B'⁆ := rfl
  have hU : P.blockU K ⁅p, p'⁆ = 1 := by
    refine map_commutatorElement_eq_one_of_commute _ ?_
    obtain ⟨r, hr⟩ := hBs
    obtain ⟨r', hr'⟩ := hB's
    show Commute ((B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u)
      ((B' : Matrix (Fin n) (Fin n) K).submatrix P.u P.u)
    rw [← hr, ← hr']
    exact (scalar_commute r (fun _ => Commute.all _ _) _)
  have hF : P.blockFree K ⁅p, p'⁆ = 1 :=
    map_commutatorElement_eq_one_of_commute _ (hcommF _ _)
  have hmem : ⁅B, B'⁆ ∈ Subgroup.centralizer {P.mat K} := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hB hB') (inv_mem hB)) (inv_mem hB')
  refine P.mem_radical_of_blocks hmem (fun a b => ?_) (fun i j hi hj => ?_)
  · have := congrFun (congrFun hU a) b
    rw [← hc, one_apply_of_injective P.u_injective]
    exact this
  · have := congrFun (congrFun hF ⟨i, hi⟩) ⟨j, hj⟩
    rw [← hc]
    change ((⁅p, p'⁆ : P.parabolic K) : SpecialLinearGroup (Fin n) K) i j = _
    have e : (1 : Matrix P.free P.free K) ⟨i, hi⟩ ⟨j, hj⟩ = (1 : Matrix (Fin n) (Fin n) K) i j :=
      (one_apply_of_injective Subtype.val_injective ⟨i, hi⟩ ⟨j, hj⟩).symm
    rw [← e]
    exact this

end InvPlacement

section Rank

variable {n k : ℕ}

open Subgroup in
theorem le_normalizer_of_forall_isPGroup_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    {H Λ Q : Subgroup G} (hHΛ : H ≤ normalizer (Λ : Set G)) (hQΛ : Q ≤ Λ) (hQ : IsPGroup p Q)
    (hΛQ : Λ ≤ normalizer (Q : Set G))
    (hmax : ∀ T : Subgroup G, IsPGroup p T → T ≤ Λ → Λ ≤ normalizer (T : Set G) → T ≤ Q) :
    H ≤ normalizer (Q : Set G) := by
  intro h hh
  have hmemT : ∀ g, g ∈ Q.map (MulAut.conj h).toMonoidHom ↔ h⁻¹ * g * h ∈ Q := fun g => by
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  set T := Q.map (MulAut.conj h).toMonoidHom with hT
  have hhN : h ∈ normalizer (Λ : Set G) := hHΛ hh
  have hhN' : h⁻¹ ∈ normalizer (Λ : Set G) := inv_mem hhN
  have hTΛ : T ≤ Λ := fun g hg => by
    have h1 := (hmemT g).1 hg
    have h2 := (mem_normalizer_iff.1 hhN (h⁻¹ * g * h)).1 (hQΛ h1)
    simpa [mul_assoc] using h2
  have hΛT : Λ ≤ normalizer (T : Set G) := by
    intro x hx
    have hx' : h⁻¹ * x * h ∈ Λ := by
      have h1 := (mem_normalizer_iff.1 hhN' x).1 hx
      simpa [mul_assoc] using h1
    rw [mem_normalizer_iff]
    intro g
    rw [hmemT, hmemT]
    have e : h⁻¹ * (x * g * x⁻¹) * h =
        (h⁻¹ * x * h) * (h⁻¹ * g * h) * (h⁻¹ * x * h)⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.1 (hΛQ hx') _
  have hle := hmax T (hQ.map _) hTΛ hΛT
  have hcardT : Nat.card T = Nat.card Q :=
    Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
  have heq : T = Q := eq_of_le_of_card_ge hle hcardT.ge
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 : h * g * h⁻¹ ∈ T := by
      rw [hmemT]
      simpa [mul_assoc] using hg
    rwa [heq] at h1
  · intro hg
    have h1 : h * g * h⁻¹ ∈ T := by
      rw [heq]
      exact hg
    rw [hmemT] at h1
    simpa [mul_assoc] using h1

open Subgroup in
theorem perfectCore_centralizer_elt_le_map_core {K : Type*} [Field K] [CharP K 2]
    (P : InvPlacement n k) :
    perfectCore (centralizer {P.elt K}) ≤ (P.core K).map (LinearFlag.proj n K) := by
  calc perfectCore (centralizer {P.elt K})
      ≤ CFSG.Quasithin.derivedSeriesOf (centralizer {P.elt K}) 1 :=
        CFSG.Quasithin.perfectCore_le_derivedSeriesOf _ 1
    _ = ⁅centralizer {P.elt K}, centralizer {P.elt K}⁆ := by
        rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero]
    _ ≤ _ := by
        rw [P.centralizer_elt, ← Subgroup.map_commutator]
        exact map_mono P.commutator_centralizer_le_core

open Subgroup in
theorem map_core_le_centralizer_elt {K : Type*} [Field K] [CharP K 2] (P : InvPlacement n k) :
    (P.core K).map (LinearFlag.proj n K) ≤ centralizer {P.elt K} := by
  rw [P.centralizer_elt]
  exact map_mono P.core_le_centralizer

open Subgroup in
theorem leviOneP_le_perfectCore [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (P : InvPlacement n k) :
    P.leviOneP K ≤ perfectCore (centralizer {P.elt K}) := by
  have := InvPlacement.isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have hperf : ⁅P.leviOneP K, P.leviOneP K⁆ = P.leviOneP K := by
    have : Group.IsPerfect (P.leviOne K) := Group.IsPerfect.range _
    rw [InvPlacement.leviOneP, ← Subgroup.map_commutator, Subgroup.commutator_eq_self]
  refine le_perfectCore_of_perfect ?_ hperf
  rw [P.centralizer_elt]
  exact map_mono P.leviOne_le_centralizer

open Subgroup in
theorem commutator_leviOneP_radicalP_le [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (P : InvPlacement n k) :
    ⁅P.leviOneP K, P.radicalP K⁆ ≤ perfectCore (centralizer {P.elt K}) := by
  rw [commutator_le]
  intro m hm r hr
  have hmΛ := leviOneP_le_perfectCore hq P hm
  have hrC : r ∈ centralizer {P.elt K} := by
    rw [P.centralizer_elt]
    exact map_mono P.radical_le_centralizer hr
  have hrN : r ∈ normalizer (perfectCore (centralizer {P.elt K}) : Set _) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer hrC)
  have h1 : r * m⁻¹ * r⁻¹ ∈ perfectCore (centralizer {P.elt K}) :=
    (mem_normalizer_iff.1 hrN _).1 (inv_mem hmΛ)
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact mul_mem hmΛ (by rw [← mul_assoc]; exact h1)

open Subgroup in
theorem two_le_card_free_of_radical_data [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) (P : InvPlacement n k) {Q S : Subgroup (LinearFlag.projectiveSL n K)}
    (hQΛ : Q ≤ perfectCore (centralizer {P.elt K})) (hQ : IsPGroup 2 Q)
    (hΛQ : perfectCore (centralizer {P.elt K}) ≤
      normalizer (Q : Set (LinearFlag.projectiveSL n K)))
    (hmax : ∀ T : Subgroup (LinearFlag.projectiveSL n K), IsPGroup 2 T →
      T ≤ perfectCore (centralizer {P.elt K}) →
      perfectCore (centralizer {P.elt K}) ≤ normalizer (T : Set (LinearFlag.projectiveSL n K)) →
      T ≤ Q)
    (hQQ : ⁅Q, Q⁆ ≠ ⊥) (hSΛ : S ≤ perfectCore (centralizer {P.elt K})) (hS : ⁅S, S⁆ = S)
    (hS1 : S ≠ ⊥)
    (hSC : S ≤ centralizer ((⁅Q, Q⁆ : Subgroup (LinearFlag.projectiveSL n K)) :
      Set (LinearFlag.projectiveSL n K))) :
    2 ≤ P.free.card := by
  set Λ := perfectCore (centralizer {P.elt K}) with hΛ
  by_contra hlt
  push Not at hlt
  have hcard := P.card_free
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · omega
    · exact h
  rcases (by omega : P.free.card = 0 ∨ P.free.card = 1) with h0 | h1
  ·
    have hJ : P.free = ∅ := Finset.card_eq_zero.1 h0
    have hN : (P.core K).map (LinearFlag.proj n K) ≤
        normalizer (Q : Set (LinearFlag.projectiveSL n K)) :=
      (le_normalizer_of_forall_isPGroup_le (H := centralizer {P.elt K}) (Λ := Λ)
        (fun x hx => CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ (le_normalizer hx))
        hQΛ hQ hΛQ hmax).trans' (map_core_le_centralizer_elt P)
    have hQR := P.le_radicalP_of_isPGroup_of_free_eq_empty hq hk hJ hQ
      (hQΛ.trans (perfectCore_centralizer_elt_le_map_core P)) hN
    apply hQQ
    rw [eq_bot_iff, ← P.commutator_radicalP_eq_bot_of_free_eq_empty (K := K) hJ]
    exact commutator_mono hQR hQR
  ·
    obtain ⟨l, hl⟩ := Finset.card_eq_one.1 h1
    have hlJ : l ∈ P.free := by rw [hl]; exact Finset.mem_singleton_self l
    have hk2 : 2 ≤ k := by omega
    have hRΛ : P.radicalP K ⊓ Λ ≤ Q := by
      refine hmax _ (P.isPGroup_radicalP.to_le inf_le_left) inf_le_right ?_
      intro x hx
      have hxC : x ∈ centralizer {P.elt K} := (CFSG.Quasithin.perfectCore_le _) hx
      have hxR : x ∈ normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) := by
        rw [P.centralizer_elt] at hxC
        obtain ⟨B, hB, rfl⟩ := hxC
        exact le_normalizer_map _ ⟨B, P.parabolic_le_normalizer_radical
          (P.centralizer_le_parabolic hB), rfl⟩
      have hxΛ : x ∈ normalizer (Λ : Set (LinearFlag.projectiveSL n K)) := le_normalizer hx
      rw [mem_normalizer_iff] at hxR hxΛ ⊢
      intro g
      rw [mem_inf, mem_inf, hxR g, hxΛ g]
    have hroot1 : ∀ a : Fin k, LinearFlag.proj n K
        (Matrix.SpecialLinearGroup.transvection (P.u_ne_of_mem_free hlJ a) (1 : K)) ∈ Q := by
      intro a
      refine hRΛ ⟨Subgroup.mem_map_of_mem _ (P.transvection_mem_radical _ (by
        rw [InvPlacement.level_u, P.mem_free.1 hlJ]; omega) 1), ?_⟩
      refine commutator_leviOneP_radicalP_le hq P ?_
      rw [InvPlacement.leviOneP, InvPlacement.radicalP, ← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ (P.transvection_u_free_mem_commutator hk2 hlJ a 1)
    have hroot2 : ∀ b : Fin k, LinearFlag.proj n K
        (Matrix.SpecialLinearGroup.transvection (P.ne_w_of_mem_free hlJ b) (1 : K)) ∈ Q := by
      intro b
      refine hRΛ ⟨Subgroup.mem_map_of_mem _ (P.transvection_mem_radical _ (by
        rw [InvPlacement.level_w, P.mem_free.1 hlJ]; omega) 1), ?_⟩
      refine commutator_leviOneP_radicalP_le hq P ?_
      rw [InvPlacement.leviOneP, InvPlacement.radicalP, ← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ (P.transvection_free_w_mem_commutator hk2 hlJ b 1)
    have hroot : ∀ a b : Fin k, LinearFlag.proj n K
        (Matrix.SpecialLinearGroup.transvection (P.u_ne_w a b) (1 : K)) ∈ ⁅Q, Q⁆ := by
      intro a b
      have h := Subgroup.commutator_mem_commutator (hroot1 a) (hroot2 b)
      rwa [← map_commutatorElement, Matrix.SpecialLinearGroup.commutatorElement_transvection _ _
        (P.u_ne_w a b) 1 1, one_mul] at h
    have hlift : ∀ s ∈ S, ∃ B ∈ centralizer {P.mat K}, LinearFlag.proj n K B = s ∧
        (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u ∈ Set.range (scalar (Fin k)) := by
      intro s hs
      have hsC : s ∈ centralizer {P.elt K} := (CFSG.Quasithin.perfectCore_le _) (hSΛ hs)
      rw [P.centralizer_elt] at hsC
      obtain ⟨B, hB, rfl⟩ := hsC
      refine ⟨B, hB, rfl, P.submatrix_u_mem_range_scalar_of_commute fun a b => ?_⟩
      have hcomm := (mem_centralizer_iff.1 (hSC hs)) _ (hroot a b)
      exact InvPlacement.commute_of_proj_commute (InvPlacement.transvection_mul_self _ _)
        hcomm.symm
    have hSR : S ≤ P.radicalP K := by
      rw [← hS, commutator_le]
      intro s hs s' hs'
      obtain ⟨B, hB, rfl, hBs⟩ := hlift s hs
      obtain ⟨B', hB', rfl, hB's⟩ := hlift s' hs'
      rw [← map_commutatorElement]
      exact Subgroup.mem_map_of_mem _
        (P.commutatorElement_mem_radical_of_free_card_eq_one h1 hB hB' hBs hB's)
    have hSp : IsPGroup 2 S := P.isPGroup_radicalP.to_le hSR
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable S := by
      have := hSp.isNilpotent
      infer_instance
    exact hS1 (perfect_eq_bot_of_le hsolv hS le_rfl)

end Rank

end CFSG.SeitzReduction.LinearPilot
