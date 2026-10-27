module

public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.LieType.SeitzGeneration.OrthThree

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.Open CFSG.RankThree.Classical
  CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Blk

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure QBlock (Q : QuadraticForm K V) (M : Type) [AddCommGroup M] [Module K M] where
  ι : M →ₗ[K] V
  m : V →ₗ[K] M
  qM : M → K
  m_ι : ∀ x, m (ι x) = x
  Q_add : ∀ (v : V) (y : M), m v = 0 → Q (v + ι y) = Q v + qM y

namespace QBlock

variable {Q : QuadraticForm K V} {M : Type} [AddCommGroup M] [Module K M] (B : QBlock Q M)

@[expose] def blk (T : M →ₗ[K] M) : V →ₗ[K] V :=
  LinearMap.id + B.ι ∘ₗ (T - LinearMap.id) ∘ₗ B.m

theorem blk_apply (T : M →ₗ[K] M) (v : V) : B.blk T v = v + B.ι (T (B.m v) - B.m v) := by
  simp [blk]

theorem blk_ι (T : M →ₗ[K] M) (x : M) : B.blk T (B.ι x) = B.ι (T x) := by
  rw [blk_apply, B.m_ι, map_sub]
  abel

theorem blk_of_m_eq_zero (T : M →ₗ[K] M) {v : V} (hv : B.m v = 0) : B.blk T v = v := by
  rw [blk_apply, hv, map_zero, sub_zero, map_zero, add_zero]

theorem blk_comp (T T' : M →ₗ[K] M) (v : V) : B.blk (T ∘ₗ T') v = B.blk T (B.blk T' v) := by
  simp only [blk_apply, LinearMap.comp_apply, map_add, map_sub, B.m_ι]
  abel

theorem blk_id (v : V) : B.blk LinearMap.id v = v := by
  simp [blk_apply]

theorem Q_blk {Q : QuadraticForm K V} (B : QBlock Q M) (T : M →ₗ[K] M)
    (hT : ∀ x, B.qM (T x) = B.qM x) (v : V) : Q (B.blk T v) = Q v := by
  have h0 : B.m (v - B.ι (B.m v)) = 0 := by rw [map_sub, B.m_ι, sub_self]
  have e2 : B.blk T v = (v - B.ι (B.m v)) + B.ι (T (B.m v)) := by
    rw [blk_apply, map_sub]
    abel
  calc Q (B.blk T v) = Q ((v - B.ι (B.m v)) + B.ι (T (B.m v))) := by rw [e2]
    _ = Q (v - B.ι (B.m v)) + B.qM (T (B.m v)) := B.Q_add _ _ h0
    _ = Q (v - B.ι (B.m v)) + B.qM (B.m v) := by rw [hT]
    _ = Q ((v - B.ι (B.m v)) + B.ι (B.m v)) := (B.Q_add _ _ h0).symm
    _ = Q v := by rw [sub_add_cancel]

theorem blk_comm {M' : Type} [AddCommGroup M'] [Module K M'] (B' : QBlock Q M')
    (h1 : ∀ y, B.m (B'.ι y) = 0) (h2 : ∀ x, B'.m (B.ι x) = 0) (T : M →ₗ[K] M)
    (T' : M' →ₗ[K] M') (v : V) : B.blk T (B'.blk T' v) = B'.blk T' (B.blk T v) := by
  have e1 : B.m (B'.blk T' v) = B.m v := by rw [B'.blk_apply, map_add, h1, add_zero]
  have e2 : B'.m (B.blk T v) = B'.m v := by rw [B.blk_apply, map_add, h2, add_zero]
  rw [B.blk_apply T (B'.blk T' v), e1, B'.blk_apply T' v, B'.blk_apply T' (B.blk T v), e2,
    B.blk_apply T v]
  abel

@[expose] def blkEquiv (T : M →ₗ[K] M) (hT : T ∘ₗ T ∘ₗ T = LinearMap.id) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (B.blk T) (B.blk (T ∘ₗ T))
    (LinearMap.ext fun v => by
      change B.blk T (B.blk (T ∘ₗ T) v) = v
      rw [← blk_comp, hT, blk_id])
    (LinearMap.ext fun v => by
      change B.blk (T ∘ₗ T) (B.blk T v) = v
      rw [← blk_comp, LinearMap.comp_assoc, hT, blk_id])

variable (T : M →ₗ[K] M) (hT : T ∘ₗ T ∘ₗ T = LinearMap.id)

theorem blkEquiv_apply (v : V) : B.blkEquiv T hT v = B.blk T v := rfl

theorem blkEquiv_pow_ι (n : ℕ) (x : M) : (B.blkEquiv T hT ^ n) (B.ι x) = B.ι ((T ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', LinearEquiv.mul_apply, ih, blkEquiv_apply, blk_ι,
      Module.End.mul_apply]

theorem blkEquiv_pow_of_m_eq_zero (n : ℕ) {v : V} (hv : B.m v = 0) :
    (B.blkEquiv T hT ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, blkEquiv_apply, blk_of_m_eq_zero _ _ hv]

theorem blkEquiv_pow_three : B.blkEquiv T hT ^ 3 = 1 := by
  ext v
  rw [pow_succ, pow_succ, pow_one, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  change B.blk T (B.blk T (B.blk T v)) = v
  rw [← blk_comp, ← blk_comp, LinearMap.comp_assoc, hT, blk_id]

end QBlock

end Blk

section Assembly

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem zpow_eq_pow_emod_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) (i : ℤ) :
    g ^ i = g ^ (i % 3).toNat := by
  have h3 : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  have hnn : (0 : ℤ) ≤ i % 3 := Int.emod_nonneg i (by norm_num)
  calc g ^ i = g ^ (i % 3 + 3 * (i / 3)) := by rw [Int.emod_add_mul_ediv]
    _ = g ^ (i % 3) * (g ^ (3 : ℤ)) ^ (i / 3) := by rw [zpow_add, zpow_mul]
    _ = g ^ (i % 3).toNat := by
      rw [h3, one_zpow, mul_one, ← zpow_natCast, Int.toNat_of_nonneg hnn]

variable {Q : QuadraticForm K V} {M₁ M₂ : Type} [AddCommGroup M₁] [Module K M₁]
  [AddCommGroup M₂] [Module K M₂]

theorem independent_of_blocks (B₁ : QBlock Q M₁) (B₂ : QBlock Q M₂)
    (h12 : ∀ y, B₁.m (B₂.ι y) = 0) (h21 : ∀ x, B₂.m (B₁.ι x) = 0) (S S' : M₁ →ₗ[K] M₁)
    (T : M₂ →ₗ[K] M₂) (hS3 : S ∘ₗ S ∘ₗ S = LinearMap.id) (hS'3 : S' ∘ₗ S' ∘ₗ S' = LinearMap.id)
    (hT3 : T ∘ₗ T ∘ₗ T = LinearMap.id)
    (hind : ∀ a b : ℕ, a < 3 → b < 3 → S ^ a * S' ^ b = 1 → a = 0 ∧ b = 0)
    (hind2 : ∀ c : ℕ, c < 3 → T ^ c = 1 → c = 0) (i j k : ℤ)
    (h : B₁.blkEquiv S hS3 ^ i * B₁.blkEquiv S' hS'3 ^ j * B₂.blkEquiv T hT3 ^ k = 1) :
    (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
  rw [zpow_eq_pow_emod_three (B₁.blkEquiv_pow_three S hS3) i,
    zpow_eq_pow_emod_three (B₁.blkEquiv_pow_three S' hS'3) j,
    zpow_eq_pow_emod_three (B₂.blkEquiv_pow_three T hT3) k] at h
  have hlt : ∀ z : ℤ, (z % 3).toNat < 3 := fun z => by
    have := Int.emod_lt_of_pos z (by norm_num : (0 : ℤ) < 3)
    omega
  have hdvd : ∀ z : ℤ, (z % 3).toNat = 0 → (3 : ℤ) ∣ z := fun z hz => by
    have h1 : z % 3 = 0 := by
      have := Int.emod_nonneg z (by norm_num : (3 : ℤ) ≠ 0)
      omega
    exact Int.dvd_of_emod_eq_zero h1
  have key1 : S ^ (i % 3).toNat * S' ^ (j % 3).toNat = 1 := by
    refine LinearMap.ext fun x => ?_
    have h1 := congrArg (fun f : V ≃ₗ[K] V => f (B₁.ι x)) h
    simp only [LinearEquiv.mul_apply] at h1
    rw [B₂.blkEquiv_pow_of_m_eq_zero T hT3 _ (h21 x), B₁.blkEquiv_pow_ι S' hS'3,
      B₁.blkEquiv_pow_ι S hS3] at h1
    have h2 := congrArg B₁.m (show B₁.ι ((S ^ (i % 3).toNat) ((S' ^ (j % 3).toNat) x)) =
      B₁.ι x from h1)
    rw [B₁.m_ι, B₁.m_ι] at h2
    exact h2
  have key2 : T ^ (k % 3).toNat = 1 := by
    refine LinearMap.ext fun y => ?_
    have h1 := congrArg (fun f : V ≃ₗ[K] V => f (B₂.ι y)) h
    simp only [LinearEquiv.mul_apply] at h1
    rw [B₂.blkEquiv_pow_ι T hT3, B₁.blkEquiv_pow_of_m_eq_zero S' hS'3 _ (h12 _),
      B₁.blkEquiv_pow_of_m_eq_zero S hS3 _ (h12 _)] at h1
    have h2 := congrArg B₂.m (show B₂.ι ((T ^ (k % 3).toNat) y) = B₂.ι y from h1)
    rw [B₂.m_ι, B₂.m_ι] at h2
    exact h2
  obtain ⟨ha, hb⟩ := hind _ _ (hlt i) (hlt j) key1
  exact ⟨hdvd i ha, hdvd j hb, hdvd k (hind2 _ (hlt k) key2)⟩

end Assembly

section Rank

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {M₁ M₂ : Type} [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂]
  [Module K M₂]

theorem not_rankLE2_orthDerived_of_blocks (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ x ∈ U, Q x = 0) (B₁ : QBlock Q M₁)
    (B₂ : QBlock Q M₂) (h12 : ∀ y, B₁.m (B₂.ι y) = 0) (h21 : ∀ x, B₂.m (B₁.ι x) = 0)
    (S S' : M₁ →ₗ[K] M₁) (T : M₂ →ₗ[K] M₂) (hS : ∀ x, B₁.qM (S x) = B₁.qM x)
    (hS' : ∀ x, B₁.qM (S' x) = B₁.qM x) (hT' : ∀ y, B₂.qM (T y) = B₂.qM y)
    (hS3 : S ∘ₗ S ∘ₗ S = LinearMap.id) (hS'3 : S' ∘ₗ S' ∘ₗ S' = LinearMap.id)
    (hT3 : T ∘ₗ T ∘ₗ T = LinearMap.id) (hSS' : S ∘ₗ S' = S' ∘ₗ S)
    (hind : ∀ a b : ℕ, a < 3 → b < 3 → S ^ a * S' ^ b = 1 → a = 0 ∧ b = 0)
    (hind2 : ∀ c : ℕ, c < 3 → T ^ c = 1 → c = 0) : ¬ RankLE2 3 (orthDerived Q) := by
  intro hrank
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
      LinearEquiv.ext (congrFun h)
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  have hm₁ : B₁.blkEquiv S hS3 ∈ orthDerived Q :=
    mem_orthDerived_of_odd_pow hQ hT hodd
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => B₁.Q_blk S hS v)
      (B₁.blkEquiv_pow_three S hS3)
  have hm₂ : B₁.blkEquiv S' hS'3 ∈ orthDerived Q :=
    mem_orthDerived_of_odd_pow hQ hT hodd
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => B₁.Q_blk S' hS' v)
      (B₁.blkEquiv_pow_three S' hS'3)
  have hm₃ : B₂.blkEquiv T hT3 ∈ orthDerived Q :=
    mem_orthDerived_of_odd_pow hQ hT hodd
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => B₂.Q_blk T hT' v)
      (B₂.blkEquiv_pow_three T hT3)
  refine false_of_three_independent (G := orthDerived Q) Nat.prime_three hrank
    (e₁ := ⟨B₁.blkEquiv S hS3, hm₁⟩) (e₂ := ⟨B₁.blkEquiv S' hS'3, hm₂⟩)
    (e₃ := ⟨B₂.blkEquiv T hT3, hm₃⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    change B₁.blk S (B₁.blk S' v) = B₁.blk S' (B₁.blk S v)
    rw [← B₁.blk_comp, ← B₁.blk_comp, hSS']
  · exact Subtype.ext (LinearEquiv.ext fun v => B₁.blk_comm B₂ h12 h21 S T v)
  · exact Subtype.ext (LinearEquiv.ext fun v => B₁.blk_comm B₂ h12 h21 S' T v)
  · exact Subtype.ext (B₁.blkEquiv_pow_three S hS3)
  · exact Subtype.ext (B₁.blkEquiv_pow_three S' hS'3)
  · exact Subtype.ext (B₂.blkEquiv_pow_three T hT3)
  · intro i j k hijk
    have h := congrArg Subtype.val hijk
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_one] at h
    exact independent_of_blocks B₁ B₂ h12 h21 S S' T hS3 hS'3 hT3 hind hind2 i j k h

end Rank

section Transfer

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem not_rankLE2_statedProj (hQ : ⇑Q = Q₀) (hE : orthDerived Q = elementaryGroup Q)
    (hnd : (polarBilin Q).Nondegenerate) [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : ¬ RankLE2 p (orthDerived Q)) :
    ¬ RankLE2 p (StatedProj (StatedOmega Q₀)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ι → K) := inferInstance
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun g => (g : (ι → K) → (ι → K))) DFunLike.coe_injective
  let ψ : StatedOmega Q₀ ≃* orthDerived Q :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega Q₀,
      ((ψ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
        toLinEquiv ι K (y : GL ι K) := fun y => rfl
  let π : orthDerived Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  have hker : π.ker = (scalars K (ι → K)).subgroupOf (orthDerived Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  intro hP
  apply h
  intro F hF
  have hEker : ∀ x ∈ F, π x = 1 → x = 1 := by
    intro x hx hπx
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hF.2 x hx)
    have h2 : orderOf x ∣ Nat.card π.ker := by
      let y : π.ker := ⟨x, hπx⟩
      calc orderOf x = orderOf y := Subgroup.orderOf_coe y
        _ ∣ Nat.card π.ker := orderOf_dvd_natCard y
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) hker'
  have hinj : Function.Injective (π.comp F.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hEker x hx (by simpa using h))
  have hF' : IsElemAbelian p (F.map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _
  have hcard : Nat.card (F.map π) = Nat.card F := by
    have hrange : (π.comp F.subtype).range = F.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hcard]
  exact hP _ hF'

end Transfer

end CFSG.LieType.SeitzGeneration
