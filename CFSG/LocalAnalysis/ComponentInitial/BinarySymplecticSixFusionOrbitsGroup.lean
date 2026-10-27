module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Module.ZMod

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits

open scoped IsMulCommutative

open Subgroup MulAction

variable {G : Type*} [Group G]

@[expose] def conjClass (M : Subgroup G) (z : G) : Set G := {x | ∃ m ∈ M, m * z * m⁻¹ = x}

theorem conj_mem_conjClass {M : Subgroup G} {z x m : G} (hm : m ∈ M) (hx : x ∈ conjClass M z) :
    m * x * m⁻¹ ∈ conjClass M z := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨m * n, M.mul_mem hm hn, by group⟩

instance (M : Subgroup G) (z : G) : MulAction M (conjClass M z) where
  smul m x := ⟨m * x * (m : G)⁻¹, conj_mem_conjClass m.2 x.2⟩
  one_smul x := Subtype.ext (by change (1 : G) * x * (1 : G)⁻¹ = x; group)
  mul_smul m n x := Subtype.ext (by
    change (m * n : G) * x * (m * n : G)⁻¹ = m * (n * x * (n : G)⁻¹) * (m : G)⁻¹
    group)

theorem coe_smul_conjClass {M : Subgroup G} {z : G} (m : M) (x : conjClass M z) :
    ((m • x : conjClass M z) : G) = m * x * (m : G)⁻¹ :=
  rfl

theorem self_mem_conjClass (M : Subgroup G) (z : G) : z ∈ conjClass M z :=
  ⟨1, M.one_mem, by group⟩

instance (M : Subgroup G) (z : G) : IsPretransitive M (conjClass M z) where
  exists_smul_eq x y := by
    obtain ⟨a, ha, hx⟩ := x.2
    obtain ⟨c, hc, hy⟩ := y.2
    refine ⟨⟨c * a⁻¹, M.mul_mem hc (M.inv_mem ha)⟩, Subtype.ext ?_⟩
    rw [coe_smul_conjClass, ← hx, ← hy]
    group

theorem stabilizer_conjClass (M : Subgroup G) (z : G) :
    stabilizer M (⟨z, self_mem_conjClass M z⟩ : conjClass M z) =
      (centralizer ({z} : Set G)).subgroupOf M := by
  ext m
  rw [mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff, Subtype.ext_iff,
    coe_smul_conjClass]
  constructor
  · intro h
    calc (m : G) * z = m * z * (m : G)⁻¹ * m := by group
      _ = z * m := by rw [h]
  · intro h
    change (m : G) * z * (m : G)⁻¹ = z
    rw [h]
    group

theorem card_conjClass (M : Subgroup G) (z : G) :
    Nat.card (conjClass M z) = (centralizer ({z} : Set G)).relIndex M := by
  rw [← index_stabilizer_of_transitive M (⟨z, self_mem_conjClass M z⟩ : conjClass M z),
    stabilizer_conjClass]
  rfl

theorem mem_ker_toPermHom_conjClass {M : Subgroup G} {z : G} (m : M) :
    m ∈ (toPermHom M (conjClass M z)).ker ↔
      ∀ x ∈ conjClass M z, (m : G) * x * (m : G)⁻¹ = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h x hx
    exact congrArg (fun σ : Equiv.Perm (conjClass M z) => (σ ⟨x, hx⟩ : G)) h
  · intro h
    ext ⟨x, hx⟩
    exact h x hx

theorem conjClass_mono {M M' : Subgroup G} (h : M ≤ M') (z : G) :
    conjClass M z ⊆ conjClass M' z := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, h hm, rfl⟩

theorem map_conj_eq {P : Subgroup G} {g : G} (hg : g ∈ normalizer (P : Set G)) :
    P.map (MulAut.conj g : G →* G) = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hg y).1 hy
  · intro hx
    refine ⟨g⁻¹ * x * g, (mem_normalizer_iff.1 hg _).2 (by simpa [mul_assoc] using hx), ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

@[expose] def restrictAut (α : MulAut G) (P : Subgroup G) (hP : P.map (α : G →* G) = P) :
    MulAut P :=
  (α.subgroupMap P).trans (MulEquiv.subgroupCongr hP)

theorem coe_restrictAut (α : MulAut G) {P : Subgroup G} (hP : P.map (α : G →* G) = P) (x : P) :
    (restrictAut α P hP x : G) = α x :=
  rfl

theorem coe_restrictAut_pow (α : MulAut G) {P : Subgroup G} (hP : P.map (α : G →* G) = P)
    (n : ℕ) (x : P) : ((restrictAut α P hP ^ n) x : G) = (α ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem quotient_congr_pow {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (c : MulAut H)
    (hc : N.map (c : H →* H) = N) (n : ℕ) (x : H) :
    (QuotientGroup.congr N N c hc ^ n) (x : H ⧸ N) = (((c ^ n) x : H) : H ⧸ N) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, QuotientGroup.congr_mk, ih]

theorem isPGroup_zpowers_of_pow_seven {H : Type*} [Group H] {β : H} (hβ : β ^ 7 = 1) :
    IsPGroup 7 (zpowers β) := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 (orderOf_dvd_of_pow_eq_one hβ) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem eq_one_of_pow_seven_of_modEq {P : Type*} [Group P] [Finite P] (β : MulAut P)
    (hβ : β ^ 7 = 1)
    (hP : ∀ d, d ∣ Nat.card P → d ≡ Nat.card P [MOD 7] → d = Nat.card P) : β = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := (isPGroup_zpowers_of_pow_seven hβ).card_modEq_card_fixedPoints P
  have hdvd : Nat.card (fixedPoints (zpowers β) P) ∣ Nat.card P :=
    card_subgroup_dvd_card (FixedPoints.subgroup (zpowers β) P)
  have heq := hP _ hdvd hmod.symm
  have huniv : fixedPoints (zpowers β) P = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, heq]
  ext x
  have hx : x ∈ fixedPoints (zpowers β) P := huniv ▸ Set.mem_univ x
  exact hx ⟨β, mem_zpowers β⟩

theorem eq_top_of_forall_sylow_le {J : Type*} [Group J] [Finite J] (F : Subgroup J)
    (h : ∀ p : ℕ, p.Prime → ∃ P : Sylow p J, (P : Subgroup J) ≤ F) : F = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  apply Nat.dvd_antisymm (card_subgroup_dvd_card F)
  rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have := Fact.mk hp
    obtain ⟨P, hP⟩ := h p hp
    have h1 : p ^ (Nat.card J).factorization p ∣ Nat.card F := by
      rw [← P.card_eq_multiplicity]
      exact card_dvd_of_le hP
    exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h1
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem eq_one_of_pow_seven_eq_one {J : Type*} [Group J] [Finite J]
    (h7 : ¬ 7 ∣ Nat.card J)
    (hprop : ∀ m, m ∣ Nat.card J → m ≠ Nat.card J → ∀ d, d ∣ m → d ≡ m [MOD 7] → d = m)
    (hpow : ∀ p k : ℕ, p.Prime → p ^ k ≠ Nat.card J)
    (α : MulAut J) (hα : α ^ 7 = 1) : α = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfix : ∀ P : Subgroup J, P.map (α : J →* J) = P → Nat.card P ≠ Nat.card J →
      P ≤ MonoidHom.eqLocus (α : J →* J) (MonoidHom.id J) := by
    intro P hP hne x hx
    have hβ : restrictAut α P hP ^ 7 = 1 := by
      ext y
      rw [coe_restrictAut_pow, hα]
      rfl
    have h1 := eq_one_of_pow_seven_of_modEq _ hβ (hprop _ (card_subgroup_dvd_card P) hne)
    exact congrArg (fun γ : MulAut P => (γ ⟨x, hx⟩ : J)) h1
  have htop : MonoidHom.eqLocus (α : J →* J) (MonoidHom.id J) = ⊤ := by
    refine eq_top_of_forall_sylow_le _ fun p hp => ?_
    have := Fact.mk hp
    have h7n : ¬ 7 ∣ Nat.card (Sylow p J) := fun h => h7 (h.trans
      ((Classical.arbitrary (Sylow p J)).card_dvd_index.trans (index_dvd_card _)))
    obtain ⟨P, hP⟩ :=
      (isPGroup_zpowers_of_pow_seven hα).nonempty_fixed_point_of_prime_not_dvd_card _ h7n
    have hPα : (P : Subgroup J).map (α : J →* J) = P :=
      congrArg Sylow.toSubgroup (hP ⟨α, mem_zpowers α⟩)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    exact ⟨P, hfix P hPα (hk ▸ hpow p k hp)⟩
  ext x
  have hx : x ∈ MonoidHom.eqLocus (α : J →* J) (MonoidHom.id J) := htop ▸ mem_top x
  exact hx

theorem divisors_modEq_seven {n : ℕ} (hn : n = 15 ∨ n = 36) :
    ∀ m ∈ Nat.divisors n, m ≠ n → ∀ d ∈ Nat.divisors m, d % 7 = m % 7 → d = m := by
  rcases hn with rfl | rfl <;> decide

theorem eq_one_of_pow_seven {J : Type*} [Group J] [Finite J]
    (hJ : Nat.card J = 15 ∨ Nat.card J = 36) (α : MulAut J) (hα : α ^ 7 = 1) : α = 1 := by
  have hpq : ∀ {q r : ℕ}, q.Prime → r.Prime → q ≠ r → q ∣ Nat.card J → r ∣ Nat.card J →
      ∀ p k : ℕ, p.Prime → p ^ k ≠ Nat.card J := by
    intro q r hq hr hqr hqJ hrJ p k hp hpk
    rw [← hpk] at hqJ hrJ
    have h1 := (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqJ)
    have h2 := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrJ)
    exact hqr (h1.trans h2.symm)
  refine eq_one_of_pow_seven_eq_one ?_ (fun m hm hne d hd hdm => ?_) ?_ α hα
  · rcases hJ with hJ | hJ <;> rw [hJ] <;> norm_num
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact Nat.card_pos.ne' (zero_dvd_iff.1 hm)
    exact divisors_modEq_seven hJ m (Nat.mem_divisors.2 ⟨hm, Nat.card_pos.ne'⟩) hne d
      (Nat.mem_divisors.2 ⟨hd, hm0⟩) hdm
  · rcases hJ with hJ | hJ
    · exact hpq Nat.prime_three (by norm_num : Nat.Prime 5) (by norm_num) (by rw [hJ]; norm_num)
        (by rw [hJ]; norm_num)
    · exact hpq Nat.prime_two Nat.prime_three (by norm_num) (by rw [hJ]; norm_num)
        (by rw [hJ]; norm_num)

theorem eq_or_eq_of_surjective {H R K : Subgroup G} {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (σ : H →* Q) (hσ : Function.Surjective σ) (hker : σ.ker = R.subgroupOf H)
    (hRK : R ≤ K) (hKH : K ≤ H) (hn : H ≤ normalizer (K : Set G)) : K = R ∨ K = H := by
  have hKn : (K.subgroupOf H).Normal := ⟨fun k hk h => by
    rw [mem_subgroupOf] at hk ⊢
    exact (mem_normalizer_iff.1 (hn h.2) k).1 hk⟩
  rcases (hKn.map σ hσ).eq_bot_or_eq_top with h | h
  · refine Or.inl (le_antisymm (fun x hx => ?_) hRK)
    have hx' : (⟨x, hKH hx⟩ : H) ∈ σ.ker := by
      rw [MonoidHom.mem_ker, ← mem_bot, ← h]
      exact mem_map_of_mem σ (mem_subgroupOf.2 hx)
    rw [hker, mem_subgroupOf] at hx'
    exact hx'
  · refine Or.inr (le_antisymm hKH fun x hx => ?_)
    have hσx : σ ⟨x, hx⟩ ∈ (K.subgroupOf H).map σ := h ▸ mem_top _
    obtain ⟨k, hk, hkx⟩ := mem_map.1 hσx
    have hker' : k⁻¹ * ⟨x, hx⟩ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at hker'
    have hkK : (k : G) ∈ K := mem_subgroupOf.1 hk
    have : x = k * ((k : G)⁻¹ * x) := by group
    rw [this]
    exact K.mul_mem hkK (hRK (by simpa using hker'))

theorem isSimpleGroup_quotient {M R : Subgroup G} [(R.subgroupOf M).Normal] (hRM : R ≤ M)
    (hne : R ≠ M)
    (h : ∀ J : Subgroup G, R ≤ J → J ≤ M → M ≤ normalizer (J : Set G) → J = R ∨ J = M) :
    IsSimpleGroup (M ⧸ R.subgroupOf M) := by
  obtain ⟨m, hmM, hmR⟩ : ∃ m ∈ M, m ∉ R := by
    by_contra hc
    exact hne (le_antisymm hRM fun x hx => by_contra fun hxR => hc ⟨x, hx, hxR⟩)
  have : Nontrivial (M ⧸ R.subgroupOf M) := ⟨⟨((⟨m, hmM⟩ : M) : M ⧸ R.subgroupOf M), 1, by
    rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hmR⟩⟩
  refine { eq_bot_or_eq_top_of_normal := fun K hK => ?_ }
  set K' := K.comap (QuotientGroup.mk' (R.subgroupOf M)) with hK'
  have hK'n : K'.Normal := hK.comap _
  have hRJ : R ≤ K'.map M.subtype := fun r hr => by
    have h1 : ((⟨r, hRM hr⟩ : M) : M ⧸ R.subgroupOf M) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hr)
    refine ⟨⟨r, hRM hr⟩, ?_, rfl⟩
    change (⟨r, hRM hr⟩ : M) ∈ K'
    rw [hK', mem_comap, QuotientGroup.mk'_apply, h1]
    exact K.one_mem
  have hJn : M ≤ normalizer ((K'.map M.subtype : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_iff.2 fun y => by
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨⟨x, hx⟩ * w * ⟨x, hx⟩⁻¹, hK'n.conj_mem w hw ⟨x, hx⟩, rfl⟩
      · rintro ⟨w, hw, hwy⟩
        refine ⟨⟨x, hx⟩⁻¹ * w * ⟨x, hx⟩, ?_, ?_⟩
        · simpa using hK'n.conj_mem w hw ⟨x, hx⟩⁻¹
        · simp only [coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv]
          rw [show (w : G) = x * y * x⁻¹ from hwy]
          group
  rcases h _ hRJ (map_subtype_le _) hJn with hJ | hJ
  · refine Or.inl (eq_bot_iff.2 fun q hq => ?_)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) q
    have : (y : G) ∈ K'.map M.subtype := ⟨y, hq, rfl⟩
    rw [hJ] at this
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 this)
  · refine Or.inr (eq_top_iff.2 fun q _ => ?_)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (R.subgroupOf M) q
    have : (y : G) ∈ K'.map M.subtype := by
      rw [hJ]
      exact y.2
    obtain ⟨w, hw, hwy⟩ := this
    rw [← Subtype.ext hwy]
    exact hw

theorem card_mulAut_of_sq_eq_one {R : Type*} [Group R] [IsMulCommutative R] [Finite R]
    (hsq : ∀ x : R, x ^ 2 = 1) {n : ℕ} (hR : Nat.card R = 2 ^ n) :
    Nat.card (MulAut R) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) (Additive R) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      change Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [hsq]
      rfl
  have hfin : Module.finrank (ZMod 2) (Additive R) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R)
    rw [Nat.card_congr (Additive.toMul : Additive R ≃ R), hR, Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e3 : Additive R ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hfin, Module.finrank_fin_fun])
  let e2 : (Additive R ≃+ Additive R) ≃ (Additive R ≃ₗ[ZMod 2] Additive R) :=
    { toFun := fun f => { ((f : Additive R →+ Additive R).toZModLinearMap 2) with
        invFun := f.symm, left_inv := f.left_inv, right_inv := f.right_inv }
      invFun := fun g => g.toAddEquiv
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }
  let e4 : (Additive R ≃ₗ[ZMod 2] Additive R) ≃
      ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun g => e3.symm.trans (g.trans e3)
      invFun := fun g => e3.trans (g.trans e3.symm)
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }
  let e5 : ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) ≃ GL (Fin n) (ZMod 2) :=
    ((Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)).symm.toEquiv
  rw [Nat.card_congr (MulEquiv.toAdditive.trans (e2.trans (e4.trans e5))), Matrix.card_GL_field,
    ZMod.card]

theorem prod_GL_seven :
    ∏ i : Fin 7, (2 ^ 7 - 2 ^ (i : ℕ)) = 168 * (2 ^ 18 * 3 ^ 3 * 5 * 7 * 31 * 127) := by
  decide

theorem orbit_sum_cases (b₁ b₂ b₃ b₄ b₅ : Bool)
    (hd : 1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 ∣
      2 ^ 18 * 3 ^ 3 * 5 * 7 * 31 * 127)
    (h1 : 1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 ≠ 1) :
    (1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 = 8 ∧
        ((b₁, b₂, b₃, b₄, b₅) = (true, false, false, false, false) ∨
          (b₁, b₂, b₃, b₄, b₅) = (false, true, false, false, false))) ∨
      1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 = 15 ∨
      1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 = 36 ∨
      (1 + cond b₁ 7 0 + cond b₂ 7 0 + cond b₃ 21 0 + cond b₄ 28 0 + cond b₅ 28 0 = 64 ∧
        ((b₁, b₂, b₃, b₄, b₅) = (true, true, true, true, false) ∨
          (b₁, b₂, b₃, b₄, b₅) = (true, false, false, true, true) ∨
          (b₁, b₂, b₃, b₄, b₅) = (false, true, false, true, true) ∨
          (b₁, b₂, b₃, b₄, b₅) = (true, true, true, false, true))) := by
  revert hd h1
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;> norm_num

theorem inter_eq_cond {α : Type*} {P Ω : Set α} [Decidable (P ⊆ Ω)]
    (h : P ⊆ Ω ∨ Disjoint P Ω) : P ∩ Ω = cond (decide (P ⊆ Ω)) P ∅ := by
  by_cases hP : P ⊆ Ω
  · simp [Set.inter_eq_left.2 hP, hP]
  · simp [(h.resolve_left hP).inter_eq, hP]

theorem ncard_cond {α : Type*} (c : Bool) (P : Set α) :
    (cond c P ∅).ncard = cond c P.ncard 0 := by
  cases c <;> simp

theorem disjoint_cond_left {α : Type*} (c : Bool) {P Q : Set α} (h : Disjoint P Q) :
    Disjoint (cond c P ∅) Q := by
  cases c
  · exact Set.empty_disjoint Q
  · exact h

theorem disjoint_cond_right {α : Type*} (c : Bool) {P Q : Set α} (h : Disjoint Q P) :
    Disjoint Q (cond c P ∅) :=
  (disjoint_cond_left c h.symm).symm

theorem pattern_of_pieces {α : Type*} [Finite α] {Ω P₁ P₂ P₃ P₄ P₅ : Set α} {z : α}
    (hz : z ∈ Ω) (hsub : Ω ⊆ {z} ∪ P₁ ∪ P₂ ∪ P₃ ∪ P₄ ∪ P₅)
    (h₁ : P₁ ⊆ Ω ∨ Disjoint P₁ Ω) (h₂ : P₂ ⊆ Ω ∨ Disjoint P₂ Ω) (h₃ : P₃ ⊆ Ω ∨ Disjoint P₃ Ω)
    (h₄ : P₄ ⊆ Ω ∨ Disjoint P₄ Ω) (h₅ : P₅ ⊆ Ω ∨ Disjoint P₅ Ω)
    (hz₁ : z ∉ P₁) (hz₂ : z ∉ P₂) (hz₃ : z ∉ P₃) (hz₄ : z ∉ P₄) (hz₅ : z ∉ P₅)
    (h₁₂ : Disjoint P₁ P₂) (h₁₃ : Disjoint P₁ P₃) (h₁₄ : Disjoint P₁ P₄) (h₁₅ : Disjoint P₁ P₅)
    (h₂₃ : Disjoint P₂ P₃) (h₂₄ : Disjoint P₂ P₄) (h₂₅ : Disjoint P₂ P₅) (h₃₄ : Disjoint P₃ P₄)
    (h₃₅ : Disjoint P₃ P₅) (h₄₅ : Disjoint P₄ P₅)
    (hc₁ : Nat.card P₁ = 7) (hc₂ : Nat.card P₂ = 7) (hc₃ : Nat.card P₃ = 21)
    (hc₄ : Nat.card P₄ = 28) (hc₅ : Nat.card P₅ = 28)
    (hdvd : Nat.card Ω ∣ 2 ^ 18 * 3 ^ 3 * 5 * 7 * 31 * 127) (hne : Nat.card Ω ≠ 1) :
    (Nat.card Ω = 8 ∨ Nat.card Ω = 15 ∨ Nat.card Ω = 36 ∨ Nat.card Ω = 64) ∧
    (Nat.card Ω = 8 → Ω = {z} ∪ P₁ ∨ Ω = {z} ∪ P₂) ∧
    (Nat.card Ω = 64 → Ω = {z} ∪ P₁ ∪ P₂ ∪ P₃ ∪ P₄ ∨ Ω = {z} ∪ P₁ ∪ P₄ ∪ P₅ ∨
      Ω = {z} ∪ P₂ ∪ P₄ ∪ P₅ ∨ Ω = {z} ∪ P₁ ∪ P₂ ∪ P₃ ∪ P₅) := by
  classical
  have hΩ : Ω = {z} ∪ cond (decide (P₁ ⊆ Ω)) P₁ ∅ ∪ cond (decide (P₂ ⊆ Ω)) P₂ ∅ ∪
      cond (decide (P₃ ⊆ Ω)) P₃ ∅ ∪ cond (decide (P₄ ⊆ Ω)) P₄ ∅ ∪
      cond (decide (P₅ ⊆ Ω)) P₅ ∅ := by
    rw [← inter_eq_cond h₁, ← inter_eq_cond h₂, ← inter_eq_cond h₃, ← inter_eq_cond h₄,
      ← inter_eq_cond h₅]
    ext x
    constructor
    · intro hx
      rcases hsub hx with ((((hx' | hx') | hx') | hx') | hx') | hx'
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx'))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hx', hx⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hx', hx⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hx', hx⟩))
      · exact Or.inl (Or.inr ⟨hx', hx⟩)
      · exact Or.inr ⟨hx', hx⟩
    · rintro (((((hx | hx) | hx) | hx) | hx) | hx)
      · rw [Set.mem_singleton_iff.1 hx]
        exact hz
      all_goals exact hx.2
  generalize decide (P₁ ⊆ Ω) = c₁ at hΩ
  generalize decide (P₂ ⊆ Ω) = c₂ at hΩ
  generalize decide (P₃ ⊆ Ω) = c₃ at hΩ
  generalize decide (P₄ ⊆ Ω) = c₄ at hΩ
  generalize decide (P₅ ⊆ Ω) = c₅ at hΩ
  have e1 : Disjoint ({z} : Set α) (cond c₁ P₁ ∅) :=
    disjoint_cond_right _ (Set.disjoint_singleton_left.2 hz₁)
  have e2 : Disjoint ({z} ∪ cond c₁ P₁ ∅) (cond c₂ P₂ ∅) :=
    disjoint_cond_right _ (Set.disjoint_union_left.2
      ⟨Set.disjoint_singleton_left.2 hz₂, disjoint_cond_left _ h₁₂⟩)
  have e3 : Disjoint ({z} ∪ cond c₁ P₁ ∅ ∪ cond c₂ P₂ ∅) (cond c₃ P₃ ∅) :=
    disjoint_cond_right _ (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨Set.disjoint_singleton_left.2 hz₃, disjoint_cond_left _ h₁₃⟩, disjoint_cond_left _ h₂₃⟩)
  have e4 : Disjoint ({z} ∪ cond c₁ P₁ ∅ ∪ cond c₂ P₂ ∅ ∪ cond c₃ P₃ ∅) (cond c₄ P₄ ∅) :=
    disjoint_cond_right _ (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_singleton_left.2 hz₄, disjoint_cond_left _ h₁₄⟩,
        disjoint_cond_left _ h₂₄⟩, disjoint_cond_left _ h₃₄⟩)
  have e5 : Disjoint ({z} ∪ cond c₁ P₁ ∅ ∪ cond c₂ P₂ ∅ ∪ cond c₃ P₃ ∅ ∪ cond c₄ P₄ ∅)
      (cond c₅ P₅ ∅) :=
    disjoint_cond_right _ (Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2
      ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨Set.disjoint_singleton_left.2 hz₅,
        disjoint_cond_left _ h₁₅⟩, disjoint_cond_left _ h₂₅⟩, disjoint_cond_left _ h₃₅⟩,
          disjoint_cond_left _ h₄₅⟩)
  have hcard : Nat.card Ω = 1 + cond c₁ 7 0 + cond c₂ 7 0 + cond c₃ 21 0 + cond c₄ 28 0 +
      cond c₅ 28 0 := by
    rw [Nat.card_coe_set_eq, hΩ, Set.ncard_union_eq e5, Set.ncard_union_eq e4,
      Set.ncard_union_eq e3, Set.ncard_union_eq e2, Set.ncard_union_eq e1, Set.ncard_singleton,
      ncard_cond, ncard_cond, ncard_cond, ncard_cond, ncard_cond, ← Nat.card_coe_set_eq P₁,
      ← Nat.card_coe_set_eq P₂, ← Nat.card_coe_set_eq P₃, ← Nat.card_coe_set_eq P₄,
      ← Nat.card_coe_set_eq P₅, hc₁, hc₂, hc₃, hc₄, hc₅]
  rw [hcard] at hdvd hne ⊢
  have key := orbit_sum_cases _ _ _ _ _ hdvd hne
  refine ⟨?_, fun h8 => ?_, fun h64 => ?_⟩
  · rcases key with ⟨h, -⟩ | h | h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases key with ⟨-, h | h⟩ | h | h | ⟨h, -⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      left
      rw [hΩ]
      simp
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      right
      rw [hΩ]
      simp
    all_goals omega
  · rcases key with ⟨h, -⟩ | h | h | ⟨-, h | h | h | h⟩
    any_goals omega
    all_goals simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; rw [hΩ]
    · left; simp
    · right; left; simp
    · right; right; left; simp
    · right; right; right; simp

theorem eq_or_eq_of_maximal [Finite G] {z : G} {R N₀ M : Subgroup G} (hRN₀ : R ≤ N₀)
    (hN₀M : N₀ ≤ M) (hN₀z : N₀ ≤ centralizer ({z} : Set G))
    (hstab : M ⊓ centralizer ({z} : Set G) ≤ N₀) (hMR : M ≤ normalizer (R : Set G))
    (hzR : conjClass M z ⊆ R) (hRab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hfaith : ∀ m ∈ M, (∀ x ∈ conjClass M z, m * x * m⁻¹ = x) → m ∈ R)
    (hsimp : ∀ K : Subgroup G, R ≤ K → K ≤ N₀ → N₀ ≤ normalizer (K : Set G) → K = R ∨ K = N₀)
    (hmax : ∀ K : Subgroup G, N₀ ≤ K → K ≤ M → K = N₀ ∨ K = M)
    (hdeg : Nat.card (conjClass M z) = 15 ∨ Nat.card (conjClass M z) = 36)
    {g : G} (hg : g ∈ N₀) (hg7 : orderOf g = 7) (hR2 : ∀ r ∈ R, r * r = 1)
    {J : Subgroup G} (hRJ : R ≤ J) (hJM : J ≤ M) (hJn : M ≤ normalizer (J : Set G)) :
    J = R ∨ J = M := by
  have hzRmem : z ∈ R := hzR (self_mem_conjClass M z)
  rcases hmax (J ⊔ N₀) le_sup_right (sup_le hJM hN₀M) with hK | hK
  · left
    have hJN₀ : J ≤ N₀ := hK ▸ le_sup_left
    refine le_antisymm (fun j hj => hfaith j (hJM hj) fun x hx => ?_) hRJ
    obtain ⟨m, hm, rfl⟩ := hx
    have h1 : m⁻¹ * j * m ∈ J := by
      have := (mem_normalizer_iff.1 (hJn (M.inv_mem hm)) j).1 hj
      simpa using this
    have h2 : m⁻¹ * j * m * z = z * (m⁻¹ * j * m) :=
      mem_centralizer_singleton_iff.1 (hN₀z (hJN₀ h1))
    calc j * (m * z * m⁻¹) * j⁻¹ = m * (m⁻¹ * j * m * z) * (m⁻¹ * j * m)⁻¹ * m⁻¹ := by group
      _ = m * (z * (m⁻¹ * j * m)) * (m⁻¹ * j * m)⁻¹ * m⁻¹ := by rw [h2]
      _ = m * z * m⁻¹ := by group
  have hN₀J : N₀ ≤ normalizer (J : Set G) := hN₀M.trans hJn
  have hnorm : N₀ ≤ normalizer ((J ⊓ N₀ : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_iff.2 fun x => by
      rw [mem_inf, mem_inf, mem_normalizer_iff.1 (hN₀J hn)]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, N₀.mul_mem (N₀.mul_mem hn h2) (N₀.inv_mem hn)⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa [mul_assoc] using N₀.mul_mem (N₀.mul_mem (N₀.inv_mem hn) h2) hn⟩
  rcases hsimp (J ⊓ N₀) (le_inf hRJ hRN₀) inf_le_right hnorm with hJN | hJN
  swap
  · right
    have : N₀ ≤ J := fun n hn => by
      have h : n ∈ J ⊓ N₀ := by
        rw [hJN]
        exact hn
      exact h.1
    rw [← hK, sup_eq_left.2 this]
  exfalso
  have htrans : ∀ x ∈ conjClass M z, ∃ j ∈ J, j * z * j⁻¹ = x := by
    rintro _ ⟨m, hm, rfl⟩
    have hm' : m ∈ ((J ⊔ N₀ : Subgroup G) : Set G) := by
      rw [hK]
      exact hm
    rw [coe_mul_of_right_le_normalizer_left J N₀ hN₀J] at hm'
    obtain ⟨j, hj, n, hn, rfl⟩ := hm'
    refine ⟨j, hj, ?_⟩
    have hnz : n * z = z * n := mem_centralizer_singleton_iff.1 (hN₀z hn)
    calc j * z * j⁻¹ = j * (n * z * n⁻¹) * j⁻¹ := by rw [hnz, mul_inv_cancel_right]
      _ = j * n * z * (j * n)⁻¹ := by group
  have hJz : J ⊓ centralizer ({z} : Set G) = R := by
    refine le_antisymm (fun x hx => ?_)
      (le_inf hRJ fun r hr => mem_centralizer_singleton_iff.2 (hRab r hr z hzRmem))
    rw [← hJN]
    exact ⟨hx.1, hstab ⟨hJM hx.1, hx.2⟩⟩
  have : (R.subgroupOf J).Normal := ⟨fun r hr j => by
    rw [mem_subgroupOf] at hr ⊢
    simpa using (mem_normalizer_iff.1 (hMR (hJM j.2)) r).1 hr⟩
  have hcard : Nat.card (J ⧸ R.subgroupOf J) = Nat.card (conjClass M z) := by
    have hJM' : conjClass J z = conjClass M z :=
      le_antisymm (conjClass_mono hJM z) fun x hx => htrans x hx
    rw [← hJM', card_conjClass, ← inf_relIndex_right, inf_comm, hJz]
    rfl
  have hgR : g ∈ normalizer (R : Set G) := hMR (hN₀M hg)
  set c := restrictAut (MulAut.conj g) J (map_conj_eq (hN₀J hg)) with hc
  have hcR : (R.subgroupOf J).map (c : J →* J) = R.subgroupOf J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hy
      rw [mem_subgroupOf]
      exact (mem_normalizer_iff.1 hgR y).1 hy
    · intro hx
      refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
      rw [mem_subgroupOf] at hx
      rw [SetLike.mem_coe, mem_subgroupOf]
      refine (mem_normalizer_iff.1 hgR _).2 ?_
      have h1 : ((c (c.symm x) : J) : G) = g * (c.symm x : G) * g⁻¹ := rfl
      rw [← h1, c.apply_symm_apply]
      exact hx
  set α := QuotientGroup.congr (R.subgroupOf J) (R.subgroupOf J) c hcR with hα
  have hg7' : g ^ 7 = 1 := by rw [← hg7]; exact pow_orderOf_eq_one g
  have hα7 : α ^ 7 = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with | H j => ?_
    rw [hα, quotient_congr_pow]
    congr 1
    apply Subtype.ext
    rw [hc, coe_restrictAut_pow, ← map_pow, hg7', map_one]
    rfl
  have hα1 := eq_one_of_pow_seven (by rw [hcard]; exact hdeg) α hα7
  have hgfix : ∀ x ∈ conjClass M z, g * x * g⁻¹ = x := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := htrans x hx
    have h1 : α ((⟨j, hj⟩ : J) : J ⧸ R.subgroupOf J) = ((⟨j, hj⟩ : J) : J ⧸ R.subgroupOf J) := by
      rw [hα1]
      rfl
    rw [hα, QuotientGroup.congr_mk, QuotientGroup.eq, mem_subgroupOf] at h1
    have hs : (g * j * g⁻¹)⁻¹ * j ∈ R := by simpa [hc, coe_restrictAut] using h1
    have hgz : g * z * g⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.1 (hN₀z hg), mul_inv_cancel_right]
    have hsz := hRab _ hs z hzRmem
    calc g * (j * z * j⁻¹) * g⁻¹ = (g * j * g⁻¹) * (g * z * g⁻¹) * (g * j * g⁻¹)⁻¹ := by group
      _ = j * (((g * j * g⁻¹)⁻¹ * j)⁻¹ * (z * ((g * j * g⁻¹)⁻¹ * j))) * j⁻¹ := by
        rw [hgz]
        group
      _ = j * z * j⁻¹ := by
        rw [← hsz]
        group
  have hgRm := hR2 g (hfaith g (hN₀M hg) hgfix)
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgRm)
  rw [hg7] at h2
  norm_num at h2

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
