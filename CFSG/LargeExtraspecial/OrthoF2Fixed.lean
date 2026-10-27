module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open scoped IsMulCommutative

variable {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]

@[expose] def fixSpaceOf {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    (A : Subgroup (W ≃ₗ[K] W)) : Submodule K W where
  carrier := {v | ∀ a ∈ A, a v = v}
  add_mem' := fun hu hv a ha => by rw [map_add, hu a ha, hv a ha]
  zero_mem' := fun a _ => map_zero a
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem mem_fixSpaceOf {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    {A : Subgroup (W ≃ₗ[K] W)} {v : W} : v ∈ fixSpaceOf A ↔ ∀ a ∈ A, a v = v :=
  Iff.rfl

theorem finrank_le_two_mul_finrank_inf_fixSpace [FiniteDimensional (ZMod 2) N]
    {a : N ≃ₗ[ZMod 2] N} (haa : a * a = 1) {W : Submodule (ZMod 2) N} (hW : ∀ w ∈ W, a w ∈ W) :
    finrank (ZMod 2) W ≤ 2 * finrank (ZMod 2) ↥(W ⊓ fixSpace a) := by
  let g : W →ₗ[ZMod 2] N := ((a : N →ₗ[ZMod 2] N) - 1) ∘ₗ W.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g ≤ W ⊓ fixSpace a := by
    rintro _ ⟨w, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, commSpace_le_fixSpace haa (sub_mem_commSpace a w)⟩
    exact Submodule.sub_mem _ (hW w w.2) w.2
  have hker : finrank (ZMod 2) (LinearMap.ker g) = finrank (ZMod 2) ↥(W ⊓ fixSpace a) := by
    rw [LinearMap.ker_comp, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype]
  have h2 := Submodule.finrank_mono hrange
  omega

theorem finrank_le_two_pow_mul_finrank_iInf [FiniteDimensional (ZMod 2) N]
    (S : Finset (N ≃ₗ[ZMod 2] N)) (hinv : ∀ s ∈ S, s * s = 1)
    (hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    finrank (ZMod 2) N ≤ 2 ^ S.card * finrank (ZMod 2) ↥(⨅ s ∈ S, fixSpace s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [show (⨅ s ∈ (∅ : Finset (N ≃ₗ[ZMod 2] N)), fixSpace s) = ⊤ by simp, finrank_top]
    simp
  | insert a T haT ih =>
    have ih' := ih (fun s hs => hinv s (Finset.mem_insert_of_mem hs))
      (fun s hs t ht => hcomm s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht))
    have hW : ∀ w ∈ ⨅ s ∈ T, fixSpace s, a w ∈ ⨅ s ∈ T, fixSpace s := by
      intro w hw
      simp only [Submodule.mem_iInf, mem_fixSpace] at hw ⊢
      intro s hs
      have hc := hcomm a (Finset.mem_insert_self a T) s (Finset.mem_insert_of_mem hs)
      rw [← LinearEquiv.mul_apply, ← hc, LinearEquiv.mul_apply, hw s hs]
    have h := finrank_le_two_mul_finrank_inf_fixSpace (hinv a (Finset.mem_insert_self a T)) hW
    rw [Finset.iInf_insert, Finset.card_insert_of_notMem haT, pow_succ, inf_comm]
    calc finrank (ZMod 2) N
        ≤ 2 ^ T.card * finrank (ZMod 2) ↥(⨅ s ∈ T, fixSpace s) := ih'
      _ ≤ 2 ^ T.card * (2 * finrank (ZMod 2) ↥((⨅ s ∈ T, fixSpace s) ⊓ fixSpace a)) :=
          Nat.mul_le_mul_left _ h
      _ = 2 ^ T.card * 2 * finrank (ZMod 2) ↥((⨅ s ∈ T, fixSpace s) ⊓ fixSpace a) := by ring

theorem exists_finset_iInf_fixSpace_eq (A : Subgroup (N ≃ₗ[ZMod 2] N))
    [IsElementaryAbelian 2 A] {r : ℕ} (hcard : Nat.card A = 2 ^ r) :
    ∃ S : Finset (N ≃ₗ[ZMod 2] N), S.card ≤ r ∧ (∀ s ∈ S, s ∈ A) ∧
      (⨅ s ∈ S, fixSpace s) = fixSpaceOf A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Module (ZMod 2) (Additive A) := IsElementaryAbelian.isVectorSpace 2
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : Finite (Additive A) := inferInstanceAs (Finite A)
  have : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hdim : finrank (ZMod 2) (Additive A) = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod, show Nat.card (Additive A) = Nat.card A from rfl, hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b := Module.finBasis (ZMod 2) (Additive A)
  let g : Fin (finrank (ZMod 2) (Additive A)) → (N ≃ₗ[ZMod 2] N) :=
    fun i => ((Additive.toMul (b i) : A) : N ≃ₗ[ZMod 2] N)
  refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
  · calc (Finset.univ.image g).card ≤ (Finset.univ : Finset (Fin _)).card := Finset.card_image_le
      _ = r := by rw [Finset.card_univ, Fintype.card_fin, hdim]
  · intro s hs
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
    exact (Additive.toMul (b i)).2
  · apply le_antisymm
    · intro v hv
      simp only [Submodule.mem_iInf, mem_fixSpace] at hv
      have hfix : ∀ i, g i v = v := fun i =>
        hv (g i) (Finset.mem_image_of_mem g (Finset.mem_univ i))
      let H : Subgroup A :=
        { carrier := {y | (y : N ≃ₗ[ZMod 2] N) v = v}
          mul_mem' := fun {y z} hy hz => by
            change ((y : N ≃ₗ[ZMod 2] N) * z) v = v
            rw [LinearEquiv.mul_apply]
            change (y : N ≃ₗ[ZMod 2] N) ((z : N ≃ₗ[ZMod 2] N) v) = v
            rw [show (z : N ≃ₗ[ZMod 2] N) v = v from hz]
            exact hy
          one_mem' := rfl
          inv_mem' := fun {y} hy => by
            change ((y : N ≃ₗ[ZMod 2] N))⁻¹ v = v
            conv_lhs => rw [← show (y : N ≃ₗ[ZMod 2] N) v = v from hy]
            exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ v }
      have hspan : Submodule.span (ZMod 2) (Set.range b) ≤
          AddSubgroup.toZModSubmodule 2 H.toAddSubgroup := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hfix i
      rw [b.span_eq] at hspan
      rw [mem_fixSpaceOf]
      intro a ha
      exact hspan (Submodule.mem_top (x := Additive.ofMul ⟨a, ha⟩))
    · intro v hv
      simp only [Submodule.mem_iInf, mem_fixSpace]
      intro s hs
      exact hv s ((Finset.mem_image.mp hs).choose_spec.2 ▸ (Additive.toMul (b _)).2)

theorem timmesfeld_3_1_one [FiniteDimensional (ZMod 2) N] (A : Subgroup (N ≃ₗ[ZMod 2] N))
    [IsElementaryAbelian 2 A] {r : ℕ} (hcard : Nat.card A = 2 ^ r) :
    finrank (ZMod 2) N ⌈/⌉ 2 ^ r ≤ finrank (ZMod 2) (fixSpaceOf A) ∧
      finrank (ZMod 2) N ≤ 2 ^ r * finrank (ZMod 2) (fixSpaceOf A) := by
  obtain ⟨S, hSr, hSA, hSeq⟩ := exists_finset_iInf_fixSpace_eq A hcard
  have hinv : ∀ s ∈ S, s * s = 1 := fun s hs => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian s (hSA s hs)
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨s, hSA s hs⟩ ⟨t, hSA t ht⟩)
  have h := finrank_le_two_pow_mul_finrank_iInf S hinv hcomm
  rw [hSeq] at h
  have h2 : finrank (ZMod 2) N ≤ 2 ^ r * finrank (ZMod 2) (fixSpaceOf A) :=
    h.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hSr))
  exact ⟨(ceilDiv_le_iff_le_smul (by positivity)).mpr (by rwa [smul_eq_mul]), h2⟩

theorem timmesfeld_3_1_two [FiniteDimensional (ZMod 2) N] (A : Subgroup (N ≃ₗ[ZMod 2] N))
    {r : ℕ} (hcard : Nat.card A = 2 ^ r) {x : N}
    (htv : ∀ a ∈ A, a ≠ 1 → commSpace a = (ZMod 2) ∙ x) :
    finrank (ZMod 2) (fixSpaceOf A) = finrank (ZMod 2) N - r ∧ r ≤ finrank (ZMod 2) N ∧
      IsElementaryAbelian 2 A := by
  have hmove : ∀ a ∈ A, ∀ v, a v - v ∈ (ZMod 2) ∙ x := by
    intro a ha v
    by_cases h1 : a = 1
    · subst h1
      rw [LinearEquiv.coe_one, id, sub_self]
      exact Submodule.zero_mem _
    · rw [← htv a ha h1]
      exact sub_mem_commSpace a v
  by_cases hx : x = 0
  · subst hx
    have hA : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      by_contra h1
      have := one_le_finrank_commSpace h1
      rw [htv a ha h1, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot] at this
      omega
    subst hA
    rw [Subgroup.card_bot] at hcard
    have hr : r = 0 := Nat.pow_right_injective le_rfl (hcard.symm.trans (pow_zero 2).symm)
    subst hr
    have hfix : fixSpaceOf (⊥ : Subgroup (N ≃ₗ[ZMod 2] N)) = ⊤ := by
      ext v
      simp only [mem_fixSpaceOf, Subgroup.mem_bot, Submodule.mem_top, iff_true]
      rintro a rfl
      rfl
    refine ⟨by rw [hfix, finrank_top, Nat.sub_zero], Nat.zero_le _, ?_⟩
    have h1 : ∀ a : (⊥ : Subgroup (N ≃ₗ[ZMod 2] N)), a = 1 := fun a =>
      Subtype.ext (Subgroup.mem_bot.mp a.2)
    exact { is_comm := ⟨fun a b => by rw [h1 a, h1 b]⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
              rw [h1 a, one_pow] }
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Module.Dual (ZMod 2) N, ξ x = 1 := by
    have h : ¬ ∀ φ : Module.Dual (ZMod 2) N, φ x = 0 := fun h =>
      hx ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) x).mp h)
    push Not at h
    obtain ⟨φ, hφ⟩ := h
    exact ⟨φ, zmod2_eq_one_of_ne_zero hφ⟩
  have hcoef : ∀ a ∈ A, ∀ v, a v - v = ξ (a v - v) • x := by
    intro a ha v
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hmove a ha v)
    rw [← hc, map_smul, hξ, smul_eq_mul, mul_one]
  have hax : ∀ a ∈ A, a x = x := by
    intro a ha
    rcases mem_span_singleton_iff.mp (hmove a ha x) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      apply hx
      have h2 : a x = x + x := by
        calc a x = (a x - x) + x := (sub_add_cancel _ _).symm
          _ = x + x := by rw [h]
      rw [vec_add_self] at h2
      exact a.injective (h2.trans (map_zero a).symm)
  let φ : A → Module.Dual (ZMod 2) N := fun a => ξ ∘ₗ ((a : N →ₗ[ZMod 2] N) - 1)
  have hφapp : ∀ (a : A) v, φ a v = ξ ((a : N ≃ₗ[ZMod 2] N) v - v) := fun a v => rfl
  have hφmul : ∀ a b : A, φ (a * b) = φ a + φ b := by
    intro a b
    ext v
    rw [LinearMap.add_apply, hφapp, hφapp, hφapp]
    have hb : (b : N ≃ₗ[ZMod 2] N) v = v + ξ ((b : N ≃ₗ[ZMod 2] N) v - v) • x := by
      rw [← hcoef b b.2 v]
      abel
    have key : (a : N ≃ₗ[ZMod 2] N) ((b : N ≃ₗ[ZMod 2] N) v) - (b : N ≃ₗ[ZMod 2] N) v =
        (a : N ≃ₗ[ZMod 2] N) v - v := by
      rw [hb, map_add, map_smul, hax a a.2]
      abel
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply,
      show (a : N ≃ₗ[ZMod 2] N) ((b : N ≃ₗ[ZMod 2] N) v) - v =
        ((a : N ≃ₗ[ZMod 2] N) ((b : N ≃ₗ[ZMod 2] N) v) - (b : N ≃ₗ[ZMod 2] N) v) +
          ((b : N ≃ₗ[ZMod 2] N) v - v) by abel, map_add, key]
  have hφone : φ 1 = 0 := by
    ext v
    rw [hφapp, OneMemClass.coe_one, LinearEquiv.coe_one, id, sub_self, map_zero,
      LinearMap.zero_apply]
  have hφinj : Function.Injective φ := by
    intro a b hab
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have h1 := hcoef a a.2 v
    have h2 := hcoef b b.2 v
    have h3 : ξ ((a : N ≃ₗ[ZMod 2] N) v - v) = ξ ((b : N ≃ₗ[ZMod 2] N) v - v) := by
      rw [← hφapp, ← hφapp, hab]
    rw [h3, ← h2] at h1
    exact sub_left_inj.mp h1
  let Φ : Additive A →+ Module.Dual (ZMod 2) N :=
    { toFun := fun y => φ (Additive.toMul y)
      map_zero' := hφone
      map_add' := fun y z => hφmul _ _ }
  have hΦinj : Function.Injective Φ := fun y z h => Additive.toMul.injective (hφinj h)
  set P := AddSubgroup.toZModSubmodule 2 Φ.range with hP
  have hPcard : Nat.card P = 2 ^ r := by
    have e : Nat.card P = Nat.card Φ.range := rfl
    rw [e, ← Nat.card_congr (AddMonoidHom.ofInjective hΦinj).toEquiv,
      show Nat.card (Additive A) = Nat.card A from rfl, hcard]
  have hPdim : finrank (ZMod 2) P = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
    rw [Nat.card_zmod, hPcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hfix : fixSpaceOf A = P.dualCoannihilator := by
    ext v
    rw [mem_fixSpaceOf, Submodule.mem_dualCoannihilator]
    constructor
    · rintro hv ψ hψ
      rw [hP, AddSubgroup.mem_toZModSubmodule] at hψ
      obtain ⟨y, rfl⟩ := hψ
      change ξ (((Additive.toMul y : A) : N ≃ₗ[ZMod 2] N) v - v) = 0
      rw [hv _ (Additive.toMul y).2, sub_self, map_zero]
    · intro hv a ha
      have h := hv (Φ (Additive.ofMul ⟨a, ha⟩))
        (by rw [hP, AddSubgroup.mem_toZModSubmodule]; exact ⟨_, rfl⟩)
      have h' : ξ (a v - v) = 0 := h
      have h2 := hcoef a ha v
      rw [h', zero_smul] at h2
      exact sub_eq_zero.mp h2
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq P
  rw [← hfix, hPdim] at hsum
  refine ⟨by omega, by omega, ?_⟩
  exact { is_comm := ⟨fun a b => hφinj (by rw [hφmul, hφmul, add_comm])⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => hφinj (by
            rw [pow_two, hφmul, vec_add_self, hφone]) }

end CFSG.LargeExtraspecial
