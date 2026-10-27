module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ExtStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.Elementary
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.LinearAlgebra
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Shapes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem halving_zpow_cases {G : Type*} [Group G] (a : G) (h : a ^ 2 = 1) (n : ℤ) :
    a ^ n = 1 ∨ a ^ n = a := by
  rw [zpow_eq_zpow_emod' n h]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    simp [h0]
  · right
    simp [h1]

theorem halving_mem_invariants {R : Subgroup K} {k : Type*} [CommRing k] {W : Type*}
    [AddCommGroup W] [Module k W] (ρ : Representation k ↥R W) {y : K} (hy : y ∈ R)
    (hy2 : y ^ 2 = 1) (v : W) :
    v ∈ Representation.invariants (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype) ↔
      ρ ⟨y, hy⟩ v = v := by
  have hy2' : (⟨y, hy⟩ : ↥R) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
  rw [Representation.mem_invariants]
  constructor
  · intro h
    exact h ⟨⟨y, hy⟩, mem_zpowers _⟩
  · intro h g
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp g.2
    have hg : ((g : ↥(zpowers (⟨y, hy⟩ : ↥R))) : ↥R) = (⟨y, hy⟩ : ↥R) ^ n := hn.symm
    show ρ (g : ↥R) v = v
    rw [hg]
    rcases halving_zpow_cases (⟨y, hy⟩ : ↥R) hy2' n with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      exact h

theorem halving_core {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {W : Type*} [AddCommGroup W]
    [Module F W] [Module.Finite F W] (Y R R' : W →ₗ[F] W) (hY : Y * Y = 1)
    (hRR' : R * R' = 1) (hR'R : R' * R = 1) (hconj : R * Y * R' = -Y) :
    Module.finrank F W = 2 * Module.finrank F (LinearMap.ker (Y - 1)) := by
  have hRY : R * Y = -(Y * R) := by
    have h := congrArg (fun A => A * R) hconj
    simp only [mul_assoc, hR'R, mul_one, neg_mul] at h
    exact h
  have hYR : Y * R = -(R * Y) := by
    rw [hRY, neg_neg]
  have hYR' : Y * R' = -(R' * Y) := by
    have h := congrArg (fun A => R' * A) hconj
    simp only [← mul_assoc, hR'R, one_mul, mul_neg] at h
    exact h
  have hRY' : R' * Y = -(Y * R') := by
    rw [hYR', neg_neg]
  have memP : ∀ x, x ∈ LinearMap.ker (Y - 1) ↔ Y x = x := by
    intro x
    simp [LinearMap.mem_ker, sub_eq_zero]
  have memM : ∀ x, x ∈ LinearMap.ker (Y + 1) ↔ Y x = -x := by
    intro x
    simp [LinearMap.mem_ker, add_eq_zero_iff_eq_neg]
  have hYY : ∀ x, Y (Y x) = x := by
    intro x
    rw [← Module.End.mul_apply, hY]
    rfl
  have hcompl : IsCompl (LinearMap.ker (Y - 1)) (LinearMap.ker (Y + 1)) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      rw [memP] at hx
      rw [memM] at hx'
      have h : x = -x := hx.symm.trans hx'
      have h0 : (2 : F) • x = 0 := by
        rw [two_smul]
        exact eq_neg_iff_add_eq_zero.mp h
      exact (smul_eq_zero.mp h0).resolve_left h2
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      have hw : w = (2⁻¹ : F) • (w + Y w) + (2⁻¹ : F) • (w - Y w) := by
        rw [← smul_add]
        have h : (w + Y w) + (w - Y w) = (2 : F) • w := by
          rw [two_smul]
          abel
        rw [h, smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [hw]
      refine Submodule.add_mem_sup ?_ ?_
      · rw [memP, map_smul, map_add, hYY, add_comm]
      · rw [memM, map_smul, map_sub, hYY, ← smul_neg, neg_sub]
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hmap : ∀ x ∈ LinearMap.ker (Y - 1), R x ∈ LinearMap.ker (Y + 1) := by
    intro x hx
    rw [memP] at hx
    rw [memM]
    have h := congrArg (fun A => A x) hYR
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [h, hx]
  have hmap' : ∀ x ∈ LinearMap.ker (Y + 1), R' x ∈ LinearMap.ker (Y - 1) := by
    intro x hx
    rw [memM] at hx
    rw [memP]
    have h := congrArg (fun A => A x) hYR'
    simp only [Module.End.mul_apply, LinearMap.neg_apply] at h
    rw [h, hx, map_neg, neg_neg]
  have inj1 : Function.Injective (R.restrict hmap) := by
    intro a b hab
    apply Subtype.ext
    have h : R a = R b := congrArg Subtype.val hab
    have h' := congrArg R' h
    simpa [← Module.End.mul_apply, hR'R] using h'
  have inj2 : Function.Injective (R'.restrict hmap') := by
    intro a b hab
    apply Subtype.ext
    have h : R' a = R' b := congrArg Subtype.val hab
    have h' := congrArg R h
    simpa [← Module.End.mul_apply, hRR'] using h'
  have hle1 := LinearMap.finrank_le_finrank_of_injective inj1
  have hle2 := LinearMap.finrank_le_finrank_of_injective inj2
  omega

theorem finrank_eq_two_mul_fixed {R : Subgroup K} {t : K} (hR : IsExt2 R t) {f : ℕ}
    [Fact f.Prime] (hf2 : f ≠ 2) {W : Type} [AddCommGroup W] [Module (ZMod f) W]
    [Module.Finite (ZMod f) W] (ρ : Representation (ZMod f) ↥R W)
    (hρt : ∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) {y r : K} (hy : y ∈ R) (hr : r ∈ R) (hy2 : y ^ 2 = 1)
    (hyr : r * y * r⁻¹ = t * y) :
    Module.finrank (ZMod f) W = 2 * Module.finrank (ZMod f)
      ↥(Representation.invariants (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype)) := by
  have h2 : (2 : ZMod f) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod f) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hf2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hinv : Representation.invariants (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype)
      = LinearMap.ker (ρ ⟨y, hy⟩ - 1) := by
    ext v
    rw [halving_mem_invariants ρ hy hy2, LinearMap.mem_ker]
    simp [sub_eq_zero]
  rw [hinv]
  have hρT : ρ ⟨t, hR.t_mem⟩ = -1 := by
    ext w
    simp [hρt]
  refine halving_core h2 (ρ ⟨y, hy⟩) (ρ ⟨r, hr⟩) (ρ ⟨r⁻¹, R.inv_mem hr⟩) ?_ ?_ ?_ ?_
  · rw [← map_mul]
    have h : (⟨y, hy⟩ * ⟨y, hy⟩ : ↥R) = 1 := Subtype.ext (by simpa [sq] using hy2)
    rw [h, map_one]
  · rw [← map_mul]
    have h : (⟨r, hr⟩ * ⟨r⁻¹, R.inv_mem hr⟩ : ↥R) = 1 := Subtype.ext (by simp)
    rw [h, map_one]
  · rw [← map_mul]
    have h : (⟨r⁻¹, R.inv_mem hr⟩ * ⟨r, hr⟩ : ↥R) = 1 := Subtype.ext (by simp)
    rw [h, map_one]
  · rw [← map_mul, ← map_mul]
    have h : (⟨r, hr⟩ * ⟨y, hy⟩ * ⟨r⁻¹, R.inv_mem hr⟩ : ↥R)
        = ⟨t, hR.t_mem⟩ * ⟨y, hy⟩ := Subtype.ext (by simpa using hyr)
    rw [h, map_mul, hρT, neg_mul, one_mul]
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem ext2Dim_zpowers_eq {t e : K} (ht2 : t ^ 2 = 1) (he : e ∈ zpowers t) : e = 1 ∨ e = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
  have h : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul]
    have h2 : t ^ (2 : ℤ) = 1 := by simpa using ht2
    rw [h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [h, h0]
    simp
  · right
    rw [h, h1]
    simp

theorem ext2Dim_not_cyclic {R : Subgroup K} {t : K} (hR : IsExt2 R t) (hcard : Nat.card R = 8) :
    ¬ IsCyclic ↥R := by
  intro hc
  have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg⟩ := hc.exists_generator
    obtain ⟨m, hm⟩ := hg ⟨a, ha⟩
    obtain ⟨n, hn⟩ := hg ⟨b, hb⟩
    have h : (⟨a, ha⟩ : ↥R) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self g m n).eq
    exact congrArg Subtype.val h
  have hle : R ≤ zpowers t := fun a ha => hR.center_le a ha (fun r hr => hcomm a ha r hr)
  have h1 : Nat.card R ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
  have h2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hR.t_sq hR.t_ne
  omega

theorem ext2Dim_caseB {R : Subgroup K} {t : K} (hR : IsExt2 R t) (hcard : Nat.card R = 8)
    (hno : ∀ y ∈ R, y ^ 2 = 1 → y ∈ zpowers t) {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W] [Nontrivial W]
    (ρ : Representation (ZMod f) ↥R W) (hρt : ∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) :
    2 ≤ Module.finrank (ZMod f) W := by
  have huniq : ∀ e ∈ R, e ^ 2 = 1 → e = 1 ∨ e = t := fun e he he2 =>
    ext2Dim_zpowers_eq hR.t_sq (hno e he he2)
  have hpg : IsPGroup 2 ↥R := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  have hnc : ¬ IsCyclic ↥R := ext2Dim_not_cyclic hR hcard
  obtain ⟨n, hn3, hnn, ⟨e⟩⟩ :=
    quaternion_of_unique_involution hpg hR.t_mem hR.t_sq hR.t_ne huniq hnc
  have hn : n = 3 := by
    have h8 : 2 ^ n = 2 ^ 3 := by rw [← hnn, hcard]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h8
  subst hn
  obtain ⟨i, j, t', hshape, hi, hj, hi2, hj2, hji⟩ := shape3 e
  have ht't : t' = t := (huniq t' hshape.t_mem hshape.t_sq).resolve_left hshape.t_ne
  rw [ht't] at hi2 hj2 hji
  have hρt' : ρ ⟨t, hR.t_mem⟩ = -1 := by
    ext w
    simp [hρt]
  have hII : ρ ⟨i, hi⟩ * ρ ⟨i, hi⟩ = -1 := by
    rw [← map_mul]
    have h : (⟨i, hi⟩ : ↥R) * ⟨i, hi⟩ = ⟨t, hR.t_mem⟩ :=
      Subtype.ext (by show i * i = t; rw [← pow_two]; exact hi2)
    rw [h, hρt']
  have hJJ : ρ ⟨j, hj⟩ * ρ ⟨j, hj⟩ = -1 := by
    rw [← map_mul]
    have h : (⟨j, hj⟩ : ↥R) * ⟨j, hj⟩ = ⟨t, hR.t_mem⟩ :=
      Subtype.ext (by show j * j = t; rw [← pow_two]; exact hj2)
    rw [h, hρt']
  have hJI : ρ ⟨j, hj⟩ * ρ ⟨i, hi⟩ = -(ρ ⟨i, hi⟩ * ρ ⟨j, hj⟩) := by
    rw [← map_mul]
    have h : (⟨j, hj⟩ : ↥R) * ⟨i, hi⟩ = ⟨t, hR.t_mem⟩ * ⟨i, hi⟩ * ⟨j, hj⟩ := by
      apply Subtype.ext
      show j * i = t * i * j
      calc j * i = (j * i * j⁻¹) * j := by group
        _ = t * i * j := by rw [hji]
    rw [h, map_mul, map_mul, hρt']
    simp
  obtain ⟨m, hm⟩ := la_even (Fact.out) hf2 W (ρ ⟨i, hi⟩) (ρ ⟨j, hj⟩) hII hJJ hJI
  have hpos : 0 < Module.finrank (ZMod f) W := Module.finrank_pos
  omega

theorem ext2Dim_exists_subrep {R R' : Subgroup K} (h : R' ≤ R) {f : ℕ} {W : Type} [AddCommGroup W]
    [Module (ZMod f) W] (ρ : Representation (ZMod f) ↥R W) (W₁ : Submodule (ZMod f) W)
    (hW₁ : ∀ (g : ↥R') (w : W), w ∈ W₁ → ρ (Subgroup.inclusion h g) w ∈ W₁) :
    ∃ ρ₁ : Representation (ZMod f) ↥R' ↥W₁, ∀ (g : ↥R') (w : ↥W₁),
      ((ρ₁ g w : ↥W₁) : W) = ρ (Subgroup.inclusion h g) (w : W) :=
  ⟨Representation.subrepresentation (ρ.comp (Subgroup.inclusion h)) W₁
    (fun g w hw => hW₁ g w hw), fun g w => rfl⟩

theorem ext2Dim_stepA {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {k : ℕ}
    (ih : ∀ {R : Subgroup K} {t : K} (hR : IsExt2 R t), Nat.card R = 2 ^ (1 + 2 * k) →
      ∀ {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W]
      [Nontrivial W] (ρ : Representation (ZMod f) ↥R W),
      (∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) → 2 ^ k ≤ Module.finrank (ZMod f) W)
    {R : Subgroup K} {t : K} (hR : IsExt2 R t) {W : Type} [AddCommGroup W] [Module (ZMod f) W]
    [Module.Finite (ZMod f) W] [Nontrivial W] (ρ : Representation (ZMod f) ↥R W)
    (hρt : ∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) {y r : K} (hy : y ∈ R) (hr : r ∈ R) (hy2 : y ^ 2 = 1)
    (hyr : r * y * r⁻¹ = t * y) {R' : Subgroup K} (hR' : IsExt2 R' t) (hle : R' ≤ R)
    (hcomm : ∀ g ∈ R', y * g = g * y) (hcard' : Nat.card R' = 2 ^ (1 + 2 * k)) :
    2 ^ (k + 1) ≤ Module.finrank (ZMod f) W := by
  have hdim := finrank_eq_two_mul_fixed hR hf2 ρ hρt hy hr hy2 hyr
  set W₁ : Submodule (ZMod f) W :=
    Representation.invariants (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype) with hW₁def
  have hpos : 0 < Module.finrank (ZMod f) W := Module.finrank_pos
  have hpos₁ : 0 < Module.finrank (ZMod f) ↥W₁ := by omega
  haveI : Nontrivial ↥W₁ := Module.finrank_pos_iff.mp hpos₁
  have hinv : ∀ (g : ↥R') (w : W), w ∈ W₁ → ρ (Subgroup.inclusion hle g) w ∈ W₁ := by
    intro g w hw
    rw [hW₁def, Representation.mem_invariants] at hw ⊢
    intro h
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h.2
    have hyg : Commute (⟨y, hy⟩ : ↥R) (Subgroup.inclusion hle g) := Subtype.ext (hcomm g g.2)
    have hhg : Commute (h : ↥R) (Subgroup.inclusion hle g) := by
      rw [← hn]
      exact hyg.zpow_left n
    have h1 : ρ (h : ↥R) (ρ (Subgroup.inclusion hle g) w) =
        ρ (Subgroup.inclusion hle g) (ρ (h : ↥R) w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hhg.eq]
    rw [show (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype) h = ρ (h : ↥R) from rfl, h1]
    have h2 := hw h
    rw [show (ρ.comp (zpowers (⟨y, hy⟩ : ↥R)).subtype) h = ρ (h : ↥R) from rfl] at h2
    rw [h2]
  obtain ⟨ρ₁, hρ₁⟩ := ext2Dim_exists_subrep hle ρ W₁ hinv
  have hρ₁t : ∀ w, ρ₁ ⟨t, hR'.t_mem⟩ w = -w := by
    intro w
    apply Subtype.ext
    rw [hρ₁]
    exact hρt w
  have hk' := ih hR' hcard' ρ₁ hρ₁t
  calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    _ ≤ 2 * Module.finrank (ZMod f) ↥W₁ := by omega
    _ = Module.finrank (ZMod f) W := hdim.symm

theorem ext2Dim_step {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {k : ℕ}
    (ih : ∀ {R : Subgroup K} {t : K} (hR : IsExt2 R t), Nat.card R = 2 ^ (1 + 2 * k) →
      ∀ {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W]
      [Nontrivial W] (ρ : Representation (ZMod f) ↥R W),
      (∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) → 2 ^ k ≤ Module.finrank (ZMod f) W)
    {R : Subgroup K} {t : K} (hR : IsExt2 R t) (hk : Nat.card R = 2 ^ (1 + 2 * (k + 1)))
    {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W] [Nontrivial W]
    (ρ : Representation (ZMod f) ↥R W) (hρt : ∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) :
    2 ^ (k + 1) ≤ Module.finrank (ZMod f) W := by
  by_cases hy : ∃ y ∈ R, y ^ 2 = 1 ∧ y ∉ zpowers t
  · obtain ⟨y, hyR, hy2, hyt⟩ := hy
    obtain ⟨r, hrR, hryr⟩ := hR.exists_swap hyR hyt
    have hcomm : ⁅r, y⁆ = t := by
      rw [commutatorElement_def, hryr]
      group
    obtain ⟨hR', hcard4⟩ := hR.decomp hrR hyR hcomm
    have hcard' : Nat.card ↥(R ⊓ centralizer ({r, y} : Set K)) = 2 ^ (1 + 2 * k) := by
      have h2 : 2 ^ (1 + 2 * (k + 1)) = 4 * 2 ^ (1 + 2 * k) := by ring
      rw [hk, h2] at hcard4
      omega
    refine ext2Dim_stepA hf2 ih hR ρ hρt hyR hrR hy2 hryr hR' inf_le_left ?_ hcard'
    intro g hg
    exact (mem_centralizer_iff.mp hg.2) y (by simp)
  · push Not at hy
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hcard8 : Nat.card R = 8 := by simpa using hk
      have := ext2Dim_caseB hR hcard8 hy hf2 ρ hρt
      simpa using this
    · exfalso
      obtain ⟨y, hyR, hy2, hyt⟩ := hR.exists_noncentral_involution hk (by omega)
      exact hyt (hy y hyR hy2)

theorem ext2Dim_main {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) (k : ℕ) :
    ∀ {R : Subgroup K} {t : K} (hR : IsExt2 R t), Nat.card R = 2 ^ (1 + 2 * k) →
      ∀ {W : Type} [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W]
      [Nontrivial W] (ρ : Representation (ZMod f) ↥R W),
      (∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) → 2 ^ k ≤ Module.finrank (ZMod f) W := by
  induction k with
  | zero =>
    intro R t hR hk W _ _ _ _ ρ hρt
    have h := Module.finrank_pos (R := ZMod f) (M := W)
    simp only [pow_zero]
    omega
  | succ k ih =>
    intro R t hR hk W _ _ _ _ ρ hρt
    exact ext2Dim_step hf2 ih hR hk ρ hρt

theorem ext2_module_dim {R : Subgroup K} {t : K} (hR : IsExt2 R t) {k : ℕ}
    (hk : Nat.card R = 2 ^ (1 + 2 * k)) {f : ℕ} [Fact f.Prime] (hf2 : f ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod f) W] [Module.Finite (ZMod f) W] [Nontrivial W]
    (ρ : Representation (ZMod f) ↥R W) (hρt : ∀ w, ρ ⟨t, hR.t_mem⟩ w = -w) :
    2 ^ k ≤ Module.finrank (ZMod f) W :=
  ext2Dim_main hf2 k hR hk ρ hρt
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
