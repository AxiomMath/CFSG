module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextU
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem regPre_facts {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E) :
    (∀ x ∈ H.regPre E, ∃ hxN : x ∈ normalizer (U : Set G),
      ∀ c, H.perm ⟨x, hxN⟩ c = H.perm ⟨x, hxN⟩ 0 + c) ∧
    (∀ x ∈ H.regPre E, ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b) ∧
    (∀ x ∈ H.regPre E, d⁻¹ * x * d ∈ H.regPre E) ∧
    (∀ c : K, ∃ x ∈ H.regPre E, ∃ hxN : x ∈ normalizer (U : Set G), H.perm ⟨x, hxN⟩ 0 = c) := by
  have hdN := H.d_mem_normalizer_U
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun c => ?_⟩
  · obtain ⟨hxN, hxE⟩ := (H.mem_regPre).mp hx
    exact ⟨hxN, hE.trans _ hxE⟩
  · obtain ⟨hxN, hxE⟩ := (H.mem_regPre).mp hx
    exact H.conj_szA₁_of_perm_eq_add ⟨x, hxN⟩ (hE.trans _ hxE)
  · obtain ⟨hxN, hxE⟩ := (H.mem_regPre).mp hx
    have hmem : d⁻¹ * x * d ∈ normalizer (U : Set G) := mul_mem (mul_mem (inv_mem hdN) hxN) hdN
    refine (H.mem_regPre).mpr ⟨hmem, ?_⟩
    set δ : normalizer (U : Set G) := ⟨d⁻¹, inv_mem hdN⟩ with hδ
    have e : (⟨d⁻¹ * x * d, hmem⟩ : normalizer (U : Set G)) = δ * ⟨x, hxN⟩ * δ⁻¹ :=
      Subtype.ext (by simp [hδ])
    have h1 := hE.normal.conj_mem ⟨H.perm ⟨x, hxN⟩, hE.le hxE⟩ (mem_subgroupOf.mpr hxE)
      ⟨H.perm δ, δ, rfl⟩
    rw [mem_subgroupOf] at h1
    rw [e, map_mul, map_mul, map_inv]
    exact h1
  · obtain ⟨e, he, -⟩ := hE.reg 0 c
    obtain ⟨n, hn⟩ := hE.le e.2
    exact ⟨n, (H.mem_regPre).mpr ⟨n.2, by rw [hn]; exact e.2⟩, n.2, by rw [hn]; exact he⟩

theorem exists_mem_u3C1U_V₁_perm_eq {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E)
    (hsc : U3C1TorusScalar L T f d) (s : K) :
    ∃ x, ∃ hx : x ∈ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t,
      H.perm ⟨x, H.u3C1U_V₁_le hx⟩ 0 = s := by
  classical
  obtain ⟨E', _, _, _, σ, hEcard, hσ, u, w, hc, hA, ℓ, hℓ0, hℓo, hdu⟩ := hsc
  have : Fintype E' := Fintype.ofFinite E'
  obtain ⟨hXtr, hXA, hdX, htr⟩ := H.regPre_facts hE
  set X := H.regPre E with hXdef
  have hXN : ∀ x ∈ X, x ∈ normalizer (U : Set G) := fun x hx => (hXtr x hx).1
  have hXT : ∀ x ∈ X, x ∈ normalizer (szT₁ L T : Set G) := fun x hx =>
    H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu (hXN x hx)
  have htrans : ∀ x (hx : x ∈ X) (c : K),
      H.perm ⟨x, hXN x hx⟩ c = H.perm ⟨x, hXN x hx⟩ 0 + c := fun x hx c => by
    obtain ⟨hxN, h⟩ := hXtr x hx
    exact h c
  have hXadd : ∀ x (hx : x ∈ X) y (hy : y ∈ X), H.perm ⟨x * y, hXN _ (mul_mem hx hy)⟩ 0 =
      H.perm ⟨x, hXN x hx⟩ 0 + H.perm ⟨y, hXN y hy⟩ 0 := by
    intro x hx y hy
    have e : (⟨x * y, hXN _ (mul_mem hx hy)⟩ : normalizer (U : Set G)) =
        ⟨x, hXN x hx⟩ * ⟨y, hXN y hy⟩ := rfl
    rw [e, map_mul, Equiv.Perm.mul_apply, htrans x hx]
  have hXinv : ∀ x (hx : x ∈ X),
      H.perm ⟨x⁻¹, hXN _ (inv_mem hx)⟩ 0 = H.perm ⟨x, hXN x hx⟩ 0 := by
    intro x hx
    have h1 := hXadd x hx x⁻¹ (inv_mem hx)
    have e : (⟨x * x⁻¹, hXN _ (mul_mem hx (inv_mem hx))⟩ : normalizer (U : Set G)) = 1 :=
      Subtype.ext (mul_inv_cancel x)
    rw [e, map_one, Equiv.Perm.one_apply] at h1
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination -h1 - H.perm ⟨x, hXN x hx⟩ 0 * h2
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : a ^ Fintype.card E' = a := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  have hℓσ : σ ℓ ≠ ℓ := by
    intro h1
    rw [hσ] at h1
    apply (U3C1Torus.pow_facts H.stage.start.two_le hℓo).2.1
    have h2 : ℓ ^ (2 ^ f - 1) * ℓ = 1 * ℓ := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, h1, one_mul]
    exact mul_right_cancel₀ hℓ0 h2
  have hconjT : ∀ x ∈ X, ∀ y ∈ szT₁ L T, x * y * x⁻¹ ∈ szT₁ L T := fun x hx y hy =>
    (mem_normalizer_iff.mp (hXT x hx) y).mp hy
  have hconjT' : ∀ x ∈ X, ∀ y ∈ szT₁ L T, x⁻¹ * y * x ∈ szT₁ L T := fun x hx y hy =>
    (mem_normalizer_iff''.mp (hXT x hx) y).mp hy
  have hdich : ∀ x ∈ X, ∃ l : E', l * σ l = 1 ∧
      ((∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) ∨
        (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * σ (u y))) := fun x hx =>
    hc.exists_norm_one hℓσ (hXT x hx) fun y hy hu => hXA x hx y ((hA y hy).mpr hu)
  have hne0 : ∀ l : E', l * σ l = 1 → l ≠ 0 := fun l hl h0 => by
    rw [h0, zero_mul] at hl; exact zero_ne_one hl
  obtain ⟨y₁, hy₁, hu₁⟩ := hc.u_surj 1
  obtain ⟨y₂, hy₂, hu₂⟩ := hc.u_surj ℓ
  have hnorm : ∀ x ∈ X, ∀ l : E', (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) →
      l * σ l = 1 := by
    intro x hx l hl
    obtain ⟨l₀, hl₀, hl₀x | hl₀x⟩ := hdich x hx
    · have := (hl y₁ hy₁).symm.trans (hl₀x y₁ hy₁)
      rw [hu₁, mul_one, mul_one] at this
      rwa [this]
    · exfalso
      have h1 := (hl y₁ hy₁).symm.trans (hl₀x y₁ hy₁)
      rw [hu₁, map_one, mul_one, mul_one] at h1
      have h2 := (hl y₂ hy₂).symm.trans (hl₀x y₂ hy₂)
      rw [hu₂, ← h1] at h2
      exact hℓσ (mul_left_cancel₀ (hne0 l (h1 ▸ hl₀)) h2).symm
  have hdu' : ∀ z ∈ szT₁ L T, u (d⁻¹ * z * d) = ℓ⁻¹ * u z := by
    intro z hz
    have h1 := hdu _ (H.stage.conj_d_mem_T₁ hz)
    rw [show d * (d⁻¹ * z * d) * d⁻¹ = z by group] at h1
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hℓ0, one_mul]
  have hduntw : ∀ x ∈ X, ∀ l : E', (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) →
      ∀ y ∈ szT₁ L T, u ((d⁻¹ * x * d) * y * (d⁻¹ * x * d)⁻¹) = l * u y := by
    intro x hx l hl y hy
    have hdy : d * y * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp H.stage.d_norm.1.2 y).mp hy
    rw [show (d⁻¹ * x * d) * y * (d⁻¹ * x * d)⁻¹ = d⁻¹ * (x * (d * y * d⁻¹) * x⁻¹) * d by group,
      hdu' _ (hconjT x hx _ hdy), hl _ hdy, hdu y hy]
    calc ℓ⁻¹ * (l * (ℓ * u y)) = (ℓ⁻¹ * ℓ) * (l * u y) := by ring
      _ = l * u y := by rw [inv_mul_cancel₀ hℓ0, one_mul]

  set P : K → Prop := fun c => ∃ x ∈ X,
    (∃ l : E', ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) ∧
      ∃ hxN : x ∈ normalizer (U : Set G), H.perm ⟨x, hxN⟩ 0 = c with hPdef
  have hP0 : P 0 := ⟨1, one_mem _, ⟨1, fun y _ => by simp⟩, one_mem _, by
    show H.perm 1 0 = 0
    rw [map_one]
    rfl⟩
  have hPadd : ∀ c c', P c → P c' → P (c + c') := by
    rintro c c' ⟨x, hx, ⟨l, hl⟩, hxN, rfl⟩ ⟨x', hx', ⟨l', hl'⟩, hx'N, rfl⟩
    refine ⟨x * x', mul_mem hx hx', ⟨l * l', fun y hy => ?_⟩, hXN _ (mul_mem hx hx'), ?_⟩
    · rw [show x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ by group,
        hl _ (hconjT x' hx' y hy), hl' y hy, mul_assoc]
    · exact hXadd x hx x' hx'
  have hPmu : ∀ c, P c → P (μ * c) := by
    rintro c ⟨x, hx, ⟨l, hl⟩, hxN, rfl⟩
    exact ⟨d⁻¹ * x * d, hdX x hx, ⟨l, hduntw x hx l hl⟩, hXN _ (hdX x hx),
      H.perm_conj_d_zero hxN (hXN _ (hdX x hx))⟩
  have hPmun : ∀ n : ℕ, ∀ c, P c → P (μ ^ n * c) := by
    intro n
    induction n with
    | zero => intro c hc'; simpa using hc'
    | succ n ih =>
      intro c hc'
      have := hPmu _ (ih c hc')
      rwa [← mul_assoc, ← pow_succ'] at this
  have hPtw : ∀ c c', ¬ P c → ¬ P c' → P (c + c') := by
    intro c c' hc' hc''
    obtain ⟨x, hx, hxN, hxc⟩ := htr c
    obtain ⟨x', hx', hx'N, hx'c⟩ := htr c'
    obtain ⟨l, hl, hlx | hlx⟩ := hdich x hx
    · exact absurd ⟨x, hx, ⟨l, hlx⟩, hxN, hxc⟩ hc'
    obtain ⟨l', hl', hlx' | hlx'⟩ := hdich x' hx'
    · exact absurd ⟨x', hx', ⟨l', hlx'⟩, hx'N, hx'c⟩ hc''
    have hl0 := hne0 l hl
    have hinv : ∀ z ∈ szT₁ L T, u (x⁻¹ * z * x) = (σ l)⁻¹ * σ (u z) := by
      intro z hz
      have h1 := hlx _ (hconjT' x hx z hz)
      rw [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at h1
      have h2 : σ (u z) = σ l * u (x⁻¹ * z * x) := by rw [h1, map_mul, hσσ]
      rw [h2, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ).mpr hl0), one_mul]
    refine ⟨x⁻¹ * x', mul_mem (inv_mem hx) hx', ⟨(σ l)⁻¹ * σ l', fun y hy => ?_⟩,
      hXN _ (mul_mem (inv_mem hx) hx'), ?_⟩
    · rw [show x⁻¹ * x' * y * (x⁻¹ * x')⁻¹ = x⁻¹ * (x' * y * x'⁻¹) * x by group,
        hinv _ (hconjT x' hx' y hy), hlx' y hy, map_mul, hσσ, mul_assoc]
    · rw [hXadd _ (inv_mem hx) x' hx', hXinv x hx]
      exact congrArg₂ (· + ·) hxc hx'c
  have hμ1 : μ ≠ 1 := ne_one_of_generator (by
    rw [H.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) H.stage.start.two_le) H.gen
  have hex : ∃ p, p ≠ 0 ∧ P p := by
    by_cases h1 : P 1
    · exact ⟨1, one_ne_zero, h1⟩
    by_cases h2 : P μ
    · exact ⟨μ, H.mu_ne_zero, h2⟩
    refine ⟨1 + μ, fun h0 => hμ1 ?_, hPtw 1 μ h1 h2⟩
    have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h0 - h3
  obtain ⟨p, hp0, hPp⟩ := hex
  have hPall : ∀ c, P c := by
    intro c
    by_cases hc0 : c = 0
    · rw [hc0]; exact hP0
    obtain ⟨n, hn⟩ := H.gen (c / p) (div_ne_zero hc0 hp0)
    have := hPmun n p hPp
    rwa [hn, div_mul_cancel₀ c hp0] at this
  obtain ⟨x, hx, ⟨l, hl⟩, hxN, hxs⟩ := hPall s
  have hlq : l ^ (2 ^ f + 1) = 1 := by
    have := hnorm x hx l hl
    rwa [hσ, ← pow_succ'] at this
  have hxq := U3RootCoords.u_conj_pow (hXT x hx) hl (2 ^ f + 1)
  have hxqX : x ^ (2 ^ f + 1) ∈ X := pow_mem hx _
  have hmem : x ^ (2 ^ f + 1) ∈ u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t := by
    refine ⟨by rw [H.stage.szR_V₁_eq H.lam]; exact hXN _ hxqX,
      mem_centralizer_iff.mpr fun b hb => ?_, hXT _ hxqX, fun y hy => ?_⟩
    · calc b * x ^ (2 ^ f + 1) =
            (x ^ (2 ^ f + 1) * b * (x ^ (2 ^ f + 1))⁻¹) * x ^ (2 ^ f + 1) := by
            rw [hXA _ hxqX b hb]
        _ = x ^ (2 ^ f + 1) * b := by group
    · have hz : x ^ (2 ^ f + 1) * y * (x ^ (2 ^ f + 1))⁻¹ ∈ szT₁ L T :=
        (mem_normalizer_iff.mp (hXT _ hxqX) y).mp hy
      refine (hA _ (mul_mem (inv_mem hy) hz)).mpr ?_
      rw [hc.u_mul_inv hy hz, hxq y hy, hlq, one_mul, sub_self]
  have hpow : ∀ n : ℕ, H.perm ⟨x ^ n, hXN _ (pow_mem hx n)⟩ 0 =
      (n : K) * H.perm ⟨x, hXN x hx⟩ 0 := by
    intro n
    induction n with
    | zero =>
      have e : (⟨x ^ 0, hXN _ (pow_mem hx 0)⟩ : normalizer (U : Set G)) = 1 :=
        Subtype.ext (pow_zero x)
      rw [e, map_one, Equiv.Perm.one_apply, Nat.cast_zero, zero_mul]
    | succ n ih =>
      have e : (⟨x ^ (n + 1), hXN _ (pow_mem hx (n + 1))⟩ : normalizer (U : Set G)) =
          ⟨x ^ n, hXN _ (pow_mem hx n)⟩ * ⟨x, hXN x hx⟩ := Subtype.ext (pow_succ x n)
      rw [e, map_mul, Equiv.Perm.mul_apply, htrans _ (pow_mem hx n), ih, Nat.cast_succ]
      ring
  refine ⟨x ^ (2 ^ f + 1), hmem, ?_⟩
  have h1 := hpow (2 ^ f + 1)
  have hq : ((2 ^ f + 1 : ℕ) : K) = 1 := by
    have hf0 : f ≠ 0 := by have := H.stage.start.two_le; omega
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow hf0, zero_add,
      Nat.cast_one]
  rw [hq, one_mul] at h1
  exact h1.trans hxs

theorem nextUData_u3C1U {E : Subgroup (Equiv.Perm K)} (hE : H.RegData E)
    (hsc : U3C1TorusScalar L T f d) :
    H.NextUData (u3C1U L T (U₁ ⊓ centralizer (szT₁ L T : Set G)) t) where
  le := H.u3C1U_V₁_le
  normal := H.normalizer_le_normalizer_u3C1U_V₁
  U_le := H.U_le_u3C1U_V₁
  trans _ hx s := H.perm_u3C1U_V₁ hx s
  mem_U _ hx h0 := H.mem_U_of_mem_u3C1U_V₁ hx h0
  surj s := H.exists_mem_u3C1U_V₁_perm_eq hE hsc s
  conj_T₁ _ hx y hy := hx.2.2.2 y hy

end U3C1Next

end CFSG.SeitzReduction.RankOne
