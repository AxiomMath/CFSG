module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRScalar

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ A₁ R₂ X : Subgroup G} {σ : E →+* E}
  {u v : G → E} {t d : G}

theorem pow_conj_t_mem (hA₁R : A₁ ≤ R₂) (hR₂c : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r' = r' * r)
    {x r : G} (hr : r ∈ R₂) (hxR : ∀ r' ∈ R₂, r'⁻¹ * (x * r' * x⁻¹) ∈ A₁)
    (hxA : ∀ a ∈ A₁, x * a * x⁻¹ = a) (hxt : x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁) (j : ℕ) :
    x ^ j * t * (x ^ j)⁻¹ * (r ^ j * t)⁻¹ ∈ A₁ := by
  induction j with
  | zero => simp
  | succ j ih =>
    set a := x ^ j * t * (x ^ j)⁻¹ * (r ^ j * t)⁻¹ with ha
    set b := x * t * x⁻¹ * (r * t)⁻¹ with hb
    have hrj : r ^ j ∈ R₂ := pow_mem hr j
    set c := (r ^ j)⁻¹ * (x * r ^ j * x⁻¹) with hc
    have hcA : c ∈ A₁ := hxR _ hrj
    have e1 : x ^ j * t * (x ^ j)⁻¹ = a * (r ^ j * t) := by rw [ha]; group
    have e2 : x * t * x⁻¹ = b * (r * t) := by rw [hb]; group
    have e3 : x * r ^ j * x⁻¹ = r ^ j * c := by rw [hc]; group
    have e : x ^ (j + 1) * t * (x ^ (j + 1))⁻¹ =
        (x * a * x⁻¹) * (x * r ^ j * x⁻¹) * (x * t * x⁻¹) := by
      rw [pow_succ', show x * x ^ j * t * (x * x ^ j)⁻¹ = x * (x ^ j * t * (x ^ j)⁻¹) * x⁻¹ by
        group, e1]
      group
    have hxa : x * a * x⁻¹ = a := hxA a ih
    rw [e, hxa, e3, e2]
    have hcb : c * b = b * c := hR₂c c (hA₁R hcA) b (hA₁R hxt)
    have hrb : r ^ j * b = b * r ^ j := hR₂c _ hrj b (hA₁R hxt)
    have e4 : a * (r ^ j * c) * (b * (r * t)) * (r ^ (j + 1) * t)⁻¹ = a * c * b := by
      rw [pow_succ]
      calc a * (r ^ j * c) * (b * (r * t)) * (r ^ j * r * t)⁻¹ =
          a * (r ^ j * (c * b)) * r * (r ^ j * r)⁻¹ := by group
        _ = a * (r ^ j * (b * c)) * r * (r ^ j * r)⁻¹ := by rw [hcb]
        _ = a * ((r ^ j * b) * c) * r * (r ^ j * r)⁻¹ := by group
        _ = a * ((b * r ^ j) * c) * r * (r ^ j * r)⁻¹ := by rw [hrb]
        _ = a * b * (r ^ j * c * r) * (r ^ j * r)⁻¹ := by group
        _ = a * b * (r ^ j * (c * r)) * (r ^ j * r)⁻¹ := by group
        _ = a * b * (r ^ j * (r * c)) * (r ^ j * r)⁻¹ := by
            rw [hR₂c c (hA₁R hcA) r hr]
        _ = a * b * (r ^ j * r * c) * (r ^ j * r)⁻¹ := by group
        _ = a * b * c := by
            have hrr : r ^ j * r * c * (r ^ j * r)⁻¹ = c := by
              rw [← hR₂c c (hA₁R hcA) _ (mul_mem hrj hr), mul_inv_cancel_right]
            rw [mul_assoc (a * b), hrr]
        _ = a * c * b := by rw [mul_assoc, ← hcb, ← mul_assoc]
    rw [e4]
    exact mul_mem (mul_mem ih hcA) hxt

theorem mul_conj_t_mem (hA₁R : A₁ ≤ R₂) (hR₂c : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r' = r' * r)
    {x x' r r' : G} (hr' : r' ∈ R₂)
    (hxR : ∀ s ∈ R₂, s⁻¹ * (x * s * x⁻¹) ∈ A₁) (hxA : ∀ a ∈ A₁, x * a * x⁻¹ = a)
    (hxt : x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁) (hx't : x' * t * x'⁻¹ * (r' * t)⁻¹ ∈ A₁) :
    x * x' * t * (x * x')⁻¹ * (r' * r * t)⁻¹ ∈ A₁ := by
  set b := x * t * x⁻¹ * (r * t)⁻¹ with hb
  set b' := x' * t * x'⁻¹ * (r' * t)⁻¹ with hb'
  set c := r'⁻¹ * (x * r' * x⁻¹) with hc
  have hcA : c ∈ A₁ := hxR r' hr'
  have e : x * x' * t * (x * x')⁻¹ = (x * b' * x⁻¹) * (x * r' * x⁻¹) * (x * t * x⁻¹) := by
    rw [hb']; group
  have e2 : x * t * x⁻¹ = b * (r * t) := by rw [hb]; group
  have e3 : x * r' * x⁻¹ = r' * c := by rw [hc]; group
  rw [e, hxA b' hx't, e2, e3]
  have hcb : c * b = b * c := hR₂c c (hA₁R hcA) b (hA₁R hxt)
  have hcbr : (c * b) * r' = r' * (c * b) :=
    hR₂c _ (mul_mem (hA₁R hcA) (hA₁R hxt)) r' hr'
  have e4 : b' * (r' * c) * (b * (r * t)) * (r' * r * t)⁻¹ = b' * (r' * (c * b) * r'⁻¹) := by
    group
  rw [e4, ← hcbr, mul_inv_cancel_right]
  exact mul_mem hx't (mul_mem hcA hxt)

theorem inv_conj_t_mem (hA₁R : A₁ ≤ R₂) (hR₂c : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r' = r' * r)
    {x r : G} (hr : r ∈ R₂) (hxR' : ∀ s ∈ R₂, s⁻¹ * (x⁻¹ * s * x⁻¹⁻¹) ∈ A₁)
    (hxA : ∀ a ∈ A₁, x * a * x⁻¹ = a) (hxt : x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁) :
    x⁻¹ * t * x⁻¹⁻¹ * (r⁻¹ * t)⁻¹ ∈ A₁ := by
  set b := x * t * x⁻¹ * (r * t)⁻¹ with hb
  set c := r⁻¹ * (x⁻¹ * r * x⁻¹⁻¹) with hc
  have hcA : c ∈ A₁ := hxR' r hr
  have hxb : x⁻¹ * b * x = b := by
    have h1 := hxA b hxt
    calc x⁻¹ * b * x = x⁻¹ * (x * b * x⁻¹) * x := by rw [h1]
      _ = b := by group
  have ht : t = x⁻¹ * (b * (r * t)) * x := by rw [hb]; group
  have e1 : x⁻¹ * t * x = (x⁻¹ * r * x)⁻¹ * (x⁻¹ * b * x)⁻¹ * t := by
    calc x⁻¹ * t * x = (x⁻¹ * r * x)⁻¹ * (x⁻¹ * b * x)⁻¹ * (x⁻¹ * (b * (r * t)) * x) := by
          group
      _ = _ := by rw [← ht]
  have e2 : x⁻¹ * r * x = r * c := by rw [hc]; group
  rw [inv_inv, e1, hxb, e2]
  have hbr : b * r = r * b := hR₂c b (hA₁R hxt) r hr
  have e3 : (r * c)⁻¹ * b⁻¹ * t * (r⁻¹ * t)⁻¹ = c⁻¹ * (r⁻¹ * b⁻¹ * r) := by group
  have e4 : r⁻¹ * b⁻¹ * r = b⁻¹ := by
    rw [show r⁻¹ * b⁻¹ * r = (r⁻¹ * b * r)⁻¹ by group, mul_assoc, hbr, inv_mul_cancel_left]
  rw [e3, e4]
  exact mul_mem (inv_mem hcA) (inv_mem hxt)

theorem conj_triv {d w : G} (hdT : d ∈ normalizer (T₁ : Set G))
    (hdA : d ∈ normalizer (A₁ : Set G)) (hw : ∀ y ∈ T₁, y⁻¹ * (w * y * w⁻¹) ∈ A₁) :
    ∀ y ∈ T₁, y⁻¹ * (d * w * d⁻¹ * y * (d * w * d⁻¹)⁻¹) ∈ A₁ := by
  intro y hy
  have hy' : d⁻¹ * y * d ∈ T₁ := (mem_normalizer_iff''.mp hdT y).mp hy
  have h1 := (mem_normalizer_iff.mp hdA _).mp (hw _ hy')
  rwa [show d * ((d⁻¹ * y * d)⁻¹ * (w * (d⁻¹ * y * d) * w⁻¹)) * d⁻¹ =
    y⁻¹ * (d * w * d⁻¹ * y * (d * w * d⁻¹)⁻¹) by group] at h1

theorem exists_trivial_of_transitive [Finite E] [CharP E 2] (hc : U3RootCoords T₁ σ u v)
    (hA : ∀ y ∈ T₁, y ∈ A₁ ↔ u y = 0) {μ₀ : E} (hμ₀ : σ μ₀ ≠ μ₀) (hσσ : ∀ a, σ (σ a) = a)
    {q : ℕ} (hq : ∀ a, σ a = a ^ q) (hqev : Even q)
    (hXT : X ≤ normalizer (T₁ : Set G)) (hXA : ∀ x ∈ X, ∀ a ∈ A₁, x * a * x⁻¹ = a)
    (hA₁R : A₁ ≤ R₂) (hR₂c : ∀ r ∈ R₂, ∀ r' ∈ R₂, r * r' = r' * r)
    (hR₂sq : ∀ r ∈ R₂, r ^ 2 ∈ A₁) (hXR : ∀ x ∈ X, ∀ r ∈ R₂, r⁻¹ * (x * r * x⁻¹) ∈ A₁)
    (htr : ∀ r ∈ R₂, ∃ x ∈ X, x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁)
    (hdX : d ∈ normalizer (X : Set G)) (hdR : d ∈ normalizer (R₂ : Set G))
    (hdA : d ∈ normalizer (A₁ : Set G)) (hdt : d * t = t * d)
    (hdT : d ∈ normalizer (T₁ : Set G))
    (hdtr : ∀ r ∈ R₂, r ∉ A₁ → ∀ r' ∈ R₂, r' ∉ A₁ →
      ∃ n : ℕ, (d ^ n * r * (d ^ n)⁻¹)⁻¹ * r' ∈ A₁)
    (hfour : ∃ r ∈ R₂, ∃ r' ∈ R₂, r ∉ A₁ ∧ r' ∉ A₁ ∧ r⁻¹ * r' ∉ A₁) :
    ∀ r ∈ R₂, ∃ x ∈ X, (∀ y ∈ T₁, y⁻¹ * (x * y * x⁻¹) ∈ A₁) ∧
      x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁ := by
  classical
  have hconjT : ∀ x ∈ X, ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁ := fun x hx y hy =>
    (mem_normalizer_iff.mp (hXT hx) y).mp hy
  have hconjT' : ∀ x ∈ X, ∀ y ∈ T₁, x⁻¹ * y * x ∈ T₁ := fun x hx y hy =>
    (mem_normalizer_iff''.mp (hXT hx) y).mp hy
  have hdich : ∀ x ∈ X, ∃ l : E, l * σ l = 1 ∧ ((∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∨
      (∀ y ∈ T₁, u (x * y * x⁻¹) = l * σ (u y))) := fun x hx =>
    hc.exists_norm_one hμ₀ (hXT hx) fun y hy hu => hXA x hx y ((hA y hy).mpr hu)
  have hne0 : ∀ l : E, l * σ l = 1 → l ≠ 0 := fun l hl h0 => by
    rw [h0, zero_mul] at hl; exact zero_ne_one hl
  obtain ⟨y₁, hy₁, hu₁⟩ := hc.u_surj 1
  obtain ⟨y₂, hy₂, hu₂⟩ := hc.u_surj μ₀
  have hnorm : ∀ x ∈ X, ∀ l : E, (∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) → l * σ l = 1 := by
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
      exact hμ₀ (mul_left_cancel₀ (hne0 l (h1 ▸ hl₀)) h2).symm
  have hdX' : ∀ x ∈ X, d * x * d⁻¹ ∈ X := fun x hx => (mem_normalizer_iff.mp hdX x).mp hx
  have hdtd : d⁻¹ * t * d = t := by rw [mul_assoc, ← hdt, inv_mul_cancel_left]
  have hdA' : ∀ a ∈ A₁, d * a * d⁻¹ ∈ A₁ := fun a ha => (mem_normalizer_iff.mp hdA a).mp ha
  set P : G → Prop := fun r => ∃ x ∈ X, (∃ l : E, ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∧
    x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁ with hPdef
  have hP1 : ∀ a ∈ A₁, P a := fun a ha => ⟨1, one_mem _, ⟨1, fun y _ => by simp⟩, by
    rw [show (1 : G) * t * 1⁻¹ * (a * t)⁻¹ = a⁻¹ by group]; exact inv_mem ha⟩
  have hP2 : ∀ r ∈ R₂, ∀ r' ∈ R₂, P r → P r' → P (r' * r) := by
    rintro r - r' hr' ⟨x, hx, ⟨l, hl⟩, hxt⟩ ⟨x', hx', ⟨l', hl'⟩, hx't⟩
    refine ⟨x * x', mul_mem hx hx', ⟨l * l', fun y hy => ?_⟩,
      mul_conj_t_mem hA₁R hR₂c hr' (hXR x hx) (hXA x hx) hxt hx't⟩
    rw [show x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ by group,
      hl _ (hconjT x' hx' y hy), hl' y hy, mul_assoc]
  have triv_iff : ∀ {z : G}, z ∈ normalizer (T₁ : Set G) →
      ((∀ y ∈ T₁, y⁻¹ * (z * y * z⁻¹) ∈ A₁) ↔ ∀ y ∈ T₁, u (z * y * z⁻¹) = u y) := by
    intro z hzT
    constructor
    · intro h y hy
      have hzy : z * y * z⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hzT y).mp hy
      have h1 := (hA _ (mul_mem (inv_mem hy) hzy)).mp (h y hy)
      rw [hc.u_mul_inv hy hzy] at h1
      exact sub_eq_zero.mp h1
    · intro h y hy
      have hzy : z * y * z⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hzT y).mp hy
      refine (hA _ (mul_mem (inv_mem hy) hzy)).mpr ?_
      rw [hc.u_mul_inv hy hzy, h y hy, sub_self]
  have hP4 : ∀ r ∈ R₂, P r → P (d * r * d⁻¹) := by
    rintro r - ⟨x, hx, ⟨l, hl⟩, hxt⟩
    have hz : d * x * d⁻¹ ∈ X := hdX' x hx
    refine ⟨d * x * d⁻¹, hz, ?_, ?_⟩
    · obtain ⟨l', hl', hlz | hlz⟩ := hdich _ hz
      · exact ⟨l', hlz⟩
      refine ⟨1, ?_⟩
      have hz2 : ∀ y ∈ T₁, u ((d * x * d⁻¹) ^ 2 * y * ((d * x * d⁻¹) ^ 2)⁻¹) = u y := by
        intro y hy
        rw [show (d * x * d⁻¹) ^ 2 * y * ((d * x * d⁻¹) ^ 2)⁻¹ =
          (d * x * d⁻¹) * ((d * x * d⁻¹) * y * (d * x * d⁻¹)⁻¹) * (d * x * d⁻¹)⁻¹ by
            simp only [sq]; group,
          hlz _ (hconjT _ hz y hy), hlz y hy, map_mul, hσσ, ← mul_assoc, hl', one_mul]
      have hz2' := (triv_iff (pow_mem (hXT hz) 2)).mpr hz2
      have hx2' := conj_triv (inv_mem hdT) (inv_mem hdA) hz2'
      rw [show d⁻¹ * (d * x * d⁻¹) ^ 2 * d⁻¹⁻¹ = x ^ 2 by simp only [sq]; group] at hx2'
      have hx2 := (triv_iff (pow_mem (hXT hx) 2)).mp hx2'
      have hl2 : l * l = 1 := by
        have h1 := (U3RootCoords.u_conj_pow (hXT hx) hl 2 y₁ hy₁).symm.trans (hx2 y₁ hy₁)
        rwa [hu₁, mul_one, sq] at h1
      have hl1 : l = 1 := by
        rcases mul_self_eq_one_iff.mp hl2 with h1 | h1
        · exact h1
        · rw [h1, CharTwo.neg_eq]
      have hxtriv := (triv_iff (hXT hx)).mpr fun y hy => by rw [hl y hy, hl1, one_mul]
      intro y hy
      rw [(triv_iff (hXT hz)).mp (conj_triv hdT hdA hxtriv) y hy, one_mul]
    · have e : d * x * d⁻¹ * t * (d * x * d⁻¹)⁻¹ * (d * r * d⁻¹ * t)⁻¹ =
          d * x * (d⁻¹ * t * d) * x⁻¹ * (d⁻¹ * t * d)⁻¹ * r⁻¹ * d⁻¹ := by group
      rw [e, hdtd, show d * x * t * x⁻¹ * t⁻¹ * r⁻¹ * d⁻¹ =
        d * (x * t * x⁻¹ * (r * t)⁻¹) * d⁻¹ by group]
      exact hdA' _ hxt
  have hP4n : ∀ n : ℕ, ∀ r ∈ R₂, P r → P (d ^ n * r * (d ^ n)⁻¹) := by
    intro n
    induction n with
    | zero => intro r _ hr; simpa using hr
    | succ n ih =>
      intro r hr hPr
      have h1 := hP4 _ ((mem_normalizer_iff.mp (pow_mem hdR n) r).mp hr) (ih r hr hPr)
      rwa [show d * (d ^ n * r * (d ^ n)⁻¹) * d⁻¹ = d ^ (n + 1) * r * (d ^ (n + 1))⁻¹ by
        rw [pow_succ']; group] at h1
  have hP5 : ∀ r ∈ R₂, ∀ r' ∈ R₂, ∀ x ∈ X, ∀ x' ∈ X,
      ¬ (∃ l : E, ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) →
      ¬ (∃ l : E, ∀ y ∈ T₁, u (x' * y * x'⁻¹) = l * u y) →
      x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁ → x' * t * x'⁻¹ * (r' * t)⁻¹ ∈ A₁ → P (r * r'⁻¹) := by
    intro r hr r' hr' x hx x' hx' hnx hnx' hxt hx't
    obtain ⟨l, hl, hlx | hlx⟩ := hdich x hx
    · exact absurd ⟨l, hlx⟩ hnx
    obtain ⟨l', hl', hlx' | hlx'⟩ := hdich x' hx'
    · exact absurd ⟨l', hlx'⟩ hnx'
    have hl'0 := hne0 l' hl'
    have hinv' : ∀ z ∈ T₁, u (x'⁻¹ * z * x') = (σ l')⁻¹ * σ (u z) := by
      intro z hz
      have h1 := hlx' _ (hconjT' x' hx' z hz)
      rw [show x' * (x'⁻¹ * z * x') * x'⁻¹ = z by group] at h1
      have h2 : σ (u z) = σ l' * u (x'⁻¹ * z * x') := by rw [h1, map_mul, hσσ]
      rw [h2, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero σ).mpr hl'0), one_mul]
    refine ⟨x'⁻¹ * x, mul_mem (inv_mem hx') hx, ⟨(σ l')⁻¹ * σ l, fun y hy => ?_⟩, ?_⟩
    · rw [show x'⁻¹ * x * y * (x'⁻¹ * x)⁻¹ = x'⁻¹ * (x * y * x⁻¹) * x' by group,
        hinv' _ (hconjT x hx y hy), hlx y hy, map_mul, hσσ, mul_assoc]
    · have h1 := inv_conj_t_mem hA₁R hR₂c hr' (fun s hs => hXR _ (inv_mem hx') s hs)
        (hXA x' hx') hx't
      exact mul_conj_t_mem hA₁R hR₂c hr (hXR _ (inv_mem hx'))
        (fun a ha => hXA _ (inv_mem hx') a ha) (by simpa using h1) hxt
  have hPall : ∀ r ∈ R₂, P r := by
    by_contra hcon
    push Not at hcon
    obtain ⟨r₀, hr₀, hPr₀⟩ := hcon
    have hnot : ∀ r ∈ R₂, ¬ P r → ∃ x ∈ X,
        ¬ (∃ l : E, ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∧ x * t * x⁻¹ * (r * t)⁻¹ ∈ A₁ := by
      intro r hr hPr
      obtain ⟨x, hx, hxt⟩ := htr r hr
      exact ⟨x, hx, fun hun => hPr ⟨x, hx, hun, hxt⟩, hxt⟩
    obtain ⟨s, hs, s', hs', hsA, hs'A, hss'⟩ := hfour
    have hex : ∃ p ∈ R₂, p ∉ A₁ ∧ P p := by
      by_cases h1 : P s
      · exact ⟨s, hs, hsA, h1⟩
      by_cases h2 : P s'
      · exact ⟨s', hs', hs'A, h2⟩
      obtain ⟨x, hx, hnx, hxt⟩ := hnot s hs h1
      obtain ⟨x', hx', hnx', hx't⟩ := hnot s' hs' h2
      refine ⟨s' * s⁻¹, mul_mem hs' (inv_mem hs), fun h3 => hss' ?_,
        hP5 s' hs' s hs x' hx' x hx hnx' hnx hx't hxt⟩
      rwa [hR₂c s' hs' _ (inv_mem hs)] at h3
    obtain ⟨p, hp, hpA, hPp⟩ := hex
    apply hPr₀
    by_cases hr₀A : r₀ ∈ A₁
    · exact hP1 r₀ hr₀A
    obtain ⟨n, hn⟩ := hdtr p hp hpA r₀ hr₀ hr₀A
    have hpn : d ^ n * p * (d ^ n)⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (pow_mem hdR n) p).mp hp
    have h1 := hP2 _ (hA₁R hn) _ hpn (hP1 _ hn) (hP4n n p hp hPp)
    rwa [mul_inv_cancel_left] at h1
  intro r hr
  obtain ⟨x, hx, ⟨l, hl⟩, hxt⟩ := hPall r hr
  have hlq : l ^ (q + 1) = 1 := by
    have := hnorm x hx l hl
    rwa [hq, ← pow_succ'] at this
  have hxq := U3RootCoords.u_conj_pow (hXT hx) hl (q + 1)
  refine ⟨x ^ (q + 1), pow_mem hx _, fun y hy => ?_, ?_⟩
  · have hz : x ^ (q + 1) * y * (x ^ (q + 1))⁻¹ ∈ T₁ :=
      (mem_normalizer_iff.mp (pow_mem (hXT hx) _) y).mp hy
    refine (hA _ (mul_mem (inv_mem hy) hz)).mpr ?_
    rw [hc.u_mul_inv hy hz, hxq y hy, hlq, one_mul, sub_self]
  · have h1 := pow_conj_t_mem (t := t) hA₁R hR₂c hr (hXR x hx) (hXA x hx) hxt (q + 1)
    obtain ⟨m, hm⟩ := hqev
    have hrq : r ^ q ∈ A₁ := by
      rw [hm, ← two_mul, pow_mul]
      exact pow_mem (hR₂sq r hr) m
    have e : x ^ (q + 1) * t * (x ^ (q + 1))⁻¹ * (r * t)⁻¹ =
        (x ^ (q + 1) * t * (x ^ (q + 1))⁻¹ * (r ^ (q + 1) * t)⁻¹) * r ^ q := by
      rw [pow_succ]; group
    rw [e]
    exact mul_mem h1 hrq

end U3C1

end CFSG.SeitzReduction.RankOne
