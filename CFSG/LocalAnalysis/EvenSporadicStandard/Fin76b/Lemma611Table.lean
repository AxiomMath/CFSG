module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611Wreath

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

section Klein

variable {K : Type*} [Group K]

structure KleinPair (α t : K) : Prop where
  α2 : α * α = 1
  t2 : t * t = 1
  comm : α * t = t * α
  α1 : α ≠ 1
  t1 : t ≠ 1
  αt : α ≠ t

def kleinMap (α t : K) (v : ZMod 2 × ZMod 2) : K := α ^ v.1.val * t ^ v.2.val

theorem pow_eq_pow_mod_two {x : K} (hx : x * x = 1) (n : ℕ) : x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, sq, hx, one_pow, one_mul]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[simp] theorem kleinMap_zero (α t : K) : kleinMap α t 0 = 1 := by simp [kleinMap]

theorem kleinMap_one_zero (α t : K) : kleinMap α t (1, 0) = α := by simp [kleinMap]

theorem kleinMap_zero_one (α t : K) : kleinMap α t (0, 1) = t := by simp [kleinMap]

theorem kleinMap_one_one (α t : K) : kleinMap α t (1, 1) = α * t := by simp [kleinMap]

namespace KleinPair

variable {α t : K} (h : KleinPair α t)
include h

theorem kleinMap_add (v w : ZMod 2 × ZMod 2) :
    kleinMap α t (v + w) = kleinMap α t v * kleinMap α t w := by
  obtain ⟨a, b⟩ := v
  obtain ⟨a', b'⟩ := w
  have hc' : Commute t α := h.comm.symm
  have hc : t ^ b.val * α ^ a'.val = α ^ a'.val * t ^ b.val :=
    (hc'.pow_pow b.val a'.val).eq
  simp only [kleinMap, Prod.mk_add_mk, ZMod.val_add]
  rw [← pow_eq_pow_mod_two h.α2, ← pow_eq_pow_mod_two h.t2, pow_add, pow_add]
  calc α ^ a.val * α ^ a'.val * (t ^ b.val * t ^ b'.val)
      = α ^ a.val * (α ^ a'.val * t ^ b.val) * t ^ b'.val := by simp only [mul_assoc]
    _ = α ^ a.val * (t ^ b.val * α ^ a'.val) * t ^ b'.val := by rw [hc]
    _ = α ^ a.val * t ^ b.val * (α ^ a'.val * t ^ b'.val) := by simp only [mul_assoc]

theorem kleinMap_eq_one {u : ZMod 2 × ZMod 2} (hu : kleinMap α t u = 1) : u = 0 := by
  obtain ⟨a, b⟩ := u
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · rw [kleinMap_zero_one] at hu
    exact absurd hu h.t1
  · rw [kleinMap_one_zero] at hu
    exact absurd hu h.α1
  · rw [kleinMap_one_one] at hu
    exact absurd ((eq_inv_of_mul_eq_one_left hu).trans (inv_eq_of_mul_eq_one_right h.t2)) h.αt

theorem kleinMap_injective : Function.Injective (kleinMap α t) := by
  intro v w hvw
  have hdbl : ∀ v : ZMod 2 × ZMod 2, v + v = 0 := by decide
  have hcancel : ∀ v w : ZMod 2 × ZMod 2, v + w = 0 → v = w := by decide
  refine hcancel v w (h.kleinMap_eq_one ?_)
  rw [h.kleinMap_add, ← hvw, ← h.kleinMap_add, hdbl, kleinMap_zero]

theorem kleinMap_inv (v : ZMod 2 × ZMod 2) : (kleinMap α t v)⁻¹ = kleinMap α t v := by
  have hdbl : ∀ v : ZMod 2 × ZMod 2, v + v = 0 := by decide
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← h.kleinMap_add, hdbl, kleinMap_zero]

end KleinPair

def ZCentral (α t x : K) : Prop := Commute x α ∧ Commute x t

namespace ZCentral

variable {α t x y : K}

theorem pow (hx : ZCentral α t x) (n : ℕ) : ZCentral α t (x ^ n) :=
  ⟨hx.1.pow_left n, hx.2.pow_left n⟩

theorem commute_kleinMap (hx : ZCentral α t x) (v : ZMod 2 × ZMod 2) :
    Commute x (kleinMap α t v) :=
  (hx.1.pow_right _).mul_right (hx.2.pow_right _)

theorem kleinMap (h : KleinPair α t) (v : ZMod 2 × ZMod 2) :
    ZCentral α t (kleinMap α t v) := by
  have hc : Commute α t := h.comm
  refine ⟨((Commute.refl α).pow_left _).mul_left (hc.symm.pow_left _), ?_⟩
  exact (hc.pow_left _).mul_left ((Commute.refl t).pow_left _)

end ZCentral

section Words

variable {α t : K}

theorem comm_mul_of (h : KleinPair α t) {a b g : K} {u u' : ZMod 2 × ZMod 2}
    (ha : ZCentral α t a) (hb : b * g * b⁻¹ * g⁻¹ = kleinMap α t u)
    (hab : a * g * a⁻¹ * g⁻¹ = kleinMap α t u') :
    a * b * g * (a * b)⁻¹ * g⁻¹ = kleinMap α t (u' + u) := by
  have h1 : a * b * g * (a * b)⁻¹ * g⁻¹ =
      a * (b * g * b⁻¹ * g⁻¹) * a⁻¹ * (a * g * a⁻¹ * g⁻¹) := by group
  rw [h1, hb, hab]
  have hc : a * kleinMap α t u = kleinMap α t u * a := (ha.commute_kleinMap u).eq
  calc a * kleinMap α t u * a⁻¹ * kleinMap α t u'
      = kleinMap α t u * a * a⁻¹ * kleinMap α t u' := by rw [hc]
    _ = kleinMap α t u * kleinMap α t u' := by group
    _ = kleinMap α t (u' + u) := by rw [← h.kleinMap_add, add_comm]

theorem comm_pow_val {x g : K} {u : ZMod 2 × ZMod 2} (hx : x * g * x⁻¹ * g⁻¹ = kleinMap α t u)
    (e : ZMod 2) : x ^ e.val * g * (x ^ e.val)⁻¹ * g⁻¹ = kleinMap α t (e • u) := by
  rcases zmod_two_cases e with rfl | rfl
  · simp
  · simpa using hx

def word (x₁ x₂ x₃ x₄ : K) (e : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : K :=
  x₁ ^ e.1.val * (x₂ ^ e.2.1.val * (x₃ ^ e.2.2.1.val * x₄ ^ e.2.2.2.val))

def wsum (u₁ u₂ u₃ u₄ : ZMod 2 × ZMod 2) (e : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    ZMod 2 × ZMod 2 :=
  e.1 • u₁ + (e.2.1 • u₂ + (e.2.2.1 • u₃ + e.2.2.2 • u₄))

theorem comm_word (h : KleinPair α t) {x₁ x₂ x₃ x₄ g : K} {u₁ u₂ u₃ u₄ : ZMod 2 × ZMod 2}
    (hx₁ : ZCentral α t x₁) (hx₂ : ZCentral α t x₂) (hx₃ : ZCentral α t x₃)
    (hg : ZCentral α t g) (h₁ : x₁ * g * x₁⁻¹ * g⁻¹ = kleinMap α t u₁)
    (h₂ : x₂ * g * x₂⁻¹ * g⁻¹ = kleinMap α t u₂) (h₃ : x₃ * g * x₃⁻¹ * g⁻¹ = kleinMap α t u₃)
    (h₄ : x₄ * g * x₄⁻¹ * g⁻¹ = kleinMap α t u₄) (v : ZMod 2 × ZMod 2)
    (e : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    (kleinMap α t v * word x₁ x₂ x₃ x₄ e) * g * (kleinMap α t v * word x₁ x₂ x₃ x₄ e)⁻¹ * g⁻¹ =
      kleinMap α t (wsum u₁ u₂ u₃ u₄ e) := by
  have q₃₄ := comm_mul_of h (hx₃.pow e.2.2.1.val) (comm_pow_val h₄ e.2.2.2)
    (comm_pow_val h₃ e.2.2.1)
  have q₂ := comm_mul_of h (hx₂.pow e.2.1.val) q₃₄ (comm_pow_val h₂ e.2.1)
  have q₁ := comm_mul_of h (hx₁.pow e.1.val) q₂ (comm_pow_val h₁ e.1)
  have hv : kleinMap α t v * g * (kleinMap α t v)⁻¹ * g⁻¹ = kleinMap α t 0 := by
    rw [kleinMap_zero, ← (hg.commute_kleinMap v).eq]
    group
  have q := comm_mul_of h (ZCentral.kleinMap h v) q₁ hv
  rw [zero_add] at q
  exact q

theorem exists_kleinMap_eq_of_mem (h : KleinPair α t) {x : K}
    (hx : x ∈ (zpowers α ⊔ zpowers t : Subgroup K)) : ∃ v, kleinMap α t v = x := by
  have hc : Commute α t := h.comm
  have hcent : zpowers t ≤ centralizer (zpowers α : Set K) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hc i j).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent hx
  rcases mem_zpowers_sq_eq_one h.α2 ha with rfl | rfl <;>
    rcases mem_zpowers_sq_eq_one h.t2 hb with rfl | rfl
  · exact ⟨0, by simp [kleinMap]⟩
  · exact ⟨(0, 1), by simp [kleinMap]⟩
  · exact ⟨(1, 0), by simp [kleinMap]⟩
  · exact ⟨(1, 1), by simp [kleinMap]⟩

theorem kleinMap_mem (α t : K) (v : ZMod 2 × ZMod 2) :
    kleinMap α t v ∈ (zpowers α ⊔ zpowers t : Subgroup K) :=
  mul_mem (pow_mem (mem_sup_left (mem_zpowers α)) _) (pow_mem (mem_sup_right (mem_zpowers t)) _)

theorem table_inj : ∀ e e' : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2,
    wsum 0 (1, 1) 0 (0, 1) e = wsum 0 (1, 1) 0 (0, 1) e' →
    wsum (1, 1) 0 (0, 1) 0 e = wsum (1, 1) 0 (0, 1) 0 e' →
    wsum 0 (0, 1) 0 (1, 0) e = wsum 0 (0, 1) 0 (1, 0) e' →
    wsum (0, 1) 0 (1, 0) 0 e = wsum (0, 1) 0 (1, 0) 0 e' → e = e' := by
  decide

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
theorem table_final : ∀ (ζ : ZMod 2 × ZMod 2) (e : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2),
    (wsum 0 (1, 1) 0 (0, 1) e = 0 ∨ wsum 0 (1, 1) 0 (0, 1) e = ζ) →
    (wsum (1, 1) 0 (0, 1) 0 e = 0 ∨ wsum (1, 1) 0 (0, 1) 0 e = ζ) →
    (wsum 0 (0, 1) 0 (1, 0) e = 0 ∨ wsum 0 (0, 1) 0 (1, 0) e = ζ) →
    (wsum (0, 1) 0 (1, 0) 0 e = 0 ∨ wsum (0, 1) 0 (1, 0) 0 e = ζ) → e = 0 := by
  decide

end Words

end Klein

theorem no_table_in_wreath {K : Type*} [Group K] [Finite K] {z α t g₁ g₂ h₁ h₂ : K}
    (hWreath : WreathAlt K (QuotientGroup.mk z)) (hz : z * z = 1)
    (hα2 : α * α = 1) (ht2 : t * t = 1) (hα1 : α ≠ 1) (ht1 : t ≠ 1) (hαt : α ≠ t)
    (hαt' : α * t = t * α) (hzα : z * α * z⁻¹ = α * t) (hzt : z * t * z⁻¹ = t)
    (htcomm : t ∈ _root_.commutator K) (hnconj : ∀ g : K, g * z * g⁻¹ ≠ α)
    (hC2 : IsPGroup 2 (Subgroup.closure ({α, t, g₁, g₂, h₁, h₂} : Set K)))
    (hcα : ∀ c ∈ ({g₁, g₂, h₁, h₂} : Set K), c * α = α * c)
    (hct : ∀ c ∈ ({g₁, g₂, h₁, h₂} : Set K), c * t = t * c)
    (_hsq : ∀ c ∈ ({g₁, g₂, h₁, h₂} : Set K), c * c ∈ (zpowers α ⊔ zpowers t : Subgroup K))
    (h12 : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = α * t) (h34 : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = α)
    (h14 : g₁ * h₂ * g₁⁻¹ * h₂⁻¹ = t) (h23 : g₂ * h₁ * g₂⁻¹ * h₁⁻¹ = t)
    (h13 : g₁ * h₁ = h₁ * g₁) (h24 : g₂ * h₂ = h₂ * g₂) : False := by
  classical
  have hK : KleinPair α t := ⟨hα2, ht2, hαt', hα1, ht1, hαt⟩
  set S : Set K := {α, t, g₁, g₂, h₁, h₂} with hS
  set C : Subgroup K := Subgroup.closure S with hC
  have hαC : α ∈ C := subset_closure (by simp [hS])
  have htC : t ∈ C := subset_closure (by simp [hS])
  have hg₁C : g₁ ∈ C := subset_closure (by simp [hS])
  have hg₂C : g₂ ∈ C := subset_closure (by simp [hS])
  have hh₁C : h₁ ∈ C := subset_closure (by simp [hS])
  have hh₂C : h₂ ∈ C := subset_closure (by simp [hS])
  have hZ₁ : ZCentral α t g₁ := ⟨hcα g₁ (by simp), hct g₁ (by simp)⟩
  have hZ₂ : ZCentral α t g₂ := ⟨hcα g₂ (by simp), hct g₂ (by simp)⟩
  have hZ₃ : ZCentral α t h₁ := ⟨hcα h₁ (by simp), hct h₁ (by simp)⟩
  have hZ₄ : ZCentral α t h₂ := ⟨hcα h₂ (by simp), hct h₂ (by simp)⟩
  have hcentα : ∀ c ∈ C, c * α = α * c := by
    have hle : C ≤ centralizer ({α} : Set K) := by
      rw [hC, closure_le]
      intro s hs
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rw [SetLike.mem_coe]
      rcases hs with h | h | h | h | h | h <;> rw [h] <;> apply mem_centralizer_singleton_iff.2
      · rfl
      · exact hαt'.symm
      · exact hZ₁.1
      · exact hZ₂.1
      · exact hZ₃.1
      · exact hZ₄.1
    exact fun c hc => mem_centralizer_singleton_iff.1 (hle hc)
  have hcentt : ∀ c ∈ C, c * t = t * c := by
    have hle : C ≤ centralizer ({t} : Set K) := by
      rw [hC, closure_le]
      intro s hs
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rw [SetLike.mem_coe]
      rcases hs with h | h | h | h | h | h <;> rw [h] <;> apply mem_centralizer_singleton_iff.2
      · exact hαt'
      · rfl
      · exact hZ₁.2
      · exact hZ₂.2
      · exact hZ₃.2
      · exact hZ₄.2
    exact fun c hc => mem_centralizer_singleton_iff.1 (hle hc)
  have hsymmι : ∀ x y : K, ∀ u, x * y * x⁻¹ * y⁻¹ = kleinMap α t u →
      y * x * y⁻¹ * x⁻¹ = kleinMap α t u := by
    intro x y u hxy
    have : y * x * y⁻¹ * x⁻¹ = (x * y * x⁻¹ * y⁻¹)⁻¹ := by group
    rw [this, hxy, hK.kleinMap_inv]
  have hdiag : ∀ x : K, x * x * x⁻¹ * x⁻¹ = kleinMap α t 0 := by
    intro x
    rw [kleinMap_zero]
    group
  have hcommι : ∀ x y : K, x * y = y * x → x * y * x⁻¹ * y⁻¹ = kleinMap α t 0 := by
    intro x y hxy
    rw [kleinMap_zero, hxy]
    group
  have e12 : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = kleinMap α t (1, 1) := by rw [kleinMap_one_one]; exact h12
  have e34 : h₁ * h₂ * h₁⁻¹ * h₂⁻¹ = kleinMap α t (1, 0) := by rw [kleinMap_one_zero]; exact h34
  have e14 : g₁ * h₂ * g₁⁻¹ * h₂⁻¹ = kleinMap α t (0, 1) := by rw [kleinMap_zero_one]; exact h14
  have e23 : g₂ * h₁ * g₂⁻¹ * h₁⁻¹ = kleinMap α t (0, 1) := by rw [kleinMap_zero_one]; exact h23
  have e13 : g₁ * h₁ * g₁⁻¹ * h₁⁻¹ = kleinMap α t 0 := hcommι _ _ h13
  have e24 : g₂ * h₂ * g₂⁻¹ * h₂⁻¹ = kleinMap α t 0 := hcommι _ _ h24
  have e21 := hsymmι _ _ _ e12
  have e43 := hsymmι _ _ _ e34
  have e41 := hsymmι _ _ _ e14
  have e32 := hsymmι _ _ _ e23
  have e31 := hsymmι _ _ _ e13
  have e42 := hsymmι _ _ _ e24
  have hcw₁ := fun v e => comm_word hK hZ₁ hZ₂ hZ₃ hZ₁ (hdiag g₁) e21 e31 e41 v e
  have hcw₂ := fun v e => comm_word hK hZ₁ hZ₂ hZ₃ hZ₂ e12 (hdiag g₂) e32 e42 v e
  have hcw₃ := fun v e => comm_word hK hZ₁ hZ₂ hZ₃ hZ₃ e13 e23 (hdiag h₁) e43 v e
  have hcw₄ := fun v e => comm_word hK hZ₁ hZ₂ hZ₃ hZ₄ e14 e24 e34 (hdiag h₂) v e
  have hinj : ∀ v v' e e', kleinMap α t v * word g₁ g₂ h₁ h₂ e =
      kleinMap α t v' * word g₁ g₂ h₁ h₂ e' → v = v' ∧ e = e' := by
    intro v v' e e' hval
    have a₁ := hcw₁ v e
    have a₂ := hcw₂ v e
    have a₃ := hcw₃ v e
    have a₄ := hcw₄ v e
    rw [hval, hcw₁ v' e'] at a₁
    rw [hval, hcw₂ v' e'] at a₂
    rw [hval, hcw₃ v' e'] at a₃
    rw [hval, hcw₄ v' e'] at a₄
    have he : e = e' := table_inj e e' (hK.kleinMap_injective a₁).symm
      (hK.kleinMap_injective a₂).symm (hK.kleinMap_injective a₃).symm
      (hK.kleinMap_injective a₄).symm
    subst he
    exact ⟨hK.kleinMap_injective (mul_right_cancel hval), rfl⟩
  have hwC : ∀ e, word g₁ g₂ h₁ h₂ e ∈ C := by
    intro e
    exact C.mul_mem (C.pow_mem hg₁C _) (C.mul_mem (C.pow_mem hg₂C _)
      (C.mul_mem (C.pow_mem hh₁C _) (C.pow_mem hh₂C _)))
  have hιC : ∀ v, kleinMap α t v ∈ C := fun v =>
    C.mul_mem (C.pow_mem hαC _) (C.pow_mem htC _)
  let Φ : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) → C := fun p =>
    ⟨kleinMap α t p.1 * word g₁ g₂ h₁ h₂ p.2, C.mul_mem (hιC _) (hwC _)⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨v, e⟩ ⟨v', e'⟩ hΦ
    obtain ⟨rfl, rfl⟩ := hinj v v' e e' (congrArg Subtype.val hΦ)
    rfl
  have hcardVE : Nat.card ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) = 64 := by
    simp
  have h64 : 64 ≤ Nat.card C := by
    rw [← hcardVE]
    exact Nat.card_le_card_of_injective Φ hΦinj
  obtain ⟨hCeq, p, hpC, hpZ, ζ, hζ, hcomm⟩ := exists_noncentral_small_commutator hWreath hz hC2
    h64 hαC htC hcentα hcentt hα2 ht2 hα1 ht1 hαt hzα hzt htcomm hnconj
  have hbij : Function.Bijective Φ := hΦinj.bijective_of_nat_card_le (by rw [hCeq, hcardVE])
  obtain ⟨⟨v, e⟩, hve⟩ := hbij.2 ⟨p, hpC⟩
  have hp : p = kleinMap α t v * word g₁ g₂ h₁ h₂ e := (congrArg Subtype.val hve).symm
  obtain ⟨ζ', hζ'⟩ := exists_kleinMap_eq_of_mem hK hζ
  have k₁ : wsum 0 (1, 1) 0 (0, 1) e = 0 ∨ wsum 0 (1, 1) 0 (0, 1) e = ζ' := by
    rcases hcomm g₁ hg₁C with h | h
    · left
      apply hK.kleinMap_injective
      rw [kleinMap_zero, ← hcw₁ v e, ← hp]
      exact h
    · right
      apply hK.kleinMap_injective
      rw [hζ', ← hcw₁ v e, ← hp]
      exact h
  have k₂ : wsum (1, 1) 0 (0, 1) 0 e = 0 ∨ wsum (1, 1) 0 (0, 1) 0 e = ζ' := by
    rcases hcomm g₂ hg₂C with h | h
    · left
      apply hK.kleinMap_injective
      rw [kleinMap_zero, ← hcw₂ v e, ← hp]
      exact h
    · right
      apply hK.kleinMap_injective
      rw [hζ', ← hcw₂ v e, ← hp]
      exact h
  have k₃ : wsum 0 (0, 1) 0 (1, 0) e = 0 ∨ wsum 0 (0, 1) 0 (1, 0) e = ζ' := by
    rcases hcomm h₁ hh₁C with h | h
    · left
      apply hK.kleinMap_injective
      rw [kleinMap_zero, ← hcw₃ v e, ← hp]
      exact h
    · right
      apply hK.kleinMap_injective
      rw [hζ', ← hcw₃ v e, ← hp]
      exact h
  have k₄ : wsum (0, 1) 0 (1, 0) 0 e = 0 ∨ wsum (0, 1) 0 (1, 0) 0 e = ζ' := by
    rcases hcomm h₂ hh₂C with h | h
    · left
      apply hK.kleinMap_injective
      rw [kleinMap_zero, ← hcw₄ v e, ← hp]
      exact h
    · right
      apply hK.kleinMap_injective
      rw [hζ', ← hcw₄ v e, ← hp]
      exact h
  have he0 : e = 0 := table_final ζ' e k₁ k₂ k₃ k₄
  have hw0 : word g₁ g₂ h₁ h₂ 0 = 1 := by simp [word]
  apply hpZ
  rw [hp, he0, hw0, mul_one]
  exact kleinMap_mem α t v

end CFSG.EvenSporadicStandard.Fin76b
