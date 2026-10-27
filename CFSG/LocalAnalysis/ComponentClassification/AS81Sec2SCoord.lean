module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2V4
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.Quasithin.Background.F9Pairing

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

abbrev Pair := (Fin 5 → ZMod 2) × (Fin 5 → ZMod 2)

theorem card_evens2 : Nat.card {m : Pair // IsEven m.1 ∧ IsEven m.2} = 256 := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd (p := IsEven) (q := IsEven)), Nat.card_prod,
    card_even]

variable {G : Type} [Group G]

structure Special (S Z : Subgroup G) : Prop where
  card : Nat.card Z = 4
  center : centerIn S = Z
  comm : ⁅S, S⁆ = Z
  sq : ∀ s ∈ S, s * s ∈ Z
  elem : ∀ c ∈ Z, c * c = 1

namespace Special

variable {S Z : Subgroup G} (hS : Special S Z)
include hS

theorem le : Z ≤ S := fun c hc => by
  rw [← hS.center] at hc
  exact hc.1

theorem comm_mem {s t : G} (hs : s ∈ S) (ht : t ∈ S) : s * t * s⁻¹ * t⁻¹ ∈ Z := by
  rw [← hS.comm]
  have := Subgroup.commutator_mem_commutator hs ht
  rwa [commutatorElement_def] at this

theorem comm_Z {c s : G} (hc : c ∈ Z) (hs : s ∈ S) : c * s = s * c := by
  rw [← hS.center] at hc
  exact (mem_centralizer_iff.mp hc.2 s hs).symm

theorem inv_eq {c : G} (hc : c ∈ Z) : c⁻¹ = c :=
  inv_eq_of_mul_eq_one_right (hS.elem c hc)

theorem conj_Z {c s : G} (hc : c ∈ Z) (hs : s ∈ S) : s * c * s⁻¹ = c := by
  rw [← hS.comm_Z hc hs, mul_inv_cancel_right]

theorem conj_Z' {c s : G} (hc : c ∈ Z) (hs : s ∈ S) : s⁻¹ * c * s = c := by
  rw [mul_assoc, hS.comm_Z hc hs, inv_mul_cancel_left]

theorem comm_mul_left {s s' t : G} (hs : s ∈ S) (hs' : s' ∈ S) (ht : t ∈ S) :
    s * s' * t * (s * s')⁻¹ * t⁻¹ = (s * t * s⁻¹ * t⁻¹) * (s' * t * s'⁻¹ * t⁻¹) := by
  calc s * s' * t * (s * s')⁻¹ * t⁻¹
      = (s * (s' * t * s'⁻¹ * t⁻¹) * s⁻¹) * (s * t * s⁻¹ * t⁻¹) := by group
    _ = (s' * t * s'⁻¹ * t⁻¹) * (s * t * s⁻¹ * t⁻¹) := by rw [hS.conj_Z (hS.comm_mem hs' ht) hs]
    _ = (s * t * s⁻¹ * t⁻¹) * (s' * t * s'⁻¹ * t⁻¹) :=
        hS.comm_Z (hS.comm_mem hs' ht) (hS.le (hS.comm_mem hs ht))

theorem comm_mul_right {s t t' : G} (hs : s ∈ S) (ht : t ∈ S) (ht' : t' ∈ S) :
    s * (t * t') * s⁻¹ * (t * t')⁻¹ = (s * t * s⁻¹ * t⁻¹) * (s * t' * s⁻¹ * t'⁻¹) := by
  have h := hS.comm_Z (hS.comm_mem hs ht') (S.inv_mem ht)
  calc s * (t * t') * s⁻¹ * (t * t')⁻¹
      = s * t * s⁻¹ * (s * t' * s⁻¹ * t'⁻¹) * t⁻¹ := by group
    _ = s * t * s⁻¹ * ((s * t' * s⁻¹ * t'⁻¹) * t⁻¹) := by rw [mul_assoc]
    _ = s * t * s⁻¹ * (t⁻¹ * (s * t' * s⁻¹ * t'⁻¹)) := by rw [h]
    _ = (s * t * s⁻¹ * t⁻¹) * (s * t' * s⁻¹ * t'⁻¹) := by group

omit hS in
theorem comm_inv (s t : G) : (s * t * s⁻¹ * t⁻¹)⁻¹ = t * s * t⁻¹ * s⁻¹ := by group

theorem comm_mul_Z {s t c : G} (hs : s ∈ S) (ht : t ∈ S) (hc : c ∈ Z) :
    s * (t * c) * s⁻¹ * (t * c)⁻¹ = s * t * s⁻¹ * t⁻¹ := by
  rw [hS.comm_mul_right hs ht (hS.le hc)]
  have h1 : s * c * s⁻¹ * c⁻¹ = 1 := by
    rw [← hS.comm_Z hc hs]
    group
  rw [h1, mul_one]

theorem eq_one_or_eq {c w : G} (hc : c ∈ Z) (hw : w ∈ zpowers c) : w = 1 ∨ w = c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
    rw [hm, zpow_mul, zpow_two, hS.elem c hc, one_zpow]
  · right
    obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
    rw [hm, zpow_add, zpow_mul, zpow_two, hS.elem c hc, one_zpow, one_mul, zpow_one]

theorem inf_zpowers {c d w : G} (hc : c ∈ Z) (hd : d ∈ Z) (hcd : c ≠ d)
    (hwc : w ∈ zpowers c) (hwd : w ∈ zpowers d) : w = 1 := by
  rcases hS.eq_one_or_eq hc hwc with h | h
  · exact h
  · rcases hS.eq_one_or_eq hd hwd with h' | h'
    · exact h'
    · exact absurd (h.symm.trans h') hcd

theorem eq_of_four {a b c d x : G} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) (hd : d ∈ Z)
    (hx : x ∈ Z) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hS.card]; norm_num)
  by_contra h
  push Not at h
  obtain ⟨hxa, hxb, hxc, hxd⟩ := h
  let f : Fin 5 → Z := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨x, hx⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f, eq_comm]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin, hS.card] at this
  omega

theorem mul_mem_zpowers {c w₁ w₂ : G} (hc : c ∈ Z) (hc1 : c ≠ 1) (hw₁ : w₁ ∈ Z)
    (hw₂ : w₂ ∈ Z) (h₁ : w₁ ∉ zpowers c) (h₂ : w₂ ∉ zpowers c) : w₁ * w₂ ∈ zpowers c := by
  by_contra h
  have hne : ∀ {w : G}, w ∉ zpowers c → w ≠ 1 ∧ w ≠ c := fun hw =>
    ⟨fun e => hw (e ▸ one_mem _), fun e => hw (e ▸ mem_zpowers c)⟩
  have h12 : w₁ ≠ w₂ := by
    rintro rfl
    exact h (by rw [hS.elem _ hw₁]; exact one_mem _)
  rcases hS.eq_of_four (one_mem Z) hc hw₁ hw₂ (Z.mul_mem hw₁ hw₂) hc1.symm (hne h₁).1.symm
      (hne h₂).1.symm (hne h₁).2.symm (hne h₂).2.symm h12 with e | e | e | e
  · exact (hne h).1 e
  · exact (hne h).2 e
  · exact (hne h₂).1 (by simpa using e)
  · exact (hne h₁).1 (by simpa using e)

@[expose] def perp (c : G) (U : Subgroup G) : Subgroup G where
  carrier := {s | s ∈ S ∧ ∀ t ∈ U ⊓ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, fun t ht => ?_⟩
    rw [hS.comm_mul_left ha hb ht.2]
    exact mul_mem (ha' t ht) (hb' t ht)
  one_mem' := ⟨S.one_mem, fun t _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨S.inv_mem ha, fun t ht => ?_⟩
    have e : a⁻¹ * t * a⁻¹⁻¹ * t⁻¹ = a⁻¹ * (a * t * a⁻¹ * t⁻¹)⁻¹ * a := by group
    rw [e, hS.conj_Z' (Z.inv_mem (hS.comm_mem ha ht.2)) ha]
    exact inv_mem (ha' t ht)

theorem Z_le_perp (c : G) (U : Subgroup G) : Z ≤ hS.perp c U := fun w hw =>
  ⟨hS.le hw, fun t ht => by
    rw [hS.comm_Z hw ht.2, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _⟩

theorem conj_eq_of_conj_eq {x c : G} (hxZ : x ∈ normalizer (Z : Set G)) (hx3 : x ^ 3 = 1)
    (hc : c ∈ Z) (hc1 : c ≠ 1) (hxc : x * c * x⁻¹ = c) {w : G} (hw : w ∈ Z) :
    x * w * x⁻¹ = w := by
  have hxc' : x⁻¹ * c * x = c := by
    calc x⁻¹ * c * x = x⁻¹ * (x * c * x⁻¹) * x := by rw [hxc]
      _ = c := by group
  by_cases hwc : w ∈ zpowers c
  · rcases hS.eq_one_or_eq hc hwc with rfl | rfl
    · group
    · exact hxc
  have hw' : x * w * x⁻¹ ∈ Z := (mem_normalizer_iff.mp hxZ w).mp hw
  have hw'c : x * w * x⁻¹ ∉ zpowers c := by
    intro h
    apply hwc
    have e : w = x⁻¹ * (x * w * x⁻¹) * x := by group
    rcases hS.eq_one_or_eq hc h with h1 | h1
    · rw [e, h1]
      simp
    · rw [e, h1, hxc']
      exact mem_zpowers c
  have hwinv : w⁻¹ ∉ zpowers c := fun h => hwc (by simpa using inv_mem h)
  have hmem := hS.mul_mem_zpowers hc hc1 (Z.inv_mem hw) hw' hwinv hw'c
  rcases hS.eq_one_or_eq hc hmem with h | h
  · calc x * w * x⁻¹ = w * (w⁻¹ * (x * w * x⁻¹)) := by group
      _ = w := by rw [h, mul_one]
  · exfalso
    have h1 : x * w * x⁻¹ = c * w := by
      calc x * w * x⁻¹ = w * (w⁻¹ * (x * w * x⁻¹)) := by group
        _ = w * c := by rw [h]
        _ = c * w := (hS.comm_Z hc (hS.le hw)).symm
    have h3 : x ^ 3 * w * (x ^ 3)⁻¹ = c * w := by
      have e : x ^ 3 * w * (x ^ 3)⁻¹ = x * (x * (x * w * x⁻¹) * x⁻¹) * x⁻¹ := by
        rw [pow_three]
        group
      have e2 : x * (c * w) * x⁻¹ = (x * c * x⁻¹) * (x * w * x⁻¹) := by group
      have hcc : c * (c * w) = w := by rw [← mul_assoc, hS.elem c hc, one_mul]
      rw [e, h1, e2, hxc, h1, hcc, h1]
    rw [hx3, one_mul, inv_one, mul_one] at h3
    apply hc1
    calc c = c * w * w⁻¹ := by group
      _ = 1 := by rw [← h3, mul_inv_cancel]

theorem conj_mem_perp {y c u : G} (hy : y ∈ normalizer (S : Set G)) (hu : u ∈ hS.perp c S) :
    y * u * y⁻¹ ∈ hS.perp (y * c * y⁻¹) S := by
  refine ⟨(mem_normalizer_iff.mp hy u).mp hu.1, fun t ht => ?_⟩
  have ht' : y⁻¹ * t * y ∈ S := by
    have := (mem_normalizer_iff.mp (inv_mem hy) t).mp ht.2
    simpa using this
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hu.2 _ ⟨ht', ht'⟩)
  refine mem_zpowers_iff.mpr ⟨k, ?_⟩
  have e : y * u * y⁻¹ * t * (y * u * y⁻¹)⁻¹ * t⁻¹ =
      y * (u * (y⁻¹ * t * y) * u⁻¹ * (y⁻¹ * t * y)⁻¹) * y⁻¹ := by group
  rw [e, ← hk, conj_zpow]

theorem perp_inf_le {c d : G} (hc : c ∈ Z) (hd : d ∈ Z) (hcd : c ≠ d) :
    hS.perp c S ⊓ hS.perp d S ≤ Z := by
  rintro u ⟨hu, hu'⟩
  rw [← hS.center]
  refine ⟨hu.1, mem_centralizer_iff.mpr fun t ht => ?_⟩
  have h1 := hS.inf_zpowers hc hd hcd (hu.2 t ⟨ht, ht⟩) (hu'.2 t ⟨ht, ht⟩)
  calc t * u = (u * t * u⁻¹ * t⁻¹)⁻¹ * u * t := by group
    _ = u * t := by rw [h1, inv_one, one_mul]

@[expose] noncomputable def ell (c w : G) : ZMod 2 := by
  classical
  exact if w ∈ zpowers c then 0 else 1

omit hS in
theorem ell_eq_zero_iff (c w : G) : ell c w = 0 ↔ w ∈ zpowers c := by
  classical
  unfold ell
  split_ifs with h <;> simp [h]

theorem ell_mul {c w₁ w₂ : G} (hc : c ∈ Z) (hc1 : c ≠ 1) (hw₁ : w₁ ∈ Z) (hw₂ : w₂ ∈ Z) :
    ell c (w₁ * w₂) = ell c w₁ + ell c w₂ := by
  classical
  by_cases h₁ : w₁ ∈ zpowers c <;> by_cases h₂ : w₂ ∈ zpowers c
  · have : w₁ * w₂ ∈ zpowers c := mul_mem h₁ h₂
    simp [ell, h₁, h₂, this]
  · have : w₁ * w₂ ∉ zpowers c := fun h => h₂ (by simpa using mul_mem (inv_mem h₁) h)
    simp [ell, h₁, h₂, this]
  · have : w₁ * w₂ ∉ zpowers c := fun h => h₁ (by simpa using mul_mem h (inv_mem h₂))
    simp [ell, h₁, h₂, this]
  · have : w₁ * w₂ ∈ zpowers c := hS.mul_mem_zpowers hc hc1 hw₁ hw₂ h₁ h₂
    simp only [ell, h₁, h₂, this, ↓reduceIte]
    decide

end Special

theorem pair_add_self (m : Pair) : m + m = 0 := by
  have h : ∀ x : ZMod 2, x + x = 0 := by decide
  ext k <;> exact h _

theorem special_of (h24 : Step24) [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hS : Sec2Setting G A R g E F) : Special (sec2S A R E F) (sec2Z A E F) := by
  obtain ⟨h1, h2, h3, h4⟩ := h24 G A R g E F hS
  refine ⟨h1, h2, h3, h4, fun c hc => ?_⟩
  have hc' : c ∈ centerIn (E ⊔ F) := hc.2
  rw [← hS.frame.inf_eq_center] at hc'
  have := hS.frame.elemE.2 c hc'.1
  rwa [sq] at this

structure Coord (S Z H : Subgroup G) where
  φ : ↥H →* alternatingGroup (Fin 5)
  surj : Function.Surjective φ
  ker : φ.ker = S.subgroupOf H
  S₂ : Subgroup G
  S₃ : Subgroup G
  ψ₂ : G → (Fin 5 → ZMod 2)
  ψ₃ : G → (Fin 5 → ZMod 2)
  sup : S₂ ⊔ S₃ = S
  inf : S₂ ⊓ S₃ = Z
  Z_le₂ : Z ≤ S₂
  Z_le₃ : Z ≤ S₃
  le₂ : S₂ ≤ S
  le₃ : S₃ ≤ S
  add₂ : ∀ a ∈ S₂, ∀ b ∈ S₂, ψ₂ (a * b) = ψ₂ a + ψ₂ b
  add₃ : ∀ a ∈ S₃, ∀ b ∈ S₃, ψ₃ (a * b) = ψ₃ a + ψ₃ b
  ker₂ : ∀ a ∈ S₂, ψ₂ a = 0 ↔ a ∈ Z
  ker₃ : ∀ a ∈ S₃, ψ₃ a = 0 ↔ a ∈ Z
  even₂ : ∀ a ∈ S₂, IsEven (ψ₂ a)
  even₃ : ∀ a ∈ S₃, IsEven (ψ₃ a)
  onto₂ : ∀ v, IsEven v → ∃ a ∈ S₂, ψ₂ a = v
  onto₃ : ∀ v, IsEven v → ∃ a ∈ S₃, ψ₃ a = v
  conj₂ : ∀ h : ↥H, ∀ a ∈ S₂, (h : G) * a * (h : G)⁻¹ ∈ S₂ ∧
    ψ₂ ((h : G) * a * (h : G)⁻¹) = act (φ h) (ψ₂ a)
  conj₃ : ∀ h : ↥H, ∀ a ∈ S₃, (h : G) * a * (h : G)⁻¹ ∈ S₃ ∧
    ψ₃ ((h : G) * a * (h : G)⁻¹) = act (φ h) (ψ₃ a)

theorem nonempty_coord (h26 : Step26) [Finite G] {A R : Subgroup G} {g : G} {E F : Subgroup G}
    (hS : Sec2Setting G A R g E F) :
    Nonempty (Coord (sec2S A R E F) (sec2Z A E F) (sec2H E F)) := by
  obtain ⟨-, -, -, -, -, -, ⟨φ, hφ, hker, S₂, S₃, ψ₂, ψ₃, hsup, hinf, hi⟩, -, -⟩ :=
    h26 G A R g E F hS
  obtain ⟨hZ₂, hle₂, hadd₂, hker₂, hsum₂, honto₂, hconj₂⟩ := hi (S₂, ψ₂) (Set.mem_insert _ _)
  obtain ⟨hZ₃, hle₃, hadd₃, hker₃, hsum₃, honto₃, hconj₃⟩ :=
    hi (S₃, ψ₃) (Set.mem_insert_of_mem _ rfl)
  exact ⟨⟨φ, hφ, hker, S₂, S₃, ψ₂, ψ₃, hsup, hinf, hZ₂, hZ₃, hle₂, hle₃, hadd₂, hadd₃, hker₂,
    hker₃, hsum₂, hsum₃, honto₂, honto₃, hconj₂, hconj₃⟩⟩

namespace Coord

variable {S Z H : Subgroup G} (C : Coord S Z H) (hS : Special S Z)
include hS

theorem le_normalizer : C.S₂ ≤ normalizer (C.S₃ : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  have haS := C.le₂ ha
  constructor
  · intro hb
    have e : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact C.S₃.mul_mem (C.Z_le₃ (hS.comm_mem haS (C.le₃ hb))) hb
  · intro hb
    have hb' := C.le₃ hb
    have e : b = (a⁻¹ * (a * b * a⁻¹) * a⁻¹⁻¹ * (a * b * a⁻¹)⁻¹) * (a * b * a⁻¹) := by group
    rw [e]
    exact C.S₃.mul_mem (C.Z_le₃ (hS.comm_mem (S.inv_mem haS) hb')) hb

theorem exists_mul {s : G} (hs : s ∈ S) : ∃ a ∈ C.S₂, ∃ b ∈ C.S₃, a * b = s := by
  have h : ((C.S₂ ⊔ C.S₃ : Subgroup G) : Set G) = (C.S₂ : Set G) * (C.S₃ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C.S₂ C.S₃ (C.le_normalizer hS) ▸ rfl
  have hs' : s ∈ ((C.S₂ ⊔ C.S₃ : Subgroup G) : Set G) := by
    rw [C.sup]
    exact hs
  rw [h] at hs'
  obtain ⟨a, ha, b, hb, rfl⟩ := hs'
  exact ⟨a, ha, b, hb, rfl⟩

omit hS in
@[expose] noncomputable def Ψ (s : G) : Pair := by
  classical
  exact if h : ∃ p : G × G, p.1 ∈ C.S₂ ∧ p.2 ∈ C.S₃ ∧ p.1 * p.2 = s then
    (C.ψ₂ h.choose.1, C.ψ₃ h.choose.2) else 0

omit hS in
theorem Ψ_of_mul {a b : G} (ha : a ∈ C.S₂) (hb : b ∈ C.S₃) : C.Ψ (a * b) = (C.ψ₂ a, C.ψ₃ b) := by
  classical
  have h : ∃ p : G × G, p.1 ∈ C.S₂ ∧ p.2 ∈ C.S₃ ∧ p.1 * p.2 = a * b := ⟨(a, b), ha, hb, rfl⟩
  rw [Ψ, dite_eq_left h]
  have hs := h.choose_spec
  generalize h.choose = p at hs ⊢
  obtain ⟨a', b'⟩ := p
  obtain ⟨ha', hb', hab⟩ := hs
  simp only at ha' hb' hab ⊢
  have hc₂ : a'⁻¹ * a ∈ C.S₂ := C.S₂.mul_mem (C.S₂.inv_mem ha') ha
  have hc₃ : a'⁻¹ * a ∈ C.S₃ := by
    have e : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    rw [e]
    exact C.S₃.mul_mem hb' (C.S₃.inv_mem hb)
  have hcZ : a'⁻¹ * a ∈ Z := C.inf ▸ ⟨hc₂, hc₃⟩
  have hc0₂ : C.ψ₂ (a'⁻¹ * a) = 0 := (C.ker₂ _ hc₂).mpr hcZ
  have hc0₃ : C.ψ₃ (a'⁻¹ * a) = 0 := (C.ker₃ _ hc₃).mpr hcZ
  refine Prod.ext ?_ ?_
  · show C.ψ₂ a' = C.ψ₂ a
    have e := C.add₂ a' ha' (a'⁻¹ * a) hc₂
    rw [mul_inv_cancel_left, hc0₂, add_zero] at e
    exact e.symm
  · show C.ψ₃ b' = C.ψ₃ b
    have e := C.add₃ (a'⁻¹ * a) hc₃ b hb
    have e' : a'⁻¹ * a * b = b' := by
      calc a'⁻¹ * a * b = a'⁻¹ * (a * b) := by group
        _ = a'⁻¹ * (a' * b') := by rw [hab]
        _ = b' := by group
    rw [e', hc0₃, zero_add] at e
    exact e

theorem Ψ_mul {s t : G} (hs : s ∈ S) (ht : t ∈ S) : C.Ψ (s * t) = C.Ψ s + C.Ψ t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_mul hS hs
  obtain ⟨a', ha', b', hb', rfl⟩ := C.exists_mul hS ht
  have hc : a'⁻¹ * b * a'⁻¹⁻¹ * b⁻¹ ∈ Z := hS.comm_mem (S.inv_mem (C.le₂ ha')) (C.le₃ hb)
  have e : a * b * (a' * b') = (a * a') * ((a'⁻¹ * b * a'⁻¹⁻¹ * b⁻¹) * b * b') := by group
  rw [e, C.Ψ_of_mul (C.S₂.mul_mem ha ha')
    (C.S₃.mul_mem (C.S₃.mul_mem (C.Z_le₃ hc) hb) hb'), C.Ψ_of_mul ha hb,
    C.Ψ_of_mul ha' hb', C.add₂ _ ha _ ha', C.add₃ _ (C.S₃.mul_mem (C.Z_le₃ hc) hb) _ hb',
    C.add₃ _ (C.Z_le₃ hc) _ hb, (C.ker₃ _ (C.Z_le₃ hc)).mpr hc, zero_add]
  rfl

omit hS in
theorem Ψ_one : C.Ψ 1 = 0 := by
  have h := C.Ψ_of_mul C.S₂.one_mem C.S₃.one_mem
  rw [mul_one] at h
  rw [h, (C.ker₂ 1 C.S₂.one_mem).mpr Z.one_mem, (C.ker₃ 1 C.S₃.one_mem).mpr Z.one_mem]
  rfl

theorem Ψ_eq_zero_iff {s : G} (hs : s ∈ S) : C.Ψ s = 0 ↔ s ∈ Z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_mul hS hs
  rw [C.Ψ_of_mul ha hb, Prod.mk_eq_zero, C.ker₂ a ha, C.ker₃ b hb]
  constructor
  · rintro ⟨haZ, hbZ⟩
    exact Z.mul_mem haZ hbZ
  · intro h
    have hb' : b ∈ C.S₂ := by
      have e : b = a⁻¹ * (a * b) := by group
      rw [e]
      exact C.S₂.mul_mem (C.S₂.inv_mem ha) (C.Z_le₂ h)
    have hbZ : b ∈ Z := C.inf ▸ ⟨hb', hb⟩
    refine ⟨?_, hbZ⟩
    have e : a = (a * b) * b⁻¹ := by group
    rw [e]
    exact Z.mul_mem h (Z.inv_mem hbZ)

theorem Ψ_inv {s : G} (hs : s ∈ S) : C.Ψ s⁻¹ = C.Ψ s := by
  have h := C.Ψ_mul hS (S.inv_mem hs) hs
  rw [inv_mul_cancel, C.Ψ_one] at h
  have h2 := pair_add_self (C.Ψ s)
  calc C.Ψ s⁻¹ = C.Ψ s⁻¹ + (C.Ψ s + C.Ψ s) := by rw [h2, add_zero]
    _ = (C.Ψ s⁻¹ + C.Ψ s) + C.Ψ s := by rw [add_assoc]
    _ = C.Ψ s := by rw [← h, zero_add]

theorem Ψ_eq_iff {s t : G} (hs : s ∈ S) (ht : t ∈ S) : C.Ψ s = C.Ψ t ↔ s * t⁻¹ ∈ Z := by
  rw [← C.Ψ_eq_zero_iff hS (S.mul_mem hs (S.inv_mem ht)), C.Ψ_mul hS hs (S.inv_mem ht),
    C.Ψ_inv hS ht]
  constructor
  · intro h
    rw [h, pair_add_self]
  · intro h
    calc C.Ψ s = C.Ψ s + (C.Ψ t + C.Ψ t) := by rw [pair_add_self, add_zero]
      _ = (C.Ψ s + C.Ψ t) + C.Ψ t := by rw [add_assoc]
      _ = C.Ψ t := by rw [h, zero_add]

theorem Ψ_even {s : G} (hs : s ∈ S) : IsEven (C.Ψ s).1 ∧ IsEven (C.Ψ s).2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_mul hS hs
  rw [C.Ψ_of_mul ha hb]
  exact ⟨C.even₂ a ha, C.even₃ b hb⟩

omit hS in
theorem exists_Ψ_eq {v w : Fin 5 → ZMod 2} (hv : IsEven v) (hw : IsEven w) :
    ∃ s ∈ S, C.Ψ s = (v, w) := by
  obtain ⟨a, ha, rfl⟩ := C.onto₂ v hv
  obtain ⟨b, hb, rfl⟩ := C.onto₃ w hw
  exact ⟨a * b, S.mul_mem (C.le₂ ha) (C.le₃ hb), C.Ψ_of_mul ha hb⟩

theorem Ψ_conj (h : ↥H) {s : G} (hs : s ∈ S) :
    C.Ψ ((h : G) * s * (h : G)⁻¹) = act₂ (C.φ h) (C.Ψ s) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := C.exists_mul hS hs
  have e : (h : G) * (a * b) * (h : G)⁻¹ =
      ((h : G) * a * (h : G)⁻¹) * ((h : G) * b * (h : G)⁻¹) := by group
  rw [e, C.Ψ_of_mul (C.conj₂ h a ha).1 (C.conj₃ h b hb).1, C.Ψ_of_mul ha hb,
    (C.conj₂ h a ha).2, (C.conj₃ h b hb).2]
  rfl

@[expose] noncomputable def img (U : Subgroup G) : AddSubgroup Pair where
  carrier := {m | ∃ s ∈ U ⊓ S, C.Ψ s = m}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, (U ⊓ S).mul_mem ha hb, C.Ψ_mul hS ha.2 hb.2⟩
  zero_mem' := ⟨1, (U ⊓ S).one_mem, C.Ψ_one⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    have h := pair_add_self (C.Ψ a)
    rw [eq_neg_iff_add_eq_zero]
    exact h

theorem Ψ_mem_img {U : Subgroup G} {s : G} (hs : s ∈ U) (hsS : s ∈ S) : C.Ψ s ∈ C.img hS U :=
  ⟨s, ⟨hs, hsS⟩, rfl⟩

theorem mem_of_Ψ_mem_img {U : Subgroup G} (hZU : Z ≤ U) {s : G} (hs : s ∈ S)
    (h : C.Ψ s ∈ C.img hS U) : s ∈ U := by
  obtain ⟨t, ht, hts⟩ := h
  have hst : s * t⁻¹ ∈ Z := (C.Ψ_eq_iff hS hs ht.2).mp hts.symm
  have e : s = (s * t⁻¹) * t := by group
  rw [e]
  exact U.mul_mem (hZU hst) ht.1

theorem img_even {U : Subgroup G} {m : Pair} (hm : m ∈ C.img hS U) : IsEven m.1 ∧ IsEven m.2 := by
  obtain ⟨s, hs, rfl⟩ := hm
  exact C.Ψ_even hS hs.2

@[expose] noncomputable def ΨU {U : Subgroup G} (hU : U ≤ S) : ↥U →* Multiplicative Pair where
  toFun u := Multiplicative.ofAdd (C.Ψ u)
  map_one' := by
    show Multiplicative.ofAdd (C.Ψ 1) = 1
    rw [C.Ψ_one]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (C.Ψ (a * b)) = _
    rw [C.Ψ_mul hS (hU a.2) (hU b.2)]
    rfl

theorem ΨU_apply {U : Subgroup G} (hU : U ≤ S) (u : ↥U) :
    C.ΨU hS hU u = Multiplicative.ofAdd (C.Ψ u) := rfl

theorem card_range_ΨU {U : Subgroup G} (hU : U ≤ S) :
    Nat.card (C.ΨU hS hU).range = Nat.card (C.img hS U) := by
  refine Nat.card_congr
    { toFun := fun m => ⟨Multiplicative.toAdd m.1, by
        obtain ⟨u, hu⟩ := m.2
        rw [← hu]
        exact C.Ψ_mem_img hS u.2 (hU u.2)⟩
      invFun := fun m => ⟨Multiplicative.ofAdd m.1, by
        obtain ⟨s, hs, hsm⟩ := m.2
        exact ⟨⟨s, hs.1⟩, by
          rw [ΨU_apply]
          show Multiplicative.ofAdd (C.Ψ s) = _
          rw [hsm]⟩⟩
      left_inv := fun m => rfl
      right_inv := fun m => rfl }

theorem card_eq [Finite G] {U : Subgroup G} (hU : U ≤ S) :
    Nat.card U = Nat.card (U ⊓ Z : Subgroup G) * Nat.card (C.img hS U) := by
  have hker : Nat.card (C.ΨU hS hU).ker = Nat.card (U ⊓ Z : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun u => ⟨u.1, u.1.2, (C.Ψ_eq_zero_iff hS (hU u.1.2)).mp
          (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp u.2))⟩
        invFun := fun u => ⟨⟨u.1, u.2.1⟩, MonoidHom.mem_ker.mpr
          (congrArg Multiplicative.ofAdd ((C.Ψ_eq_zero_iff hS (hU u.2.1)).mpr u.2.2))⟩
        left_inv := fun u => rfl
        right_inv := fun u => rfl }
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (C.ΨU hS hU).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (C.ΨU hS hU)).toEquiv,
    C.card_range_ΨU hS hU, hker, mul_comm]

theorem card_eq_four_mul [Finite G] {U : Subgroup G} (hZU : Z ≤ U) (hU : U ≤ S) :
    Nat.card U = 4 * Nat.card (C.img hS U) := by
  rw [C.card_eq hS hU, inf_eq_right.mpr hZU, hS.card]

theorem card_img_S : Nat.card (C.img hS S) = 256 := by
  rw [← card_evens2]
  refine Nat.card_congr
    { toFun := fun m => ⟨m.1, C.img_even hS m.2⟩
      invFun := fun m => ⟨m.1, by
        obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq m.2.1 m.2.2
        exact ⟨s, ⟨hs, hs⟩, hsm⟩⟩
      left_inv := fun m => rfl
      right_inv := fun m => rfl }

include C in
theorem card_S [Finite G] : Nat.card S = 1024 := by
  rw [C.card_eq_four_mul hS hS.le le_rfl, C.card_img_S hS]

include C in
theorem conj_eq_of_mem_H [Finite G] (hHS : H ≤ normalizer (S : Set G)) {h c : G} (hh : h ∈ H)
    (hc : c ∈ Z) : h * c * h⁻¹ = c := by
  have hHZ : ∀ k ∈ H, ∀ w ∈ Z, k * w * k⁻¹ ∈ Z := by
    intro k hk w hw
    rw [← hS.center] at hw ⊢
    refine ⟨(mem_normalizer_iff.mp (hHS hk) w).mp hw.1, mem_centralizer_iff.mpr fun t ht => ?_⟩
    have ht' : k⁻¹ * t * k ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem (hHS hk)) t).mp ht
      simpa using this
    have h1 := mem_centralizer_iff.mp hw.2 _ ht'
    calc t * (k * w * k⁻¹) = k * ((k⁻¹ * t * k) * w) * k⁻¹ := by group
      _ = k * (w * (k⁻¹ * t * k)) * k⁻¹ := by rw [h1]
      _ = k * w * k⁻¹ * t := by group
  by_cases hc1 : c = 1
  · rw [hc1, mul_one, mul_inv_cancel]
  let _ : MulAction ↥H ↥Z :=
    { smul := fun k w => ⟨(k : G) * w * (k : G)⁻¹, hHZ k k.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : ↥H) : G) * w * ((1 : ↥H) : G)⁻¹ = w
        simp)
      mul_smul := fun k k' w => Subtype.ext (by
        show (k * k' : G) * w * (k * k' : G)⁻¹ = (k : G) * ((k' : G) * w * (k' : G)⁻¹) * (k : G)⁻¹
        group) }
  have hsmul : ∀ (k : ↥H) (w : ↥Z), ((k • w : ↥Z) : G) = (k : G) * w * (k : G)⁻¹ := fun _ _ => rfl
  set K := MulAction.stabilizer ↥H (⟨c, hc⟩ : ↥Z) with hK
  have hidx : K.index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    have hsub : MulAction.orbit ↥H (⟨c, hc⟩ : ↥Z) ⊆ {w | w ≠ 1} := by
      rintro _ ⟨k, rfl⟩ h1
      apply hc1
      have := congrArg Subtype.val h1
      rw [hsmul] at this
      have e : c = (k : G)⁻¹ * ((k : G) * c * (k : G)⁻¹) * (k : G) := by group
      rw [e, this]
      simp
    have hcard : ({w | w ≠ 1} : Set ↥Z).ncard = 3 := by
      rw [show ({w | w ≠ 1} : Set ↥Z) = {1}ᶜ by ext; simp, Set.ncard_compl, Set.ncard_singleton,
        hS.card]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hcard.le
  have hSK : C.φ.ker ≤ K := by
    intro k hk
    rw [C.ker] at hk
    have hk' : (k : G) ∈ S := hk
    apply Subtype.ext
    rw [hsmul]
    show (k : G) * c * (k : G)⁻¹ = c
    rw [← hS.comm_Z hc hk', mul_inv_cancel_right]
  have hidx' : (K.map C.φ).index ≤ 3 := by
    rw [Subgroup.index_map_eq K C.surj hSK]
    exact hidx
  have htop : K.map C.φ = ⊤ := by
    have hcore := Subgroup.index_normalCore_dvd_factorial_index (K.map C.φ)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map C.φ).normalCore with h | h
    · rw [h, Subgroup.index_bot, card_alternatingGroup_five] at hcore
      have h6 : Nat.factorial (K.map C.φ).index ∣ Nat.factorial 3 :=
        Nat.factorial_dvd_factorial hidx'
      have := Nat.le_of_dvd (by decide) (hcore.trans h6)
      norm_num [Nat.factorial] at this
    · exact eq_top_iff.mpr (h ▸ Subgroup.normalCore_le _)
  obtain ⟨k, hkK, hk⟩ := (show C.φ ⟨h, hh⟩ ∈ K.map C.φ by rw [htop]; exact mem_top _)
  have hk' : k⁻¹ * ⟨h, hh⟩ ∈ C.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel]
  have hmem : k * (k⁻¹ * ⟨h, hh⟩) ∈ K := K.mul_mem hkK (hSK hk')
  rw [mul_inv_cancel_left] at hmem
  have := congrArg Subtype.val hmem
  rwa [hsmul] at this

theorem img_invariant {U : Subgroup G} (hHU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (hHS : H ≤ normalizer (S : Set G)) :
    ∀ σ ∈ alternatingGroup (Fin 5), ∀ m ∈ C.img hS U, act₂ σ m ∈ C.img hS U := by
  intro σ hσ m hm
  obtain ⟨h, hh⟩ := C.surj ⟨σ, hσ⟩
  obtain ⟨s, hs, rfl⟩ := hm
  refine ⟨(h : G) * s * (h : G)⁻¹, ⟨hHU h h.2 s hs.1, (mem_normalizer_iff.mp (hHS h.2) s).mp hs.2⟩,
    ?_⟩
  rw [C.Ψ_conj hS h hs.2, hh]

theorem card_img_perp [Finite G] (hHS : H ≤ normalizer (S : Set G)) {d : G} (hd : d ∈ Z)
    {u : G} (hu : u ∈ hS.perp d S) (huZ : u ∉ Z) : 16 ≤ Nat.card (C.img hS (hS.perp d S)) := by
  have hinv : ∀ h ∈ H, ∀ v ∈ hS.perp d S, h * v * h⁻¹ ∈ hS.perp d S := by
    intro h hh v hv
    have := hS.conj_mem_perp (hHS hh) hv
    rwa [C.conj_eq_of_mem_H hS hHS hh hd] at this
  refine card_le_of_pair_invariant (fun m hm => C.img_even hS hm)
    (C.img_invariant hS hinv hHS) ?_
  intro h
  have hmem : C.Ψ u ∈ C.img hS (hS.perp d S) := C.Ψ_mem_img hS hu hu.1
  rw [h, AddSubgroup.mem_bot, C.Ψ_eq_zero_iff hS hu.1] at hmem
  exact huZ hmem

theorem img_perp_inf {c d : G} (hc : c ∈ Z) (hd : d ∈ Z) (hcd : c ≠ d) :
    C.img hS (hS.perp c S) ⊓ C.img hS (hS.perp d S) = ⊥ := by
  rw [eq_bot_iff]
  rintro m ⟨⟨u, hu, rfl⟩, hm⟩
  have hu' : u ∈ hS.perp d S := C.mem_of_Ψ_mem_img hS (hS.Z_le_perp d S) hu.2 hm
  rw [AddSubgroup.mem_bot, C.Ψ_eq_zero_iff hS hu.2]
  exact hS.perp_inf_le hc hd hcd ⟨hu.1, hu'⟩

theorem exists_mul_mul [Finite G] {c d : G} (hc : c ∈ Z) (hd : d ∈ Z) (hcd : c ≠ d)
    (h₁ : 16 ≤ Nat.card (C.img hS (hS.perp c S))) (h₂ : 16 ≤ Nat.card (C.img hS (hS.perp d S)))
    {t : G} (ht : t ∈ S) : ∃ z ∈ Z, ∃ a ∈ hS.perp c S, ∃ b ∈ hS.perp d S, t = z * (a * b) := by
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab⟩ := exists_add_of_inf_eq_bot
    (fun m hm => C.img_even hS hm) (fun m hm => C.img_even hS hm) (C.img_perp_inf hS hc hd hcd)
    h₁ h₂ (C.Ψ_even hS ht)
  rw [← C.Ψ_mul hS ha.2 hb.2] at hab
  have hz := (C.Ψ_eq_iff hS ht (S.mul_mem ha.2 hb.2)).mp hab.symm
  exact ⟨t * (a * b)⁻¹, hz, a, ha.1, b, hb.1, by group⟩

include C in
theorem mem_of_comm_mem_zpowers [Finite G] (hHS : H ≤ normalizer (S : Set G)) {x : G}
    (hxS : x ∈ normalizer (S : Set G)) (hxZ : x ∈ normalizer (Z : Set G)) (hx3 : x ^ 3 = 1)
    (hxc : closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = Z) {c : G} (hc : c ∈ Z)
    (hc1 : c ≠ 1) {s : G} (hs : s ∈ S) (hsc : ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c) :
    s ∈ Z := by
  by_contra hsZ
  have hmove : ∀ d ∈ Z, d ≠ 1 → x * d * x⁻¹ ≠ d := by
    intro d hd hd1 h
    have hbot : closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = ⊥ := by
      rw [closure_eq_bot_iff]
      rintro _ ⟨w, hw, rfl⟩
      have h1 := hS.conj_eq_of_conj_eq hxZ hx3 hd hd1 h hw
      calc w⁻¹ * x⁻¹ * w * x = w⁻¹ * x⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
        _ = 1 := by group
    have h4 := hS.card
    rw [← hxc, hbot, card_bot] at h4
    norm_num at h4
  have hc₂ : x * c * x⁻¹ ∈ Z := (mem_normalizer_iff.mp hxZ c).mp hc
  have hc₃ : x⁻¹ * c * x⁻¹⁻¹ ∈ Z := (mem_normalizer_iff.mp (inv_mem hxZ) c).mp hc
  have h12 : c ≠ x * c * x⁻¹ := fun h => hmove c hc hc1 h.symm
  have h13 : c ≠ x⁻¹ * c * x⁻¹⁻¹ := by
    intro h
    apply hmove c hc hc1
    calc x * c * x⁻¹ = x * (x⁻¹ * c * x⁻¹⁻¹) * x⁻¹ := by rw [← h]
      _ = c := by group
  have h23 : x * c * x⁻¹ ≠ x⁻¹ * c * x⁻¹⁻¹ := by
    intro h
    apply h13
    have hx2 : x * x = x⁻¹ := by
      calc x * x = x ^ 3 * x⁻¹ := by rw [pow_three]; group
        _ = x⁻¹ := by rw [hx3, one_mul]
    calc c = x * (x⁻¹ * c * x⁻¹⁻¹) * x⁻¹ := by group
      _ = x * (x * c * x⁻¹) * x⁻¹ := by rw [← h]
      _ = (x * x) * c * (x * x)⁻¹ := by group
      _ = x⁻¹ * c * x⁻¹⁻¹ := by rw [hx2]
  have hs₁ : s ∈ hS.perp c S := ⟨hs, fun t ht => hsc t ht.2⟩
  have hs₂ := hS.conj_mem_perp hxS hs₁
  have hs₃ := hS.conj_mem_perp (inv_mem hxS) hs₁
  have hnZ : ∀ y ∈ normalizer (Z : Set G), y * s * y⁻¹ ∉ Z := by
    intro y hy h
    apply hsZ
    have := (mem_normalizer_iff.mp (inv_mem hy) _).mp h
    simpa [mul_assoc] using this
  have k₁ := C.card_img_perp hS hHS hc hs₁ hsZ
  have k₂ := C.card_img_perp hS hHS hc₂ hs₂ (hnZ x hxZ)
  have k₃ := C.card_img_perp hS hHS hc₃ hs₃ (hnZ x⁻¹ (inv_mem hxZ))
  have habel : ∀ u ∈ hS.perp c S, ∀ u' ∈ hS.perp c S, u * u' * u⁻¹ * u'⁻¹ = 1 := by
    intro u hu u' hu'
    obtain ⟨z, hz, w, hw, v, hv, rfl⟩ := C.exists_mul_mul hS hc₃ hc₂ h23.symm k₃ k₂ hu.1
    have hzS := hS.le hz
    have e1 := hS.comm_mul_left hzS (S.mul_mem hw.1 hv.1) hu'.1
    have e2 := hS.comm_mul_left hw.1 hv.1 hu'.1
    have hz1 : z * u' * z⁻¹ * u'⁻¹ = 1 := by
      rw [hS.comm_Z hz hu'.1]
      group
    have hv1 : v * u' * v⁻¹ * u'⁻¹ = 1 := by
      have a1 := hv.2 u' ⟨hu'.1, hu'.1⟩
      have a2 : v * u' * v⁻¹ * u'⁻¹ ∈ zpowers c := by
        have := inv_mem (hu'.2 v ⟨hv.1, hv.1⟩)
        rwa [Special.comm_inv] at this
      exact hS.inf_zpowers hc₂ hc h12.symm a1 a2
    have hmem : z * (w * v) * u' * (z * (w * v))⁻¹ * u'⁻¹ ∈ zpowers (x⁻¹ * c * x⁻¹⁻¹) := by
      rw [e1, hz1, one_mul, e2, hv1, mul_one]
      exact hw.2 u' ⟨hu'.1, hu'.1⟩
    exact hS.inf_zpowers hc₃ hc h13.symm hmem (hu.2 u' ⟨hu'.1, hu'.1⟩)
  apply hsZ
  rw [← hS.center]
  refine ⟨hs, mem_centralizer_iff.mpr fun t ht => ?_⟩
  obtain ⟨z, hz, a, ha, b, hb, rfl⟩ := C.exists_mul_mul hS hc hc₂ h12 k₁ k₂ ht
  have hzS := hS.le hz
  have e1 := hS.comm_mul_right hs hzS (S.mul_mem ha.1 hb.1)
  have e2 := hS.comm_mul_right hs ha.1 hb.1
  have hz1 : s * z * s⁻¹ * z⁻¹ = 1 := by
    rw [← hS.comm_Z hz hs]
    group
  have hb1 : s * b * s⁻¹ * b⁻¹ = 1 := by
    have a1 := hsc b hb.1
    have a2 : s * b * s⁻¹ * b⁻¹ ∈ zpowers (x * c * x⁻¹) := by
      have := inv_mem (hb.2 s ⟨hs, hs⟩)
      rwa [Special.comm_inv] at this
    exact hS.inf_zpowers hc hc₂ h12 a1 a2
  have hcomm : s * (z * (a * b)) * s⁻¹ * (z * (a * b))⁻¹ = 1 := by
    rw [e1, hz1, one_mul, e2, habel s hs₁ a ha, hb1, mul_one]
  calc z * (a * b) * s = (s * (z * (a * b)) * s⁻¹ * (z * (a * b))⁻¹)⁻¹ * s * (z * (a * b)) := by
        group
    _ = s * (z * (a * b)) := by rw [hcomm, inv_one, one_mul]

include C in
theorem card_perp_mul [Finite G] {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hnd : ∀ s ∈ S, (∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c) → s ∈ Z)
    {U : Subgroup G} (hU : U ≤ S) :
    Nat.card (hS.perp c U) * Nat.card (C.img hS U) = Nat.card S := by
  have hl : ∀ b : ↥(C.ΨU hS hU).range, ∃ u : ↥U, C.ΨU hS hU u = b := fun b =>
    MonoidHom.mem_range.mp b.2
  choose l hl using hl
  have hl' : ∀ b, Multiplicative.ofAdd (C.Ψ (l b)) = (b : Multiplicative Pair) := hl
  have hlU : ∀ b, (l b : G) ∈ U := fun b => (l b).2
  have hlS : ∀ b, (l b : G) ∈ S := fun b => hU (l b).2
  let β : ↥S → ↥(C.ΨU hS hU).range → Multiplicative (ZMod 2) := fun a b =>
    Multiplicative.ofAdd (Special.ell c ((a : G) * l b * (a : G)⁻¹ * (l b : G)⁻¹))
  have hβ1 : ∀ a₁ a₂ b, β (a₁ * a₂) b = β a₁ b * β a₂ b := by
    intro a₁ a₂ b
    show Multiplicative.ofAdd (Special.ell c ((a₁ * a₂ : G) * l b * (a₁ * a₂ : G)⁻¹ *
      (l b : G)⁻¹)) = _
    rw [hS.comm_mul_left a₁.2 a₂.2 (hlS b), hS.ell_mul hc hc1 (hS.comm_mem a₁.2 (hlS b))
      (hS.comm_mem a₂.2 (hlS b))]
    rfl
  have hlmul : ∀ b₁ b₂, ∃ z ∈ Z, (l (b₁ * b₂) : G) = z * ((l b₁ : G) * l b₂) := by
    intro b₁ b₂
    have h1 : C.Ψ (l (b₁ * b₂)) = C.Ψ ((l b₁ : G) * l b₂) := by
      have e := hl' (b₁ * b₂)
      rw [C.Ψ_mul hS (hlS b₁) (hlS b₂)]
      apply Multiplicative.ofAdd.injective
      rw [e, ofAdd_add, hl', hl']
      rfl
    have hz := (C.Ψ_eq_iff hS (hlS _) (S.mul_mem (hlS b₁) (hlS b₂))).mp h1
    exact ⟨_, hz, by group⟩
  have hβ2 : ∀ a b₁ b₂, β a (b₁ * b₂) = β a b₁ * β a b₂ := by
    intro a b₁ b₂
    obtain ⟨z, hz, hzl⟩ := hlmul b₁ b₂
    show Multiplicative.ofAdd (Special.ell c ((a : G) * l (b₁ * b₂) * (a : G)⁻¹ *
      (l (b₁ * b₂) : G)⁻¹)) = _
    rw [hzl, hS.comm_mul_right a.2 (hS.le hz) (S.mul_mem (hlS b₁) (hlS b₂)),
      hS.comm_mul_right a.2 (hlS b₁) (hlS b₂)]
    have hz1 : (a : G) * z * (a : G)⁻¹ * z⁻¹ = 1 := by
      rw [← hS.comm_Z hz a.2]
      group
    rw [hz1, one_mul, hS.ell_mul hc hc1 (hS.comm_mem a.2 (hlS b₁)) (hS.comm_mem a.2 (hlS b₂))]
    rfl
  have hB : ∀ b : ↥(C.ΨU hS hU).range, b ^ 2 = 1 := by
    intro b
    apply Subtype.ext
    show Multiplicative.toAdd ((b : Multiplicative Pair) ^ 2) = Multiplicative.toAdd 1
    rw [toAdd_pow, toAdd_one, two_nsmul, pair_add_self]
  have hC : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have key := CFSG.Quasithin.card_mul_card_radical_eq hB hC β hβ1 hβ2
  have hβ0 : ∀ a b, β a b = 1 ↔ (a : G) * l b * (a : G)⁻¹ * (l b : G)⁻¹ ∈ zpowers c := by
    intro a b
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0 ↔ _
    rw [Equiv.apply_eq_iff_eq, Special.ell_eq_zero_iff]
  have hl1 : (l 1 : G) ∈ Z := by
    have h1 : Multiplicative.ofAdd (C.Ψ (l 1)) = Multiplicative.ofAdd 0 := hl' 1
    exact (C.Ψ_eq_zero_iff hS (hlS 1)).mp (Multiplicative.ofAdd.injective h1)
  have hradB : Nat.card {b : ↥(C.ΨU hS hU).range // ∀ a, β a b = 1} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun a => (hβ0 a 1).mpr ?_⟩, fun b => Subtype.ext (Subtype.ext ?_)⟩
    · rw [← hS.comm_Z hl1 a.2]
      simp
    · have hZb : (l b.1 : G) ∈ Z := by
        apply hnd _ (hlS b.1)
        intro t ht
        have := inv_mem ((hβ0 ⟨t, ht⟩ b.1).mp (b.2 ⟨t, ht⟩))
        rwa [Special.comm_inv] at this
      rw [← hl' b.1, (C.Ψ_eq_zero_iff hS (hlS b.1)).mpr hZb]
      rfl
  have hradA : Nat.card {a : ↥S // ∀ b, β a b = 1} = Nat.card (hS.perp c U) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, a.1.2, fun t ht => ?_⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => (hβ0 _ b).mpr (a.2.2 _ ⟨hlU b, hlS b⟩)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
    let bt : ↥(C.ΨU hS hU).range := ⟨C.ΨU hS hU ⟨t, ht.1⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
    have hb := (hβ0 a.1 bt).mp (a.2 bt)
    have h1 : Multiplicative.ofAdd (C.Ψ (l bt)) = Multiplicative.ofAdd (C.Ψ t) := hl' bt
    have hz := (C.Ψ_eq_iff hS (hlS bt) ht.2).mp (Multiplicative.ofAdd.injective h1)
    have hz' : t⁻¹ * (l bt : G) ∈ Z := by
      have e2 : t⁻¹ * (l bt : G) = t⁻¹ * ((l bt : G) * t⁻¹) * t := by group
      rw [e2, hS.conj_Z' hz ht.2]
      exact hz
    have e : (l bt : G) = t * (t⁻¹ * (l bt : G)) := by group
    rw [e, hS.comm_mul_Z a.1.2 ht.2 hz'] at hb
    exact hb
  rw [hradB, mul_one, hradA, C.card_range_ΨU hS hU] at key
  rw [key, mul_comm]

include C in
theorem card_le_of_isotropic [Finite G] {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hnd : ∀ s ∈ S, (∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c) → s ∈ Z)
    {U : Subgroup G} (hU : U ≤ S)
    (hiso : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ zpowers c) : Nat.card U ≤ 64 := by
  have hle : U ≤ hS.perp c U := fun u hu => ⟨hU hu, fun t ht => hiso u hu t ht.1⟩
  have h1 := C.card_perp_mul hS hc hc1 hnd hU
  have h2 := C.card_eq hS hU
  have h3 := Subgroup.card_le_of_le hle
  have h4 : Nat.card (U ⊓ Z : Subgroup G) ≤ 4 := hS.card ▸ Subgroup.card_le_of_le inf_le_right
  have h5 : Nat.card U ≤ 4 * Nat.card (C.img hS U) := by
    rw [h2]
    exact Nat.mul_le_mul_right _ h4
  have h6 := Nat.mul_le_mul h3 h5
  rw [C.card_S hS] at h1
  nlinarith

include C in
theorem Z_le_of_isotropic [Finite G] {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hnd : ∀ s ∈ S, (∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c) → s ∈ Z)
    {U : Subgroup G} (hU : U ≤ S)
    (hiso : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ zpowers c) (hcard : Nat.card U = 64) :
    Z ≤ U := by
  have hle : U ≤ hS.perp c U := fun u hu => ⟨hU hu, fun t ht => hiso u hu t ht.1⟩
  have h1 := C.card_perp_mul hS hc hc1 hnd hU
  have h2 := C.card_eq hS hU
  have h3 := Subgroup.card_le_of_le hle
  have h4 : Nat.card (U ⊓ Z : Subgroup G) ≤ 4 := hS.card ▸ Subgroup.card_le_of_le inf_le_right
  rw [C.card_S hS] at h1
  rw [hcard] at h2 h3
  have h5 : Nat.card (C.img hS U) ≤ 16 := by nlinarith
  have h6 : Nat.card (U ⊓ Z : Subgroup G) = 4 := by nlinarith
  have h7 : U ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h6, hS.card])
  exact h7 ▸ inf_le_left

include C in
theorem perp_eq_of_isotropic [Finite G] {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1)
    (hnd : ∀ s ∈ S, (∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ zpowers c) → s ∈ Z)
    {U : Subgroup G} (hZU : Z ≤ U) (hU : U ≤ S)
    (hiso : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ zpowers c) (hcard : Nat.card U = 64) :
    hS.perp c U = U := by
  have hle : U ≤ hS.perp c U := fun u hu => ⟨hU hu, fun t ht => hiso u hu t ht.1⟩
  have h1 := C.card_perp_mul hS hc hc1 hnd hU
  have h2 := C.card_eq_four_mul hS hZU hU
  have hS1 := C.card_S hS
  have himg : Nat.card (C.img hS U) = 16 := by omega
  have h3 : Nat.card (hS.perp c U) = 64 := by
    rw [himg, hS1] at h1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h3, hcard])).symm

end Coord

end Sec2

end CFSG.ComponentClassification.AS81
