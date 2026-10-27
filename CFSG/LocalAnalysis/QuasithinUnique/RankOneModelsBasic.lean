module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique

open Subgroup

variable {G : Type*} [Group G] {F : Type*} [Field F]

@[expose] def scalarActing (φ : Multiplicative F →* G) : Subgroup G where
  carrier := {n | ∃ c : Fˣ, ∀ x : F,
    n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x))}
  one_mem' := ⟨1, fun x => by simp⟩
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun x => ?_⟩
    calc a * b * φ (Multiplicative.ofAdd x) * (a * b)⁻¹
        = a * (b * φ (Multiplicative.ofAdd x) * b⁻¹) * a⁻¹ := by group
      _ = a * φ (Multiplicative.ofAdd ((d : F) * x)) * a⁻¹ := by rw [hd]
      _ = φ (Multiplicative.ofAdd ((c : F) * ((d : F) * x))) := hc _
      _ = φ (Multiplicative.ofAdd (((c * d : Fˣ) : F) * x)) := by rw [Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro a ⟨c, hc⟩
    refine ⟨c⁻¹, fun x => ?_⟩
    have h := hc (((c⁻¹ : Fˣ) : F) * x)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    calc a⁻¹ * φ (Multiplicative.ofAdd x) * a⁻¹⁻¹
        = a⁻¹ * (a * φ (Multiplicative.ofAdd (((c⁻¹ : Fˣ) : F) * x)) * a⁻¹) * a⁻¹⁻¹ := by
          rw [h]
      _ = φ (Multiplicative.ofAdd (((c⁻¹ : Fˣ) : F) * x)) := by group

theorem mem_scalarActing_iff (φ : Multiplicative F →* G) (n : G) :
    n ∈ scalarActing φ ↔ ∃ c : Fˣ, ∀ x : F,
      n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x)) := Iff.rfl

theorem scalarActing_le_normalizer (φ : Multiplicative F →* G) :
    scalarActing φ ≤ normalizer (φ.range : Set G) := by
  have key : ∀ n ∈ scalarActing φ, ∀ h ∈ φ.range, n * h * n⁻¹ ∈ φ.range := by
    rintro n ⟨c, hc⟩ _ ⟨x, rfl⟩
    exact ⟨Multiplicative.ofAdd ((c : F) * Multiplicative.toAdd x), by
      rw [← hc]; rfl⟩
  intro n hn
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key n hn h hh, fun hh => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hh
  simpa [mul_assoc] using this

@[expose] def scalarMulAut (c : Fˣ) : MulAut (Multiplicative F) where
  toFun x := Multiplicative.ofAdd ((c : F) * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd (((c⁻¹ : Fˣ) : F) * Multiplicative.toAdd x)
  left_inv x := by
    simp only [toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      ofAdd_toAdd]
  right_inv x := by
    simp only [toAdd_ofAdd, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      ofAdd_toAdd]
  map_mul' x y := by
    simp only [toAdd_mul, mul_add, ofAdd_add]

@[simp] theorem scalarMulAut_apply (c : Fˣ) (x : Multiplicative F) :
    scalarMulAut c x = Multiplicative.ofAdd ((c : F) * Multiplicative.toAdd x) := rfl

@[expose] def scalarMulAutHom (F : Type*) [Field F] : Fˣ →* MulAut (Multiplicative F) where
  toFun := scalarMulAut
  map_one' := by
    ext x
    simp
  map_mul' c d := by
    ext x
    simp [mul_assoc]

@[expose] noncomputable def scalarAutHom (φ : Multiplicative F →* G) (hinj : Function.Injective φ) :
    Fˣ →* MulAut φ.range :=
  (MulAut.congr (MonoidHom.ofInjective hinj)).toMonoidHom.comp (scalarMulAutHom F)

theorem scalarAutHom_apply (φ : Multiplicative F →* G) (hinj : Function.Injective φ) (c : Fˣ)
    (v : φ.range) :
    scalarAutHom φ hinj c v = MonoidHom.ofInjective hinj
      (scalarMulAut c ((MonoidHom.ofInjective hinj).symm v)) := rfl

theorem scalarAutHom_apply_ofInjective (φ : Multiplicative F →* G) (hinj : Function.Injective φ)
    (c : Fˣ) (x : F) :
    ((scalarAutHom φ hinj c (MonoidHom.ofInjective hinj (Multiplicative.ofAdd x)) : φ.range) : G) =
      φ (Multiplicative.ofAdd ((c : F) * x)) := by
  rw [scalarAutHom_apply, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply, scalarMulAut_apply,
    toAdd_ofAdd]

theorem scalarAutHom_injective (φ : Multiplicative F →* G)
    (hinj : Function.Injective φ) : Function.Injective (scalarAutHom φ hinj) := by
  intro c d h
  have h1 := congrArg (fun α : MulAut φ.range =>
    ((α (MonoidHom.ofInjective hinj (Multiplicative.ofAdd 1)) : φ.range) : G)) h
  simp only [scalarAutHom_apply_ofInjective, mul_one] at h1
  exact Units.ext (Multiplicative.ofAdd.injective (hinj h1))

theorem exists_eq_ofInjective (φ : Multiplicative F →* G) (hinj : Function.Injective φ)
    (v : φ.range) : ∃ x : F, v = MonoidHom.ofInjective hinj (Multiplicative.ofAdd x) :=
  ⟨Multiplicative.toAdd ((MonoidHom.ofInjective hinj).symm v), by simp⟩

theorem range_scalarAutHom_eq (φ : Multiplicative F →* G) (hinj : Function.Injective φ)
    (hsc1 : ∀ c : Fˣ, ∃ n ∈ normalizer (φ.range : Set G), ∀ x : F,
      n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x)))
    (hsc2 : normalizer (φ.range : Set G) ≤ scalarActing φ) :
    (scalarAutHom φ hinj).range = φ.range.normalizerMonoidHom.range := by
  ext α
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨n, hn, hnc⟩ := hsc1 c
    refine ⟨⟨n, hn⟩, ?_⟩
    ext v
    obtain ⟨x, rfl⟩ := exists_eq_ofInjective φ hinj v
    rw [scalarAutHom_apply_ofInjective, ← hnc]
    rfl
  · rintro ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨c, hc⟩ := hsc2 hn
    refine ⟨c, ?_⟩
    ext v
    obtain ⟨x, rfl⟩ := exists_eq_ofInjective φ hinj v
    rw [scalarAutHom_apply_ofInjective, ← hc]
    rfl

theorem normalizer_action_of_scalar [Finite F] (φ : Multiplicative F →* G)
    (hinj : Function.Injective φ)
    (hsc1 : ∀ c : Fˣ, ∃ n ∈ normalizer (φ.range : Set G), ∀ x : F,
      n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x)))
    (hsc2 : normalizer (φ.range : Set G) ≤ scalarActing φ) :
    Nat.card φ.range = Nat.card F ∧ IsCyclic φ.range.normalizerMonoidHom.range ∧
      Nat.card φ.range.normalizerMonoidHom.range = Nat.card F - 1 ∧
      ∀ v w : φ.range, v ≠ 1 → w ≠ 1 →
        ∃! α : φ.range.normalizerMonoidHom.range, (α : MulAut φ.range) v = w := by
  have hrange := range_scalarAutHom_eq φ hinj hsc1 hsc2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm).trans
      (Nat.card_congr Multiplicative.toAdd)
  · rw [← hrange]
    exact isCyclic_of_surjective (scalarAutHom φ hinj).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  · rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective (scalarAutHom_injective φ hinj)).toEquiv.symm).trans
      (Nat.card_units F)
  · intro v w hv hw
    obtain ⟨x, rfl⟩ := exists_eq_ofInjective φ hinj v
    obtain ⟨y, rfl⟩ := exists_eq_ofInjective φ hinj w
    have hx : x ≠ 0 := fun h => hv (by rw [h, ofAdd_zero, map_one])
    have hy : y ≠ 0 := fun h => hw (by rw [h, ofAdd_zero, map_one])
    let c : Fˣ := Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx))
    have hcx : (c : F) * x = y := by
      change y * x⁻¹ * x = y
      rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]
    have hmem : scalarAutHom φ hinj c ∈ φ.range.normalizerMonoidHom.range := hrange ▸ ⟨c, rfl⟩
    refine ⟨⟨scalarAutHom φ hinj c, hmem⟩, ?_, ?_⟩
    · apply Subtype.ext
      change ((scalarAutHom φ hinj c (MonoidHom.ofInjective hinj (Multiplicative.ofAdd x)) :
        φ.range) : G) = _
      rw [scalarAutHom_apply_ofInjective, hcx, MonoidHom.ofInjective_apply]
    · rintro ⟨β, hβ⟩ hβy
      have hβ' : β ∈ (scalarAutHom φ hinj).range := hrange ▸ hβ
      obtain ⟨d, rfl⟩ := hβ'
      have h1 := congrArg Subtype.val hβy
      change ((scalarAutHom φ hinj d (MonoidHom.ofInjective hinj (Multiplicative.ofAdd x)) :
        φ.range) : G) = _ at h1
      rw [scalarAutHom_apply_ofInjective, MonoidHom.ofInjective_apply] at h1
      have h2 : (d : F) * x = y := Multiplicative.ofAdd.injective (hinj h1)
      have hdc : d = c := Units.ext (mul_right_cancel₀ hx (h2.trans hcx.symm))
      exact Subtype.ext (congrArg (scalarAutHom φ hinj) hdc)


def HasFieldScalarStructure (V : Subgroup G) (q : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : Multiplicative F →* G),
    CharP F 2 ∧ Nat.card F = q ∧ Function.Injective φ ∧ φ.range = V ∧
    (∀ c : Fˣ, ∃ n ∈ normalizer (V : Set G), ∀ x : F,
      n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x))) ∧
    (∀ n ∈ normalizer (V : Set G), ∃ c : Fˣ, ∀ x : F,
      n * φ (Multiplicative.ofAdd x) * n⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x)))

namespace HasFieldScalarStructure

variable {V : Subgroup G} {q : ℕ}

theorem mul_comm (h : HasFieldScalarStructure V q) : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  obtain ⟨F, _, _, φ, -, -, -, rfl, -, -⟩ := h
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, _root_.mul_comm a b]

theorem sq_eq_one (h : HasFieldScalarStructure V q) : ∀ x ∈ V, x ^ 2 = 1 := by
  obtain ⟨F, _, _, φ, hchar, -, -, rfl, -, -⟩ := h
  rintro _ ⟨a, rfl⟩
  rw [← map_pow, pow_two, ← ofAdd_toAdd a, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero,
    map_one]

theorem card_eq (h : HasFieldScalarStructure V q) : Nat.card V = q := by
  obtain ⟨F, _, _, φ, -, hcard, hinj, rfl, -, -⟩ := h
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm).trans
    ((Nat.card_congr Multiplicative.toAdd).trans hcard)

theorem normalizer_action (h : HasFieldScalarStructure V q) :
    IsCyclic V.normalizerMonoidHom.range ∧ Nat.card V.normalizerMonoidHom.range = q - 1 ∧
      ∀ v w : V, v ≠ 1 → w ≠ 1 →
        ∃! α : V.normalizerMonoidHom.range, (α : MulAut V) v = w := by
  obtain ⟨F, _, _, φ, -, hcard, hinj, rfl, hsc1, hsc2⟩ := h
  obtain ⟨-, h2, h3, h4⟩ := normalizer_action_of_scalar φ hinj hsc1 (fun n hn => hsc2 n hn)
  exact ⟨h2, h3.trans (by rw [hcard]), h4⟩

theorem ne_bot (h : HasFieldScalarStructure V q) (hq : 2 ≤ q) : V ≠ ⊥ := by
  intro hV
  have h1 := h.card_eq
  rw [hV, Subgroup.card_bot] at h1
  omega

theorem exists_normalizer_conj (h : HasFieldScalarStructure V q) {v w : V} (hv : v ≠ 1)
    (hw : w ≠ 1) : ∃ n ∈ normalizer (V : Set G), n * (v : G) * n⁻¹ = (w : G) := by
  obtain ⟨α, hα, -⟩ := h.normalizer_action.2.2 v w hv hw
  obtain ⟨⟨n, hn⟩, hnα⟩ := α.2
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun β : MulAut V => ((β v : V) : G)) hnα
  simpa [hα] using this

theorem map {H : Type*} [Group H] (h : HasFieldScalarStructure V q) (e : G ≃* H) :
    HasFieldScalarStructure (V.map e.toMonoidHom) q := by
  obtain ⟨F, _, _, φ, hchar, hcard, hinj, rfl, hsc1, hsc2⟩ := h
  have hnorm : ∀ n' : H, n' ∈ normalizer ((φ.range.map e.toMonoidHom : Subgroup H) : Set H) ↔
      e.symm n' ∈ normalizer (φ.range : Set G) := fun n' => by
    rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv]
  refine ⟨F, inferInstance, inferInstance, e.toMonoidHom.comp φ, hchar, hcard,
    e.injective.comp hinj, (MonoidHom.range_comp _ _), ?_, ?_⟩
  · intro c
    obtain ⟨n, hn, hnc⟩ := hsc1 c
    refine ⟨e n, (hnorm _).2 (by rwa [MulEquiv.symm_apply_apply]), fun x => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hnc]
  · intro n' hn'
    obtain ⟨c, hc⟩ := hsc2 _ ((hnorm n').1 hn')
    refine ⟨c, fun x => ?_⟩
    have h1 := congrArg e (hc x)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
    exact h1

theorem exists_normalizer_conj_inv (h : HasFieldScalarStructure V q) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ n ∈ normalizer (V : Set G), n⁻¹ * a * n = b := by
  obtain ⟨n, hn, hnb⟩ := h.exists_normalizer_conj (v := ⟨b, hb⟩) (w := ⟨a, ha⟩)
    (fun h1 => hb1 (congrArg Subtype.val h1)) (fun h1 => ha1 (congrArg Subtype.val h1))
  refine ⟨n, hn, ?_⟩
  have : n * b * n⁻¹ = a := hnb
  rw [← this]
  group

theorem centralizes_of_fixed (h : HasFieldScalarStructure V q) {n : G}
    (hn : n ∈ normalizer (V : Set G)) {a : G} (ha : a ∈ V) (ha1 : a ≠ 1) (hna : n⁻¹ * a * n = a) :
    ∀ x ∈ V, n⁻¹ * x * n = x := by
  obtain ⟨F, _, _, φ, -, -, hinj, rfl, -, hsc2⟩ := h
  obtain ⟨c, hc⟩ := hsc2 n⁻¹ (inv_mem hn)
  obtain ⟨y, rfl⟩ := ha
  have hy : Multiplicative.toAdd y ≠ 0 := fun h0 => ha1 (by
    rw [show y = 1 from Multiplicative.toAdd.injective h0, map_one])
  have h1 := hc (Multiplicative.toAdd y)
  rw [inv_inv, ofAdd_toAdd] at h1
  have hcy : (c : F) * Multiplicative.toAdd y = Multiplicative.toAdd y := by
    have := hinj (h1.symm.trans (show n⁻¹ * φ y * n = φ y from hna))
    simpa using congrArg Multiplicative.toAdd this
  have hc1 : (c : F) = 1 := by
    have : ((c : F) - 1) * Multiplicative.toAdd y = 0 := by rw [sub_mul, hcy, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hy)
  rintro _ ⟨z, rfl⟩
  have := hc (Multiplicative.toAdd z)
  rw [inv_inv, ofAdd_toAdd, hc1, one_mul, ofAdd_toAdd] at this
  exact this

theorem exists_generator (h : HasFieldScalarStructure V q) :
    ∃ g ∈ normalizer (V : Set G), ∀ n ∈ normalizer (V : Set G), ∃ k : ℕ, ∀ x ∈ V,
      n⁻¹ * x * n = (g ^ k)⁻¹ * x * g ^ k := by
  obtain ⟨F, _, _, φ, -, -, hinj, rfl, hsc1, hsc2⟩ := h
  obtain ⟨c₀, hc₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n₀, hn₀, hn₀c⟩ := hsc1 c₀
  have hpow : ∀ k : ℕ, ∀ x : F, n₀ ^ k * φ (Multiplicative.ofAdd x) * (n₀ ^ k)⁻¹ =
      φ (Multiplicative.ofAdd (((c₀ ^ k : Fˣ) : F) * x)) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      calc n₀ ^ (k + 1) * φ (Multiplicative.ofAdd x) * (n₀ ^ (k + 1))⁻¹
          = n₀ * (n₀ ^ k * φ (Multiplicative.ofAdd x) * (n₀ ^ k)⁻¹) * n₀⁻¹ := by group
        _ = n₀ * φ (Multiplicative.ofAdd (((c₀ ^ k : Fˣ) : F) * x)) * n₀⁻¹ := by rw [ih]
        _ = φ (Multiplicative.ofAdd ((c₀ : F) * (((c₀ ^ k : Fˣ) : F) * x))) := hn₀c _
        _ = φ (Multiplicative.ofAdd (((c₀ ^ (k + 1) : Fˣ) : F) * x)) := by
          rw [pow_succ', Units.val_mul, mul_assoc]
  refine ⟨n₀⁻¹, inv_mem hn₀, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := hsc2 n⁻¹ (inv_mem hn)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, c₀ ^ k = c :=
    mem_powers_iff_mem_zpowers.2 (hc₀ c)
  refine ⟨k, ?_⟩
  rintro _ ⟨z, rfl⟩
  have h1 := hc (Multiplicative.toAdd z)
  have h2 := hpow k (Multiplicative.toAdd z)
  simp only [inv_inv, ofAdd_toAdd] at h1 h2
  rw [inv_pow, inv_inv, h1, ← hk, ← h2]

end HasFieldScalarStructure


theorem normalizer_le_stabilizer_of_semiregular {Ω : Type*} [MulAction G Ω] (α : Ω)
    {P V : Subgroup G} (hVP : V ≤ P) (hPα : P ≤ MulAction.stabilizer G α)
    (hsemi : ∀ (ω : Ω) (u : G), u ∈ P → ω ≠ α → u • ω = ω → u = 1) (hV : V ≠ ⊥) :
    normalizer (V : Set G) ≤ MulAction.stabilizer G α := by
  intro g hg
  by_contra hgα
  have hω : g • α ≠ α := hgα
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
  have hconj : g⁻¹ * (v : G) * g ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * (v : G) * g)).2 (by
      rw [show g * (g⁻¹ * (v : G) * g) * g⁻¹ = v by group]
      exact v.2)
  have hfix : (g⁻¹ * (v : G) * g) • α = α := MulAction.mem_stabilizer_iff.1 (hPα (hVP hconj))
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at hfix
  exact hv1 (Subtype.ext (hsemi (g • α) v (hVP v.2) hω hfix))

theorem stabilizer_le_normalizer_of_characteristic {Ω : Type*} [MulAction G Ω] (α : Ω)
    {P V : Subgroup G} (hVP : V ≤ P) (hPα : P ≤ MulAction.stabilizer G α)
    (hPn : (P.subgroupOf (MulAction.stabilizer G α)).Normal)
    [hVc : (V.subgroupOf P).Characteristic] :
    MulAction.stabilizer G α ≤ normalizer (V : Set G) := by
  intro g hg
  have hconj : ∀ s ∈ MulAction.stabilizer G α, ∀ x ∈ P, s * x * s⁻¹ ∈ P :=
    fun s hs x hx => (Subgroup.normal_subgroupOf_iff hPα).1 hPn x s hx hs
  have key : ∀ s ∈ MulAction.stabilizer G α, ∀ v ∈ V, s * v * s⁻¹ ∈ V := by
    intro s hs v hv
    let e : P ≃* P :=
      { toFun := fun x => ⟨s * x * s⁻¹, hconj s hs x x.2⟩
        invFun := fun x => ⟨s⁻¹ * x * s⁻¹⁻¹, hconj s⁻¹ (inv_mem hs) x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    have h := (Subgroup.Characteristic.fixed hVc e).ge
      (Subgroup.mem_subgroupOf.2 hv : (⟨v, hVP hv⟩ : P) ∈ V.subgroupOf P)
    exact Subgroup.mem_subgroupOf.1 h
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem normalizer_eq_stabilizer_of_regular_root {Ω : Type*} [MulAction G Ω] (α : Ω)
    {P V : Subgroup G} (hVP : V ≤ P) (hPα : P ≤ MulAction.stabilizer G α)
    (hPn : (P.subgroupOf (MulAction.stabilizer G α)).Normal)
    (hreg : ∀ x y : Ω, x ≠ α → y ≠ α → ∃! u : P, (u : G) • x = y)
    [(V.subgroupOf P).Characteristic] (hV : V ≠ ⊥) :
    normalizer (V : Set G) = MulAction.stabilizer G α := by
  refine le_antisymm (normalizer_le_stabilizer_of_semiregular α hVP hPα ?_ hV)
    (stabilizer_le_normalizer_of_characteristic α hVP hPα hPn)
  intro ω u hu hω hfix
  have h1 := (hreg ω ω hω hω).unique (y₁ := ⟨u, hu⟩) (y₂ := 1) hfix (one_smul _ _)
  exact congrArg Subtype.val h1

theorem hasFieldScalarStructure_of_regular_root {Ω : Type*} [MulAction G Ω] (α : Ω)
    (P T : Subgroup G) (F : Type) [Field F] [Finite F] [CharP F 2] (φ : Multiplicative F →* G)
    (hinj : Function.Injective φ) (hVP : φ.range ≤ P) (hPα : P ≤ MulAction.stabilizer G α)
    (hsemi : ∀ (ω : Ω) (u : G), u ∈ P → ω ≠ α → u • ω = ω → u = 1)
    (hBα : MulAction.stabilizer G α ≤ P ⊔ T)
    (hP : ∀ p ∈ P, ∀ x : F,
      p * φ (Multiplicative.ofAdd x) * p⁻¹ = φ (Multiplicative.ofAdd x))
    (hT : ∀ t ∈ T, ∃ c : Fˣ, ∀ x : F,
      t * φ (Multiplicative.ofAdd x) * t⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x)))
    (hTs : ∀ c : Fˣ, ∃ t ∈ T, ∀ x : F,
      t * φ (Multiplicative.ofAdd x) * t⁻¹ = φ (Multiplicative.ofAdd ((c : F) * x))) :
    HasFieldScalarStructure φ.range (Nat.card F) := by
  have hPs : P ≤ scalarActing φ := fun p hp => ⟨1, fun x => by simpa using hP p hp x⟩
  have hTsc : T ≤ scalarActing φ := hT
  have hV : φ.range ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨φ (Multiplicative.ofAdd 1), Multiplicative.ofAdd 1, rfl⟩, fun h => ?_⟩
    have h1 : φ (Multiplicative.ofAdd 1) = 1 := congrArg Subtype.val h
    rw [← map_one φ] at h1
    exact one_ne_zero (Multiplicative.ofAdd.injective (hinj h1))
  have hN : normalizer (φ.range : Set G) ≤ scalarActing φ :=
    (normalizer_le_stabilizer_of_semiregular α hVP hPα hsemi hV).trans
      (hBα.trans (sup_le hPs hTsc))
  refine ⟨F, inferInstance, inferInstance, φ, inferInstance, rfl, hinj, rfl, fun c => ?_,
    fun n hn => hN hn⟩
  obtain ⟨t, ht, htc⟩ := hTs c
  exact ⟨t, scalarActing_le_normalizer φ (hTsc ht), htc⟩

end CFSG.QuasithinUnique
