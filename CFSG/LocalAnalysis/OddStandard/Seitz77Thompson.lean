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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

variable {Γ : Type*} [Group Γ]

@[expose] def fixSubgroup (σ : MulAut Γ) : Subgroup Γ where
  carrier := {g | σ g = g}
  mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) => by
    show σ (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := by
    show σ 1 = 1
    exact map_one σ
  inv_mem' := fun {a} (ha : σ a = a) => by
    show σ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSubgroup {σ : MulAut Γ} {g : Γ} : g ∈ fixSubgroup σ ↔ σ g = g := Iff.rfl

structure FreeLayer (σ : MulAut Γ) (N T : Subgroup Γ) : Prop where
  le : N ≤ T
  normal : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N
  invT : ∀ g ∈ T, σ g ∈ T
  invN : ∀ n ∈ N, σ n ∈ N
  comm : ∀ g ∈ T, ∀ h ∈ T, g * h * g⁻¹ * h⁻¹ ∈ N
  sq : ∀ g ∈ T, g * g ∈ N
  free : ∀ g ∈ T, g⁻¹ * σ g ∈ N → ∃ f ∈ T, g⁻¹ * (f * σ f) ∈ N

inductive FreeSeries (σ : MulAut Γ) : Subgroup Γ → Prop
  | bot : FreeSeries σ ⊥
  | step {N T : Subgroup Γ} : FreeLayer σ N T → FreeSeries σ N → FreeSeries σ T

variable {σ : MulAut Γ}

theorem FreeSeries.exists_cocycle (hσ : ∀ g, σ (σ g) = g) {T : Subgroup Γ}
    (h : FreeSeries σ T) : ∀ g ∈ T, g * σ g = 1 → ∃ f ∈ T, g = f⁻¹ * σ f := by
  induction h with
  | bot =>
    intro g hg _
    refine ⟨1, one_mem _, ?_⟩
    rw [mem_bot.mp hg]
    simp
  | @step N T hl _ ih =>
    intro g hg hgσ
    have hσg : σ g = g⁻¹ := eq_inv_of_mul_eq_one_right hgσ
    have h1 : g⁻¹ * σ g ∈ N := by
      rw [hσg, ← mul_inv_rev]
      exact inv_mem (hl.sq g hg)
    obtain ⟨f, hfT, hf⟩ := hl.free g hg h1
    have hσf : σ f ∈ T := hl.invT f hfT
    have hg' : f⁻¹ * g * σ f ∈ N := by
      set n₁ := g⁻¹ * (f * σ f) with hn₁
      have heq : f⁻¹ * g * σ f = (σ f * n₁⁻¹ * (σ f)⁻¹) * (σ f * σ f) := by
        rw [hn₁]
        group
      rw [heq]
      exact mul_mem (hl.normal _ hσf _ (inv_mem hf)) (hl.sq _ hσf)
    have hinv : (f⁻¹ * g * σ f) * σ (f⁻¹ * g * σ f) = 1 := by
      rw [map_mul, map_mul, map_inv, hσg, hσ f]
      group
    obtain ⟨m, hmN, hm⟩ := ih _ hg' hinv
    have hmT : m ∈ T := hl.le hmN
    refine ⟨m * f⁻¹, mul_mem hmT (inv_mem hfT), ?_⟩
    have hg2 : g = f * (f⁻¹ * g * σ f) * (σ f)⁻¹ := by group
    rw [hg2, hm]
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
    group

theorem card_fix_sq_of_free {Q : Type*} [Group Q] (hcomm : ∀ a b : Q, a * b = b * a)
    (ρ : Q →* Q) (hρ : ∀ q, ρ (ρ q) = q) (hsq : ∀ q : Q, q * q = 1)
    (hfree : ∀ q, ρ q = q → ∃ f, q = f * ρ f) :
    Nat.card {q : Q // ρ q = q} ^ 2 = Nat.card Q := by
  classical
  let φ : Q →* Q := MonoidHom.mk' (fun q => q * ρ q) (fun a b => by
    rw [map_mul]
    calc a * b * (ρ a * ρ b) = a * (b * ρ a) * ρ b := by group
      _ = a * (ρ a * b) * ρ b := by rw [hcomm b (ρ a)]
      _ = a * ρ a * (b * ρ b) := by group)
  have hker : ∀ q, q ∈ φ.ker ↔ ρ q = q := by
    intro q
    rw [MonoidHom.mem_ker]
    show q * ρ q = 1 ↔ ρ q = q
    have hqq : q⁻¹ = q := inv_eq_of_mul_eq_one_right (hsq q)
    constructor
    · intro h
      have := eq_inv_of_mul_eq_one_right h
      rwa [hqq] at this
    · intro h
      rw [h]
      exact hsq q
  have hrange : ∀ q, q ∈ φ.range ↔ ρ q = q := by
    intro q
    constructor
    · rintro ⟨f, rfl⟩
      show ρ (f * ρ f) = f * ρ f
      rw [map_mul, hρ, hcomm]
    · intro h
      obtain ⟨f, hf⟩ := hfree q h
      exact ⟨f, hf.symm⟩
  have hk : Nat.card φ.ker = Nat.card {q : Q // ρ q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hr : Nat.card φ.range = Nat.card {q : Q // ρ q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hk, hr] at h
  rw [sq]
  exact h


@[expose] def restrictAut {T : Subgroup Γ} (hT : ∀ g ∈ T, σ g ∈ T) : T →* T where
  toFun g := ⟨σ g, hT g g.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : Γ) (b : Γ))

theorem FreeSeries.card_fix_sq (hσ : ∀ g, σ (σ g) = g) {T : Subgroup Γ} (h : FreeSeries σ T) :
    Nat.card ↥(T ⊓ fixSubgroup σ) ^ 2 = Nat.card ↥T := by
  induction h with
  | bot => simp
  | @step N T hl hN ih =>
    have hB := hN.exists_cocycle hσ
    have hnorm : (N.subgroupOf T).Normal := ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      simpa using hl.normal g g.2 n hn⟩
    set N' : Subgroup T := N.subgroupOf T with hN'
    let σT : T →* T := restrictAut hl.invT
    have hσT : ∀ x : T, σT (σT x) = x := fun x => Subtype.ext (hσ (x : Γ))
    have hmap : N' ≤ N'.comap σT := fun n hn => by
      have hn' : (n : Γ) ∈ N := mem_subgroupOf.1 hn
      exact mem_subgroupOf.2 (hl.invN _ hn')
    let ρ : T ⧸ N' →* T ⧸ N' := QuotientGroup.map N' N' σT hmap
    have hρmk : ∀ x : T, ρ (x : T ⧸ N') = ((σT x : T) : T ⧸ N') := fun x =>
      QuotientGroup.map_mk N' N' σT hmap x
    have hρ : ∀ q, ρ (ρ q) = q := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g => rw [hρmk, hρmk, hσT]
    have hsq : ∀ q : T ⧸ N', q * q = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hN', mem_subgroupOf]
        exact hl.sq g g.2
    have hcomm : ∀ a b : T ⧸ N', a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with
      | H x =>
        induction b using QuotientGroup.induction_on with
        | H y =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN',
            mem_subgroupOf]
          have := hl.comm (y⁻¹ : Γ) (inv_mem y.2) (x⁻¹ : Γ) (inv_mem x.2)
          convert this using 1
          simp [mul_assoc]
    have hfree : ∀ q : T ⧸ N', ρ q = q → ∃ f, q = f * ρ f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        intro hg
        rw [hρmk, QuotientGroup.eq, hN', mem_subgroupOf] at hg
        have h0 : (σ (g : Γ))⁻¹ * (g : Γ) ∈ N := hg
        have h1 : (g : Γ)⁻¹ * σ g ∈ N := by
          have := inv_mem h0
          rwa [mul_inv_rev, inv_inv] at this
        obtain ⟨f, hfT, hf⟩ := hl.free g g.2 h1
        refine ⟨((⟨f, hfT⟩ : T) : T ⧸ N'), ?_⟩
        rw [hρmk, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN', mem_subgroupOf]
        simpa [σT, restrictAut] using hf
    have hQ := card_fix_sq_of_free hcomm ρ hρ hsq hfree
    let F : Subgroup Γ := T ⊓ fixSubgroup σ
    let incl : F →* T := Subgroup.inclusion inf_le_left
    let π : F →* T ⧸ N' := (QuotientGroup.mk' N').comp incl
    have hrange : ∀ q : T ⧸ N', q ∈ π.range ↔ ρ q = q := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        constructor
        · rintro ⟨f, hf⟩
          have hf' : ((incl f : T) : T ⧸ N') = (g : T ⧸ N') := hf
          rw [← hf', hρmk]
          congr 1
          exact Subtype.ext f.2.2
        · intro hg
          rw [hρmk, QuotientGroup.eq, hN', mem_subgroupOf] at hg
          have h0 : (σ (g : Γ))⁻¹ * (g : Γ) ∈ N := hg
          have hn : (g : Γ)⁻¹ * σ g ∈ N := by
            have := inv_mem h0
            rwa [mul_inv_rev, inv_inv] at this
          have hcoc : ((g : Γ)⁻¹ * σ g) * σ ((g : Γ)⁻¹ * σ g) = 1 := by
            rw [map_mul, map_inv, hσ g]
            group
          obtain ⟨m, hmN, hm⟩ := hB _ hn hcoc
          have hmT : m ∈ T := hl.le hmN
          have hfT : (g : Γ) * m⁻¹ ∈ T := mul_mem g.2 (inv_mem hmT)
          have hfix : σ ((g : Γ) * m⁻¹) = (g : Γ) * m⁻¹ := by
            have hσg : σ g = (g : Γ) * ((g : Γ)⁻¹ * σ g) := by group
            rw [map_mul, map_inv, hσg, hm]
            group
          refine ⟨⟨(g : Γ) * m⁻¹, ⟨hfT, hfix⟩⟩, ?_⟩
          show ((incl ⟨(g : Γ) * m⁻¹, ⟨hfT, hfix⟩⟩ : T) : T ⧸ N') = (g : T ⧸ N')
          rw [QuotientGroup.eq, hN', mem_subgroupOf]
          have hmm : ((g : Γ) * m⁻¹)⁻¹ * (g : Γ) = m := by group
          show ((g : Γ) * m⁻¹)⁻¹ * (g : Γ) ∈ N
          rw [hmm]
          exact hmN
    have hr : Nat.card π.range = Nat.card {q : T ⧸ N' // ρ q = q} :=
      Nat.card_congr (Equiv.subtypeEquivRight hrange)
    have hkermem : ∀ x : F, x ∈ π.ker ↔ (x : Γ) ∈ N := by
      intro x
      rw [MonoidHom.mem_ker]
      show ((incl x : T) : T ⧸ N') = 1 ↔ _
      rw [QuotientGroup.eq_one_iff, hN', mem_subgroupOf]
      rfl
    let e : π.ker ≃ ↥(N ⊓ fixSubgroup σ) :=
      { toFun := fun x => ⟨(x.1 : Γ), ((hkermem x.1).1 x.2), x.1.2.2⟩
        invFun := fun y => ⟨⟨(y : Γ), ⟨hl.le y.2.1, y.2.2⟩⟩, (hkermem _).2 y.2.1⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    have hk : Nat.card π.ker = Nat.card ↥(N ⊓ fixSubgroup σ) := Nat.card_congr e
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hk, hr] at h1
    have hN'card : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hl.le).toEquiv
    have hT' := Subgroup.card_eq_card_quotient_mul_card_subgroup N'
    rw [hN'card] at hT'
    have hFcard : Nat.card ↥F = Nat.card ↥(T ⊓ fixSubgroup σ) := rfl
    calc Nat.card ↥(T ⊓ fixSubgroup σ) ^ 2 = Nat.card ↥F ^ 2 := rfl
      _ = (Nat.card ↥(N ⊓ fixSubgroup σ) * Nat.card {q : T ⧸ N' // ρ q = q}) ^ 2 := by rw [h1]
      _ = Nat.card ↥(N ⊓ fixSubgroup σ) ^ 2 * Nat.card {q : T ⧸ N' // ρ q = q} ^ 2 := by ring
      _ = Nat.card N * Nat.card (T ⧸ N') := by rw [ih, hQ]
      _ = Nat.card T := by rw [hT', mul_comm]

theorem fixSubgroup_conj (x : Γ) : fixSubgroup (MulAut.conj x) = centralizer {x} := by
  ext g
  simp only [mem_fixSubgroup, MulAut.conj_apply, mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    calc x * g = x * g * x⁻¹ * x := by group
      _ = g * x := by rw [h]
  · intro h
    calc x * g * x⁻¹ = (g * x) * x⁻¹ := by rw [h]
      _ = g := by group

theorem FreeSeries.exists_conj {x : Γ} (hx : x * x = 1) {T : Subgroup Γ}
    (h : FreeSeries (MulAut.conj x) T) {g : Γ} (hg : g ∈ T) (hgx : (g * x) * (g * x) = 1) :
    ∃ f ∈ T, f⁻¹ * x * f = g * x := by
  have hσ : ∀ y : Γ, (MulAut.conj x) ((MulAut.conj x) y) = y := fun y => by
    simp only [MulAut.conj_apply]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x⁻¹ * x⁻¹) := by group
      _ = y := by rw [hx, hxi, hx]; group
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hc : g * (MulAut.conj x) g = 1 := by
    simp only [MulAut.conj_apply]
    calc g * (x * g * x⁻¹) = (g * x) * (g * x) := by rw [hxi]; group
      _ = 1 := hgx
  obtain ⟨f, hfT, hf⟩ := h.exists_cocycle hσ g hg hc
  refine ⟨f, hfT, ?_⟩
  rw [hf]
  simp only [MulAut.conj_apply]
  group

theorem FreeSeries.card_centralizer_sq {x : Γ} (hx : x * x = 1) {T : Subgroup Γ}
    (h : FreeSeries (MulAut.conj x) T) :
    Nat.card ↥(T ⊓ centralizer {x}) ^ 2 = Nat.card ↥T := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hσ : ∀ y : Γ, (MulAut.conj x) ((MulAut.conj x) y) = y := fun y => by
    simp only [MulAut.conj_apply]
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x⁻¹ * x⁻¹) := by group
      _ = y := by rw [hx, hxi, hx]; group
  have := h.card_fix_sq hσ
  rwa [fixSubgroup_conj] at this

end CFSG.OddStandard.Seitz77
