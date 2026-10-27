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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

@[expose] def wordProd {H : Type*} [Monoid H] {k : ℕ} (g : Fin k → H) : List (Fin k) → H
  | [] => 1
  | i :: w => g i * wordProd g w

@[expose] def foxSum {A : Type*} [AddCommGroup A] {k : ℕ} (a : Fin k → A → A) (m : Fin k → A) :
    List (Fin k) → A
  | [] => 0
  | i :: w => m i + a i (foxSum a m w)

theorem wordProd_cons {H : Type*} [Monoid H] {k : ℕ} (g : Fin k → H) (i : Fin k)
    (w : List (Fin k)) : wordProd g (i :: w) = g i * wordProd g w := rfl

theorem map_wordProd {H H' : Type*} [Monoid H] [Monoid H'] (f : H →* H') {k : ℕ} (g : Fin k → H)
    (w : List (Fin k)) : f (wordProd g w) = wordProd (f ∘ g) w := by
  induction w with
  | nil => exact map_one f
  | cons i w ih => rw [wordProd_cons, map_mul, ih]; rfl

theorem foxSum_add {A : Type*} [AddCommGroup A] {k : ℕ} (a : Fin k → A → A)
    (ha : ∀ i x y, a i (x + y) = a i x + a i y) (m m' : Fin k → A) (w : List (Fin k)) :
    foxSum a (m + m') w = foxSum a m w + foxSum a m' w := by
  induction w with
  | nil => simp [foxSum]
  | cons i w ih => simp only [foxSum, ih, ha, Pi.add_apply]; abel

theorem foxSum_zero {A : Type*} [AddCommGroup A] {k : ℕ} (a : Fin k → A → A)
    (ha : ∀ i x y, a i (x + y) = a i x + a i y) (w : List (Fin k)) : foxSum a 0 w = 0 := by
  have h := foxSum_add a ha 0 0 w
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem foxSum_neg {A : Type*} [AddCommGroup A] {k : ℕ} (a : Fin k → A → A)
    (ha : ∀ i x y, a i (x + y) = a i x + a i y) (m : Fin k → A) (w : List (Fin k)) :
    foxSum a (-m) w = -foxSum a m w := by
  have h := foxSum_add a ha m (-m) w
  rw [add_neg_cancel, foxSum_zero a ha] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem deriv_wordProd {N A : Type*} [Group N] [AddCommGroup A] (act : N → A → A) (φ : N → A)
    (hφ : ∀ x y, φ (x * y) = φ x + act x (φ y)) (hφ1 : φ 1 = 0) {k : ℕ} (n : Fin k → N)
    (a : Fin k → A → A) (ha : ∀ i, act (n i) = a i) (w : List (Fin k)) :
    φ (wordProd n w) = foxSum a (φ ∘ n) w := by
  induction w with
  | nil => exact hφ1
  | cons i w ih => rw [wordProd_cons, hφ, ih, ha]; rfl

theorem wordProd_ι_mul {N E : Type*} [Group N] [AddCommGroup E] (ι : E → N)
    (hι : ∀ x y, ι (x + y) = ι x * ι y) {k : ℕ} (n : Fin k → N) (a : Fin k → E → E)
    (hconj : ∀ i x, n i * ι x * (n i)⁻¹ = ι (a i x)) (e : Fin k → E) (w : List (Fin k)) :
    wordProd (fun i => ι (e i) * n i) w = ι (foxSum a e w) * wordProd n w := by
  have hι0 : ι 0 = 1 := by
    have h := hι 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  induction w with
  | nil => simp [wordProd, foxSum, hι0]
  | cons i w ih =>
    rw [wordProd_cons, ih, wordProd_cons, foxSum, hι, ← hconj i]
    group

section Induced

variable {N G₀ E Ω : Type*} [Group N] [Group G₀] [AddCommGroup E]

@[expose] def indAct (ρ : G₀ →* AddMonoid.End E) (α : G₀ →* Equiv.Perm Ω) (g : G₀) (f : Ω → E) :
    Ω → E := fun ω => ρ g (f (α g⁻¹ ω))

theorem indAct_add (ρ : G₀ →* AddMonoid.End E) (α : G₀ →* Equiv.Perm Ω) (g : G₀)
    (f f' : Ω → E) : indAct ρ α g (f + f') = indAct ρ α g f + indAct ρ α g f' := by
  ext ω
  simp [indAct]

theorem endMul_apply (f g : AddMonoid.End E) (x : E) : (f * g) x = f (g x) := rfl

theorem perm_apply_inv' (f : Equiv.Perm Ω) (x : Ω) : f (f⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]

theorem perm_inv_apply' (f : Equiv.Perm Ω) (x : Ω) : f⁻¹ (f x) = x := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

theorem indAct_apply (ρ : G₀ →* AddMonoid.End E) (α : G₀ →* Equiv.Perm Ω) (g : G₀)
    (f : Ω → E) (ω : Ω) : indAct ρ α g f ω = ρ g (f (α g⁻¹ ω)) := rfl

theorem exists_indDeriv (π : N →* G₀) (hπ : Function.Surjective π) (ι : E → N)
    (hιπ : ∀ x, π (ι x) = 1) (ρ : G₀ →* AddMonoid.End E)
    (hconj : ∀ n x, n * ι x * n⁻¹ = ι (ρ (π n) x)) (α : G₀ →* Equiv.Perm Ω) (ω₀ : Ω)
    (htr : ∀ ω, ∃ g, α g ω₀ = ω) (δ : N → E)
    (hδ : ∀ n m, α (π n) ω₀ = ω₀ → α (π m) ω₀ = ω₀ → δ (n * m) = δ n + ρ (π n) (δ m))
    (hδι : ∀ x, δ (ι x) = x) :
    ∃ φ : N → (Ω → E), (∀ n m, φ (n * m) = φ n + indAct ρ α (π n) (φ m)) ∧
      ∀ x, φ (ι x) = fun _ => x := by
  have hr : ∀ ω, ∃ r : N, α (π r) ω₀ = ω := fun ω => by
    obtain ⟨g, hg⟩ := htr ω
    obtain ⟨r, rfl⟩ := hπ g
    exact ⟨r, hg⟩
  choose r hr using hr
  have hstab : ∀ n ω, α (π ((r ω)⁻¹ * n * r (α (π n)⁻¹ ω))) ω₀ = ω₀ := by
    intro n ω
    have h1 := perm_inv_apply' (α (π (r ω))) ω₀
    rw [hr ω] at h1
    simp only [map_mul, map_inv, Equiv.Perm.coe_mul, Function.comp_apply, hr, perm_apply_inv', h1]
  refine ⟨fun n ω => ρ (π (r ω)) (δ ((r ω)⁻¹ * n * r (α (π n)⁻¹ ω))), ?_, ?_⟩
  · intro n m
    ext ω
    simp only [Pi.add_apply, indAct_apply]
    set ω' := α (π n)⁻¹ ω
    have hω'' : α (π (n * m))⁻¹ ω = α (π m)⁻¹ ω' := by
      simp only [ω', map_mul, mul_inv_rev, Equiv.Perm.coe_mul, Function.comp_apply]
    have hsplit : (r ω)⁻¹ * (n * m) * r (α (π (n * m))⁻¹ ω) =
        ((r ω)⁻¹ * n * r ω') * ((r ω')⁻¹ * m * r (α (π m)⁻¹ ω')) := by
      rw [hω'']; group
    rw [hsplit, hδ _ _ (hstab n ω) (hstab m ω'), map_add]
    congr 1
    have hmul : π (r ω) * π ((r ω)⁻¹ * n * r ω') = π n * π (r ω') := by
      simp only [map_mul, map_inv]; group
    rw [← endMul_apply, ← map_mul, hmul, map_mul, endMul_apply]
  · intro x
    ext ω
    have h1 : α (π (ι x))⁻¹ ω = ω := by rw [hιπ, inv_one, map_one, Equiv.Perm.one_apply]
    simp only
    rw [h1]
    have h2 : (r ω)⁻¹ * ι x * r ω = ι (ρ (π (r ω)⁻¹) x) := by
      rw [← hconj]; group
    rw [h2, hδι, map_inv, ← endMul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem exists_retraction (π : N →* G₀) (ι : E → N) (hι : ∀ x y, ι (x + y) = ι x * ι y)
    (hιinj : Function.Injective ι) (ρ : G₀ →* AddMonoid.End E)
    (hconj : ∀ n x, n * ι x * n⁻¹ = ι (ρ (π n) x)) (hιπ : ∀ x, π (ι x) = 1)
    (NK X : Subgroup N) (hXι : ∀ x, ι x ∈ X → ι x = 1)
    (hdec : ∀ n ∈ NK, ∃ x, ∃ k ∈ X, n = ι x * k) (hιNK : ∀ x, ι x ∈ NK) :
    ∃ δ : N → E, (∀ n m, n ∈ NK → m ∈ NK → δ (n * m) = δ n + ρ (π n) (δ m)) ∧
      ∀ x, δ (ι x) = x := by
  have hι0 : ι 0 = 1 := by
    have h := hι 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hιneg : ∀ x, ι (-x) = (ι x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hι, neg_add_cancel, hι0])
  have huniq : ∀ x y, ∀ k ∈ X, ∀ l ∈ X, ι x * k = ι y * l → x = y := by
    intro x y k hk l hl h
    have h1 : ι (-y + x) = l * k⁻¹ := by
      rw [hι, hιneg]
      calc (ι y)⁻¹ * ι x = (ι y)⁻¹ * (ι x * k) * k⁻¹ := by group
        _ = (ι y)⁻¹ * (ι y * l) * k⁻¹ := by rw [h]
        _ = l * k⁻¹ := by group
    have h2 := hXι _ (h1 ▸ X.mul_mem hl (X.inv_mem hk))
    rw [← hι0] at h2
    have := hιinj h2
    rw [neg_add_eq_zero] at this
    exact this.symm
  classical
  let δ : N → E := fun n => if h : n ∈ NK then (hdec n h).choose else 0
  have hδ : ∀ n (h : n ∈ NK), ∃ k ∈ X, n = ι (δ n) * k := by
    intro n h
    simp only [δ, dite_eq_left h]
    exact (hdec n h).choose_spec
  refine ⟨δ, fun n m hn hm => ?_, fun x => ?_⟩
  · obtain ⟨k, hk, hnk⟩ := hδ n hn
    obtain ⟨l, hl, hml⟩ := hδ m hm
    obtain ⟨kl, hkl, hnm⟩ := hδ (n * m) (NK.mul_mem hn hm)
    apply huniq _ _ kl hkl (k * l) (X.mul_mem hk hl)
    have hk' : π k = π n := by
      rw [hnk, map_mul, hιπ, one_mul]
    rw [← hnm]
    calc n * m = (ι (δ n) * k) * (ι (δ m) * l) := by rw [← hnk, ← hml]
      _ = ι (δ n) * (k * ι (δ m) * k⁻¹) * (k * l) := by group
      _ = ι (δ n) * ι (ρ (π k) (δ m)) * (k * l) := by rw [hconj]
      _ = ι (δ n + ρ (π n) (δ m)) * (k * l) := by rw [hk', hι]
  · obtain ⟨k, hk, hx⟩ := hδ (ι x) (hιNK x)
    have h1 : ι x * 1 = ι (δ (ι x)) * k := by rw [mul_one]; exact hx
    exact (huniq _ _ 1 X.one_mem k hk h1).symm

end Induced

section Split

variable {N G₀ E Ω : Type*} [Group N] [Group G₀] [AddCommGroup E]

theorem ι_zero_of_add {ι : E → N} (hι : ∀ x y, ι (x + y) = ι x * ι y) : ι 0 = 1 := by
  have h := hι 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem exists_splitting (π : N →* G₀) (hπ : Function.Surjective π) (ι : E → N)
    (hι : ∀ x y, ι (x + y) = ι x * ι y) (hιπ : ∀ x, π (ι x) = 1)
    (hker : ∀ n, π n = 1 → ∃ x, ι x = n) (ρ : G₀ →* AddMonoid.End E)
    (hconj : ∀ n x, n * ι x * n⁻¹ = ι (ρ (π n) x)) {k : ℕ} (s : Fin k → G₀)
    (hs : Subgroup.closure (Set.range s) = ⊤) (rels : List (List (Fin k)))
    (hrel : ∀ w ∈ rels, wordProd s w = 1)
    (hpres : ∀ h : Fin k → N, (∀ w ∈ rels, wordProd h w = 1) →
      ∃ σ : G₀ →* N, ∀ i, σ (s i) = h i)
    (α : G₀ →* Equiv.Perm Ω) (ω₀ : Ω) (htr : ∀ ω, ∃ g, α g ω₀ = ω) (δ : N → E)
    (hδ : ∀ n m, α (π n) ω₀ = ω₀ → α (π m) ω₀ = ω₀ → δ (n * m) = δ n + ρ (π n) (δ m))
    (hδι : ∀ x, δ (ι x) = x)
    (hfox : ∀ (m : Fin k → Ω → E) (c : List (Fin k) → E),
      (∀ w ∈ rels, foxSum (fun i => indAct ρ α (s i)) m w = fun _ => c w) →
      ∃ e : Fin k → E, ∀ w ∈ rels, foxSum (fun i => ρ (s i)) e w = c w) :
    ∃ σ : G₀ →* N, ∀ g, π (σ g) = g := by
  choose n hn using fun i => hπ (s i)
  have hπn : π ∘ n = s := funext hn
  have hw : ∀ w ∈ rels, ∃ x, ι x = wordProd n w := fun w hw =>
    hker _ (by rw [map_wordProd, hπn, hrel w hw])
  classical
  let c : List (Fin k) → E := fun w => if h : w ∈ rels then (hw w h).choose else 0
  have hc : ∀ w ∈ rels, ι (c w) = wordProd n w := fun w hw' => by
    simp only [c, dite_eq_left hw']
    exact (hw w hw').choose_spec
  obtain ⟨φ, hφ, hφι⟩ := exists_indDeriv π hπ ι hιπ ρ hconj α ω₀ htr δ hδ hδι
  have hφ1 : φ 1 = 0 := by
    have h := hφι 0
    rw [ι_zero_of_add hι] at h
    rw [h]
    rfl
  obtain ⟨e, he⟩ := hfox (φ ∘ n) c (fun w hw' => by
    rw [← deriv_wordProd (fun x => indAct ρ α (π x)) φ hφ hφ1 n _ (fun i => by rw [hn i]) w,
      ← hc w hw', hφι])
  let n' : Fin k → N := fun i => ι (-e i) * n i
  have hn' : ∀ w ∈ rels, wordProd n' w = 1 := by
    intro w hw'
    have hcj : ∀ i x, n i * ι x * (n i)⁻¹ = ι (ρ (s i) x) := fun i x => by
      rw [hconj, hn i]
    have h := wordProd_ι_mul ι hι n (fun i => ρ (s i)) hcj (-e) w
    simp only [Pi.neg_apply] at h
    have h2 := foxSum_neg (fun i => ρ (s i)) (fun i x y => map_add _ x y) e w
    rw [he w hw'] at h2
    change wordProd (fun i => ι (-e i) * n i) w = 1
    rw [h, h2, ← hc w hw', ← hι, neg_add_cancel, ι_zero_of_add hι]
  obtain ⟨σ, hσ⟩ := hpres n' hn'
  refine ⟨σ, fun g => ?_⟩
  have h : π.comp σ = MonoidHom.id G₀ := MonoidHom.eq_of_eqOn_dense hs (by
    rintro _ ⟨i, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, hσ, n', map_mul, hιπ, one_mul, hn,
      MonoidHom.id_apply])
  exact DFunLike.congr_fun h g

theorem deriv_ext {A : Type*} [AddCommGroup A] (ρ : G₀ →* AddMonoid.End A) (d d' : G₀ → A)
    (hd : ∀ g h, d (g * h) = d g + ρ g (d h)) (hd' : ∀ g h, d' (g * h) = d' g + ρ g (d' h))
    {S : Set G₀} (hS : Subgroup.closure S = ⊤) (h : ∀ g ∈ S, d g = d' g) (g : G₀) :
    d g = d' g := by
  have h1 : ∀ f : G₀ → A, (∀ g h, f (g * h) = f g + ρ g (f h)) → f 1 = 0 := fun f hf => by
    have := hf 1 1
    rw [mul_one, map_one] at this
    exact (left_eq_add.1 this)
  have hinv : ∀ f : G₀ → A, (∀ g h, f (g * h) = f g + ρ g (f h)) →
      ∀ g, f g⁻¹ = -ρ g⁻¹ (f g) := fun f hf g => by
    have := hf g⁻¹ g
    rw [inv_mul_cancel, h1 f hf] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let H : Subgroup G₀ :=
    { carrier := {g | d g = d' g}
      one_mem' := by simp only [Set.mem_ofPred_eq, h1 d hd, h1 d' hd']
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at *
        rw [hd, hd', ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        rw [hinv d hd, hinv d' hd', ha] }
  have hle : Subgroup.closure S ≤ H := (Subgroup.closure_le H).2 h
  rw [hS] at hle
  exact hle (Subgroup.mem_top g)

theorem splitting_conj (π : N →* G₀) (ι : E → N) (hι : ∀ x y, ι (x + y) = ι x * ι y)
    (hιinj : Function.Injective ι) (hker : ∀ n, π n = 1 → ∃ x, ι x = n)
    (ρ : G₀ →* AddMonoid.End E) (hconj : ∀ n x, n * ι x * n⁻¹ = ι (ρ (π n) x)) {k : ℕ}
    (s : Fin k → G₀) (hs : Subgroup.closure (Set.range s) = ⊤) (rels : List (List (Fin k)))
    (hrel : ∀ w ∈ rels, wordProd s w = 1)
    (hcob : ∀ e : Fin k → E, (∀ w ∈ rels, foxSum (fun i => ρ (s i)) e w = 0) →
      ∃ x : E, ∀ i, e i = ρ (s i) x - x)
    (σ σ' : G₀ →* N) (hσ : ∀ g, π (σ g) = g) (hσ' : ∀ g, π (σ' g) = g) :
    ∃ y : E, ∀ g, σ' g = ι y * σ g * (ι y)⁻¹ := by
  have hd : ∀ g, ∃ x, ι x = σ' g * (σ g)⁻¹ := fun g => hker _ (by
    rw [map_mul, map_inv, hσ, hσ', mul_inv_cancel])
  choose d hd using hd
  have hι0 := ι_zero_of_add hι
  have hder : ∀ g h, d (g * h) = d g + ρ g (d h) := by
    intro g h
    apply hιinj
    rw [hι, hd, hd, ← hσ g, ← hconj, hσ g, hd, map_mul, map_mul]
    group
  have hd1 : d 1 = 0 := hιinj (by rw [hd, map_one, map_one, inv_one, mul_one, hι0])
  obtain ⟨x, hx⟩ := hcob (d ∘ s) (fun w hw => by
    rw [← deriv_wordProd (fun g => ρ g) d hder hd1 s _ (fun i => rfl) w, hrel w hw, hd1])
  have hext := deriv_ext ρ d (fun g => ρ g x - x) hder (fun g h => by
      simp only [map_mul, endMul_apply, map_sub]; abel) hs (by rintro _ ⟨i, rfl⟩; exact hx i)
  refine ⟨-x, fun g => ?_⟩
  have h1 : σ' g = ι (d g) * σ g := by rw [hd]; group
  have h2 : σ g * ι x * (σ g)⁻¹ = ι (ρ g x) := by rw [hconj, hσ]
  rw [h1, hext g, sub_eq_neg_add, hι, ← h2]
  have h3 : (ι (-x))⁻¹ = ι x := by
    rw [inv_eq_iff_mul_eq_one, ← hι, neg_add_cancel, hι0]
  rw [h3]
  group

end Split

end CFSG.EvenSmallLie.OmegaEight.NSplit
