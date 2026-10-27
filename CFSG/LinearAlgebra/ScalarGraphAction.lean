module

public import TauCeti.FieldTheory.Finite.MinpolyOrbit
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

public section

open scoped Pointwise

namespace CFSG.ScalarGraphAction

variable {F P : Type*} [Field F] [AddGroup P]

@[expose] def scalarMulHom {F P : Type*} [Field F] [Group P] (a : F) :
    Multiplicative (F) × P →* Multiplicative (F) × P where
  toFun x := (Multiplicative.ofAdd (a * x.1.toAdd), x.2)
  map_one' := by
    ext <;> simp
  map_mul' := by
    intro x y
    apply Prod.ext
    · change Multiplicative.ofAdd (a * (x * y).1.toAdd) =
        Multiplicative.ofAdd (a * x.1.toAdd) *
          Multiplicative.ofAdd (a * y.1.toAdd)
      rw [Prod.fst_mul, toAdd_mul, ← ofAdd_add, mul_add]
    · rfl

@[expose] def scalarGraphHom {F P : Type*} [Field F] [Group P]
    (φ : P →* Multiplicative (F)) (a : F) :
    P →* Multiplicative (F) × P where
  toFun p := (Multiplicative.ofAdd (a * (φ p).toAdd), p)
  map_one' := by
    ext <;> simp
  map_mul' := by
    intro p q
    apply Prod.ext
    · change Multiplicative.ofAdd (a * (φ (p * q)).toAdd) =
        Multiplicative.ofAdd (a * (φ p).toAdd) *
          Multiplicative.ofAdd (a * (φ q).toAdd)
      rw [map_mul φ, toAdd_mul, ← ofAdd_add, mul_add]
    · rfl

theorem scalarGraphHom_range {F P : Type*} [Field F] [Group P]
    (φ : P →* Multiplicative (F)) (a : F) :
    (scalarGraphHom φ a).range =
      {x : Multiplicative (F) × P | ∃ p : P,
        x = (Multiplicative.ofAdd (a * (φ p).toAdd), p)} := by
  ext x
  constructor
  · intro hx
    change x ∈ (scalarGraphHom φ a).range at hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨p, rfl⟩



theorem graph_block_affine
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P]
    (γ : F →+ F) (α : P ≃+ P) (β : P →+ F)
    (σ : F → F)
    (hgraph : ∀ a p, γ (a * φ p) + β p = σ a * φ (α p)) :
    (∀ p : P, β p = σ 0 * φ (α p)) ∧
      (∀ a b : F,
        (σ (a + b) - σ 0) = (σ a - σ 0) + (σ b - σ 0)) ∧
      (∀ (a : F) (p : P),
        γ (a * φ p) = (σ a - σ 0) * φ (α p)) := by
  classical
  let c : F → F := fun a => σ a - σ 0
  have hβ : ∀ p : P, β p = σ 0 * φ (α p) := by
    intro p
    have h := hgraph 0 p
    simpa using h
  have hγ : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p) := by
    intro a p
    have h := hgraph a p
    have hb := hβ p
    calc
      γ (a * φ p) = γ (a * φ p) + β p - β p := by abel
      _ = σ a * φ (α p) - σ 0 * φ (α p) := by rw [h, hb]
      _ = c a * φ (α p) := by ring
  have hc : ∀ a b : F, c (a + b) = c a + c b := by
    intro a b
    obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
    have hφp0 : φ p0 ≠ 0 := by
      intro hzero
      exact hp0 (hφ (by simpa using hzero))
    obtain ⟨p, hp⟩ := α.surjective p0
    have hq' : φ (α p) ≠ 0 := by rw [hp]; exact hφp0
    have harg : (a + b) * φ p = a * φ p + b * φ p := by ring
    have hγadd : γ ((a + b) * φ p) = γ (a * φ p) + γ (b * φ p) := by
      rw [harg, map_add]
    have heq : c (a + b) * φ (α p) = (c a + c b) * φ (α p) := by
      calc
        c (a + b) * φ (α p) = γ ((a + b) * φ p) := (hγ (a + b) p).symm
        _ = γ (a * φ p) + γ (b * φ p) := hγadd
        _ = c a * φ (α p) + c b * φ (α p) := by rw [hγ a p, hγ b p]
        _ = (c a + c b) * φ (α p) := by ring
    exact mul_right_cancel₀ hq' heq
  refine ⟨hβ, ?_, hγ⟩
  intro a b
  exact hc a b

@[expose] def scalarGraph (φ : P →+ F) (a : F) : AddSubgroup (F × P) :=
  (AddMonoidHom.prod ((AddMonoidHom.mulLeft a).comp φ) (AddMonoidHom.id P)).range

@[simp]
theorem mem_scalarGraph (φ : P →+ F) (a x : F) (p : P) :
    (x, p) ∈ scalarGraph φ a ↔ x = a * φ p := by
  constructor
  · rintro ⟨q, hq⟩
    have h1 : a * φ q = x := by
      simpa using congrArg Prod.fst hq
    have h2 : q = p := by
      simpa using congrArg Prod.snd hq
    simpa [h2] using h1.symm
  · intro hx
    refine ⟨p, ?_⟩
    ext <;> simp [hx]

theorem exists_affine_decomposition
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P]
    (e : (F × P) ≃+ (F × P))
    (hR : ∀ r : F, (e (r, 0)).2 = 0)
    (hRinv : ∀ r : F, (e.symm (r, 0)).2 = 0)
    (σ : F ≃ F)
    (hσ : ∀ a : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ (σ a)) :
    ∃ (γ : F ≃+ F) (α : P ≃+ P) (β : P →+ F) (c : F ≃+ F),
      (∀ (r : F) (p : P), e (r, p) = (γ r + β p, α p)) ∧
      (∀ a : F, c a = σ a - σ 0) ∧
      (∀ p : P, β p = σ 0 * φ (α p)) ∧
      (∀ (a : F) (p : P), γ (a * φ p) = (σ a - σ 0) * φ (α p)) := by
  let γ₀ : F →+ F :=
    { toFun := fun r => (e (r, 0)).1
      map_zero' := by
        change (e (0 : F × P)).1 = 0
        exact congrArg Prod.fst e.map_zero
      map_add' := by
        intro r s
        have h : e (r + s, 0) = e (r, 0) + e (s, 0) := by
          simpa using map_add e (r, 0) (s, 0)
        rw [h]
        rfl }
  let α₀ : P →+ P :=
    { toFun := fun p => (e (0, p)).2
      map_zero' := by
        change (e (0 : F × P)).2 = 0
        exact congrArg Prod.snd e.map_zero
      map_add' := by
        intro p q
        have h : e (0, p + q) = e (0, p) + e (0, q) := by
          simpa using map_add e (0, p) (0, q)
        rw [h]
        rfl }
  let β₀ : P →+ F :=
    { toFun := fun p => (e (0, p)).1
      map_zero' := by
        change (e (0 : F × P)).1 = 0
        exact congrArg Prod.fst e.map_zero
      map_add' := by
        intro p q
        have h : e (0, p + q) = e (0, p) + e (0, q) := by
          simpa using map_add e (0, p) (0, q)
        rw [h]
        rfl }
  have hdecomp₀ : ∀ (r : F) (p : P), e (r, p) = (γ₀ r + β₀ p, α₀ p) := by
    intro r p
    have h : e (r, p) = e (r, 0) + e (0, p) := by
      simpa using map_add e (r, 0) (0, p)
    rw [h]
    ext
    · simp [γ₀, β₀]
    · simp [α₀, hR r]
  have hαinj : Function.Injective α₀ := by
    intro p q hpq
    have hzero : α₀ (p - q) = 0 := by
      rw [map_sub, hpq, sub_self]
    have hmemR : e (0, p - q) = (β₀ (p - q), 0) := by
      rw [hdecomp₀ 0 (p - q)]
      simp [hzero, map_zero γ₀]
    let x : F × P := e.symm (β₀ (p - q), 0)
    have hx2 : x.2 = 0 := by
      simpa [x] using hRinv (β₀ (p - q))
    have hx : e x = (β₀ (p - q), 0) := by
      simpa [x] using e.apply_symm_apply (β₀ (p - q), 0)
    have hxeq : x = (x.1, 0) := Prod.ext rfl hx2
    rw [hxeq] at hx
    have heq : e (0, p - q) = e (x.1, 0) := by rw [hmemR, hx]
    have hpq0 : p - q = 0 := (Prod.ext_iff.mp (e.injective heq)).2
    exact sub_eq_zero.mp hpq0
  have hαsurj : Function.Surjective α₀ := by
    intro q
    obtain ⟨x, hx⟩ := e.surjective (0, q)
    obtain ⟨r, p⟩ := x
    refine ⟨p, ?_⟩
    have h2 : (e (r, p)).2 = q := congrArg Prod.snd hx
    rw [hdecomp₀ r p] at h2
    exact h2
  have hγinj : Function.Injective γ₀ := by
    intro r s hrs
    have hr : e (r, 0) = (γ₀ r, 0) := Prod.ext rfl (hR r)
    have hs : e (s, 0) = (γ₀ s, 0) := Prod.ext rfl (hR s)
    have heq : e (r, 0) = e (s, 0) := by rw [hr, hs, hrs]
    exact (Prod.ext_iff.mp (e.injective heq)).1
  have hγsurj : Function.Surjective γ₀ := by
    intro y
    let x : F × P := e.symm (y, 0)
    have hx2 : x.2 = 0 := by simpa [x] using hRinv y
    refine ⟨x.1, ?_⟩
    have hx : e x = (y, 0) := by simpa [x] using e.apply_symm_apply (y, 0)
    have hxeq : x = (x.1, 0) := Prod.ext rfl hx2
    rw [hxeq] at hx
    simpa [γ₀] using congrArg Prod.fst hx
  let α : P ≃+ P := AddEquiv.ofBijective α₀ ⟨hαinj, hαsurj⟩
  let γ : F ≃+ F := AddEquiv.ofBijective γ₀ ⟨hγinj, hγsurj⟩
  have hdecomp : ∀ (r : F) (p : P), e (r, p) = (γ r + β₀ p, α p) := by
    intro r p
    have hg : γ r = γ₀ r := AddEquiv.ofBijective_apply γ₀ ⟨hγinj, hγsurj⟩ r
    have ha : α p = α₀ p := AddEquiv.ofBijective_apply α₀ ⟨hαinj, hαsurj⟩ p
    rw [hg, ha]
    exact hdecomp₀ r p
  have hgraph : ∀ (a : F) (p : P), γ (a * φ p) + β₀ p = σ a * φ (α p) := by
    intro a p
    have hsrc : (a * φ p, p) ∈ scalarGraph φ a :=
      (mem_scalarGraph φ a (a * φ p) p).2 rfl
    have hmem : e (a * φ p, p) ∈ scalarGraph φ (σ a) := by
      have hmap := AddSubgroup.mem_map_of_mem e.toAddMonoidHom hsrc
      rwa [hσ a] at hmap
    rw [hdecomp (a * φ p) p] at hmem
    exact (mem_scalarGraph φ (σ a) (γ (a * φ p) + β₀ p) (α p)).1 hmem
  obtain ⟨hβ, hcadd, hγ⟩ :=
    graph_block_affine
      φ hφ γ.toAddMonoidHom α β₀ σ (by simpa using hgraph)
  let c₀ : F →+ F :=
    { toFun := fun a => σ a - σ 0
      map_zero' := sub_self (σ 0)
      map_add' := hcadd }
  have hc_bij : Function.Bijective c₀ := by
    have hbij : Function.Bijective (fun a : F => σ a - σ 0) := by
      constructor
      · intro a b hab
        apply σ.injective
        have h := congrArg (fun x : F => x + σ 0) hab
        simpa only [sub_add_cancel] using h
      · intro y
        refine ⟨σ.symm (y + σ 0), ?_⟩
        change σ (σ.symm (y + σ 0)) - σ 0 = y
        rw [σ.apply_symm_apply]
        exact add_sub_cancel_right y (σ 0)
    simpa [c₀] using hbij
  let c : F ≃+ F := AddEquiv.ofBijective c₀ hc_bij
  refine ⟨γ, α, β₀, c, hdecomp, ?_, hβ, ?_⟩
  · intro a
    change c₀ a = σ a - σ 0
    rfl
  · simpa using hγ

theorem sigma_unique
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P]
    (f : (F × P) →+ (F × P))
    (σ τ : F ≃ F)
    (hσ : ∀ a : F, (scalarGraph φ a).map f = scalarGraph φ (σ a))
    (hτ : ∀ a : F, (scalarGraph φ a).map f = scalarGraph φ (τ a)) :
    σ = τ := by
  apply Equiv.ext
  intro a
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h
    exact hp0 (hφ (by simpa using h))
  have hG : scalarGraph φ (σ a) = scalarGraph φ (τ a) := by
    rw [← hσ a, hτ a]
  have hmem : (τ a * φ p0, p0) ∈ scalarGraph φ (σ a) := by
    rw [hG]
    exact (mem_scalarGraph φ (τ a) (τ a * φ p0) p0).2 rfl
  have h := (mem_scalarGraph φ (σ a) (τ a * φ p0) p0).1 hmem
  exact (mul_right_cancel₀ hφp0 h).symm

theorem exists_scalar_of_graph_fixing
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P]
    (e : (F × P) ≃+ (F × P))
    (hR : ∀ r : F, (e (r, 0)).2 = 0)
    (hRinv : ∀ r : F, (e.symm (r, 0)).2 = 0)
    (hfix : ∀ a : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ a) :
    ∃ (γ : F ≃+ F) (α : P ≃+ P) (β : P →+ F) (k : Fˣ),
      (∀ (r : F) (p : P), e (r, p) = (γ r + β p, α p)) ∧
      (∀ p : P, β p = 0) ∧
      (∀ r : F, γ r = (k : F) * r) ∧
      (∀ p : P, φ (α p) = (k : F) * φ p) ∧
      (∀ x : F, x ∈ φ.range → (k : F) * x ∈ φ.range) := by
  obtain ⟨γ, α, β, _, hdecomp, _, hβ, hγ⟩ :=
    exists_affine_decomposition φ hφ e hR hRinv (Equiv.refl F) (by
      intro a
      simpa using hfix a)
  have hβ0 : ∀ p : P, β p = 0 := by
    intro p
    simpa using hβ p
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h
    exact hp0 (hφ (by simpa using h))
  have hαp0 : α p0 ≠ 0 := by
    intro h
    have h' : α p0 = α 0 := by
      rw [h, α.map_zero]
    exact hp0 (α.injective h')
  have hφαp0 : φ (α p0) ≠ 0 := by
    intro h
    exact hαp0 (hφ (by simpa using h))
  have hk0 : φ (α p0) / φ p0 ≠ 0 := div_ne_zero hφαp0 hφp0
  let k : Fˣ := Units.mk0 (φ (α p0) / φ p0) hk0
  have hkval : (k : F) = φ (α p0) / φ p0 := rfl
  have hkγ : ∀ r : F, γ r = (k : F) * r := by
    intro r
    have h := hγ (r / φ p0) p0
    have har : (r / φ p0) * φ p0 = r := div_mul_cancel₀ r hφp0
    rw [har] at h
    have h' : γ r = (r / φ p0) * φ (α p0) := by simpa using h
    rw [h', hkval]
    calc
      (r / φ p0) * φ (α p0) = (r * (φ p0)⁻¹) * φ (α p0) := by
        rw [div_eq_mul_inv]
      _ = (φ (α p0) * (φ p0)⁻¹) * r := by ac_rfl
      _ = (φ (α p0) / φ p0) * r := by
        rw [div_eq_mul_inv]
  have hφα : ∀ p : P, φ (α p) = (k : F) * φ p := by
    intro p
    have h1 : γ (φ p) = φ (α p) := by
      have := hγ 1 p
      simpa using this
    have h2 : γ (φ p) = (k : F) * φ p := hkγ (φ p)
    rw [h1] at h2
    exact h2
  have hrange : ∀ x : F, x ∈ φ.range → (k : F) * x ∈ φ.range := by
    intro x hx
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨p, rfl⟩ := hx
    exact ⟨α p, hφα p⟩
  exact ⟨γ, α, β, k, hdecomp, hβ0, hkγ, hφα, hrange⟩

theorem scalarGraph_injective
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P] :
    Function.Injective (scalarGraph φ) := by
  intro a b hab
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h
    exact hp0 (hφ (by simpa using h))
  have hmem : (b * φ p0, p0) ∈ scalarGraph φ a := by
    rw [hab]
    exact (mem_scalarGraph φ b (b * φ p0) p0).2 rfl
  have hba : b * φ p0 = a * φ p0 :=
    (mem_scalarGraph φ a (b * φ p0) p0).1 hmem
  exact (mul_right_cancel₀ hφp0 hba).symm

theorem exists_affine_of_graph_family
    (φ : P →+ F) (hφ : Function.Injective φ) [Nontrivial P] [Finite F]
    (e : (F × P) ≃+ (F × P))
    (hR : ∀ r : F, (e (r, 0)).2 = 0)
    (hRinv : ∀ r : F, (e.symm (r, 0)).2 = 0)
    (hfam : ∀ a : F, ∃ b : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ b) :
    ∃ (σ : F ≃ F) (γ : F ≃+ F) (α : P ≃+ P) (β : P →+ F) (c : F ≃+ F),
      (∀ a : F,
        (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ (σ a)) ∧
      (∀ (r : F) (p : P), e (r, p) = (γ r + β p, α p)) ∧
      (∀ a : F, c a = σ a - σ 0) ∧
      (∀ p : P, β p = σ 0 * φ (α p)) ∧
      (∀ (a : F) (p : P), γ (a * φ p) = (σ a - σ 0) * φ (α p)) := by
  classical
  let bOf : F → F := fun a => Classical.choose (hfam a)
  have hbOf : ∀ a : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ (bOf a) :=
    fun a => Classical.choose_spec (hfam a)
  have hmap_inj : Function.Injective (AddSubgroup.map e.toAddMonoidHom) :=
    AddSubgroup.map_injective (f := e.toAddMonoidHom) (by simpa using e.injective)
  have hbOf_inj : Function.Injective bOf := by
    intro a₁ a₂ h
    have hmap : (scalarGraph φ a₁).map e.toAddMonoidHom =
        (scalarGraph φ a₂).map e.toAddMonoidHom := by
      calc
        (scalarGraph φ a₁).map e.toAddMonoidHom =
            scalarGraph φ (bOf a₁) := hbOf a₁
        _ = scalarGraph φ (bOf a₂) := by rw [h]
        _ = (scalarGraph φ a₂).map e.toAddMonoidHom := (hbOf a₂).symm
    have hG : scalarGraph φ a₁ = scalarGraph φ a₂ := hmap_inj hmap
    exact scalarGraph_injective φ hφ hG
  have hbOf_surj : Function.Surjective bOf :=
    (Finite.injective_iff_surjective (f := bOf)).mp hbOf_inj
  let σ : F ≃ F := Equiv.ofBijective bOf ⟨hbOf_inj, hbOf_surj⟩
  have hσ : ∀ a : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ (σ a) := by
    intro a
    have h : σ a = bOf a :=
      Equiv.ofBijective_apply bOf ⟨hbOf_inj, hbOf_surj⟩ a
    rw [h]
    exact hbOf a
  obtain ⟨γ, α, β, c, hdecomp, hc, hβ, hγ⟩ :=
    exists_affine_decomposition φ hφ e hR hRinv σ hσ
  exact ⟨σ, γ, α, β, c, hσ, hdecomp, hc, hβ, hγ⟩

section Coordinate

variable {K P W : Type*} [Field K] [Group P] [Group W]

@[expose]
def prodCoordEquiv : (K × Additive P) ≃+ Additive (Multiplicative K × P) :=
  ((AddEquiv.additiveMultiplicative K).symm.prodCongr
      (AddEquiv.refl (Additive P))).trans
    (AddEquiv.prodAdditive (G := Multiplicative K) (H := P)).symm

@[simp]
theorem prodCoordEquiv_apply (x : K) (p : Additive P) :
    prodCoordEquiv (K := K) (P := P) (x, p) =
      Additive.ofMul (Multiplicative.ofAdd x, Additive.toMul p) := by
  rfl

@[simp]
theorem prodCoordEquiv_symm_apply (x : K) (p : P) :
    (prodCoordEquiv (K := K) (P := P)).symm
        (Additive.ofMul (Multiplicative.ofAdd x, p)) = (x, Additive.ofMul p) := by
  rfl

@[expose]
def coordinateAddEquiv (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) :
    (K × Additive P) ≃+ (K × Additive P) :=
  (prodCoordEquiv (K := K) (P := P)).trans
    (((MulEquiv.toAdditive (MulAut.congr eW τ)).trans
      (prodCoordEquiv (K := K) (P := P)).symm))

@[simp] theorem coordinateAddEquiv_apply
    (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) (x : K) (p : Additive P) :
    coordinateAddEquiv eW τ (x, p) =
      ((eW (τ (eW.symm (Multiplicative.ofAdd x, p.toMul)))).1.toAdd,
        Additive.ofMul (eW (τ (eW.symm (Multiplicative.ofAdd x, p.toMul)))).2) := rfl

theorem toAddSubgroup_map
    (f : Multiplicative K × P ≃* Multiplicative K × P)
    (S : Subgroup (Multiplicative K × P)) :
    Subgroup.toAddSubgroup (S.map f.toMonoidHom) =
      (Subgroup.toAddSubgroup S).map (MulEquiv.toAdditive f).toAddMonoidHom := by
  ext x
  rw [Additive.mem_toAddSubgroup, Subgroup.mem_map, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact ⟨Additive.ofMul y, by simpa using hy, by simpa [hfy]⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨Additive.toMul z, ?_, ?_⟩
    · simpa using hz
    · simpa using congrArg Additive.toMul hzx

theorem scalarGraph_eq_coord_image
    (φ : P →* Multiplicative K) (a : K) :
    scalarGraph (MonoidHom.toAdditiveLeft φ) a =
      (Subgroup.toAddSubgroup ((scalarGraphHom φ a).range)).map
        (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [mem_scalarGraph] at hx
    refine ⟨Additive.ofMul (scalarGraphHom φ a (Additive.toMul x.2)), ?_, ?_⟩
    · change scalarGraphHom φ a (Additive.toMul x.2) ∈ (scalarGraphHom φ a).range
      exact MonoidHom.mem_range.mpr ⟨Additive.toMul x.2, rfl⟩
    · apply Prod.ext
      · change a * (φ x.2.toMul).toAdd = x.1
        exact hx.symm
      · rfl
  · rintro ⟨y, hy, rfl⟩
    change Additive.toMul y ∈ (scalarGraphHom φ a).range at hy
    obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hy
    have hy' : y = Additive.ofMul (scalarGraphHom φ a p) :=
      congrArg Additive.ofMul hp.symm
    subst y
    rw [mem_scalarGraph]
    rfl

theorem scalarGraph_map_coordinate
    (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W)
    (φ : P →* Multiplicative K) (a : K) :
    (scalarGraph (MonoidHom.toAdditiveLeft φ) a).map
        (coordinateAddEquiv eW τ).toAddMonoidHom =
      (Subgroup.toAddSubgroup ((scalarGraphHom φ a).range.map
        (MulAut.congr eW τ).toMonoidHom)).map
          (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom := by
  rw [scalarGraph_eq_coord_image]
  rw [AddSubgroup.map_map]
  have hcomp : (coordinateAddEquiv eW τ).toAddMonoidHom.comp
      (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom =
      (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom.comp
        (MulEquiv.toAdditive (MulAut.congr eW τ)).toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro y
    change coordinateAddEquiv eW τ ((prodCoordEquiv (K := K) (P := P)).symm y) =
      (prodCoordEquiv (K := K) (P := P)).symm ((MulEquiv.toAdditive (MulAut.congr eW τ)) y)
    rw [show coordinateAddEquiv eW τ =
      (prodCoordEquiv (K := K) (P := P)).trans
        ((MulEquiv.toAdditive (MulAut.congr eW τ)).trans
          (prodCoordEquiv (K := K) (P := P)).symm) from rfl]
    simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hcomp]
  rw [← AddSubgroup.map_map, toAddSubgroup_map]

theorem coordinateAddEquiv_symm
    (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) :
    (coordinateAddEquiv eW τ).symm = coordinateAddEquiv eW τ.symm := by
  rfl

end Coordinate

section Root

variable {G : Type*} [Group G]
variable {W R P : Subgroup G}
variable {K : Type*} [Field K]

theorem coordinateAddEquiv_root_zero
    (hRW : R ≤ W)
    (eR : R ≃* Multiplicative K)
    (eW : W ≃* (Multiplicative K × P))
    (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
    (τ : MulAut W)
    (hτR : ∀ r : R, ∃ r' : R,
      τ (Subgroup.inclusion hRW r) = Subgroup.inclusion hRW r')
    (x : K) :
    (coordinateAddEquiv eW τ (x, 0)).2 = 0 := by
  classical
  let r : R := eR.symm (Multiplicative.ofAdd x)
  have heWr' : eW (Subgroup.inclusion hRW r) = (Multiplicative.ofAdd x, 1) := by
    simpa [r] using heWr r
  have hsymm : eW.symm (Multiplicative.ofAdd x, (1 : P)) =
      Subgroup.inclusion hRW r := by
    rw [← heWr', eW.symm_apply_apply]
  obtain ⟨r', hr'⟩ := hτR r
  have hstep : eW (τ (eW.symm (Multiplicative.ofAdd x, (1 : P)))) = (eR r', 1) := by
    rw [hsymm, hr', heWr r']
  rw [coordinateAddEquiv_apply]
  change Additive.ofMul (eW (τ (eW.symm (Multiplicative.ofAdd x, (1 : P))))).2 = 0
  rw [hstep]
  rfl

end Root

theorem exists_affine_of_mulAut_preserving_root_family
    {K G : Type*} [Field K] [Finite K] [Group G]
    {W R P : Subgroup G}
    (hRW : R ≤ W) (hPW : P ≤ W)
    [Nontrivial P]
    (eR : R ≃* Multiplicative (K))
    (eW : W ≃* (Multiplicative (K) × P))
    (heWr : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
    (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
    (φ : P →* Multiplicative (K))
    (hφ : Function.Injective φ)
    (F : Set (Subgroup W))
    (hF : ∀ Q : Subgroup W,
      Q ∈ F ↔ ∃ a : K,
        Q.map eW.toMonoidHom = (scalarGraphHom φ a).range)
    (τ : MulAut W)
    (hτR : ∀ r : R, ∃ r' : R,
      τ (Subgroup.inclusion hRW r) = Subgroup.inclusion hRW r')
    (hτRinv : ∀ r : R, ∃ r' : R,
      τ.symm (Subgroup.inclusion hRW r) = Subgroup.inclusion hRW r')
    (hτF : ∀ Q : Subgroup W, Q ∈ F ↔ τ • Q ∈ F) :
    let e : (K × Additive P) ≃+
        (K × Additive P) := coordinateAddEquiv eW τ
    ∃ (σ : K ≃ K)
      (γ : K ≃+ K)
      (α : Additive P ≃+ Additive P)
      (β : Additive P →+ K)
      (c : K ≃+ K),
      (∀ a : K,
        (scalarGraph (MonoidHom.toAdditiveLeft φ) a).map e.toAddMonoidHom =
          scalarGraph (MonoidHom.toAdditiveLeft φ) (σ a)) ∧
      (∀ (r : K) (p : Additive P),
        e (r, p) = (γ r + β p, α p)) ∧
      (∀ a : K, c a = σ a - σ 0) ∧
      (∀ p : Additive P,
        β p = σ 0 * (MonoidHom.toAdditiveLeft φ) (α p)) ∧
      (∀ (a : K) (p : Additive P),
        γ (a * (MonoidHom.toAdditiveLeft φ) p) =
          (σ a - σ 0) * (MonoidHom.toAdditiveLeft φ) (α p)) := by
  classical
  let e : (K × Additive P) ≃+
      (K × Additive P) := coordinateAddEquiv eW τ
  have hR : ∀ r : K, (e (r, 0)).2 = 0 := by
    intro r
    simpa [e] using coordinateAddEquiv_root_zero
      (hRW := hRW) (eR := eR) (eW := eW) (heWr := heWr) (τ := τ) (hτR := hτR) r
  have hRinv : ∀ r : K, (e.symm (r, 0)).2 = 0 := by
    intro r
    have hsymm := coordinateAddEquiv_symm (eW := eW) (τ := τ)
    change ((coordinateAddEquiv eW τ).symm (r, 0)).2 = 0
    rw [hsymm]
    exact coordinateAddEquiv_root_zero
      (hRW := hRW) (eR := eR) (eW := eW) (heWr := heWr)
      (τ := τ.symm) (hτR := hτRinv) r
  have hfam : ∀ a : K, ∃ b : K,
      (scalarGraph (MonoidHom.toAdditiveLeft φ) a).map e.toAddMonoidHom =
        scalarGraph (MonoidHom.toAdditiveLeft φ) b := by
    intro a
    let Q : Subgroup W := (scalarGraphHom φ a).range.comap eW.toMonoidHom
    have hQmap : Q.map eW.toMonoidHom = (scalarGraphHom φ a).range := by
      simpa [Q] using
        Subgroup.map_comap_eq_self_of_surjective
          (f := eW.toMonoidHom) eW.surjective (scalarGraphHom φ a).range
    have hQF : Q ∈ F := (hF Q).mpr ⟨a, hQmap⟩
    have hτQF : τ • Q ∈ F := (hτF Q).mp hQF
    obtain ⟨b, hb⟩ := (hF (τ • Q)).mp hτQF
    refine ⟨b, ?_⟩
    have hcomp : (MulAut.congr eW τ).toMonoidHom.comp eW.toMonoidHom =
        eW.toMonoidHom.comp τ.toMonoidHom := by
      apply MonoidHom.ext
      intro w
      change eW (τ (eW.symm (eW w))) = eW (τ w)
      rw [eW.symm_apply_apply]
    have hcongr_map :
        (scalarGraphHom φ a).range.map (MulAut.congr eW τ).toMonoidHom =
          (τ • Q).map eW.toMonoidHom := by
      calc
        (scalarGraphHom φ a).range.map (MulAut.congr eW τ).toMonoidHom
            = (Q.map eW.toMonoidHom).map
                (MulAut.congr eW τ).toMonoidHom := by rw [← hQmap]
        _ = Q.map ((MulAut.congr eW τ).toMonoidHom.comp eW.toMonoidHom) := by
              rw [Subgroup.map_map]
        _ = Q.map (eW.toMonoidHom.comp τ.toMonoidHom) := by rw [hcomp]
        _ = (Q.map τ.toMonoidHom).map eW.toMonoidHom := by
              rw [← Subgroup.map_map]
        _ = (τ • Q).map eW.toMonoidHom := by
              rw [Subgroup.pointwise_smul_def]
              rfl
    have hrange : (scalarGraphHom φ a).range.map
        (MulAut.congr eW τ).toMonoidHom = (scalarGraphHom φ b).range := by
      rw [hcongr_map, hb]
    calc
      (scalarGraph (MonoidHom.toAdditiveLeft φ) a).map e.toAddMonoidHom
          = (Subgroup.toAddSubgroup ((scalarGraphHom φ a).range.map
              (MulAut.congr eW τ).toMonoidHom)).map
                (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom := by
            simpa [e] using scalarGraph_map_coordinate
              (eW := eW) (τ := τ) (φ := φ) a
      _ = (Subgroup.toAddSubgroup ((scalarGraphHom φ b).range)).map
                (prodCoordEquiv (K := K) (P := P)).symm.toAddMonoidHom := by
            rw [hrange]
      _ = scalarGraph (MonoidHom.toAdditiveLeft φ) b :=
            (scalarGraph_eq_coord_image (φ := φ) b).symm
  obtain ⟨σ, γ, α, β, c, hσ, hdecomp, hc, hβ, hγ⟩ :=
    exists_affine_of_graph_family
      (φ := MonoidHom.toAdditiveLeft φ) (hφ := hφ) (e := e)
      hR hRinv hfam
  exact ⟨σ, γ, α, β, c, hσ, hdecomp, hc, hβ, hγ⟩


variable {F P : Type*} [Field F] [AddGroup P]

theorem graph_block_intertwiner
    (φ : P →+ F) (hφ : Function.Injective φ)
    (α : P ≃+ P) (γ : F ≃+ F) (c : F ≃+ F)
    (h : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p))
    {s t : P} (hs : φ s ≠ 0) (ht : φ t ≠ 0) (hst : φ s ≠ φ t) :
    (φ t / φ s ≠ 0) ∧
      (φ t / φ s ≠ 1) ∧
      (φ (α s) ≠ 0) ∧
      (∀ a : F,
        c (a * (φ t / φ s)) = (φ (α t) / φ (α s)) * c a) := by
  classical
  have hs0 : s ≠ 0 := by
    intro h0
    exact hs (by simp [h0])
  have hαs : α s ≠ 0 := by
    intro h0
    apply hs0
    apply α.injective
    simpa using h0
  have hφαs : φ (α s) ≠ 0 := by
    intro h0
    exact hαs (hφ (by simpa using h0))
  have hz0 : φ t / φ s ≠ 0 := div_ne_zero ht hs
  have hz1 : φ t / φ s ≠ 1 := by
    intro hz
    apply hst
    have hmul : (φ t / φ s) * φ s = φ t := div_mul_cancel₀ (φ t) hs
    rw [hz, one_mul] at hmul
    exact hmul
  refine ⟨hz0, hz1, hφαs, ?_⟩
  intro a
  have harg : (a * (φ t / φ s)) * φ s = a * φ t := by
    rw [mul_assoc, div_mul_cancel₀ (φ t) hs]
  have hleft :
      c (a * (φ t / φ s)) * φ (α s) = c a * φ (α t) := by
    calc
      c (a * (φ t / φ s)) * φ (α s)
          = γ ((a * (φ t / φ s)) * φ s) := (h (a * (φ t / φ s)) s).symm
      _ = γ (a * φ t) := by rw [harg]
      _ = c a * φ (α t) := h a t
  calc
    c (a * (φ t / φ s))
        = (c (a * (φ t / φ s)) * φ (α s)) / φ (α s) :=
          (mul_div_cancel_right₀ _ hφαs).symm
    _ = (c a * φ (α t)) / φ (α s) := by rw [hleft]
    _ = (φ (α t) / φ (α s)) * c a := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring


section GammaSemilinear

variable [Algebra (ZMod 2) F]

theorem exists_unit_scalar_of_semilinear_graph_block
    {F P : Type*} [Field F] [AddGroup P]
    [Nontrivial P]
    (φ : P →+ F) (hφ : Function.Injective φ)
    (α : P ≃+ P) (γ c : F ≃+ F)
    (h : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p))
    (u : Fˣ) (σ : F ≃+* F)
    (hγ : ∀ x : F, γ x = (u : F) * σ x) :
    ∃ v : Fˣ, ∀ a : F, c a = (v : F) * σ a := by
  classical
  obtain ⟨p, hp0⟩ := exists_ne (0 : P)
  have hφp : φ p ≠ 0 := by
    intro h0
    apply hp0
    apply hφ
    simpa using h0
  have hαp : α p ≠ 0 := by
    intro h0
    apply hp0
    apply α.injective
    simpa using h0
  have hφαp : φ (α p) ≠ 0 := by
    intro h0
    exact hαp (hφ (by simpa using h0))
  let v0 : F := (u : F) * σ (φ p) / φ (α p)
  have hv0 : v0 ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero (Units.ne_zero u) ((map_ne_zero σ).2 hφp)
    · exact hφαp
  refine ⟨Units.mk0 v0 hv0, ?_⟩
  intro a
  rw [Units.val_mk0]
  have h0 := h a p
  rw [hγ (a * φ p)] at h0
  rw [map_mul] at h0
  calc
    c a = (c a * φ (α p)) / φ (α p) :=
      (mul_div_cancel_right₀ (c a) hφαp).symm
    _ = ((u : F) * (σ a * σ (φ p))) / φ (α p) := by rw [← h0]
    _ = ((u : F) * σ (φ p) / φ (α p)) * σ a := by
      rw [div_mul_eq_mul_div₀]
      apply congrArg (fun z : F => z / φ (α p))
      ring

theorem c_ne_refl_of_charTwo_semilinear_graph_block
    {F P : Type*} [Field F] [AddGroup P]
    [CharP F 2] [Nontrivial P]
    (φ : P →+ F) (hφ : Function.Injective φ)
    (α : P ≃+ P) (γ c : F ≃+ F)
    (h : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p))
    (u : Fˣ) (σ : F ≃+* F)
    (hγ : ∀ x : F, γ x = (u : F) * σ x)
    (hγ2 : ∀ x : F, γ (γ x) = x)
    (hγ_ne : γ ≠ AddEquiv.refl F) :
    c ≠ AddEquiv.refl F := by
  obtain ⟨v, hv⟩ :=
    exists_unit_scalar_of_semilinear_graph_block φ hφ α γ c h u σ hγ
  intro hc
  have hv1 : (v : F) = 1 := by
    have hc1 : c 1 = 1 := by
      rw [hc]
      simp
    have h1 := hv 1
    rw [hc1] at h1
    simpa using h1.symm
  have hσ : ∀ a : F, σ a = a := by
    intro a
    have hca : c a = a := by
      rw [hc]
      simp
    have h1 := hv a
    rw [hca] at h1
    simpa [hv1] using h1.symm
  have hγ_scalar : ∀ x : F, γ x = (u : F) * x := by
    intro x
    rw [hγ x, hσ x]
  have hu2 : (u : F) ^ 2 = 1 := by
    have h1 := hγ2 1
    have hγ1 : γ 1 = (u : F) := by
      simpa using hγ_scalar 1
    have hγu : γ (u : F) = (u : F) ^ 2 := by
      simpa [pow_two] using hγ_scalar (u : F)
    rw [hγ1, hγu] at h1
    simpa [pow_two] using h1
  have hu1 : (u : F) = 1 := by
    exact CharTwo.sq_inj.mp (by simpa using hu2)
  have hγ_eq : γ = AddEquiv.refl F := by
    ext x
    rw [hγ_scalar x, hu1]
    simp
  exact hγ_ne hγ_eq

theorem semilinear_of_scalar_block
    (γ : F ≃+ F) (c : F ≃+ F) (κ : F ≃ₐ[ZMod 2] F)
    {K : Set F} {x y : F} (hx : x ≠ 0)
    (h : ∀ a : F, γ (a * x) = c a * y)
    (hc : ∀ ell ∈ K, ∀ a : F, c (a * ell) = κ ell * c a) :
    ∀ ell ∈ K, ∀ a : F, γ (a * ell) = κ ell * γ a := by
  intro ell hell a
  have h1 : γ (a * ell) = c ((a / x) * ell) * y := by
    calc
      γ (a * ell) = γ (((a / x) * ell) * x) := by
        rw [mul_assoc, mul_comm ell x, ← mul_assoc, div_mul_cancel₀ a hx]
      _ = c ((a / x) * ell) * y := h ((a / x) * ell)
  have h2 : γ a = c (a / x) * y := by
    calc
      γ a = γ ((a / x) * x) := by rw [div_mul_cancel₀ a hx]
      _ = c (a / x) * y := h (a / x)
  rw [h1, h2]
  rw [hc ell hell (a / x)]
  ring

theorem gamma_semilinear_on_adjoin
    (φ : P →+ F) (α : P ≃+ P) (γ : F ≃+ F) (c : F ≃+ F)
    (h : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p))
    (κ : F ≃ₐ[ZMod 2] F)
    {s t : P} (hs : φ s ≠ 0)
    (hc : ∀ ell ∈ Algebra.adjoin (ZMod 2) ({φ t / φ s} : Set F), ∀ a : F,
      c (a * ell) = κ ell * c a) :
    ∀ ell ∈ Algebra.adjoin (ZMod 2) ({φ t / φ s} : Set F), ∀ a : F,
      γ (a * ell) = κ ell * γ a := by
  exact semilinear_of_scalar_block γ c κ hs (fun a => h a s) hc

end GammaSemilinear

section GeneratedField

variable [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]

theorem natDegree_minpoly_eq_two_or_four
    (hfin : Module.finrank (ZMod 2) F = 4)
    (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    (minpoly (ZMod 2) z).natDegree = 2 ∨
      (minpoly (ZMod 2) z).natDegree = 4 := by
  have hzi : IsIntegral (ZMod 2) z := IsIntegral.of_finite (ZMod 2) z
  have hdvd_finrank :
      (minpoly (ZMod 2) z).natDegree ∣ Module.finrank (ZMod 2) F :=
    minpoly.degree_dvd (x := z) hzi
  have hdvd : (minpoly (ZMod 2) z).natDegree ∣ 4 := by
    simpa [hfin] using hdvd_finrank
  have hz_not_range : z ∉ Set.range (algebraMap (ZMod 2) F) := by
    rintro ⟨r, hr⟩
    have htwo : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide +kernel
    rcases htwo r with rfl | rfl
    · exact hz0 (by simpa using hr.symm)
    · exact hz1 (by simpa using hr.symm)
  have htwo : 2 ≤ (minpoly (ZMod 2) z).natDegree :=
    (minpoly.two_le_natDegree_iff hzi).mpr hz_not_range
  have hdvd' : (minpoly (ZMod 2) z).natDegree ∣ 2 ^ 2 := by
    simpa using hdvd
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
  rw [hk_eq] at htwo ⊢
  interval_cases k <;> simp_all

theorem card_intermediateField_adjoin_eq_four_of_natDegree_eq_two
    (z : F) (hdeg : (minpoly (ZMod 2) z).natDegree = 2) :
    Nat.card (IntermediateField.adjoin (ZMod 2) ({z} : Set F)) = 4 := by
  let K : IntermediateField (ZMod 2) F :=
    IntermediateField.adjoin (ZMod 2) ({z} : Set F)
  have hzi : IsIntegral (ZMod 2) z := IsIntegral.of_finite (ZMod 2) z
  haveI : FiniteDimensional (ZMod 2) K := by
    dsimp [K]
    exact IntermediateField.adjoin.finiteDimensional hzi
  have hfin : Module.finrank (ZMod 2) K = 2 := by
    dsimp [K]
    rw [IntermediateField.adjoin.finrank hzi, hdeg]
  have hcard : Nat.card K = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K), hfin, Nat.card_zmod]
    norm_num
  simpa [K] using hcard

theorem algebra_adjoin_eq_top_of_natDegree_eq_four
    (hfin : Module.finrank (ZMod 2) F = 4)
    (z : F) (hdeg : (minpoly (ZMod 2) z).natDegree = 4) :
    Algebra.adjoin (ZMod 2) ({z} : Set F) = ⊤ := by
  let K : IntermediateField (ZMod 2) F :=
    IntermediateField.adjoin (ZMod 2) ({z} : Set F)
  have hzi : IsIntegral (ZMod 2) z := IsIntegral.of_finite (ZMod 2) z
  haveI : FiniteDimensional (ZMod 2) K := by
    dsimp [K]
    exact IntermediateField.adjoin.finiteDimensional hzi
  have hfinK : Module.finrank (ZMod 2) K = 4 := by
    dsimp [K]
    rw [IntermediateField.adjoin.finrank hzi, hdeg]
  have hfinF : Module.finrank (ZMod 2) F = 4 := hfin
  have hsub : K.toSubalgebra.toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank (ZMod 2) K = Module.finrank (ZMod 2) F
    rw [hfinK, hfinF]
  have hKtop : K = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    apply Subalgebra.toSubmodule_injective
    simpa using hsub
  exact Algebra.adjoin_eq_top_of_primitive_element
    (IsAlgebraic.of_finite (ZMod 2) z) (by simpa [K] using hKtop)

theorem card_adjoin_eq_four_or_algebra_adjoin_eq_top
    (hfin : Module.finrank (ZMod 2) F = 4)
    (z : F) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    Nat.card (IntermediateField.adjoin (ZMod 2) ({z} : Set F)) = 4 ∨
      Algebra.adjoin (ZMod 2) ({z} : Set F) = ⊤ := by
  rcases natDegree_minpoly_eq_two_or_four hfin z hz0 hz1 with hdeg | hdeg
  · exact Or.inl (card_intermediateField_adjoin_eq_four_of_natDegree_eq_two z hdeg)
  · exact Or.inr (algebra_adjoin_eq_top_of_natDegree_eq_four hfin z hdeg)

end GeneratedField


section PolynomialIntertwining

open Polynomial

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

theorem eval₂_intertwiner
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a) :
    ∀ (p : (ZMod 2)[X]) (a : F),
      c (a * Polynomial.eval₂ (algebraMap (ZMod 2) F) z p) =
        Polynomial.eval₂ (algebraMap (ZMod 2) F) η p * c a := by
  intro p
  refine Polynomial.induction_on p ?_ ?_ ?_
  ·
    intro r a
    rw [Polynomial.eval₂_C, Polynomial.eval₂_C]
    have htwo : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide +kernel
    rcases htwo r with rfl | rfl
    · rw [map_zero, mul_zero, map_zero, zero_mul]
    · rw [map_one, mul_one, one_mul]
  ·
    intro p q hp hq a
    rw [Polynomial.eval₂_add, mul_add, c.map_add, hp a, hq a, Polynomial.eval₂_add, add_mul]
  ·
    intro n r ih a
    have hz :
        Polynomial.eval₂ (algebraMap (ZMod 2) F) z
            (Polynomial.C r * Polynomial.X ^ (n + 1)) =
          Polynomial.eval₂ (algebraMap (ZMod 2) F) z
              (Polynomial.C r * Polynomial.X ^ n) * z := by
      rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul_X]
    have hη :
        Polynomial.eval₂ (algebraMap (ZMod 2) F) η
            (Polynomial.C r * Polynomial.X ^ (n + 1)) =
          Polynomial.eval₂ (algebraMap (ZMod 2) F) η
              (Polynomial.C r * Polynomial.X ^ n) * η := by
      rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul_X]
    rw [hz, hη]
    calc
      c (a * (Polynomial.eval₂ (algebraMap (ZMod 2) F) z
            (Polynomial.C r * Polynomial.X ^ n) * z)) =
          c ((a * Polynomial.eval₂ (algebraMap (ZMod 2) F) z
            (Polynomial.C r * Polynomial.X ^ n)) * z) := by
            rw [mul_assoc]
      _ = η * c (a * Polynomial.eval₂ (algebraMap (ZMod 2) F) z
            (Polynomial.C r * Polynomial.X ^ n)) :=
            h (a * Polynomial.eval₂ (algebraMap (ZMod 2) F) z
              (Polynomial.C r * Polynomial.X ^ n))
      _ = η * (Polynomial.eval₂ (algebraMap (ZMod 2) F) η
            (Polynomial.C r * Polynomial.X ^ n) * c a) := by
            rw [ih a]
      _ = (Polynomial.eval₂ (algebraMap (ZMod 2) F) η
            (Polynomial.C r * Polynomial.X ^ n) * η) * c a := by
            ring

theorem eval₂_eq_zero_iff
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a) :
    ∀ p : (ZMod 2)[X],
      Polynomial.eval₂ (algebraMap (ZMod 2) F) z p = 0 ↔
        Polynomial.eval₂ (algebraMap (ZMod 2) F) η p = 0 := by
  intro p
  have hc1 : c 1 ≠ 0 := by
    intro h1
    exact one_ne_zero (c.injective (by simpa [c.map_zero] using h1))
  have hk := eval₂_intertwiner z η c h p 1
  rw [one_mul] at hk
  constructor
  · intro hz
    rw [hz, c.map_zero] at hk
    exact (mul_eq_zero.mp hk.symm).resolve_right hc1
  · intro hη
    rw [hη, zero_mul] at hk
    exact c.injective (by simpa [c.map_zero] using hk)

theorem minpoly_eq_of_eval₂_eq_zero_iff
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a)
    (hzi : IsIntegral (ZMod 2) z) (hηi : IsIntegral (ZMod 2) η) :
    minpoly (ZMod 2) z = minpoly (ZMod 2) η := by
  have hzroot :
      Polynomial.eval₂ (algebraMap (ZMod 2) F) z (minpoly (ZMod 2) z) = 0 := by
    simpa [Polynomial.aeval_def] using minpoly.aeval (ZMod 2) z
  have hηroot : Polynomial.aeval η (minpoly (ZMod 2) z) = 0 := by
    rw [Polynomial.aeval_def]
    exact (eval₂_eq_zero_iff z η c h (minpoly (ZMod 2) z)).mp hzroot
  exact minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible hzi) hηroot (minpoly.monic hzi)

theorem exists_frobenius_algEquiv_of_eval₂_eq_zero_iff
    [FiniteDimensional (ZMod 2) F]
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a)
    (hzi : IsIntegral (ZMod 2) z) (hηi : IsIntegral (ZMod 2) η) :
    ∃ σ : F ≃ₐ[ZMod 2] F, σ z = η := by
  have hmin := minpoly_eq_of_eval₂_eq_zero_iff z η c h hzi hηi
  have hmem :
      η ∈ MulAction.orbit
        (Subgroup.zpowers
          (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F)) z :=
    (TauCeti.FiniteField.mem_orbit_iff_minpoly_eq (ZMod 2)).mpr hmin.symm
  obtain ⟨g, hg⟩ := hmem
  exact ⟨(g : F ≃ₐ[ZMod 2] F), by
    simpa [Subgroup.smul_def, AlgEquiv.smul_def] using hg⟩

theorem semilinear_on_adjoin
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a)
    (σ : F ≃ₐ[ZMod 2] F) (hσ : σ z = η) :
    ∀ ell ∈ Algebra.adjoin (ZMod 2) ({z} : Set F), ∀ a : F,
      c (a * ell) = σ ell * c a := by
  intro ell hell a
  obtain ⟨p, hp⟩ :=
    Algebra.adjoin_mem_exists_aeval (R := ZMod 2) (x := z) hell
  have hσeval : Polynomial.aeval η p = σ (Polynomial.aeval z p) := by
    rw [← hσ]
    exact Polynomial.aeval_algHom_apply σ z p
  have hk := eval₂_intertwiner z η c h p a
  have hk' : c (a * Polynomial.aeval z p) = Polynomial.aeval η p * c a := by
    simpa [Polynomial.aeval_def] using hk
  rw [hσeval, hp] at hk'
  exact hk'

theorem exists_semilinear_on_adjoin
    [FiniteDimensional (ZMod 2) F]
    (z η : F) (c : F ≃+ F)
    (h : ∀ a : F, c (a * z) = η * c a)
    (hzi : IsIntegral (ZMod 2) z) (hηi : IsIntegral (ZMod 2) η) :
    ∃ σ : F ≃ₐ[ZMod 2] F,
      σ z = η ∧
      ∀ ell ∈ Algebra.adjoin (ZMod 2) ({z} : Set F), ∀ a : F,
        c (a * ell) = σ ell * c a := by
  obtain ⟨σ, hσ⟩ :=
    exists_frobenius_algEquiv_of_eval₂_eq_zero_iff z η c h hzi hηi
  exact ⟨σ, hσ, semilinear_on_adjoin z η c h σ hσ⟩


theorem exists_semilinear_on_adjoin_of_graph_blocks
    [FiniteDimensional (ZMod 2) F]
    {P : Type*} [AddGroup P]
    (φ : P →+ F) (hφ : Function.Injective φ)
    (α : P ≃+ P) (γ : F ≃+ F) (c : F ≃+ F)
    (h : ∀ (a : F) (p : P), γ (a * φ p) = c a * φ (α p))
    {s t : P} (hs : φ s ≠ 0) (ht : φ t ≠ 0) (hst : φ s ≠ φ t) :
    ∃ κ : F ≃ₐ[ZMod 2] F,
      κ (φ t / φ s) = φ (α t) / φ (α s) ∧
      ∀ ell ∈ Algebra.adjoin (ZMod 2) ({φ t / φ s} : Set F), ∀ a : F,
        c (a * ell) = κ ell * c a := by
  obtain ⟨-, -, -, hinter⟩ := graph_block_intertwiner φ hφ α γ c h hs ht hst
  exact exists_semilinear_on_adjoin _ _ c hinter
    (IsIntegral.of_finite (ZMod 2) _) (IsIntegral.of_finite (ZMod 2) _)

end PolynomialIntertwining


section RootFixedShears

variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Nontrivial P]

theorem exists_shear_of_root_fixed_pow
    (φ : P →+ F) (hφ : Function.Injective φ)
    (e : (F × P) ≃+ (F × P))
    (hroot : ∀ r : F, e (r, 0) = (r, 0))
    (hfam : ∀ a : F, ∃ b : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ b)
    (n : ℕ) (hpow : ∀ v : F × P, (e^[2 ^ n]) v = v) :
    ∃ b : F, ∀ (r : F) (p : P), e (r, p) = (r + b * φ p, p) := by
  classical
  have hR : ∀ r : F, (e (r, 0)).2 = 0 := by
    intro r
    rw [hroot r]
  have hRinv : ∀ r : F, (e.symm (r, 0)).2 = 0 := by
    intro r
    have h : e.symm (r, 0) = (r, 0) := by
      simpa using (congrArg e.symm (hroot r)).symm
    rw [h]
  obtain ⟨σ, γ, α, β, c, hσ, hdecomp, hc, hβ, hγ⟩ :=
    exists_affine_of_graph_family φ hφ e hR hRinv hfam
  have hgamma : ∀ r : F, γ r = r := by
    intro r
    have h := congrArg Prod.fst (hdecomp r 0)
    rw [hroot r] at h
    simpa using h.symm
  let k : F := σ 1 - σ 0
  have hk_ne : k ≠ 0 := by
    intro hk0
    have h10 : (1 : F) = 0 := c.injective (by
      calc
        c 1 = k := hc 1
        _ = 0 := hk0
        _ = c 0 := (map_zero c).symm)
    exact one_ne_zero h10
  have halpha_scalar : ∀ p : P, φ (α p) = k⁻¹ * φ p := by
    intro p
    have h1 : φ p = k * φ (α p) := by
      simpa [k, hgamma] using hγ 1 p
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hk_ne, one_mul]
  have halpha_iter : ∀ (m : ℕ) (p : P),
      φ ((α^[m]) p) = (k⁻¹) ^ m * φ p := by
    intro m
    induction m with
    | zero =>
        intro p
        simp
    | succ m ih =>
        intro p
        rw [Function.iterate_succ_apply', halpha_scalar, ih]
        ring
  have hiter : ∀ (m : ℕ) (r : F) (p : P),
      ((e^[m]) (r, p)).2 = (α^[m]) p := by
    intro m
    induction m with
    | zero =>
        intro r p
        simp
    | succ m ih =>
        intro r p
        rw [Function.iterate_succ_apply']
        rcases hx : (e^[m]) (r, p) with ⟨r', p'⟩
        have hp' : p' = (α^[m]) p := by
          simpa [hx] using ih r p
        simpa [hdecomp, hp', Function.iterate_succ_apply']
  have halpha_pow : ∀ p : P, (α^[2 ^ n]) p = p := by
    intro p
    have h := hiter (2 ^ n) 0 p
    rw [hpow (0, p)] at h
    simpa using h.symm
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h0
    exact hp0 (hφ (by simpa using h0))
  have hscalarPow : (k⁻¹) ^ (2 ^ n) = 1 := by
    have h := halpha_iter (2 ^ n) p0
    rw [halpha_pow p0] at h
    have h' : (k⁻¹) ^ (2 ^ n) * φ p0 = 1 * φ p0 := by
      simpa using h.symm
    exact mul_right_cancel₀ hφp0 h'
  have hscalarOne : k⁻¹ = 1 := by
    have hinj : Function.Injective (fun x : F => x ^ (2 ^ n)) := by
      intro x y hxy
      apply (iterateFrobenius_inj F 2 n)
      simpa only [iterateFrobenius_def] using hxy
    exact hinj (by simpa using hscalarPow)
  have halpha_id : α = AddEquiv.refl P := by
    ext p
    have h := halpha_scalar p
    rw [hscalarOne, one_mul] at h
    simpa using hφ h
  have hc_id : ∀ a : F, c a = a := by
    intro a
    have h := hγ a p0
    rw [← hc a] at h
    have h' : a * φ p0 = c a * φ p0 := by
      simpa [hgamma, halpha_id] using h
    exact (mul_right_cancel₀ hφp0 h').symm
  have hσ_eq : ∀ a : F, σ a = a + σ 0 := by
    intro a
    have h := hc_id a
    rw [hc a] at h
    exact sub_eq_iff_eq_add.mp h
  refine ⟨σ 0, ?_⟩
  intro r p
  have hbeta : β p = σ 0 * φ p := by
    simpa [halpha_id] using hβ p
  rw [hdecomp r p, hgamma r, hbeta, halpha_id]
  simp


end RootFixedShears

theorem coordinateAddEquiv_iterate
    {K P W : Type*} [Field K] [Group P] [Group W]
    (eW : W ≃* (Multiplicative K × P)) (τ : MulAut W) (m : ℕ) :
    (coordinateAddEquiv eW τ)^[m] = coordinateAddEquiv eW (τ ^ m) := by
  induction m with
  | zero =>
      funext x
      rcases x with ⟨r, p⟩
      simp [coordinateAddEquiv_apply]
  | succ m ih =>
      funext x
      rw [Function.iterate_succ_apply', ih]
      rcases x with ⟨r, p⟩
      simp [coordinateAddEquiv_apply, pow_succ', MulAut.mul_apply]



section CoordinateComposition

variable {K P W : Type*} [Field K] [Group P] [Group W]

theorem coordinateAddEquiv_one
    (eW : W ≃* (Multiplicative K × P)) :
    coordinateAddEquiv eW (1 : MulAut W) = AddEquiv.refl _ := by
  apply AddEquiv.ext
  intro x
  rcases x with ⟨r, p⟩
  simp [coordinateAddEquiv_apply]

theorem coordinateAddEquiv_mul_apply
    (eW : W ≃* (Multiplicative K × P)) (τ υ : MulAut W) (x : K × Additive P) :
    coordinateAddEquiv eW (τ * υ) x =
      coordinateAddEquiv eW τ (coordinateAddEquiv eW υ x) := by
  rcases x with ⟨r, p⟩
  simp [coordinateAddEquiv_apply, MulAut.mul_apply]

theorem coordinateAddEquiv_mul_toAddMonoidHom
    (eW : W ≃* (Multiplicative K × P)) (τ υ : MulAut W) :
    (coordinateAddEquiv eW (τ * υ)).toAddMonoidHom =
      (coordinateAddEquiv eW τ).toAddMonoidHom.comp
        (coordinateAddEquiv eW υ).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact coordinateAddEquiv_mul_apply eW τ υ x


end CoordinateComposition

section TranslationCubes

variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Finite P]

theorem cube_shear_of_graph_translation
    (hPcard : Nat.card P = 4)
    (φ : P →+ F) (hφ : Function.Injective φ)
    (e : (F × P) ≃+ (F × P))
    (hR : ∀ r : F, (e (r, 0)).2 = 0)
    (hRinv : ∀ r : F, (e.symm (r, 0)).2 = 0)
    (b : F)
    (hshift : ∀ a : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ (a + b)) :
    ∀ (r : F) (p : P),
      (e^[3]) (r, p) = (r + b * φ p, p) := by
  classical
  have hPone : 1 < Nat.card P := by rw [hPcard]; norm_num
  haveI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hPone
  have hfam : ∀ a : F, ∃ c : F,
      (scalarGraph φ a).map e.toAddMonoidHom = scalarGraph φ c :=
    fun a => ⟨a + b, hshift a⟩
  obtain ⟨σ, γ, α, β, c, hσ, hdecomp, hc, hβ, hγ⟩ :=
    exists_affine_of_graph_family φ hφ e hR hRinv hfam
  have hσ_eq : ∀ a : F, σ a = a + b := by
    intro a
    apply scalarGraph_injective φ hφ
    rw [← hσ a, hshift a]
  have hc_id : ∀ a : F, c a = a := by
    intro a
    rw [hc a, hσ_eq a, hσ_eq 0]
    simp
  have hγ' : ∀ (a : F) (p : P),
      γ (a * φ p) = a * φ (α p) := by
    intro a p
    calc
      γ (a * φ p) = (σ a - σ 0) * φ (α p) := hγ a p
      _ = a * φ (α p) := by rw [hσ_eq a, hσ_eq 0]; simp
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h0
    exact hp0 (hφ (by simpa using h0))
  have hαp0 : α p0 ≠ 0 := by
    intro h0
    exact hp0 (α.injective (by simpa [map_zero α] using h0))
  have hφαp0 : φ (α p0) ≠ 0 := by
    intro h0
    exact hαp0 (hφ (by simpa using h0))
  let lam : F := φ (α p0) / φ p0
  have hlam_ne : lam ≠ 0 := div_ne_zero hφαp0 hφp0
  have hγ_lam : ∀ r : F, γ r = lam * r := by
    intro r
    have h := hγ' (r / φ p0) p0
    rw [div_mul_cancel₀ r hφp0] at h
    rw [h]
    dsimp [lam]
    field_simp [hφp0]
  have hφα_lam : ∀ p : P, φ (α p) = lam * φ p := by
    intro p
    calc
      φ (α p) = γ (φ p) := by simpa using (hγ' 1 p).symm
      _ = lam * φ p := hγ_lam (φ p)
  have hσ0 : σ 0 = b := by
    rw [hσ_eq 0]
    simp
  have hβ_b : ∀ p : P, β p = b * lam * φ p := by
    intro p
    rw [hβ p, hσ0, hφα_lam p]
    ring
  have he_formula : ∀ (r : F) (p : P),
      e (r, p) = (lam * r + b * lam * φ p, α p) := by
    intro r p
    rw [hdecomp r p, hγ_lam r, hβ_b p]
  let Pne := {p : P // p ≠ 0}
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype Pne := Fintype.ofFinite Pne
  have hcard_ne : Fintype.card Pne = 3 := by
    have hcardP : Fintype.card P = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hPcard
    have h := Fintype.card_subtype_compl (fun p : P => p = 0)
    have hzero : Fintype.card {p : P // p = 0} = 1 :=
      Fintype.card_subtype_eq (0 : P)
    rw [hzero, hcardP] at h
    simpa [Pne] using h
  let αn : Pne ≃ Pne :=
    { toFun := fun p => ⟨α p.1, by
        intro hzero
        exact p.2 (α.injective (by simpa using hzero))⟩
      invFun := fun p => ⟨α.symm p.1, by
        intro hzero
        exact p.2 (α.symm.injective (by simpa using hzero))⟩
      left_inv := fun p => Subtype.ext (α.symm_apply_apply p.1)
      right_inv := fun p => Subtype.ext (α.apply_symm_apply p.1) }
  have hprod_alpha :
      (∏ p : Pne, φ (α p.1)) = ∏ p : Pne, φ p.1 := by
    simpa [αn] using Equiv.prod_comp αn (fun p : Pne => φ p.1)
  have hprod_lambda :
      (∏ p : Pne, φ (α p.1)) = ∏ p : Pne, (φ p.1 * lam) := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hφα_lam p.1, mul_comm]
  have hprod_lam :
      (∏ p : Pne, (φ p.1 * lam)) =
        (∏ p : Pne, φ p.1) * lam ^ 3 := by
    have h := Finset.prod_mul_pow_card
      (s := (Finset.univ : Finset Pne))
      (f := fun p : Pne => φ p.1) (b := lam)
    rw [Finset.card_univ, hcard_ne] at h
    simpa using h.symm
  have hφ_ne : ∀ p : P, p ≠ 0 → φ p ≠ 0 := by
    intro p hp h0
    exact hp (hφ (by simpa using h0))
  have hprod_ne : (∏ p : Pne, φ p.1) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hφ_ne p.1 p.2
  have hprod_eq :
      (∏ p : Pne, φ p.1) = (∏ p : Pne, φ p.1) * lam ^ 3 := by
    calc
      (∏ p : Pne, φ p.1) = ∏ p : Pne, φ (α p.1) := hprod_alpha.symm
      _ = ∏ p : Pne, (φ p.1 * lam) := hprod_lambda
      _ = (∏ p : Pne, φ p.1) * lam ^ 3 := hprod_lam
  have hlam3 : lam ^ 3 = 1 := by
    have h' : (∏ p : Pne, φ p.1) * 1 =
        (∏ p : Pne, φ p.1) * lam ^ 3 := by
      simpa using hprod_eq
    exact (mul_left_cancel₀ hprod_ne h').symm
  have hαiter : ∀ (n : ℕ) (p : P),
      φ ((α^[n]) p) = lam ^ n * φ p := by
    intro n
    induction n with
    | zero =>
        intro p
        simp
    | succ n ih =>
        intro p
        rw [Function.iterate_succ_apply', hφα_lam, ih, pow_succ']
        ring
  have hα3 : ∀ p : P, (α^[3]) p = p := by
    intro p
    apply hφ
    rw [hαiter 3 p, hlam3]
    simp
  have hα3n : ∀ p : P, α (α (α p)) = p := by
    intro p
    simpa [Function.iterate_succ_apply'] using hα3 p
  have hlamlamlam : lam * lam * lam = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using hlam3
  have hthree : (3 : F) = 1 := by
    calc
      (3 : F) = 1 + 1 + 1 := by ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, zero_add]
  intro r p
  change e (e (e (r, p))) = (r + b * φ p, p)
  rw [he_formula, he_formula, he_formula]
  simp [hγ_lam, hβ_b, hφα_lam, hα3n, hlam3, hlamlamlam, pow_succ, mul_add, add_mul,
    add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  try ring_nf
  all_goals simp [hlam3, hthree]

end TranslationCubes


end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction

variable {V : Type*} [AddGroup V] [Finite V]
variable {A : Subgroup (Equiv.Perm V)}

theorem ker_apply_eq_add_zero
    (ρ : A →* Equiv.Perm V)
    (haff : ∀ (a : A) (v : V),
      (a : Equiv.Perm V) v = ρ a v + (a : Equiv.Perm V) 0)
    {a : A} (ha : a ∈ ρ.ker) (v : V) :
    (a : Equiv.Perm V) v = v + (a : Equiv.Perm V) 0 := by
  rw [haff a v, MonoidHom.mem_ker.mp ha]
  rfl

theorem ker_translations_surjective_of_singer
    (ρ : A →* Equiv.Perm V)
    (haff : ∀ (a : A) (v : V),
      (a : Equiv.Perm V) v = ρ a v + (a : Equiv.Perm V) 0)
    (hker : 1 < Nat.card ρ.ker)
    (t : A) (ht0 : (t : Equiv.Perm V) 0 = 0)
    (mu : Equiv.Perm V) (hmu : ∀ v : V, (t : Equiv.Perm V) v = mu v)
    (hμtrans : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      ∃ n : ℕ, (mu ^ n) v = w) :
    ∀ b : V, ∃ k : ρ.ker,
      ∀ v : V, ((k : A) : Equiv.Perm V) v = v + b := by
  classical
  have hρt : ρ t = mu := by
    ext v
    have h := haff t v
    rw [ht0, add_zero] at h
    rw [← h, hmu v]
  haveI : Nontrivial ρ.ker := Finite.one_lt_card_iff_nontrivial.mp hker
  obtain ⟨a, ha1⟩ := exists_ne (1 : ρ.ker)
  have ha0_ne : ((a : A) : Equiv.Perm V) 0 ≠ 0 := by
    intro h0
    apply ha1
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro v
    rw [ker_apply_eq_add_zero ρ haff a.2 v, h0, add_zero]
    simp
  have htpow : ∀ (m : ℕ) (v : V),
      (((t : A) : Equiv.Perm V) ^ m) v = (mu ^ m) v := by
    intro m
    induction m with
    | zero =>
        intro v
        simp
    | succ m ih =>
        intro v
        simp [pow_succ', Equiv.Perm.mul_apply, ih, hmu]
  have hmu0 : mu 0 = 0 := by
    rw [← hmu 0, ht0]
  have hmupow0 : ∀ m : ℕ, (mu ^ m) 0 = 0 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, ih, hmu0]
  have htpow0 : ∀ m : ℕ, (((t : A) : Equiv.Perm V) ^ m) 0 = 0 := by
    intro m
    rw [htpow m 0]
    exact hmupow0 m
  have htinv0 : ∀ m : ℕ,
      ((((t : A) : Equiv.Perm V) ^ m)⁻¹ : Equiv.Perm V) 0 = 0 := by
    intro m
    let p : Equiv.Perm V := ((t : A) : Equiv.Perm V) ^ m
    have hp : p 0 = 0 := by simpa [p] using htpow0 m
    have h := congrArg (fun x : V => p⁻¹ x) hp
    simpa [p] using h.symm
  intro b
  by_cases hb : b = 0
  · subst b
    refine ⟨1, ?_⟩
    intro v
    simp
  · let n : ℕ := Classical.choose (hμtrans (((a : A) : Equiv.Perm V) 0) b ha0_ne hb)
    have hn : (mu ^ n) (((a : A) : Equiv.Perm V) 0) = b :=
      Classical.choose_spec (hμtrans (((a : A) : Equiv.Perm V) 0) b ha0_ne hb)
    let c : A := t ^ n * (a : A) * (t ^ n)⁻¹
    have hc_ker : c ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      have hc_eq : ρ c =
          (ρ t) ^ n * ρ (a : A) * ((ρ t) ^ n)⁻¹ := by
        simp [c, map_mul, map_pow, map_inv]
      rw [hc_eq, hρt, MonoidHom.mem_ker.mp a.2]
      simp
    have hc0 : (c : Equiv.Perm V) 0 = b := by
      have hc_apply : (c : Equiv.Perm V) 0 =
          (((t : A) : Equiv.Perm V) ^ n) (((a : A) : Equiv.Perm V) 0) := by
        simp [c, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv,
          Equiv.Perm.mul_apply, htinv0]
      calc
        (c : Equiv.Perm V) 0
            = (((t : A) : Equiv.Perm V) ^ n) (((a : A) : Equiv.Perm V) 0) :=
              hc_apply
        _ = (mu ^ n) (((a : A) : Equiv.Perm V) 0) := htpow n _
        _ = b := hn
    refine ⟨⟨c, hc_ker⟩, ?_⟩
    intro v
    change (c : Equiv.Perm V) v = v + b
    rw [ker_apply_eq_add_zero ρ haff hc_ker v, hc0]



end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction

theorem affine_image_translation_surjective
    {F4 H : Type} [Field F4] [Finite F4] [Group H] [Finite H]
    (hFcard : Nat.card F4 = 16)
    (sigma rho : H →* Equiv.Perm F4)
    (rhoBar : sigma.range →* Equiv.Perm F4)
    (hcomp : rhoBar.comp sigma.rangeRestrict = rho)
    (haff : ∀ (h : H) (v : F4),
      sigma h v = rho h v + sigma h 0)
    (hzero : ∀ a : F4, ∃ h : H, sigma h 0 = a)
    (tau : H) (μ : F4ˣ) (hμ : orderOf μ = 15)
    (htau : ∀ a : F4, sigma tau a = (μ : F4) * a)
    (h2Lin : (Nat.card rho.range).factorization 2 ≤ 3) :
    ∀ b : F4, ∃ h : H, ∀ a : F4, sigma h a = a + b := by
  classical
  have hρrange : rho.range = rhoBar.range := by
    rw [← hcomp]
    rw [MonoidHom.range_comp]
    rw [MonoidHom.range_eq_top_of_surjective _
      (MonoidHom.rangeRestrict_surjective sigma)]
    rw [Subgroup.map_top]
  let Gamma : Subgroup (Equiv.Perm F4) := sigma.range
  letI : Fintype F4 := Fintype.ofFinite F4
  letI : Fintype Gamma := Fintype.ofFinite Gamma
  letI : MulAction Gamma F4 := MulAction.compHom F4 (Subgroup.subtype Gamma)
  have h16dvdGamma : 16 ∣ Nat.card Gamma := by
    let v0 : F4 := 0
    letI : Fintype (MulAction.orbit Gamma v0) := Fintype.ofFinite _
    letI : Fintype (MulAction.stabilizer Gamma v0) := Fintype.ofFinite _
    have horbit_univ : MulAction.orbit Gamma v0 = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      obtain ⟨h, hh⟩ := hzero a
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨sigma h, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩, hh⟩
    have hcardorbit : Fintype.card (MulAction.orbit Gamma v0) = 16 := by
      rw [← Nat.card_eq_fintype_card]
      rw [horbit_univ]
      rw [Nat.card_congr (Equiv.Set.univ F4)]
      exact hFcard
    refine ⟨Fintype.card (MulAction.stabilizer Gamma v0), ?_⟩
    calc
      Nat.card Gamma = Fintype.card Gamma := by rw [Nat.card_eq_fintype_card]
      _ = Fintype.card (MulAction.orbit Gamma v0) *
            Fintype.card (MulAction.stabilizer Gamma v0) :=
          (MulAction.card_orbit_mul_card_stabilizer_eq_card_group
            (G := Gamma) v0).symm
      _ = 16 * Fintype.card (MulAction.stabilizer Gamma v0) := by
          rw [hcardorbit]
  have hker_gt1 : 1 < Nat.card rhoBar.ker := by
    by_contra hnot
    have hker_le1 : Nat.card rhoBar.ker ≤ 1 := Nat.le_of_not_gt hnot
    have hker_pos : 0 < Nat.card rhoBar.ker := Nat.card_pos
    have hker_one : Nat.card rhoBar.ker = 1 := by omega
    have hbot : rhoBar.ker = ⊥ := Subgroup.eq_bot_of_card_eq rhoBar.ker hker_one
    have hinj : Function.Injective rhoBar :=
      (MonoidHom.ker_eq_bot_iff rhoBar).mp hbot
    have hdvd : Nat.card Gamma ∣ Nat.card rhoBar.range :=
      Subgroup.card_dvd_of_injective rhoBar.rangeRestrict
        (fun a b hab => hinj (congrArg Subtype.val hab))
    have h16range : 16 ∣ Nat.card rhoBar.range :=
      h16dvdGamma.trans hdvd
    have h16rho : 16 ∣ Nat.card rho.range := by
      simpa [hρrange] using h16range
    have hcardpos : 0 < Nat.card rho.range := Nat.card_pos
    have h16pow : (2 : ℕ) ^ 4 ∣ Nat.card rho.range := by
      simpa using h16rho
    have h4 : 4 ≤ (Nat.card rho.range).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hcardpos.ne').mp h16pow
    omega
  have haff_gamma : ∀ (a : Gamma) (v : F4),
      (a : Equiv.Perm F4) v = rhoBar a v + (a : Equiv.Perm F4) 0 := by
    intro a v
    rcases a with ⟨a, ha⟩
    obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp ha
    have hrho : rhoBar (⟨sigma h, ha⟩ : Gamma) = rho h := by
      have hsub : (sigma.rangeRestrict h : Gamma) = ⟨sigma h, ha⟩ := by
        ext
        rfl
      rw [← hsub]
      exact congrArg (fun f : H →* Equiv.Perm F4 => f h) hcomp
    change sigma h v = rhoBar (⟨sigma h, ha⟩ : Gamma) v + sigma h 0
    rw [hrho]
    exact haff h v
  let s : Gamma := ⟨sigma tau, MonoidHom.mem_range.mpr ⟨tau, rfl⟩⟩
  have hs0 : (s : Equiv.Perm F4) 0 = 0 := by
    change sigma tau 0 = 0
    rw [htau, mul_zero]
  let mu : Equiv.Perm F4 := Equiv.mulLeft₀ (μ : F4) (Units.ne_zero μ)
  have hmu : ∀ v : F4, (s : Equiv.Perm F4) v = mu v := by
    intro v
    change sigma tau v = Equiv.mulLeft₀ (μ : F4) (Units.ne_zero μ) v
    rw [htau]
    rfl
  have hcard_units : Nat.card F4ˣ = 15 := by
    rw [Nat.card_units F4, hFcard]
  have hμtop : Subgroup.zpowers μ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers μ)
    rw [Nat.card_zpowers, hμ, hcard_units]
  have hμ_nat : ∀ u : F4ˣ, ∃ n : ℕ, μ ^ n = u := by
    intro u
    have hu : u ∈ Subgroup.zpowers μ := by
      rw [hμtop]
      exact Subgroup.mem_top u
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hu
    let n : ℕ := (z % (15 : ℤ)).toNat
    have hnz : (n : ℤ) = z % 15 := by
      dsimp [n]
      exact Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num))
    refine ⟨n, ?_⟩
    have h : μ ^ n = μ ^ z := by
      rw [← zpow_natCast, hnz]
      simpa [hμ] using zpow_mod_orderOf μ z
    exact h.trans hz
  have hmu_pow_apply : ∀ (n : ℕ) (v : F4),
      (mu ^ n) v = (μ : F4) ^ n * v := by
    intro n
    induction n with
    | zero =>
        intro v
        simp
    | succ n ih =>
        intro v
        rw [pow_succ', Equiv.Perm.mul_apply, ih]
        change (μ : F4) * ((μ : F4) ^ n * v) = (μ : F4) ^ (n + 1) * v
        rw [pow_succ']
        ring
  have hμtrans : ∀ v w : F4, v ≠ 0 → w ≠ 0 →
      ∃ n : ℕ, (mu ^ n) v = w := by
    intro v w hv hw
    let u : F4ˣ := Units.mk0 (w / v) (div_ne_zero hw hv)
    obtain ⟨n, hn⟩ := hμ_nat u
    refine ⟨n, ?_⟩
    rw [hmu_pow_apply]
    change ((μ ^ n : F4ˣ) : F4) * v = w
    rw [hn]
    change (w / v) * v = w
    exact div_mul_cancel₀ w hv
  have htransK : ∀ b : F4, ∃ k : rhoBar.ker,
      ∀ v : F4, ((k : Gamma) : Equiv.Perm F4) v = v + b :=
    CFSG.ScalarGraphAction.ker_translations_surjective_of_singer
      (V := F4) (A := Gamma) rhoBar haff_gamma hker_gt1 s hs0 mu hmu hμtrans
  intro b
  obtain ⟨k, hk⟩ := htransK b
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp (k : Gamma).2
  refine ⟨h, ?_⟩
  intro a
  rw [hh]
  exact hk a



end CFSG.ScalarGraphAction


namespace CFSG.ScalarGraphAction

open CFSG.ScalarGraphAction



variable {F P : Type*} [Field F] [CharP F 2] [Finite F]
  [AddGroup P] [Finite P]

@[expose]
def shearAdd (φ : P →+ F) (b : F) : AddAut (F × P) where
  toFun v := (v.1 + b * φ v.2, v.2)
  invFun v := (v.1 - b * φ v.2, v.2)
  left_inv v := by
    ext
    · simp only [sub_eq_add_neg]
      abel
    · rfl
  right_inv v := by
    ext
    · simp only [sub_eq_add_neg]
      abel
    · rfl
  map_add' u v := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      rw [map_add, mul_add]
      abel
    · rfl

@[simp]
theorem shearAdd_apply (φ : P →+ F) (b : F) (r : F) (p : P) :
    shearAdd φ b (r, p) = (r + b * φ p, p) := rfl

@[simp]
theorem shearAdd_add_self (φ : P →+ F) (b : F) :
    shearAdd φ b + shearAdd φ b = 0 := by
  apply AddEquiv.ext
  intro v
  rcases v with ⟨r, p⟩
  have h2 : b * φ p + b * φ p = 0 := by
    rw [CharTwo.add_self_eq_zero]
  apply Prod.ext
  · simp [AddAut.add_apply, AddAut.zero_apply, shearAdd_apply, add_assoc, h2]
  · simp [AddAut.add_apply, AddAut.zero_apply, shearAdd_apply]

@[expose]
def shearAddHom (φ : P →+ F) : F →+ AddAut (F × P) where
  toFun := shearAdd φ
  map_zero' := by
    apply AddEquiv.ext
    intro v
    rcases v with ⟨r, p⟩
    apply Prod.ext
    · simp [shearAdd_apply]
    · simp [AddAut.zero_apply, shearAdd_apply]
  map_add' b c := by
    apply AddEquiv.ext
    intro v
    rcases v with ⟨r, p⟩
    apply Prod.ext
    · simp only [AddAut.add_apply, shearAdd_apply]
      change r + (b + c) * φ p = (r + c * φ p) + b * φ p
      rw [add_mul]
      abel
    · simp [AddAut.add_apply, shearAdd_apply]

@[simp]
theorem shearAdd_zero (φ : P →+ F) : shearAdd φ 0 = 0 :=
  (shearAddHom φ).map_zero

theorem shearAddHom_injective [Nontrivial P] (φ : P →+ F)
    (hφ : Function.Injective φ) :
    Function.Injective (shearAddHom φ) := by
  classical
  obtain ⟨p0, hp0⟩ := exists_ne (0 : P)
  have hφp0 : φ p0 ≠ 0 := by
    intro h0
    exact hp0 (hφ (by simpa using h0))
  intro b c hbc
  have h := congrArg (fun e : AddAut (F × P) => e (0, p0)) hbc
  have hpair : (b * φ p0, p0) = (c * φ p0, p0) := by
    simpa [shearAddHom, shearAdd_apply, zero_add] using h
  have hfirst : b * φ p0 = c * φ p0 := congrArg Prod.fst hpair
  exact mul_right_cancel₀ hφp0 hfirst

@[expose]
def shearSubgroup (φ : P →+ F) : Subgroup (Multiplicative (AddAut (F × P))) :=
  (shearAddHom φ).range.toSubgroup

@[simp]
theorem mem_shearSubgroup (φ : P →+ F) {x : Multiplicative (AddAut (F × P))} :
    x ∈ shearSubgroup φ ↔ ∃ b : F, x = Multiplicative.ofAdd (shearAdd φ b) := by
  rw [shearSubgroup, Multiplicative.mem_toSubgroup]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hb' : Multiplicative.ofAdd (shearAdd φ b) = x := by
      simpa [shearAddHom] using congrArg Multiplicative.ofAdd hb
    exact hb'.symm
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

theorem scalarGraph_map_shear (φ : P →+ F) (a b : F) :
    (scalarGraph φ a).map (shearAdd φ b).toAddMonoidHom =
      scalarGraph φ (a + b) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases y with ⟨r, p⟩
    change (r, p) ∈ scalarGraph φ a at hy
    rw [mem_scalarGraph] at hy
    change (shearAdd φ b) (r, p) ∈ scalarGraph φ (a + b)
    rw [shearAdd_apply]
    rw [mem_scalarGraph]
    rw [hy, add_mul]
  · intro hz
    rcases z with ⟨r, p⟩
    change (r, p) ∈ scalarGraph φ (a + b) at hz
    rw [mem_scalarGraph] at hz
    refine ⟨(a * φ p, p), ?_, ?_⟩
    · exact (mem_scalarGraph φ a (a * φ p) p).2 rfl
    · change (shearAdd φ b) (a * φ p, p) = (r, p)
      rw [shearAdd_apply]
      apply Prod.ext
      · change a * φ p + b * φ p = r
        simpa only [Prod.fst, Prod.snd, add_mul] using hz.symm
      · rfl

private theorem conj_shear_is_shear
    {H : Type} [Group H]
    (φ : P →+ F) (hPcard : Nat.card P = 4) (hφ : Function.Injective φ)
    (ρ : H →* Multiplicative (AddAut (F × P)))
    (hroot : ∀ (h : H) (r : F),
      (Multiplicative.toAdd (ρ h) (r, 0)).2 = 0)
    (hfam : ∀ (h : H) (a : F), ∃ b : F,
      (scalarGraph φ a).map
          (Multiplicative.toAdd (ρ h)).toAddMonoidHom =
        scalarGraph φ b)
    (h : H) (b : F) :
    ∃ b' : F,
      Multiplicative.toAdd (ρ h) + shearAdd φ b +
          -Multiplicative.toAdd (ρ h) = shearAdd φ b' := by
  classical
  have hPone : 1 < Nat.card P := by
    rw [hPcard]
    norm_num
  haveI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hPone
  let act : H → AddAut (F × P) := fun h => Multiplicative.toAdd (ρ h)
  let a : AddAut (F × P) := act h
  let aInv : AddAut (F × P) := act h⁻¹
  let s : AddAut (F × P) := shearAdd φ b
  let e : AddAut (F × P) := a + s + -a
  have hneg : -a = aInv := by
    change -(Multiplicative.toAdd (ρ h)) = Multiplicative.toAdd (ρ h⁻¹)
    rw [map_inv]
    simp
  have hroot_e : ∀ r : F, e (r, 0) = (r, 0) := by
    intro r
    let y : F × P := a.symm (r, 0)
    have hy2 : y.2 = 0 := by
      have hh : (aInv (r, 0)).2 = 0 := by
        simpa [aInv, act] using hroot h⁻¹ r
      rw [← hneg] at hh
      simpa [y, AddAut.neg_apply] using hh
    have hs_y : s y = y := by
      rcases y with ⟨y1, y2⟩
      change y2 = 0 at hy2
      change (shearAdd φ b) (y1, y2) = (y1, y2)
      rw [shearAdd_apply, hy2]
      simp
    calc
      e (r, 0) = a (s ((-a) (r, 0))) := by simp [e, AddAut.add_apply]
      _ = a (s y) := by simp [y, AddAut.neg_apply]
      _ = a y := by rw [hs_y]
      _ = (r, 0) := by simp [y]
  have hfam_h : ∀ x : F, ∃ c : F,
      (scalarGraph φ x).map a.toAddMonoidHom = scalarGraph φ c := by
    intro x
    simpa [a, act] using hfam h x
  have hfam_hinv : ∀ x : F, ∃ c : F,
      (scalarGraph φ x).map aInv.toAddMonoidHom = scalarGraph φ c := by
    intro x
    simpa [aInv, act] using hfam h⁻¹ x
  have hfam_e : ∀ x : F, ∃ c : F,
      (scalarGraph φ x).map e.toAddMonoidHom = scalarGraph φ c := by
    intro x
    obtain ⟨c1, hc1⟩ := hfam_hinv x
    obtain ⟨c2, hc2⟩ := hfam_h (c1 + b)
    refine ⟨c2, ?_⟩
    have hcomp : e.toAddMonoidHom =
        a.toAddMonoidHom.comp (s.toAddMonoidHom.comp aInv.toAddMonoidHom) := by
      apply AddMonoidHom.ext
      intro v
      rcases v with ⟨r, p⟩
      apply Prod.ext
      · simp [e, hneg, AddAut.add_apply, AddMonoidHom.comp_apply]
      · simp [e, hneg, AddAut.add_apply, AddMonoidHom.comp_apply]
    rw [hcomp]
    rw [← AddSubgroup.map_map (K := scalarGraph φ x)
      a.toAddMonoidHom (s.toAddMonoidHom.comp aInv.toAddMonoidHom)]
    rw [← AddSubgroup.map_map (K := scalarGraph φ x)
      s.toAddMonoidHom aInv.toAddMonoidHom]
    rw [hc1, scalarGraph_map_shear, hc2]
  have hs2 : ∀ v : F × P, s (s v) = v := by
    intro v
    rcases v with ⟨r, p⟩
    have h2 : b * φ p + b * φ p = 0 := by
      rw [CharTwo.add_self_eq_zero]
    simp [s, shearAdd_apply, add_assoc, h2]
  have hpow_e : ∀ v : F × P, (e^[2]) v = v := by
    intro v
    change e (e v) = v
    simp [e, AddAut.add_apply, AddAut.neg_apply, hs2]
  have hpow1 : ∀ v : F × P, (e^[2 ^ 1]) v = v := by
    simpa using hpow_e
  obtain ⟨b', hb'⟩ :=
    exists_shear_of_root_fixed_pow (φ := φ) (hφ := hφ) (e := e)
      hroot_e hfam_e 1 hpow1
  refine ⟨b', ?_⟩
  apply AddEquiv.ext
  intro v
  rcases v with ⟨r, p⟩
  simpa [e, a, s, act, shearAdd_apply] using hb' r p

theorem shearSubgroup_normal_in_range
    {H : Type} [Group H]
    (φ : P →+ F) (hPcard : Nat.card P = 4) (hφ : Function.Injective φ)
    (ρ : H →* Multiplicative (AddAut (F × P)))
    (hroot : ∀ (h : H) (r : F),
      (Multiplicative.toAdd (ρ h) (r, 0)).2 = 0)
    (hfam : ∀ (h : H) (a : F), ∃ b : F,
      (scalarGraph φ a).map
          (Multiplicative.toAdd (ρ h)).toAddMonoidHom =
        scalarGraph φ b) :
    ((shearSubgroup φ).subgroupOf ρ.range).Normal := by
  classical
  let K : Subgroup (Multiplicative (AddAut (F × P))) := shearSubgroup φ
  refine ⟨?_⟩
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  change (g : Multiplicative (AddAut (F × P))) *
      (n : Multiplicative (AddAut (F × P))) *
        (g : Multiplicative (AddAut (F × P)))⁻¹ ∈ K
  change (n : Multiplicative (AddAut (F × P))) ∈ shearSubgroup φ at hn
  rw [mem_shearSubgroup] at hn
  rcases hn with ⟨b, hb⟩
  rcases g.2 with ⟨h, hg⟩
  obtain ⟨b', hb'⟩ :=
    conj_shear_is_shear φ hPcard hφ ρ hroot hfam h b
  have hprod :
      (g : Multiplicative (AddAut (F × P))) *
          (n : Multiplicative (AddAut (F × P))) *
            (g : Multiplicative (AddAut (F × P)))⁻¹ =
        Multiplicative.ofAdd (shearAdd φ b') := by
    rw [← hg, hb]
    apply Multiplicative.ext
    change Multiplicative.toAdd (ρ h) + shearAdd φ b +
      -Multiplicative.toAdd (ρ h) = shearAdd φ b'
    exact hb'
  rw [hprod]
  dsimp [K]
  exact (mem_shearSubgroup φ).2 ⟨b', rfl⟩

theorem shearSubgroup_isPGroup_in_range
    {H : Type} [Group H]
    (φ : P →+ F)
    (ρ : H →* Multiplicative (AddAut (F × P))) :
    IsPGroup 2 ((shearSubgroup φ).subgroupOf ρ.range) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  refine ⟨1, ?_⟩
  change x ^ 2 = 1
  have hxK : ((x : ρ.range) : Multiplicative (AddAut (F × P))) ∈
      shearSubgroup φ :=
    Subgroup.mem_subgroupOf.mp x.2
  rw [mem_shearSubgroup] at hxK
  rcases hxK with ⟨b, hb⟩
  have hx2 : ((x : ρ.range) : Multiplicative (AddAut (F × P))) ^ 2 = 1 := by
    rw [hb, pow_two, ← ofAdd_add, shearAdd_add_self]
    rfl
  apply Subtype.ext
  apply Subtype.ext
  simpa using hx2

theorem sylow_image_contains_shears
    {H : Type} [Group H] [Finite H]
    (φ : P →+ F) (hPcard : Nat.card P = 4) (hφ : Function.Injective φ)
    (ρ : H →* Multiplicative (AddAut (F × P)))
    (hroot : ∀ (h : H) (r : F),
      (Multiplicative.toAdd (ρ h) (r, 0)).2 = 0)
    (hfam : ∀ (h : H) (a : F), ∃ b : F,
      (scalarGraph φ a).map
          (Multiplicative.toAdd (ρ h)).toAddMonoidHom =
        scalarGraph φ b)
    (hshear : ∀ b : F, ∃ h : H,
      Multiplicative.toAdd (ρ h) = shearAdd φ b)
    (U : Sylow 2 H) :
    ∀ b : F, ∃ u : H,
      u ∈ (U : Subgroup H) ∧
        Multiplicative.toAdd (ρ u) = shearAdd φ b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  have hKle : shearSubgroup φ ≤ ρ.range := by
    intro x hx
    rw [mem_shearSubgroup] at hx
    rcases hx with ⟨b, rfl⟩
    obtain ⟨h, hh⟩ := hshear b
    refine ⟨h, ?_⟩
    simpa using congrArg Multiplicative.ofAdd hh
  let K' : Subgroup ρ.range := (shearSubgroup φ).subgroupOf ρ.range
  have hKnormal : K'.Normal := by
    simpa [K'] using
      shearSubgroup_normal_in_range φ hPcard hφ ρ hroot hfam
  have hKis : IsPGroup 2 K' := by
    simpa [K'] using shearSubgroup_isPGroup_in_range φ ρ
  haveI : K'.Normal := hKnormal
  let Q : Sylow 2 ρ.range :=
    Sylow.mapSurjective (p := 2) (f := ρ.rangeRestrict)
      ρ.rangeRestrict_surjective U
  have hle : K' ≤ (Q : Subgroup ρ.range) :=
    IsPGroup.le_sylow_of_normal hKis Q
  intro b
  let s : Multiplicative (AddAut (F × P)) :=
    Multiplicative.ofAdd (shearAdd φ b)
  have hsK : s ∈ shearSubgroup φ :=
    (mem_shearSubgroup φ).2 ⟨b, rfl⟩
  let s' : ρ.range := ⟨s, hKle hsK⟩
  have hsK' : s' ∈ K' := by
    change s' ∈ (shearSubgroup φ).subgroupOf ρ.range
    rw [Subgroup.mem_subgroupOf]
    exact hsK
  have hsQ : s' ∈ (Q : Subgroup ρ.range) := hle hsK'
  have hsQmap : s' ∈ (U : Subgroup H).map ρ.rangeRestrict := by
    simpa [Q] using hsQ
  rw [Subgroup.mem_map] at hsQmap
  rcases hsQmap with ⟨u, huU, huEq⟩
  refine ⟨u, huU, ?_⟩
  have hu : ρ u = s := by
    simpa using congrArg
      (fun x : ρ.range => (x : Multiplicative (AddAut (F × P)))) huEq
  simpa [s] using congrArg Multiplicative.toAdd hu


end CFSG.ScalarGraphAction

namespace CFSG.ScalarGraphAction

@[expose]
def coordinateActionHom
    {F4 W P : Type*} [Field F4] [Group W] [Group P]
    (eW : W ≃* (Multiplicative F4 × P)) :
    MulAut W →* Multiplicative (AddAut (F4 × Additive P)) where
  toFun τ := Multiplicative.ofAdd (coordinateAddEquiv eW τ)
  map_one' := by
    apply Multiplicative.ext
    change coordinateAddEquiv eW (1 : MulAut W) = AddEquiv.refl (F4 × Additive P)
    exact coordinateAddEquiv_one eW
  map_mul' τ υ := by
    apply Multiplicative.ext
    apply AddEquiv.ext
    intro x
    simpa [AddAut.add_apply] using coordinateAddEquiv_mul_apply eW τ υ x


open scoped commutatorElement

theorem commutator_eq_root_of_shear_coordinates
    {G K : Type*} [Group G] [Field K]
    {R P W E : Subgroup G}
    (hRW : R ≤ W)
    (hEN : E ≤ Subgroup.normalizer (W : Set G))
    (eR : R ≃* Multiplicative K)
    (eW : W ≃* (Multiplicative K × P))
    (heW_R : ∀ r : R,
      eW (Subgroup.inclusion hRW r) = (eR r, 1))
    (phi : P →* Multiplicative K)
    (theta : E →* Multiplicative K)
    (hshear : ∀ (v : E) (w : W),
      eW (W.normalizerMonoidHom ⟨(v : G), hEN v.2⟩ w) =
        (Multiplicative.ofAdd
            ((eW w).1.toAdd + (theta v).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2)) :
    ∀ (v : E) (w : W),
      ⁅(v : G), (w : G)⁆ =
        ((eR.symm (Multiplicative.ofAdd
          ((theta v).toAdd * (phi ((eW w).2)).toAdd)) : R) : G) := by
  classical
  let rootW : E → W → R := fun v w =>
    eR.symm (Multiplicative.ofAdd
      ((theta v).toAdd * (phi ((eW w).2)).toAdd))
  have hrootW_spec : ∀ (v : E) (w : W),
      W.normalizerMonoidHom ⟨(v : G), hEN v.2⟩ w =
        w * Subgroup.inclusion hRW (rootW v w) := by
    intro v w
    apply eW.injective
    rw [map_mul, hshear v w, heW_R (rootW v w)]
    simp [rootW, eR.apply_symm_apply, ofAdd_add, Prod.mul_def]
  have hrootW_comm : ∀ (v : E) (w : W),
      (rootW v w : G) * (w : G) = (w : G) * (rootW v w : G) := by
    intro v w
    have hw : Subgroup.inclusion hRW (rootW v w) * w =
        w * Subgroup.inclusion hRW (rootW v w) := by
      apply eW.injective
      simp only [map_mul, heW_R, Prod.mul_def, mul_one, one_mul]
      exact Prod.ext (mul_comm _ _) rfl
    exact congrArg (fun x : W => (x : G)) hw
  intro v w
  have h := congrArg (fun x : W => (x : G)) (hrootW_spec v w)
  change (v : G) * (w : G) * (v : G)⁻¹ = (w : G) * (rootW v w : G) at h
  calc
    (v : G) * (w : G) * (v : G)⁻¹ * (w : G)⁻¹ =
        ((w : G) * (rootW v w : G)) * (w : G)⁻¹ := by rw [h]
    _ = (rootW v w : G) := by rw [← hrootW_comm v w]; group

theorem scalar_relation_of_commuting_elementary_products
    {G K : Type*} [Group G] [Field K] [CharP K 2]
    {R P W E B : Subgroup G}
    (hRW : R ≤ W) (hPW : P ≤ W)
    (hBE : B ≤ E) (hPE : P ≤ E)
    (hEN : E ≤ Subgroup.normalizer (W : Set G))
    (hRcentral : R ≤ Subgroup.centralizer (E : Set G))
    (hBcomm : ∀ b b' : B, b * b' = b' * b)
    (hPcomm : ∀ p p' : P, p * p' = p' * p)
    (eR : R ≃* Multiplicative K)
    (eW : W ≃* (Multiplicative K × P))
    (heW_R : ∀ r : R,
      eW (Subgroup.inclusion hRW r) = (eR r, 1))
    (heW_P : ∀ p : P,
      eW (Subgroup.inclusion hPW p) = (1, p))
    (phi : P →* Multiplicative K)
    (theta : E →* Multiplicative K)
    (hthetaP : ∀ p : P, theta ⟨(p : G), hPE p.2⟩ = 1)
    (hshear : ∀ (v : E) (w : W),
      eW (W.normalizerMonoidHom ⟨(v : G), hEN v.2⟩ w) =
        (Multiplicative.ofAdd
            ((eW w).1.toAdd + (theta v).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2))
    (b c : B) (p q : P) (v w : E)
    (hv : v = ⟨(b : G), hBE b.2⟩ * ⟨(p : G), hPE p.2⟩)
    (hw : w = ⟨(c : G), hBE c.2⟩ * ⟨(q : G), hPE q.2⟩)
    (hcomm : (v : G) * (w : G) = (w : G) * (v : G)) :
    (theta v).toAdd * (phi q).toAdd +
      (theta w).toAdd * (phi p).toAdd = 0 := by
  classical
  let bE : E := ⟨(b : G), hBE b.2⟩
  let cE : E := ⟨(c : G), hBE c.2⟩
  let pE : E := ⟨(p : G), hPE p.2⟩
  let qE : E := ⟨(q : G), hPE q.2⟩
  let rootBQ : R := eR.symm (Multiplicative.ofAdd
    ((theta bE).toAdd * (phi q).toAdd))
  let rootCP : R := eR.symm (Multiplicative.ofAdd
    ((theta cE).toAdd * (phi p).toAdd))
  have hcommBQ : ⁅(b : G), (q : G)⁆ = (rootBQ : G) := by
    have h := commutator_eq_root_of_shear_coordinates hRW hEN eR eW heW_R
      phi theta hshear bE (Subgroup.inclusion hPW q)
    simpa [rootBQ, heW_P q, Subgroup.coe_inclusion] using h
  have hcommCP : ⁅(c : G), (p : G)⁆ = (rootCP : G) := by
    have h := commutator_eq_root_of_shear_coordinates hRW hEN eR eW heW_R
      phi theta hshear cE (Subgroup.inclusion hPW p)
    simpa [rootCP, heW_P p, Subgroup.coe_inclusion] using h
  have hcommPC : ⁅(p : G), (c : G)⁆ = (rootCP : G)⁻¹ := by
    rw [← commutatorElement_inv, hcommCP]
  have hfun : ⁅(v : G), (w : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hvG : (v : G) = (b : G) * (p : G) := by
    simpa [bE, pE] using congrArg (fun x : E => (x : G)) hv
  have hwG : (w : G) = (c : G) * (q : G) := by
    simpa [cE, qE] using congrArg (fun x : E => (x : G)) hw
  have hbcMul : (b : G) * (c : G) = (c : G) * (b : G) :=
    congrArg (fun x : B => (x : G)) (hBcomm b c)
  have hpqMul : (p : G) * (q : G) = (q : G) * (p : G) :=
    congrArg (fun x : P => (x : G)) (hPcomm p q)
  have hbc : ⁅(b : G), (c : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hbcMul
  have hpq : ⁅(p : G), (q : G)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr hpqMul
  have hconjB : (b : G) * ⁅(p : G), (c : G)⁆ * (b : G)⁻¹ =
      ⁅(p : G), (c : G)⁆ := by
    have hr : ⁅(p : G), (c : G)⁆ ∈ R := by
      rw [hcommPC]
      exact R.inv_mem rootCP.2
    have hbcomm : (b : G) * ⁅(p : G), (c : G)⁆ =
        ⁅(p : G), (c : G)⁆ * (b : G) :=
      hRcentral hr (b : G) (hBE b.2)
    calc
      (b : G) * ⁅(p : G), (c : G)⁆ * (b : G)⁻¹ =
          (⁅(p : G), (c : G)⁆ * (b : G)) * (b : G)⁻¹ := by rw [hbcomm]
      _ = ⁅(p : G), (c : G)⁆ := by group
  have hconjC : (c : G) * ⁅(b : G), (q : G)⁆ * (c : G)⁻¹ =
      ⁅(b : G), (q : G)⁆ := by
    have hr : ⁅(b : G), (q : G)⁆ ∈ R := by
      rw [hcommBQ]
      exact rootBQ.2
    have hccomm : (c : G) * ⁅(b : G), (q : G)⁆ =
        ⁅(b : G), (q : G)⁆ * (c : G) :=
      hRcentral hr (c : G) (hBE c.2)
    calc
      (c : G) * ⁅(b : G), (q : G)⁆ * (c : G)⁻¹ =
          (⁅(b : G), (q : G)⁆ * (c : G)) * (c : G)⁻¹ := by rw [hccomm]
      _ = ⁅(b : G), (q : G)⁆ := by group
  have hexp : ((b : G) * ⁅(p : G), (c : G)⁆ * (b : G)⁻¹) *
      ((c : G) * ⁅(b : G), (q : G)⁆ * (c : G)⁻¹) = 1 := by
    have h := hfun
    rw [hvG, hwG, commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj, hbc, hpq] at h
    simpa [mul_assoc] using h
  rw [hconjB, hconjC] at hexp
  have hprod : (rootCP : G)⁻¹ * (rootBQ : G) = 1 := by
    rw [hcommPC, hcommBQ] at hexp
    exact hexp
  have hEqR : rootBQ = rootCP := by
    apply Subtype.ext
    have h := congrArg (fun x : G => (rootCP : G) * x) hprod
    simpa [mul_assoc] using h
  have hscalar : (theta bE).toAdd * (phi q).toAdd =
      (theta cE).toAdd * (phi p).toAdd := by
    have h := congrArg (fun x : R => (eR x).toAdd) hEqR
    simpa [rootBQ, rootCP, eR.apply_symm_apply] using h
  have hthetaV : theta v = theta bE := by
    rw [hv, map_mul, hthetaP p, mul_one]
  have hthetaW : theta w = theta cE := by
    rw [hw, map_mul, hthetaP q, mul_one]
  rw [hthetaV, hthetaW, hscalar]
  exact CharTwo.add_self_eq_zero _


theorem exists_commutator_hom_of_shear_coordinates
    {D : Type*} [Group D]
    {K : Type*} [Field K]
    {U P W V : Subgroup D} {p0 : P}
    (hUW : U ≤ W) (hPW : P ≤ W)
    (hVnorm : ∀ v : V, (v : D) ∈ Subgroup.normalizer (W : Set D))
    (eR : U ≃* Multiplicative K)
    (eW : W ≃* (Multiplicative K × P))
    (heWr : ∀ r : U, eW (Subgroup.inclusion hUW r) = (eR r, 1))
    (heWp : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
    (phi : P →* Multiplicative K)
    (hphi : Function.Injective phi)
    (hp0 : p0 ≠ 1)
    (theta : V →* Multiplicative K)
    (htheta_surj : Function.Surjective theta)
    (htheta_ker : theta.ker = W.subgroupOf V)
    (hshear : ∀ (v : V) (w : W),
      eW (W.normalizerMonoidHom ⟨(v : D), hVnorm v⟩ w) =
        (Multiplicative.ofAdd
            ((eW w).1.toAdd + (theta v).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2)) :
    ∃ lamV : V →* U,
      (∀ v : V, (lamV v : D) = ⁅(v : D), (p0 : D)⁆) ∧
      Function.Surjective lamV ∧
      lamV.ker = W.subgroupOf V ∧
      (∀ (v : V) (w : W), ⁅(v : D), (w : D)⁆ ∈ U) ∧
      (∀ v : V, eR (lamV v) =
        Multiplicative.ofAdd ((theta v).toAdd * (phi p0).toAdd)) ∧
      ∃ eScaled : Additive U ≃+ K,
        (∀ u : U, eScaled (Additive.ofMul u) = (phi p0).toAdd⁻¹ * (eR u).toAdd) ∧
        (∀ v : V, eScaled (Additive.ofMul (lamV v)) = (theta v).toAdd) := by
  classical
  let b0 : K := (phi p0).toAdd
  have hb0 : b0 ≠ 0 := by
    intro h0
    have h1 : phi p0 = 1 := by
      apply Multiplicative.toAdd.injective
      simpa [b0] using h0
    exact hp0 (hphi (by simpa using h1))
  let rootW : V → W → U := fun v w =>
    eR.symm (Multiplicative.ofAdd
      ((theta v).toAdd * (phi ((eW w).2)).toAdd))
  have hrootW_eR : ∀ (v : V) (w : W),
      eR (rootW v w) = Multiplicative.ofAdd
        ((theta v).toAdd * (phi ((eW w).2)).toAdd) := by
    intro v w
    dsimp only [rootW]
    exact eR.apply_symm_apply _
  have hcommutator : ∀ (v : V) (w : W),
      ⁅(v : D), (w : D)⁆ = (rootW v w : D) := by
    intro v w
    exact commutator_eq_root_of_shear_coordinates hUW
      (fun x hx => hVnorm ⟨x, hx⟩) eR eW heWr phi theta hshear v w
  let root : V → U := fun v => rootW v ⟨p0, hPW p0.2⟩
  have hroot_eR : ∀ v : V,
      eR (root v) = Multiplicative.ofAdd ((theta v).toAdd * b0) := by
    intro v
    have hwp : eW (⟨p0, hPW p0.2⟩ : W) = (1, p0) := by
      have heq : (⟨p0, hPW p0.2⟩ : W) = Subgroup.inclusion hPW p0 :=
        Subtype.ext (Subgroup.coe_inclusion hPW p0).symm
      rw [heq]
      exact heWp p0
    simpa [root, b0, hwp] using hrootW_eR v ⟨p0, hPW p0.2⟩
  let f : V → U := root
  have hf_apply : ∀ v : V, eR (f v) =
      Multiplicative.ofAdd ((theta v).toAdd * b0) := hroot_eR
  have hf_mul : ∀ (v w : V), f (v * w) = f v * f w := by
    intro v w
    apply eR.injective
    change eR (f (v * w)) = eR (f v * f w)
    calc
      eR (f (v * w)) = Multiplicative.ofAdd ((theta (v * w)).toAdd * b0) :=
        hf_apply (v * w)
      _ = Multiplicative.ofAdd
          (((theta v).toAdd + (theta w).toAdd) * b0) := by
        rw [map_mul theta v w, toAdd_mul]
      _ = Multiplicative.ofAdd
          ((theta v).toAdd * b0 + (theta w).toAdd * b0) := by
        rw [add_mul]
      _ = Multiplicative.ofAdd ((theta v).toAdd * b0) *
          Multiplicative.ofAdd ((theta w).toAdd * b0) := by
        rw [← ofAdd_add]
      _ = eR (f v) * eR (f w) := by
        rw [hf_apply v, hf_apply w]
      _ = eR (f v * f w) := (map_mul eR (f v) (f w)).symm
  let lamV : V →* U :=
    { toFun := f
      map_one' := by
        apply eR.injective
        change eR (f 1) = eR (1 : U)
        rw [hf_apply, map_one, toAdd_one, zero_mul]
        simp
      map_mul' := hf_mul }
  have hlamV_apply : ∀ v : V,
      (lamV v : D) = ⁅(v : D), (p0 : D)⁆ := by
    intro v
    change (root v : D) = ⁅(v : D), (p0 : D)⁆
    rw [hcommutator v ⟨p0, hPW p0.2⟩]
  have hsurj : Function.Surjective lamV := by
    intro u
    let t : K := (MulEquiv.toAdditive eR) (Additive.ofMul u)
    obtain ⟨s, hs⟩ : ∃ s : K, s * b0 = t :=
      ⟨t * b0⁻¹, by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]⟩
    obtain ⟨v, hv⟩ := htheta_surj (Multiplicative.ofAdd s)
    refine ⟨v, ?_⟩
    apply eR.injective
    change eR (f v) = eR u
    rw [hf_apply, hv, toAdd_ofAdd, hs]
    rfl
  have hker : lamV.ker = W.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker]
    constructor
    · intro hv
      have h1 : eR (f v) = 1 := by
        change eR (lamV v) = 1
        rw [hv, map_one]
      rw [hf_apply] at h1
      have h2 : (theta v).toAdd * b0 = 0 := by
        simpa using congrArg Multiplicative.toAdd h1
      have h3 : (theta v).toAdd = 0 := by
        exact (mul_eq_zero.mp h2).resolve_right hb0
      have h4 : theta v = 1 := by
        apply Multiplicative.toAdd.injective
        simpa using h3
      rw [← htheta_ker, MonoidHom.mem_ker]
      exact h4
    · intro hv
      have h4 : theta v = 1 := by
        change v ∈ theta.ker
        rw [htheta_ker]
        exact hv
      apply eR.injective
      change eR (f v) = eR (1 : U)
      rw [hf_apply, h4, toAdd_one, zero_mul]
      simp
  have hcomm : ∀ (v : V) (w : W), ⁅(v : D), (w : D)⁆ ∈ U := by
    intro v w
    rw [hcommutator v w]
    exact (rootW v w).2
  let eScaled : Additive U ≃+ K :=
    (MulEquiv.toAdditive eR).trans
      (Units.mulLeftLinearEquiv K K
        (Units.mk0 b0⁻¹ (inv_ne_zero hb0))).toAddEquiv
  have heScaled : ∀ v : V,
      eScaled (Additive.ofMul (lamV v)) = (theta v).toAdd := by
    intro v
    dsimp only [eScaled]
    change b0⁻¹ * (eR (f v)).toAdd = (theta v).toAdd
    rw [hf_apply, toAdd_ofAdd, mul_comm (theta v).toAdd b0]
    rw [← mul_assoc, inv_mul_cancel₀ hb0, one_mul]
  refine ⟨lamV, hlamV_apply, hsurj, hker, hcomm, ?_, eScaled, ?_, heScaled⟩
  · exact hf_apply
  · intro u
    rfl


theorem theta_equivariance_from_commutator
    {E R : Type*} [Group E] [Group R]
    {K : Type*} [Field K]
    (i : R →* E) (lambda : E → R) (p0 : E) (sigma : MulAut E)
    (eR : R ≃* Multiplicative K)
    (theta : E →* Multiplicative K)
    (b0 : K) (hb0 : b0 ≠ 0) (mu : K)
    (hlambda_apply : ∀ e : E, i (lambda e) = ⁅e, p0⁆)
    (hlambda_eR : ∀ e : E,
      eR (lambda e) = Multiplicative.ofAdd ((theta e).toAdd * b0))
    (hsigma_p0 : sigma p0 = p0)
    (hroot_scalar : ∀ (r r' : R), i r' = sigma (i r) →
      eR r' = Multiplicative.ofAdd (mu * (eR r).toAdd)) :
    ∀ e : E,
      theta (sigma e) =
        Multiplicative.ofAdd (mu * (theta e).toAdd) := by
  intro e
  have hlambda_sigma : i (lambda (sigma e)) = sigma (i (lambda e)) := by
    rw [hlambda_apply (sigma e), hlambda_apply e, map_commutatorElement,
      hsigma_p0]
  have hroot := hroot_scalar (lambda e) (lambda (sigma e)) hlambda_sigma
  rw [hlambda_eR e, hlambda_eR (sigma e)] at hroot
  have hcoeff : (theta (sigma e)).toAdd * b0 =
      mu * ((theta e).toAdd * b0) :=
    Multiplicative.ofAdd.injective hroot
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  apply mul_right_cancel₀ hb0
  simpa [mul_assoc] using hcoeff



theorem theta_equivariance_of_shear_coordinates
    {G K : Type*} [Group G] [Field K]
    {R P W E : Subgroup G}
    (hRW : R ≤ W) (hPW : P ≤ W) (hRE : R ≤ E) (hPE : P ≤ E)
    (hEN : E ≤ Subgroup.normalizer (W : Set G))
    (eR : R ≃* Multiplicative K) (eW : W ≃* (Multiplicative K × P))
    (heW_R : ∀ r : R, eW (Subgroup.inclusion hRW r) = (eR r, 1))
    (heW_P : ∀ p : P, eW (Subgroup.inclusion hPW p) = (1, p))
    (phi : P →* Multiplicative K) (hphi : Function.Injective phi)
    (theta : E →* Multiplicative K)
    (hshear : ∀ (v : E) (w : W),
      eW (W.normalizerMonoidHom ⟨(v : G), hEN v.2⟩ w) =
        (Multiplicative.ofAdd
            ((eW w).1.toAdd + (theta v).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2))
    (p0 : P) (hp0 : p0 ≠ 1) (sigma : MulAut E) (mu : K)
    (hfix : sigma (Subgroup.inclusion hPE p0) = Subgroup.inclusion hPE p0)
    (hscalar : ∀ r r' : R,
      Subgroup.inclusion hRE r' = sigma (Subgroup.inclusion hRE r) →
        eR r' = Multiplicative.ofAdd (mu * (eR r).toAdd)) :
    ∀ v : E, theta (sigma v) = Multiplicative.ofAdd (mu * (theta v).toAdd) := by
  classical
  have hphi0 : phi p0 ≠ 1 := by
    intro h
    apply hp0
    apply hphi
    simpa using h
  have hb0 : (phi p0).toAdd ≠ 0 := by
    intro h
    apply hphi0
    have h' := congrArg Multiplicative.ofAdd h
    simpa using h'
  let lambda : E → R := fun v =>
    eR.symm (Multiplicative.ofAdd ((theta v).toAdd * (phi p0).toAdd))
  have hlambda_apply : ∀ v : E,
      Subgroup.inclusion hRE (lambda v) = ⁅v, Subgroup.inclusion hPE p0⁆ := by
    intro v
    apply Subtype.ext
    have hphiw : (eW (Subgroup.inclusion hPW p0)).2 = p0 := by
      rw [heW_P]
    have hroot := commutator_eq_root_of_shear_coordinates hRW hEN eR eW heW_R
      phi theta hshear v (Subgroup.inclusion hPW p0)
    rw [hphiw] at hroot
    calc
      ((Subgroup.inclusion hRE (lambda v) : E) : G)
          = ((lambda v : R) : G) := rfl
      _ = ((eR.symm (Multiplicative.ofAdd
            ((theta v).toAdd * (phi p0).toAdd)) : R) : G) := rfl
      _ = ⁅(v : G), ((Subgroup.inclusion hPW p0 : W) : G)⁆ := hroot.symm
      _ = ⁅(v : G), ((Subgroup.inclusion hPE p0 : E) : G)⁆ := rfl
      _ = ((⁅v, Subgroup.inclusion hPE p0⁆ : E) : G) := rfl
  have hlambda_eR : ∀ v : E,
      eR (lambda v) =
        Multiplicative.ofAdd ((theta v).toAdd * (phi p0).toAdd) :=
    fun v => eR.apply_symm_apply _
  exact theta_equivariance_from_commutator
    (Subgroup.inclusion hRE) lambda (Subgroup.inclusion hPE p0) sigma eR theta
    (phi p0).toAdd hb0 mu hlambda_apply hlambda_eR hfix hscalar

open scoped commutatorElement in
theorem card_le_card_commutator_of_pure_shear
    {G K P : Type*} [Group G] [Finite G] [Field K] [Group P]
    {W : Subgroup G} (eW : W ≃* (Multiplicative K × P))
    (phi : P →* Multiplicative K) (hphi : Function.Injective phi)
    (h : Subgroup.normalizer (W : Set G)) (b : K) (hb : b ≠ 0)
    (hact : ∀ w : W,
      eW (W.normalizerMonoidHom h w) =
        (Multiplicative.ofAdd ((eW w).1.toAdd + b * (phi ((eW w).2)).toAdd),
          (eW w).2)) :
    Nat.card P ≤ Nat.card (⁅W, Subgroup.zpowers (h : G)⁆ : Subgroup G) := by
  classical
  let a : P → W := fun p => eW.symm ((1 : Multiplicative K), p)
  let c : P → W := fun p => a p * W.normalizerMonoidHom h (a p)⁻¹
  have ha (p : P) : eW (a p) = (1, p) := by
    simp [a]
  have hainv (p : P) : eW ((a p)⁻¹) = (1, p⁻¹) := by
    rw [map_inv, ha p]
    simp
  have hstep (p : P) :
      eW (W.normalizerMonoidHom h ((a p)⁻¹)) =
        (Multiplicative.ofAdd (-(b * (phi p).toAdd)), p⁻¹) := by
    rw [hact ((a p)⁻¹), hainv p]
    apply Prod.ext
    · change Multiplicative.ofAdd ((1 : Multiplicative K).toAdd +
          b * (phi (p⁻¹)).toAdd) =
        Multiplicative.ofAdd (-(b * (phi p).toAdd))
      simp only [toAdd_one, zero_add]
      congr 1
      rw [map_inv, toAdd_inv]
      ring
    · rfl
  have hc (p : P) : eW (c p) =
      (Multiplicative.ofAdd (-(b * (phi p).toAdd)), 1) := by
    change eW (a p * W.normalizerMonoidHom h ((a p)⁻¹)) =
      (Multiplicative.ofAdd (-(b * (phi p).toAdd)), 1)
    rw [map_mul, ha p, hstep p]
    apply Prod.ext <;> simp
  have hc_eq (p : P) : (c p : G) = ⁅(a p : G), (h : G)⁆ := by
    change (a p : G) *
      ((W.normalizerMonoidHom h ((a p)⁻¹) : W) : G) =
        ⁅(a p : G), (h : G)⁆
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
    simp only [Subgroup.coe_inv]
    group
  have hmem (p : P) : (c p : G) ∈ ⁅W, Subgroup.zpowers (h : G)⁆ := by
    rw [hc_eq p]
    exact Subgroup.commutator_mem_commutator (a p).2 (Subgroup.mem_zpowers (h : G))
  refine Nat.card_le_card_of_injective
    (fun p : P =>
      (⟨(c p : G), hmem p⟩ : ↥⁅W, Subgroup.zpowers (h : G)⁆)) ?_
  intro p q hpq
  have hcW : c p = c q := by
    have hG : (c p : G) = (c q : G) :=
      congrArg (fun z : ↥⁅W, Subgroup.zpowers (h : G)⁆ => (z : G)) hpq
    exact Subtype.ext hG
  have hcoord : -(b * (phi p).toAdd) = -(b * (phi q).toAdd) := by
    have h := congrArg (fun z : W => (eW z).1.toAdd) hcW
    rw [hc p, hc q] at h
    simpa using h
  have hmul : b * (phi p).toAdd = b * (phi q).toAdd :=
    neg_inj.mp hcoord
  have hphi_eq : phi p = phi q := by
    apply Multiplicative.ext
    exact mul_left_cancel₀ hb hmul
  exact hphi hphi_eq

open scoped commutatorElement in
theorem card_le_card_commutator_of_full_shear
    {G K P : Type*} [Group G] [Finite G] [Field K] [Group P]
    {B W : Subgroup G} (hBW : B ≤ Subgroup.normalizer (W : Set G))
    (eW : W ≃* (Multiplicative K × P))
    (phi : P →* Multiplicative K)
    (q : B →* Multiplicative K) (hq : Function.Surjective q)
    (hact : ∀ b : B, ∀ w : W,
      eW (W.normalizerMonoidHom ⟨(b : G), hBW b.2⟩ w) =
        (Multiplicative.ofAdd ((eW w).1.toAdd + (q b).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2))
    (t : W) (ht : (phi ((eW t).2)).toAdd ≠ 0) :
    Nat.card K ≤ Nat.card (⁅B, Subgroup.zpowers (t : G)⁆ : Subgroup G) := by
  classical
  let p : P := (eW t).2
  let u : K := (eW t).1.toAdd
  have hp : (phi p).toAdd ≠ 0 := ht
  let ba : K → B := fun a =>
    Classical.choose (hq (Multiplicative.ofAdd (a / (phi p).toAdd)))
  have hba (a : K) : q (ba a) = Multiplicative.ofAdd (a / (phi p).toAdd) :=
    Classical.choose_spec (hq (Multiplicative.ofAdd (a / (phi p).toAdd)))
  let action : K → W := fun a =>
    W.normalizerMonoidHom ⟨(ba a : G), hBW (ba a).2⟩ t
  let c : K → W := fun a => action a * t⁻¹
  have htcoord : eW t = (Multiplicative.ofAdd u, p) := by
    apply Prod.ext
    · exact (ofAdd_toAdd (eW t).1).symm
    · rfl
  have hstep (a : K) :
      eW (action a) = (Multiplicative.ofAdd (u + a), p) := by
    change eW (W.normalizerMonoidHom ⟨(ba a : G), hBW (ba a).2⟩ t) =
      (Multiplicative.ofAdd (u + a), p)
    rw [hact (ba a) t, hba a]
    apply Prod.ext
    · change Multiplicative.ofAdd (u + (a / (phi p).toAdd) * (phi p).toAdd) =
        Multiplicative.ofAdd (u + a)
      rw [div_mul_cancel₀ a hp]
    · rfl
  have hcoord (a : K) : eW (c a) = (Multiplicative.ofAdd a, (1 : P)) := by
    have hc_def : c a = action a * t⁻¹ := rfl
    calc
      eW (c a) = eW (action a) * eW (t⁻¹) := by
        rw [hc_def, map_mul]
      _ = (Multiplicative.ofAdd (u + a), p) * (eW t)⁻¹ := by
        rw [hstep, map_inv]
      _ = (Multiplicative.ofAdd a, (1 : P)) := by
        rw [htcoord, Prod.inv_mk]
        apply Prod.ext
        · change Multiplicative.ofAdd (u + a) * (Multiplicative.ofAdd u)⁻¹ =
            Multiplicative.ofAdd a
          rw [← ofAdd_neg, ← ofAdd_add]
          congr 1
          abel
        · simp
  have hc_mem (a : K) : (c a : G) ∈ ⁅B, Subgroup.zpowers (t : G)⁆ := by
    have hc_eq : (c a : G) = ⁅(ba a : G), (t : G)⁆ := by
      change ((W.normalizerMonoidHom ⟨(ba a : G), hBW (ba a).2⟩ t : W) : G) *
          ((t⁻¹ : W) : G) = ⁅(ba a : G), (t : G)⁆
      rw [Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
        commutatorElement_def]
    rw [hc_eq]
    exact Subgroup.commutator_mem_commutator (ba a).2 (Subgroup.mem_zpowers (t : G))
  refine Nat.card_le_card_of_injective
    (fun a : K =>
      (⟨(c a : G), hc_mem a⟩ : ↥⁅B, Subgroup.zpowers (t : G)⁆)) ?_
  intro a a' haa'
  have hcW : c a = c a' := by
    have hG : (c a : G) = (c a' : G) :=
      congrArg (fun z : ↥⁅B, Subgroup.zpowers (t : G)⁆ => (z : G)) haa'
    exact Subtype.ext hG
  have hcoord_eq : a = a' := by
    have h := congrArg (fun z : W => (eW z).1.toAdd) hcW
    rw [hcoord a, hcoord a'] at h
    simpa using h
  exact hcoord_eq

theorem card_range_le_two_of_scalar_square
    {K A : Type*} [Field K] [CharP K 2] [Group A]
    (t p : A →* Multiplicative K) (theta : K) (htheta : theta ≠ 0)
    (hsquare : ∀ a : A, (t a).toAdd * (theta + (p a).toAdd) = 0) :
    Nat.card t.range ≤ 2 := by
  classical
  have hFin : Nat.card (Fin 2) = 2 := Nat.card_fin 2
  by_cases hnonzero : ∃ a : A, (t a).toAdd ≠ 0
  ·
    obtain ⟨a0, ha0_add⟩ := hnonzero
    have ht0 : t a0 ≠ 1 := by
      intro h
      apply ha0_add
      simp [h]
    have hp_eq (a : A) (hta : (t a).toAdd ≠ 0) : (p a).toAdd = theta := by
      have h := hsquare a
      have hzero : theta + (p a).toAdd = 0 :=
        (mul_eq_zero.mp h).resolve_left hta
      exact (CharTwo.add_eq_zero.mp hzero).symm
    have hcase : ∀ a : A, t a = 1 ∨ t a = t a0 := by
      intro a
      by_cases hta : (t a).toAdd = 0
      · left
        apply Multiplicative.ext
        simpa using hta
      · right
        have hpa : (p a).toAdd = theta := hp_eq a hta
        have hpa0 : (p a0).toAdd = theta := hp_eq a0 ha0_add
        have hpa0a : (p (a0 * a)).toAdd = 0 := by
          rw [map_mul p, toAdd_mul, hpa0, hpa]
          exact CharTwo.add_eq_zero.mpr rfl
        have h := hsquare (a0 * a)
        rw [map_mul t, toAdd_mul, hpa0a] at h
        simp only [add_zero] at h
        have hsum : (t a0).toAdd + (t a).toAdd = 0 :=
          (mul_eq_zero.mp h).resolve_right htheta
        apply Multiplicative.ext
        exact (CharTwo.add_eq_zero.mp hsum).symm
    have hxcase (x : t.range) : x.1 = 1 ∨ x.1 = t a0 := by
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      rcases hcase a with h | h
      · left
        rw [← ha, h]
      · right
        rw [← ha, h]
    let f : t.range → Fin 2 := fun x => if x.1 = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro x y hxy
      have hx := hxcase x
      have hy := hxcase y
      rcases hx with hx1 | hx0 <;> rcases hy with hy1 | hy0
      · apply Subtype.ext
        rw [hx1, hy1]
      · have h1 : f x = 0 := by
          change (if x.1 = 1 then (0 : Fin 2) else 1) = 0
          exact if_pos hx1
        have h2 : f y = 1 := by
          change (if y.1 = 1 then (0 : Fin 2) else 1) = 1
          exact if_neg (by rw [hy0]; exact ht0)
        rw [h1, h2] at hxy
        exact False.elim ((by decide : (0 : Fin 2) ≠ 1) hxy)
      · have h1 : f x = 1 := by
          change (if x.1 = 1 then (0 : Fin 2) else 1) = 1
          exact if_neg (by rw [hx0]; exact ht0)
        have h2 : f y = 0 := by
          change (if y.1 = 1 then (0 : Fin 2) else 1) = 0
          exact if_pos hy1
        rw [h1, h2] at hxy
        exact False.elim ((by decide : (1 : Fin 2) ≠ 0) hxy)
      · apply Subtype.ext
        rw [hx0, hy0]
    have hcard : Nat.card t.range ≤ Nat.card (Fin 2) :=
      Nat.card_le_card_of_injective f hf
    rw [hFin] at hcard
    exact hcard
  ·
    have hzero : ∀ a : A, (t a).toAdd = 0 := by
      intro a
      by_cases h : (t a).toAdd = 0
      · exact h
      · exact False.elim (hnonzero ⟨a, h⟩)
    have hone (x : t.range) : x.1 = 1 := by
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      apply Multiplicative.ext
      rw [← ha]
      simpa using hzero a
    let f : t.range → Fin 2 := fun _ => 0
    have hf : Function.Injective f := by
      intro x y _
      apply Subtype.ext
      rw [hone x, hone y]
    have hcard : Nat.card t.range ≤ Nat.card (Fin 2) :=
      Nat.card_le_card_of_injective f hf
    rw [hFin] at hcard
    exact hcard

theorem shear_parameter_conjugation
    {G K P : Type*} [Group G] [Field K] [Group P]
    {E W : Subgroup G} (hENW : E ≤ Subgroup.normalizer (W : Set G))
    (eW : W ≃* (Multiplicative K × P))
    (phi : P →* Multiplicative K) (hphi : Function.Injective phi)
    (theta : E →* Multiplicative K)
    (hS : ∀ e : E, ∀ w : W,
      eW (W.normalizerMonoidHom ⟨(e : G), hENW e.2⟩ w) =
        (Multiplicative.ofAdd
            ((eW w).1.toAdd + (theta e).toAdd * (phi ((eW w).2)).toAdd),
          (eW w).2))
    (x : Subgroup.normalizer (W : Set G))
    (hXE : (x : G) ∈ Subgroup.normalizer (E : Set G))
    (gamma c : K ≃+ K) (alpha : Additive P ≃+ Additive P)
    (beta : Additive P →+ K)
    (hX : ∀ w : W,
      eW (W.normalizerMonoidHom x w) =
        (Multiplicative.ofAdd
            (gamma ((eW w).1.toAdd) + beta (Additive.ofMul (eW w).2)),
          (alpha (Additive.ofMul (eW w).2)).toMul))
    (hgraph : ∀ a : K, ∀ p : Additive P,
      gamma (a * (phi p.toMul).toAdd) =
        c a * (phi ((alpha p).toMul)).toAdd)
    (p0 : P) (hp0 : p0 ≠ 1) :
    ∀ e : E,
      (theta (E.normalizerMonoidHom ⟨(x : G), hXE⟩ e)).toAdd =
        c ((theta e).toAdd) := by
  intro e
  let w : W := eW.symm ((1 : Multiplicative K), p0)
  have hw : eW w = ((1 : Multiplicative K), p0) := by
    simp [w]
  let e' : E := E.normalizerMonoidHom ⟨(x : G), hXE⟩ e
  have he' : (e' : G) = (x : G) * (e : G) * (x : G)⁻¹ := by
    simpa [e'] using
      (Subgroup.normalizerMonoidHom_apply_apply_coe (H := E)
        ⟨(x : G), hXE⟩ e)
  have hconj :
      W.normalizerMonoidHom x
          (W.normalizerMonoidHom ⟨(e : G), hENW e.2⟩ w) =
        W.normalizerMonoidHom ⟨(e' : G), hENW e'.2⟩
          (W.normalizerMonoidHom x w) := by
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [he']
    group
  have hcoord := congrArg (fun z : W => (eW z).1.toAdd) hconj
  have hleft :
      (eW (W.normalizerMonoidHom x
        (W.normalizerMonoidHom ⟨(e : G), hENW e.2⟩ w))).1.toAdd =
        gamma ((theta e).toAdd * (phi p0).toAdd) + beta (Additive.ofMul p0) := by
    rw [hX (W.normalizerMonoidHom ⟨(e : G), hENW e.2⟩ w), hS e w]
    simp [hw]
  have hright :
      (eW (W.normalizerMonoidHom ⟨(e' : G), hENW e'.2⟩
        (W.normalizerMonoidHom x w))).1.toAdd =
        beta (Additive.ofMul p0) +
          (theta e').toAdd *
            (phi ((alpha (Additive.ofMul p0)).toMul)).toAdd := by
    rw [hS e' (W.normalizerMonoidHom x w), hX w]
    simp [hw]
  have hcancel :
      gamma ((theta e).toAdd * (phi p0).toAdd) =
        (theta e').toAdd *
          (phi ((alpha (Additive.ofMul p0)).toMul)).toAdd := by
    have h := hcoord
    rw [hleft, hright] at h
    rw [add_comm (beta (Additive.ofMul p0))
      ((theta e').toAdd *
        (phi ((alpha (Additive.ofMul p0)).toMul)).toAdd)] at h
    exact add_right_cancel h
  have hgraph' :
      gamma ((theta e).toAdd * (phi p0).toAdd) =
        c ((theta e).toAdd) *
          (phi ((alpha (Additive.ofMul p0)).toMul)).toAdd := by
    simpa using hgraph ((theta e).toAdd) (Additive.ofMul p0)
  have halpha_ne : alpha (Additive.ofMul p0) ≠ 0 := by
    intro hzero
    have hzero' : Additive.ofMul p0 = 0 := by
      apply alpha.injective
      simpa using hzero
    exact hp0 (by simpa using congrArg Additive.toMul hzero')
  have hphi_ne :
      (phi ((alpha (Additive.ofMul p0)).toMul)).toAdd ≠ 0 := by
    intro hzero
    have hphi_one : phi ((alpha (Additive.ofMul p0)).toMul) = 1 := by
      exact Multiplicative.toAdd.injective (by simpa using hzero)
    have hp_one : (alpha (Additive.ofMul p0)).toMul = 1 := by
      apply hphi
      simpa using hphi_one
    exact halpha_ne (Additive.toMul.injective (by simpa using hp_one))
  rw [hgraph'] at hcancel
  have hc : c ((theta e).toAdd) = (theta e').toAdd :=
    mul_right_cancel₀ hphi_ne hcancel
  simpa [e'] using hc.symm

end CFSG.ScalarGraphAction
