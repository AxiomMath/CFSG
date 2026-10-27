module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.T4ElimE8

open Module Polynomial Subgroup

section Semisimple

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem inv_isSemisimple (h2 : (2 : K) ≠ 0) (f : End K V) (hf : f * f = 1) : f.IsSemisimple := by
  have hsep : (X ^ 2 - C (1 : K) : K[X]).Separable :=
    Polynomial.separable_X_pow_sub_C (n := 2) (1 : K) (by exact_mod_cast h2) one_ne_zero
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ 2 - C (1 : K)) hsep.squarefree ?_
  simp [pow_two, hf]

theorem inv_iSup_eigenspace (h2 : (2 : K) ≠ 0) (f : End K V) (hf : f * f = 1) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h2' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have hx : x = ((2 : K)⁻¹ • (x + f x)) + ((2 : K)⁻¹ • (x - f x)) := by
    rw [← smul_add]
    have : (x + f x) + (x - f x) = (2 : K) • x := by rw [two_smul]; abel
    rw [this, smul_smul, h2', one_smul]
  have hff : ∀ y, f (f y) = y := fun y => by
    have := congrArg (fun g : End K V => g y) hf
    simpa [Module.End.mul_apply] using this
  have h1 : (2 : K)⁻¹ • (x + f x) ∈ f.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hff, one_smul, add_comm]
  have h2'' : (2 : K)⁻¹ • (x - f x) ∈ f.eigenspace (-1) := by
    rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hff, neg_one_smul, ← smul_neg, neg_sub]
  rw [hx]
  exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem 1 h1) (Submodule.mem_iSup_of_mem (-1) h2'')

theorem const_of_periodic {α : Type*} (ε : ZMod 7 → α) {d : ZMod 7} (hd : d ≠ 0)
    (h : ∀ x, ε (x + d) = ε x) : ∀ x y, ε x = ε y := by
  have hk : ∀ (k : ℕ) (x : ZMod 7), ε (x + k * d) = ε x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, h, ih]
  have hex' : ∀ d : ZMod 7, d ≠ 0 → ∀ x : ZMod 7, ∃ k : Fin 7, x = ((k : ℕ) : ZMod 7) * d := by
    decide
  have hex : ∀ d : ZMod 7, d ≠ 0 → ∀ x : ZMod 7, ∃ k : ℕ, x = (k : ZMod 7) * d := fun d hd x => by
    obtain ⟨k, hk⟩ := hex' d hd x
    exact ⟨k, hk⟩
  have hall : ∀ x, ε x = ε 0 := by
    intro x
    obtain ⟨k, hkx⟩ := hex d hd x
    have := hk k 0
    rw [zero_add, ← hkx] at this
    exact this
  intro x y
  rw [hall x, hall y]

theorem cycle7_eq [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hdim : finrank K V ≤ 6)
    (T : ZMod 7 → End K V) (hT2 : ∀ i, T i * T i = 1) (hTc : ∀ i j, T i * T j = T j * T i)
    (Gm : End K V) (hGinj : Function.Injective Gm) (hG : ∀ i, Gm * T i = T (i + 1) * Gm) :
    T 0 = T 1 := by
  classical
  have hss : ∀ i, (T i).IsSemisimple := fun i => inv_isSemisimple h2 (T i) (hT2 i)
  have hmaxeig : ∀ i μ, (T i).maxGenEigenspace μ = (T i).eigenspace μ := fun i μ =>
    ((hss i).isFinitelySemisimple).maxGenEigenspace_eq_eigenspace μ
  let W : (ZMod 7 → K) → Submodule K V := fun ε => ⨅ i, (T i).eigenspace (ε i)
  have hW : ∀ ε, W ε = ⨅ i, (T i).maxGenEigenspace (ε i) := by
    intro ε
    show ⨅ i, (T i).eigenspace (ε i) = ⨅ i, (T i).maxGenEigenspace (ε i)
    simp only [hmaxeig]
  have hmemW : ∀ ε v, v ∈ W ε ↔ ∀ i, T i v = ε i • v := by
    intro ε v
    show v ∈ (⨅ i, (T i).eigenspace (ε i)) ↔ _
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hcomm : ∀ i j, Commute (T i) (T j) := fun i j => hTc i j
  have htop : ⨆ ε, W ε = ⊤ := by
    have h' : ∀ i, ⨆ μ, (T i).maxGenEigenspace μ = ⊤ := by
      intro i; simp_rw [hmaxeig]; exact inv_iSup_eigenspace h2 (T i) (hT2 i)
    have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T
      (fun i j _ => hcomm i j) h'
    simpa only [hW] using this
  have hind : iSupIndep W := by
    have hWf : W = fun ε => ⨅ i, (T i).maxGenEigenspace (ε i) := funext hW
    rw [hWf]
    exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have : Fintype {ε // W ε ≠ ⊥} := hind.fintypeNeBotOfFiniteDimensional
  have hcard : Fintype.card {ε // W ε ≠ ⊥} ≤ 6 := (hind.subtype_ne_bot_le_finrank).trans hdim
  have hshift : ∀ (m : ℕ) (ε : ZMod 7 → K) (v : V), v ∈ W ε →
      (Gm ^ m) v ∈ W (fun i => ε (i - m)) := by
    intro m
    induction m with
    | zero => intro ε v hv; simpa using hv
    | succ m ih =>
      intro ε v hv
      have h1 := ih ε v hv
      rw [pow_succ', Module.End.mul_apply]
      rw [hmemW] at h1 ⊢
      intro i
      have h3 := h1 (i - 1)
      have h4 := congrArg (fun g : End K V => g ((Gm ^ m) v)) (hG (i - 1))
      simp only [Module.End.mul_apply, sub_add_cancel] at h4
      rw [← h4, h3, map_smul]
      congr 2
      push_cast
      ring
  have hGpow : ∀ m : ℕ, Function.Injective ((Gm ^ m : End K V) : V → V) := by
    intro m
    induction m with
    | zero => intro a b hab; simpa using hab
    | succ m ih =>
      intro a b hab
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply] at hab
      exact hGinj (ih hab)
  have hsupp : ∀ ε, W ε ≠ ⊥ → ∀ x y, ε x = ε y := by
    intro ε hε
    by_contra hnc
    push Not at hnc
    obtain ⟨x0, y0, hxy0⟩ := hnc
    have hne : ∀ m : ℕ, W (fun i => ε (i - m)) ≠ ⊥ := by
      intro m
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hε
      refine (Submodule.ne_bot_iff _).2 ⟨(Gm ^ m) v, hshift m ε v hv, ?_⟩
      intro h0
      exact hv0 (hGpow m (h0.trans (map_zero _).symm))
    let f : ZMod 7 → {ε // W ε ≠ ⊥} := fun k =>
      ⟨fun i => ε (i - k), by simpa [ZMod.natCast_zmod_val] using hne k.val⟩
    have hf : Function.Injective f := by
      intro j k hjk
      by_contra hjk'
      have hd : j - k ≠ 0 := sub_ne_zero.2 hjk'
      have hfun : ∀ i, ε (i - j) = ε (i - k) := fun i => congrFun (congrArg Subtype.val hjk) i
      have hper : ∀ x, ε (x + (j - k)) = ε x := by
        intro x
        have := hfun (x + j)
        rw [add_sub_cancel_right] at this
        rw [this]
        congr 1
        ring
      exact hxy0 (const_of_periodic ε hd hper x0 y0)
    have := Fintype.card_le_of_injective f hf
    rw [ZMod.card] at this
    omega
  have hker : ∀ ε, ∀ v ∈ W ε, T 0 v = T 1 v := by
    intro ε v hv
    by_cases hε : W ε = ⊥
    · rw [hε] at hv
      simp only [Submodule.mem_bot] at hv
      subst hv
      simp
    · have hc := hsupp ε hε 0 1
      rw [(hmemW ε v).1 hv 0, (hmemW ε v).1 hv 1, hc]
  have hle : ⨆ ε, W ε ≤ LinearMap.ker (T 0 - T 1) := by
    refine iSup_le fun ε v hv => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hker ε v hv
  rw [htop] at hle
  ext v
  have hv := hle (Submodule.mem_top (x := v))
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
  exact hv

end Semisimple

section Sigma

variable {R : Type} [Group R] [Finite R]

theorem card_modEq_fix [DecidableEq R] {τ : MulAut R} (hτ7 : τ ^ 7 = 1) (S : Finset R)
    (hS : ∀ s ∈ S, τ s ∈ S) :
    S.card ≡ (S.filter fun s => τ s = s).card [MOD 7] := by
  have : Fintype R := Fintype.ofFinite R
  let f : Function.End S := fun s => ⟨τ s, hS s s.2⟩
  have hfk : ∀ (k : ℕ) (s : S), ((f ^ k) s : R) = (τ ^ k) s := by
    intro k
    induction k with
    | zero => intro s; simp only [pow_zero]; exact rfl
    | succ k ih =>
      intro s
      rw [pow_succ, pow_succ]
      show (((f ^ k) (f s) : S) : R) = (τ ^ k * τ) (s : R)
      rw [ih (f s), MulAut.mul_apply]
  have hf7 : f ^ 7 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    rw [pow_one, hfk, hτ7]
    exact rfl
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) hf7
  rw [Fintype.card_coe] at h
  have : Fintype.card (Function.fixedPoints f) = (S.filter fun s => τ s = s).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x => ⟨(x.1 : R), by
            simp only [Finset.mem_filter]
            exact ⟨x.1.2, by
              have := x.2
              have h2 := congrArg Subtype.val this
              exact h2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Finset.mem_filter.1 y.2).1⟩, by
              apply Subtype.ext
              exact (Finset.mem_filter.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [this] at h
  exact h

variable (hR8 : Nat.card R = 8)
include hR8

theorem fix_eq_one {τ : MulAut R} (hτ : orderOf τ = 7) {r : R} (hr : τ r = r) : r = 1 := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hτ7 : τ ^ 7 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  have h := card_modEq_fix (R := R) hτ7 Finset.univ (fun s _ => Finset.mem_univ _)
  have hcard : (Finset.univ : Finset R).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hR8]
  rw [hcard] at h
  set F := (Finset.univ : Finset R).filter fun s => τ s = s with hF
  have hle : F.card ≤ 8 := by
    calc F.card ≤ (Finset.univ : Finset R).card := Finset.card_le_univ _
      _ = 8 := hcard
  have hpos : 0 < F.card := Finset.card_pos.2 ⟨1, by simp [hF]⟩
  have h8 : F.card = 1 ∨ F.card = 8 := by
    unfold Nat.ModEq at h
    omega
  rcases h8 with h1 | h8
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
    have h1m : (1 : R) ∈ F := by simp [hF]
    have hrm : r ∈ F := by simp [hF, hr]
    rw [ha, Finset.mem_singleton] at h1m hrm
    rw [hrm, h1m]
  · exfalso
    have hall : ∀ s : R, τ s = s := by
      intro s
      have hFc : F.card = Fintype.card R := by rw [h8, ← Nat.card_eq_fintype_card, hR8]
      have : F = Finset.univ := Finset.eq_univ_of_card F hFc
      have hs : s ∈ F := by rw [this]; exact Finset.mem_univ s
      simpa [hF] using hs
    have : τ = 1 := MulEquiv.ext hall
    rw [this, orderOf_one] at hτ
    omega

theorem inv_subgroup_card {τ : MulAut R} (hτ : orderOf τ = 7) (W : Subgroup R)
    (hW : ∀ w ∈ W, τ w ∈ W) : Nat.card W = 1 ∨ Nat.card W = 8 := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have hτ7 : τ ^ 7 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
  let S : Finset R := (W : Set R).toFinset
  have hmem : ∀ s, s ∈ S ↔ s ∈ W := fun s => by simp [S]
  have h := card_modEq_fix hτ7 S (fun s hs => (hmem _).2 (hW s ((hmem s).1 hs)))
  have hfix : S.filter (fun s => τ s = s) = {1} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_singleton, hmem]
    constructor
    · rintro ⟨-, hs⟩; exact fix_eq_one hR8 hτ hs
    · rintro rfl; exact ⟨W.one_mem, map_one τ⟩
  rw [hfix, Finset.card_singleton] at h
  have hcardS : S.card = Nat.card W := by
    rw [Nat.card_eq_fintype_card]
    simp [S, Set.toFinset_card]
  have hle : Nat.card W ≤ 8 := by
    rw [← hR8]
    exact Nat.card_le_card_of_injective _ W.subtype_injective
  have hpos : 0 < Nat.card W := Nat.card_pos
  rw [hcardS] at h
  unfold Nat.ModEq at h
  omega

end Sigma

section Proj

open Matrix

variable {K : Type} [Field K] {n : ℕ} [NeZero n]

abbrev sc (c : Kˣ) : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) c

omit [NeZero n] in
@[simp] theorem sc_one : (sc 1 : GL (Fin n) K) = 1 := map_one _

omit [NeZero n] in
theorem sc_comm (c : Kˣ) (M : GL (Fin n) K) : sc c * M = M * sc c :=
  Matrix.GeneralLinearGroup.scalar_commute (n := Fin n) c M

theorem sc_inj {c d : Kˣ} (h : (sc c : GL (Fin n) K) = sc d) : c = d := by
  have h0 : (Fin n) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) h
  simp [Matrix.GeneralLinearGroup.coe_scalar] at this
  exact Units.ext this

theorem sc_mul_cancel {c d : Kˣ} {M : GL (Fin n) K} (h : sc c * M = sc d * M) : c = d :=
  sc_inj (mul_right_cancel h)

variable {R : Type} [Group R]

structure ProjData (σ : MulAut R) (A : R → GL (Fin n) K) (G : GL (Fin n) K) : Prop where
  mul : ∀ r s, ∃ c : Kˣ, A (r * s) = sc c * (A r * A s)
  faithful : ∀ r, (∃ c : Kˣ, A r = sc c) → r = 1
  conj : ∀ r, ∃ c : Kˣ, G * A r * G⁻¹ = sc c * A (σ r)

variable {σ : MulAut R} {A : R → GL (Fin n) K} {G : GL (Fin n) K}

omit [NeZero n] in
theorem ProjData.one (h : ProjData σ A G) : ∃ c : Kˣ, A 1 = sc c := by
  obtain ⟨c, hc⟩ := h.mul 1 1
  rw [one_mul] at hc
  refine ⟨c⁻¹, ?_⟩
  have h1 : sc c⁻¹ * A 1 = A 1 * A 1 := by
    calc sc c⁻¹ * A 1 = sc c⁻¹ * (sc c * (A 1 * A 1)) := by rw [← hc]
      _ = A 1 * A 1 := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  exact (mul_right_cancel h1).symm

omit [NeZero n] in
theorem ProjData.mul_inv_scalar (h : ProjData σ A G) (r : R) : ∃ c : Kˣ, A r * A r⁻¹ = sc c := by
  obtain ⟨c₁, hc₁⟩ := h.mul r r⁻¹
  obtain ⟨c₀, hc₀⟩ := h.one
  rw [mul_inv_cancel, hc₀] at hc₁
  refine ⟨c₁⁻¹ * c₀, ?_⟩
  calc A r * A r⁻¹ = sc c₁⁻¹ * (sc c₁ * (A r * A r⁻¹)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = sc c₁⁻¹ * sc c₀ := by rw [← hc₁]
    _ = sc (c₁⁻¹ * c₀) := by rw [← map_mul]

omit [NeZero n] in
theorem ProjData.inj (h : ProjData σ A G) {r s : R} {c : Kˣ} (hrs : A r = sc c * A s) : r = s := by
  obtain ⟨d, hd⟩ := h.mul (r * s⁻¹) s
  rw [inv_mul_cancel_right] at hd
  obtain ⟨e, he⟩ := h.mul_inv_scalar s
  have h1 : A (r * s⁻¹) * A s = sc d⁻¹ * A r := by
    calc A (r * s⁻¹) * A s = sc d⁻¹ * (sc d * (A (r * s⁻¹) * A s)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      _ = sc d⁻¹ * A r := by rw [← hd]
  have h2 : A (r * s⁻¹) * A s = sc (d⁻¹ * c) * A s := by
    rw [h1, hrs, ← mul_assoc, ← map_mul]
  have h3 : A (r * s⁻¹) = sc (d⁻¹ * c) := mul_right_cancel h2
  have := h.faithful _ ⟨_, h3⟩
  rwa [mul_inv_eq_one] at this

omit [NeZero n] in
theorem ProjData.sq_scalar (h : ProjData σ A G) (hR2 : ∀ r : R, r * r = 1) (r : R) :
    ∃ c : Kˣ, A r * A r = sc c := by
  obtain ⟨d, hd⟩ := h.mul r r
  obtain ⟨c₀, hc₀⟩ := h.one
  rw [hR2, hc₀] at hd
  refine ⟨d⁻¹ * c₀, ?_⟩
  calc A r * A r = sc d⁻¹ * (sc d * (A r * A r)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = sc d⁻¹ * sc c₀ := by rw [← hd]
    _ = sc (d⁻¹ * c₀) := by rw [← map_mul]

omit [NeZero n] in
theorem ProjData.comm_scalar (h : ProjData σ A G) (hRc : ∀ r s : R, r * s = s * r) (r s : R) :
    ∃ c : Kˣ, A r * A s = sc c * (A s * A r) := by
  obtain ⟨c₁, h₁⟩ := h.mul r s
  obtain ⟨c₂, h₂⟩ := h.mul s r
  rw [hRc r s] at h₁
  refine ⟨c₁⁻¹ * c₂, ?_⟩
  have h3 : sc c₁ * (A r * A s) = sc c₂ * (A s * A r) := by rw [← h₁, ← h₂]
  calc A r * A s = sc c₁⁻¹ * (sc c₁ * (A r * A s)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = sc c₁⁻¹ * (sc c₂ * (A s * A r)) := by rw [h3]
    _ = sc (c₁⁻¹ * c₂) * (A s * A r) := by rw [← mul_assoc, ← map_mul]

omit [NeZero n] in
theorem sc_mul_left_comm (c : Kˣ) (M N : GL (Fin n) K) : M * (sc c * N) = sc c * (M * N) := by
  rw [← mul_assoc, ← sc_comm, mul_assoc]

theorem neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : Kˣ) ≠ 1 := by
  intro h
  apply h2
  have h' : ((-1 : Kˣ) : K) = 1 := by rw [h]; rfl
  have : (-1 : K) = 1 := by simpa using h'
  linear_combination -this

theorem ProjData.sign (h : ProjData σ A G) (hR2 : ∀ r : R, r * r = 1)
    (hRc : ∀ r s : R, r * s = s * r) (r s : R) :
    A r * A s = A s * A r ∨ A r * A s = sc (-1) * (A s * A r) := by
  obtain ⟨c, hc⟩ := h.comm_scalar hRc r s
  obtain ⟨l, hl⟩ := h.sq_scalar hR2 s
  have hY : A r * (A s * A s) = (A s * A s) * A r := by rw [hl]; exact (sc_comm l (A r)).symm
  have hX : A r * (A s * A s) = sc (c * c) * ((A s * A s) * A r) := by
    calc A r * (A s * A s) = (A r * A s) * A s := by rw [mul_assoc]
      _ = (sc c * (A s * A r)) * A s := by rw [hc]
      _ = sc c * (A s * (A r * A s)) := by rw [mul_assoc, mul_assoc]
      _ = sc c * (A s * (sc c * (A s * A r))) := by rw [hc]
      _ = sc c * (sc c * (A s * (A s * A r))) := by rw [sc_mul_left_comm]
      _ = sc (c * c) * ((A s * A s) * A r) := by
        rw [← mul_assoc, ← map_mul, mul_assoc (A s) (A s) (A r)]
  have hcc : c * c = 1 := by
    have h3 : sc 1 * ((A s * A s) * A r) = sc (c * c) * ((A s * A s) * A r) := by
      rw [sc_one, one_mul, ← hX, hY]
    exact (sc_mul_cancel h3).symm
  have hc1 : (c : K) * c = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hcc
    simpa using this
  rcases mul_self_eq_one_iff.1 hc1 with h1 | h1
  · left
    have : c = 1 := Units.ext h1
    rw [hc, this, sc_one, one_mul]
  · right
    have : c = -1 := Units.ext (by simpa using h1)
    rw [hc, this]

variable (A) in
noncomputable def esgn (r s : R) : Kˣ := by
  classical exact if A r * A s = A s * A r then 1 else -1

theorem esgn_spec (h : ProjData σ A G) (hR2 : ∀ r : R, r * r = 1) (hRc : ∀ r s : R, r * s = s * r)
    (r s : R) : A r * A s = sc (esgn A r s) * (A s * A r) := by
  classical
  by_cases hcm : A r * A s = A s * A r
  · have : esgn A r s = 1 := by unfold esgn; simp [hcm]
    rw [this, sc_one, one_mul]; exact hcm
  · have : esgn A r s = -1 := by unfold esgn; simp [hcm]
    rw [this]
    rcases h.sign hR2 hRc r s with h1 | h1
    · exact absurd h1 hcm
    · exact h1

omit [NeZero n] [Group R] in
theorem esgn_eq_one_iff (h2 : (2 : K) ≠ 0) (r s : R) :
    esgn A r s = 1 ↔ A r * A s = A s * A r := by
  classical
  by_cases hcm : A r * A s = A s * A r
  · have : esgn A r s = 1 := by unfold esgn; simp [hcm]
    simp [this, hcm]
  · have : esgn A r s = -1 := by unfold esgn; simp [hcm]
    rw [this]
    simp only [hcm, iff_false]
    exact neg_one_ne_one h2

theorem esgn_mul (h : ProjData σ A G) (hR2 : ∀ r : R, r * r = 1) (hRc : ∀ r s : R, r * s = s * r)
    (r s t : R) : esgn A r (s * t) = esgn A r s * esgn A r t := by
  obtain ⟨c, hc⟩ := h.mul s t
  have e1 := esgn_spec h hR2 hRc r s
  have e2 := esgn_spec h hR2 hRc r t
  have e3 := esgn_spec h hR2 hRc r (s * t)
  have hL : A r * A (s * t) = sc (c * (esgn A r s * esgn A r t)) * (A s * A t * A r) := by
    calc A r * A (s * t) = A r * (sc c * (A s * A t)) := by rw [hc]
      _ = sc c * (A r * (A s * A t)) := by rw [sc_mul_left_comm]
      _ = sc c * ((A r * A s) * A t) := by rw [mul_assoc]
      _ = sc c * ((sc (esgn A r s) * (A s * A r)) * A t) := by rw [e1]
      _ = sc c * (sc (esgn A r s) * (A s * (A r * A t))) := by rw [mul_assoc, mul_assoc]
      _ = sc c * (sc (esgn A r s) * (A s * (sc (esgn A r t) * (A t * A r)))) := by rw [e2]
      _ = sc c * (sc (esgn A r s) * (sc (esgn A r t) * (A s * (A t * A r)))) := by
          rw [sc_mul_left_comm (esgn A r t) (A s) (A t * A r)]
      _ = sc (c * (esgn A r s * esgn A r t)) * (A s * A t * A r) := by
          rw [← mul_assoc (sc (esgn A r s)), ← map_mul, ← mul_assoc, ← map_mul, mul_assoc (A s)]
  have hR : A r * A (s * t) = sc (esgn A r (s * t) * c) * (A s * A t * A r) := by
    calc A r * A (s * t) = sc (esgn A r (s * t)) * (A (s * t) * A r) := e3
      _ = sc (esgn A r (s * t)) * ((sc c * (A s * A t)) * A r) := by rw [hc]
      _ = sc (esgn A r (s * t) * c) * (A s * A t * A r) := by
          rw [mul_assoc (sc c), ← mul_assoc (sc (esgn A r (s * t))), ← map_mul]
  have := sc_mul_cancel (hR.symm.trans hL)
  have h5 : esgn A r (s * t) * c = (esgn A r s * esgn A r t) * c := by
    rw [this, mul_comm c]
  exact mul_right_cancel h5

omit [NeZero n] [Group R] in
theorem esgn_cases (r s : R) : esgn A r s = 1 ∨ esgn A r s = -1 := by
  classical
  by_cases hcm : A r * A s = A s * A r
  · left; unfold esgn; simp [hcm]
  · right; unfold esgn; simp [hcm]

variable (A) in
def Cm (r s : R) : Prop := A r * A s = A s * A r

theorem cm_mul (h : ProjData σ A G) (h2 : (2 : K) ≠ 0) (hR2 : ∀ r : R, r * r = 1)
    (hRc : ∀ r s : R, r * s = s * r) (r s t : R) :
    Cm A r (s * t) ↔ (Cm A r s ↔ Cm A r t) := by
  have hm := esgn_mul h hR2 hRc r s t
  have h1 : ∀ r s : R, esgn A r s = 1 ↔ Cm A r s := fun r s => esgn_eq_one_iff (A := A) h2 r s
  rw [← h1 r (s * t), ← h1 r s, ← h1 r t, hm]
  rcases esgn_cases (A := A) r s with e1 | e1 <;>
    rcases esgn_cases (A := A) r t with e2 | e2 <;>
    simp [e1, e2, neg_one_ne_one h2]

omit [NeZero n] [Group R] in
theorem cm_symm {r s : R} : Cm A r s ↔ Cm A s r := by
  unfold Cm; exact ⟨Eq.symm, Eq.symm⟩

omit [NeZero n] [Group R] in
theorem cm_refl (r : R) : Cm A r r := by unfold Cm; exact rfl

omit [NeZero n] in
theorem cm_one (h : ProjData σ A G) (r : R) : Cm A r 1 := by
  obtain ⟨c, hc⟩ := h.one
  unfold Cm
  rw [hc]
  exact (sc_comm c (A r)).symm

omit [NeZero n] in
theorem cm_conj (h : ProjData σ A G) (r s : R) : Cm A (σ r) (σ s) ↔ Cm A r s := by
  obtain ⟨c, hc⟩ := h.conj r
  obtain ⟨d, hd⟩ := h.conj s
  have k1 : G * (A r * A s) * G⁻¹ = sc (c * d) * (A (σ r) * A (σ s)) := by
    calc G * (A r * A s) * G⁻¹ = (G * A r * G⁻¹) * (G * A s * G⁻¹) := by group
      _ = (sc c * A (σ r)) * (sc d * A (σ s)) := by rw [hc, hd]
      _ = sc c * (sc d * (A (σ r) * A (σ s))) := by
          rw [mul_assoc, sc_mul_left_comm d]
      _ = sc (c * d) * (A (σ r) * A (σ s)) := by rw [← mul_assoc, ← map_mul]
  have k2 : G * (A s * A r) * G⁻¹ = sc (d * c) * (A (σ s) * A (σ r)) := by
    calc G * (A s * A r) * G⁻¹ = (G * A s * G⁻¹) * (G * A r * G⁻¹) := by group
      _ = (sc d * A (σ s)) * (sc c * A (σ r)) := by rw [hc, hd]
      _ = sc d * (sc c * (A (σ s) * A (σ r))) := by
          rw [mul_assoc, sc_mul_left_comm c]
      _ = sc (d * c) * (A (σ s) * A (σ r)) := by rw [← mul_assoc, ← map_mul]
  unfold Cm
  constructor
  · intro hσ'
    have h3 : G * (A r * A s) * G⁻¹ = G * (A s * A r) * G⁻¹ := by
      rw [k1, k2, mul_comm d c, hσ']
    exact mul_left_cancel (mul_right_cancel h3)
  · intro hcm
    have h3 : sc (c * d) * (A (σ r) * A (σ s)) = sc (c * d) * (A (σ s) * A (σ r)) := by
      rw [← k1, mul_comm c d, ← k2, hcm]
    exact mul_left_cancel h3

structure ProjData' (σ : MulAut R) (A : R → GL (Fin n) K) (G : GL (Fin n) K) : Prop where
  proj : ProjData σ A G
  two : (2 : K) ≠ 0
  sq : ∀ r : R, r * r = 1
  comm : ∀ r s : R, r * s = s * r

def cmSub (hb : ProjData' σ A G) (r : R) : Subgroup R where
  carrier := {s | Cm A r s}
  mul_mem' := fun {s t} hs ht =>
    (cm_mul hb.proj hb.two hb.sq hb.comm r s t).2 ⟨fun _ => ht, fun _ => hs⟩
  one_mem' := cm_one hb.proj r
  inv_mem' := fun {s} hs => by
    rw [inv_eq_of_mul_eq_one_right (hb.sq s)]; exact hs

def radSub (hb : ProjData' σ A G) : Subgroup R where
  carrier := {r | ∀ s, Cm A r s}
  mul_mem' := fun {r r'} hr hr' s =>
    cm_symm.2 ((cm_mul hb.proj hb.two hb.sq hb.comm s r r').2
      ⟨fun _ => cm_symm.1 (hr' s), fun _ => cm_symm.1 (hr s)⟩)
  one_mem' := fun s => cm_symm.2 (cm_one hb.proj s)
  inv_mem' := fun {r} hr => by
    rw [inv_eq_of_mul_eq_one_right (hb.sq r)]; exact hr

theorem mem_cmSub (hb : ProjData' σ A G) {r s : R} : s ∈ cmSub hb r ↔ Cm A r s := Iff.rfl

theorem radSub_inv (hb : ProjData' σ A G) {r : R} (hr : r ∈ radSub hb) : σ r ∈ radSub hb := by
  intro s
  obtain ⟨s', rfl⟩ := σ.surjective s
  exact (cm_conj hb.proj r s').2 (hr s')

theorem comm_all [Finite R] (hb : ProjData' σ A G) (hR8 : Nat.card R = 8) (hσ : orderOf σ = 7) :
    ∀ r s : R, A r * A s = A s * A r := by
  classical
  have : Fintype R := Fintype.ofFinite R
  have h := hb.proj
  rcases inv_subgroup_card hR8 hσ (radSub hb) (fun w hw => radSub_inv hb hw) with h1 | h8
  · exfalso
    have hbot : radSub hb = ⊥ := Subgroup.card_eq_one.1 h1
    have hnt : Nontrivial R := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    have hidx : ∀ x : R, x ≠ 1 → Nat.card (cmSub hb x) = 4 := by
      intro x hx
      have hxn : x ∉ radSub hb := by rw [hbot]; simpa using hx
      have : ∃ s₀, ¬ Cm A x s₀ := by
        by_contra hcon
        push Not at hcon
        exact hxn hcon
      obtain ⟨s₀, hs₀⟩ := this
      have hidx2 : (cmSub hb x).index = 2 := by
        rw [Subgroup.index_eq_two_iff]
        refine ⟨s₀, fun b => ?_⟩
        have := cm_mul hb.proj hb.two hb.sq hb.comm x b s₀
        simp only [mem_cmSub]
        tauto
      have := Subgroup.card_mul_index (cmSub hb x)
      rw [hidx2, hR8] at this
      omega
    obtain ⟨r, hr1⟩ := exists_ne (1 : R)
    have hex : ∃ s ∈ cmSub hb r, s ≠ 1 ∧ s ≠ r := by
      by_contra hcon
      push Not at hcon
      have hsub : ((cmSub hb r : Set R).toFinset) ⊆ {1, r} := by
        intro s hs
        rw [Set.mem_toFinset] at hs
        by_cases hs1 : s = 1
        · simp [hs1]
        · simp [hcon s hs hs1]
      have h2le : (cmSub hb r : Set R).toFinset.card ≤ 2 :=
        (Finset.card_le_card hsub).trans Finset.card_le_two
      have : Nat.card (cmSub hb r) = (cmSub hb r : Set R).toFinset.card := by
        rw [Nat.card_eq_fintype_card, Set.toFinset_card]; rfl
      have := hidx r hr1
      omega
    obtain ⟨s, hsK, hs1, hsr⟩ := hex
    have hsK' : Cm A r s := hsK
    have hcs4 := hidx s hs1
    have hcr4 := hidx r hr1
    have hrs1 : r * s ≠ 1 := by
      intro hrs
      apply hsr
      have := inv_eq_of_mul_eq_one_right hrs
      rw [← this, inv_eq_of_mul_eq_one_right (hb.sq r)]
    have hF4 : ({1, r, s, r * s} : Finset R).card = 4 := by
      have h1 : (1 : R) ∉ ({r, s, r * s} : Finset R) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hr1.symm, hs1.symm, hrs1.symm⟩
      have h2 : r ∉ ({s, r * s} : Finset R) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hsr.symm, fun h => hs1 ?_⟩
        exact (mul_eq_left.1 h.symm)
      have h3 : s ∉ ({r * s} : Finset R) := by
        simp only [Finset.mem_singleton]
        intro h
        exact hr1 (mul_eq_right.1 h.symm)
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
    let D : Subgroup R := cmSub hb r ⊓ cmSub hb s
    have hFD : ({1, r, s, r * s} : Finset R) ⊆ (D : Set R).toFinset := by
      intro t ht
      rw [Set.mem_toFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact D.one_mem
      · exact ⟨cm_refl _, cm_symm.1 hsK'⟩
      · exact ⟨hsK', cm_refl _⟩
      · exact D.mul_mem ⟨cm_refl _, cm_symm.1 hsK'⟩ ⟨hsK', cm_refl _⟩
    have hDcard : 4 ≤ Nat.card D := by
      have h5 : Nat.card D = (D : Set R).toFinset.card := by
        rw [Nat.card_eq_fintype_card, Set.toFinset_card]; rfl
      rw [h5, ← hF4]
      exact Finset.card_le_card hFD
    have hDr : D = cmSub hb r := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have hDs : D = cmSub hb s := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    have hrs : cmSub hb r = cmSub hb s := hDr.symm.trans hDs
    have hmem : r * s ∈ radSub hb := by
      intro t
      have e1 := cm_mul hb.proj hb.two hb.sq hb.comm t r s
      have e2 : Cm A r t ↔ Cm A s t := by
        rw [← mem_cmSub hb, hrs, mem_cmSub hb]
      have e3 : Cm A t r ↔ Cm A t s :=
        ⟨fun h => cm_symm.1 (e2.1 (cm_symm.1 h)), fun h => cm_symm.1 (e2.2 (cm_symm.1 h))⟩
      exact cm_symm.1 (e1.2 e3)
    exact hrs1 (Subgroup.mem_bot.1 (hbot ▸ hmem))
  · have : radSub hb = ⊤ := (Subgroup.card_eq_iff_eq_top (radSub hb)).1 (by rw [h8, hR8])
    intro r s
    have hr : r ∈ radSub hb := by rw [this]; trivial
    exact hr s

theorem isSquare_mul_of_not [Finite K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hna : ¬ IsSquare a)
    (hnb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h1 : quadraticChar K a = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hna
  have h2 : quadraticChar K b = -1 := quadraticChar_neg_one_iff_not_isSquare.2 hnb
  have h3 : quadraticChar K (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).1 h3

noncomputable def lam (hb : ProjData' σ A G) (r : R) : Kˣ := (hb.proj.sq_scalar hb.sq r).choose

omit [NeZero n] in
theorem lam_spec (hb : ProjData' σ A G) (r : R) : A r * A r = sc (lam hb r) :=
  (hb.proj.sq_scalar hb.sq r).choose_spec

theorem lam_mul (hb : ProjData' σ A G) (hcomm : ∀ r s : R, A r * A s = A s * A r) (r s : R) :
    ∃ c : Kˣ, lam hb (r * s) = c * c * (lam hb r * lam hb s) := by
  obtain ⟨c, hc⟩ := hb.proj.mul r s
  refine ⟨c, sc_inj (n := n) (K := K) ?_⟩
  rw [← lam_spec hb, hc]
  calc sc c * (A r * A s) * (sc c * (A r * A s))
      = sc c * (sc c * ((A r * A s) * (A r * A s))) := by
        rw [mul_assoc, sc_mul_left_comm c (A r * A s) (A r * A s)]
    _ = sc (c * c) * ((A r * A s) * (A r * A s)) := by rw [← mul_assoc, ← map_mul]
    _ = sc (c * c) * ((A r * A r) * (A s * A s)) := by
        congr 1
        calc A r * A s * (A r * A s) = A r * (A s * A r) * A s := by group
          _ = A r * (A r * A s) * A s := by rw [hcomm s r]
          _ = A r * A r * (A s * A s) := by group
    _ = sc (c * c * (lam hb r * lam hb s)) := by
        rw [lam_spec hb r, lam_spec hb s, ← map_mul, ← map_mul]

theorem lam_conj (hb : ProjData' σ A G) (r : R) : ∃ d : Kˣ, lam hb r = d * d * lam hb (σ r) := by
  obtain ⟨d, hd⟩ := hb.proj.conj r
  refine ⟨d, sc_inj (n := n) (K := K) ?_⟩
  have h1 : G * (A r * A r) * G⁻¹ = (G * A r * G⁻¹) * (G * A r * G⁻¹) := by group
  rw [lam_spec hb r] at h1
  rw [hd] at h1
  have h2 : G * sc (lam hb r) * G⁻¹ = sc (lam hb r) := by
    rw [← sc_comm, mul_assoc, mul_inv_cancel, mul_one]
  rw [h2] at h1
  rw [h1]
  calc sc d * A (σ r) * (sc d * A (σ r)) = sc d * (sc d * (A (σ r) * A (σ r))) := by
        rw [mul_assoc, sc_mul_left_comm d (A (σ r)) (A (σ r))]
    _ = sc (d * d * lam hb (σ r)) := by
        rw [lam_spec hb (σ r), ← mul_assoc, ← map_mul, ← map_mul]

theorem isSquare_units_iff {u : Kˣ} : IsSquare u ↔ IsSquare (u : K) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, by simp⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro h0
      apply u.ne_zero
      rw [hy, h0, mul_zero]
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

theorem exists_involution_lift [Finite K] [Finite R] (hb : ProjData' σ A G) (hR8 : Nat.card R = 8)
    (hσ : orderOf σ = 7) :
    ∃ (r₀ : R) (B₀ : GL (Fin n) K) (e : Kˣ), r₀ ≠ 1 ∧ B₀ * B₀ = 1 ∧ B₀ = sc e * A r₀ := by
  classical
  have hcomm := comm_all hb hR8 hσ
  let Sq : Subgroup R :=
    { carrier := {r | IsSquare (lam hb r)}
      mul_mem' := fun {r s} hr hs => by
        obtain ⟨c, hc⟩ := lam_mul hb hcomm r s
        obtain ⟨a, ha⟩ := hr
        obtain ⟨b, hb'⟩ := hs
        exact ⟨c * a * b, by rw [hc, ha, hb']; simp only [mul_comm, mul_left_comm]⟩
      one_mem' := by
        obtain ⟨a, ha⟩ := hb.proj.one
        refine ⟨a, sc_inj (n := n) (K := K) ?_⟩
        rw [← lam_spec hb, ha, ← map_mul]
      inv_mem' := fun {r} hr => by
        rw [inv_eq_of_mul_eq_one_right (hb.sq r)]; exact hr }
  have hSqmem : ∀ r, r ∈ Sq ↔ IsSquare (lam hb r) := fun r => Iff.rfl
  have hinv : ∀ w ∈ Sq, σ w ∈ Sq := by
    intro w hw
    obtain ⟨x, hx⟩ := (hSqmem w).1 hw
    obtain ⟨d, hd⟩ := lam_conj hb w
    refine (hSqmem _).2 ⟨d⁻¹ * x, ?_⟩
    have : lam hb (σ w) = (d * d)⁻¹ * lam hb w := by rw [hd]; group
    rw [this, hx, mul_inv]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rcases inv_subgroup_card hR8 hσ Sq hinv with h1 | h8
  · exfalso
    have hbot : Sq = ⊥ := Subgroup.card_eq_one.1 h1
    have : Fintype R := Fintype.ofFinite R
    have hnt : Nontrivial R := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨r, hr1⟩ := exists_ne (1 : R)
    have hex : ∃ s : R, s ≠ 1 ∧ s ≠ r := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset R) ⊆ {1, r} := by
        intro s _
        by_cases hs1 : s = 1
        · simp [hs1]
        · simp [hcon s hs1]
      have := (Finset.card_le_card hsub).trans Finset.card_le_two
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hR8] at this
      omega
    obtain ⟨s, hs1, hsr⟩ := hex
    have hrs1 : r * s ≠ 1 := by
      intro hrs
      apply hsr
      have := inv_eq_of_mul_eq_one_right hrs
      rw [← this, inv_eq_of_mul_eq_one_right (hb.sq r)]
    have hnr : ¬ IsSquare (lam hb r) := fun h => hr1 (by
      have : r ∈ Sq := (hSqmem r).2 h
      rw [hbot, Subgroup.mem_bot] at this; exact this)
    have hns : ¬ IsSquare (lam hb s) := fun h => hs1 (by
      have : s ∈ Sq := (hSqmem s).2 h
      rw [hbot, Subgroup.mem_bot] at this; exact this)
    have hsq : IsSquare (lam hb r * lam hb s) := by
      rw [isSquare_units_iff, Units.val_mul]
      refine isSquare_mul_of_not (lam hb r).ne_zero (lam hb s).ne_zero ?_ ?_
      · rwa [← isSquare_units_iff]
      · rwa [← isSquare_units_iff]
    obtain ⟨c, hc⟩ := lam_mul hb hcomm r s
    have : r * s ∈ Sq := by
      rw [hSqmem, hc]
      obtain ⟨y, hy⟩ := hsq
      exact ⟨c * y, by rw [hy]; simp only [mul_comm, mul_left_comm]⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hrs1 this
  · have : Sq = ⊤ := (Subgroup.card_eq_iff_eq_top Sq).1 (by rw [h8, hR8])
    have hnt : Nontrivial R := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨r₀, hr₀⟩ := exists_ne (1 : R)
    have hmem : r₀ ∈ Sq := by rw [this]; trivial
    obtain ⟨μ, hμ⟩ := (hSqmem r₀).1 hmem
    refine ⟨r₀, sc μ⁻¹ * A r₀, μ⁻¹, hr₀, ?_, rfl⟩
    calc sc μ⁻¹ * A r₀ * (sc μ⁻¹ * A r₀) = sc μ⁻¹ * (sc μ⁻¹ * (A r₀ * A r₀)) := by
          rw [mul_assoc, sc_mul_left_comm μ⁻¹ (A r₀) (A r₀)]
      _ = 1 := by
          rw [lam_spec hb r₀, hμ, ← mul_assoc, ← map_mul, ← map_mul]
          group
          simp

omit [NeZero n] in
theorem conj_pow (h : ProjData σ A G) (m : ℕ) (r : R) :
    ∃ c : Kˣ, G ^ m * A r * (G ^ m)⁻¹ = sc c * A ((σ ^ m) r) := by
  induction m generalizing r with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih r
    obtain ⟨d, hd⟩ := h.conj ((σ ^ m) r)
    refine ⟨c * d, ?_⟩
    have e1 : G ^ (m + 1) * A r * (G ^ (m + 1))⁻¹ = G * (G ^ m * A r * (G ^ m)⁻¹) * G⁻¹ := by
      rw [pow_succ']; group
    have e2 : (σ ^ (m + 1)) r = σ ((σ ^ m) r) := by rw [pow_succ']; rfl
    rw [e1, hc, e2]
    calc G * (sc c * A ((σ ^ m) r)) * G⁻¹ = sc c * (G * A ((σ ^ m) r) * G⁻¹) := by
          rw [sc_mul_left_comm c G (A ((σ ^ m) r)), mul_assoc]
      _ = sc (c * d) * A (σ ((σ ^ m) r)) := by rw [hd, ← mul_assoc, ← map_mul]

omit [NeZero n] in
theorem sc_sc_swap (c d : Kˣ) (X : GL (Fin n) K) : sc c * (sc d * X) = sc d * (sc c * X) := by
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]

omit [NeZero n] in
theorem conj_sc (g : GL (Fin n) K) (c : Kˣ) (M : GL (Fin n) K) :
    g * (sc c * M) * g⁻¹ = sc c * (g * M * g⁻¹) := by
  rw [sc_mul_left_comm c g M, mul_assoc]

theorem cyclic_family (h : ProjData σ A G) {r₀ : R} {B₀ : GL (Fin n) K} {e : Kˣ}
    (hσ7 : σ ^ 7 = 1) (hB₀2 : B₀ * B₀ = 1) (hB₀e : B₀ = sc e * A r₀) :
    ∃ (H : GL (Fin n) K) (B : ZMod 7 → GL (Fin n) K),
      (∀ i, B i * B i = 1) ∧ (∀ i, H * B i * H⁻¹ = B (i + 1)) ∧ B 0 = B₀ ∧
      (∀ i, ∃ (c : Kˣ) (r : R), B i = sc c * A r) ∧ ∃ c : Kˣ, B 1 = sc c * A (σ r₀) := by
  obtain ⟨c7, hc7⟩ := conj_pow h 7 r₀
  have hσ7r : (σ ^ 7) r₀ = r₀ := by rw [hσ7]; rfl
  rw [hσ7r] at hc7
  have hg7 : G ^ 7 * B₀ * (G ^ 7)⁻¹ = sc c7 * B₀ := by
    rw [hB₀e, conj_sc, hc7, sc_sc_swap]
  have hc7sq : c7 * c7 = 1 := by
    have h1 : (G ^ 7 * B₀ * (G ^ 7)⁻¹) * (G ^ 7 * B₀ * (G ^ 7)⁻¹) = 1 := by
      calc (G ^ 7 * B₀ * (G ^ 7)⁻¹) * (G ^ 7 * B₀ * (G ^ 7)⁻¹) = G ^ 7 * (B₀ * B₀) * (G ^ 7)⁻¹ := by
            group
        _ = 1 := by rw [hB₀2]; group
    rw [hg7] at h1
    have h2 : sc c7 * B₀ * (sc c7 * B₀) = sc (c7 * c7) := by
      rw [mul_assoc, sc_mul_left_comm c7 B₀ B₀, hB₀2, mul_one, ← map_mul]
    rw [h2] at h1
    exact sc_inj (n := n) (K := K) (by rw [h1, sc_one])
  have hg7k : ∀ k : ℕ, (G ^ 7) ^ k * B₀ * ((G ^ 7) ^ k)⁻¹ = sc (c7 ^ k) * B₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : (G ^ 7) ^ (k + 1) * B₀ * ((G ^ 7) ^ (k + 1))⁻¹
          = G ^ 7 * ((G ^ 7) ^ k * B₀ * ((G ^ 7) ^ k)⁻¹) * (G ^ 7)⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih, conj_sc, hg7, ← mul_assoc, ← map_mul, pow_succ]
  have hH7 : (G ^ 8) ^ 7 * B₀ * ((G ^ 8) ^ 7)⁻¹ = B₀ := by
    have e : (G ^ 8) ^ 7 = (G ^ 7) ^ 8 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [e, hg7k 8]
    have : c7 ^ 8 = 1 := by
      have : c7 ^ 8 = (c7 * c7) ^ 4 := by rw [← pow_two, ← pow_mul]
      rw [this, hc7sq, one_pow]
    rw [this, sc_one, one_mul]
  set H : GL (Fin n) K := G ^ 8 with hH
  let B : ZMod 7 → GL (Fin n) K := fun i => H ^ i.val * B₀ * (H ^ i.val)⁻¹
  have hq : ∀ q : ℕ, (H ^ 7) ^ q * B₀ * ((H ^ 7) ^ q)⁻¹ = B₀ := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      have e1 : (H ^ 7) ^ (q + 1) * B₀ * ((H ^ 7) ^ (q + 1))⁻¹
          = H ^ 7 * ((H ^ 7) ^ q * B₀ * ((H ^ 7) ^ q)⁻¹) * (H ^ 7)⁻¹ := by
        rw [pow_succ']; group
      rw [e1, ih, hH7]
  have hBk : ∀ k : ℕ, H ^ k * B₀ * (H ^ k)⁻¹ = B (k : ZMod 7) := by
    intro k
    have hv : ((k : ZMod 7)).val = k % 7 := ZMod.val_natCast 7 k
    show _ = H ^ ((k : ZMod 7).val) * B₀ * (H ^ ((k : ZMod 7).val))⁻¹
    rw [hv]
    have hk : H ^ k = H ^ (k % 7) * (H ^ 7) ^ (k / 7) := by
      calc H ^ k = H ^ (k % 7 + 7 * (k / 7)) := by rw [Nat.mod_add_div]
        _ = H ^ (k % 7) * (H ^ 7) ^ (k / 7) := by rw [pow_add, pow_mul]
    rw [hk]
    calc H ^ (k % 7) * (H ^ 7) ^ (k / 7) * B₀ * (H ^ (k % 7) * (H ^ 7) ^ (k / 7))⁻¹
        = H ^ (k % 7) * ((H ^ 7) ^ (k / 7) * B₀ * ((H ^ 7) ^ (k / 7))⁻¹) * (H ^ (k % 7))⁻¹ := by
          group
      _ = H ^ (k % 7) * B₀ * (H ^ (k % 7))⁻¹ := by rw [hq]
  refine ⟨H, B, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show (H ^ i.val * B₀ * (H ^ i.val)⁻¹) * (H ^ i.val * B₀ * (H ^ i.val)⁻¹) = 1
    calc _ = H ^ i.val * (B₀ * B₀) * (H ^ i.val)⁻¹ := by group
      _ = 1 := by rw [hB₀2]; group
  · intro i
    have h1 : H * B i * H⁻¹ = H ^ (i.val + 1) * B₀ * (H ^ (i.val + 1))⁻¹ := by
      show H * (H ^ i.val * B₀ * (H ^ i.val)⁻¹) * H⁻¹ = _
      rw [pow_succ']; group
    rw [h1, hBk (i.val + 1)]
    congr 1
  · show H ^ (0 : ZMod 7).val * B₀ * (H ^ (0 : ZMod 7).val)⁻¹ = B₀
    simp
  · intro i
    obtain ⟨c, hc⟩ := conj_pow h (8 * i.val) r₀
    refine ⟨e * c, (σ ^ (8 * i.val)) r₀, ?_⟩
    show H ^ i.val * B₀ * (H ^ i.val)⁻¹ = _
    have : H ^ i.val = G ^ (8 * i.val) := by rw [hH, ← pow_mul]
    rw [this, hB₀e, conj_sc, hc, ← mul_assoc, ← map_mul]
  · obtain ⟨c, hc⟩ := conj_pow h 8 r₀
    have h8 : (σ ^ 8) r₀ = σ r₀ := by
      rw [show (8 : ℕ) = 7 + 1 from rfl, pow_add, hσ7, one_mul, pow_one]
    rw [h8] at hc
    refine ⟨e * c, ?_⟩
    show H ^ (1 : ZMod 7).val * B₀ * (H ^ (1 : ZMod 7).val)⁻¹ = _
    have hv : (1 : ZMod 7).val = 1 := rfl
    rw [hv, pow_one, hH, hB₀e, conj_sc, hc, ← mul_assoc, ← map_mul]

theorem no_E8_seven_core [Finite K] [Finite R] (hb : ProjData' σ A G) (hR8 : Nat.card R = 8)
    (hσ : orderOf σ = 7) (hn : n ≤ 6) : False := by
  classical
  have h := hb.proj
  have hcomm := comm_all hb hR8 hσ
  have hσ7 : σ ^ 7 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨r₀, B₀, e, hr₀, hB₀2, hB₀e⟩ := exists_involution_lift hb hR8 hσ
  obtain ⟨H, B, hB2, hHB, hB0, hBsc, c1, hB1⟩ := cyclic_family h hσ7 hB₀2 hB₀e
  have hBc : ∀ i j, B i * B j = B j * B i := by
    intro i j
    obtain ⟨c, r, hi⟩ := hBsc i
    obtain ⟨d, s, hj⟩ := hBsc j
    rw [hi, hj]
    calc sc c * A r * (sc d * A s) = sc c * (sc d * (A r * A s)) := by
          rw [mul_assoc, sc_mul_left_comm d (A r) (A s)]
      _ = sc c * (sc d * (A s * A r)) := by rw [hcomm r s]
      _ = sc d * (sc c * (A s * A r)) := sc_sc_swap c d _
      _ = sc d * A s * (sc c * A r) := by rw [mul_assoc, sc_mul_left_comm c (A s) (A r)]
  have hne : B 0 ≠ B 1 := by
    intro heq
    rw [hB0, hB₀e, hB1] at heq
    have h3 : A r₀ = sc (e⁻¹ * c1) * A (σ r₀) := by
      calc A r₀ = sc e⁻¹ * (sc e * A r₀) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
        _ = sc e⁻¹ * (sc c1 * A (σ r₀)) := by rw [heq]
        _ = sc (e⁻¹ * c1) * A (σ r₀) := by rw [← mul_assoc, ← map_mul]
    have h4 := h.inj h3
    exact hr₀ (fix_eq_one hR8 hσ h4.symm)
  let T : ZMod 7 → Module.End K (Fin n → K) := fun i => Matrix.toLin' (B i : Matrix (Fin n) (Fin n) K)
  have hmat : ∀ (M N : GL (Fin n) K), Matrix.toLin' ((M * N : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = Matrix.toLin' (M : Matrix (Fin n) (Fin n) K) * Matrix.toLin' (N : Matrix (Fin n) (Fin n) K) := by
    intro M N
    rw [Units.val_mul, Matrix.toLin'_mul]
    rfl
  have hT2 : ∀ i, T i * T i = 1 := by
    intro i
    show Matrix.toLin' (B i : Matrix (Fin n) (Fin n) K) * Matrix.toLin' (B i : Matrix (Fin n) (Fin n) K) = 1
    rw [← hmat, hB2 i]
    simp
    rfl
  have hTc : ∀ i j, T i * T j = T j * T i := by
    intro i j
    show Matrix.toLin' (B i : Matrix (Fin n) (Fin n) K) * Matrix.toLin' (B j : Matrix (Fin n) (Fin n) K) = _
    rw [← hmat, ← hmat, hBc i j]
  let Gm : Module.End K (Fin n → K) := Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)
  have hGinj : Function.Injective Gm := by
    intro v w hvw
    have h1 : (H : Matrix (Fin n) (Fin n) K).mulVec v = (H : Matrix (Fin n) (Fin n) K).mulVec w := by
      simpa [Gm, Matrix.toLin'_apply] using hvw
    have h2 := congrArg (fun u => ((H⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec u) h1
    simpa [Matrix.mulVec_mulVec] using h2
  have hG : ∀ i, Gm * T i = T (i + 1) * Gm := by
    intro i
    show Matrix.toLin' (H : Matrix (Fin n) (Fin n) K) * Matrix.toLin' (B i : Matrix (Fin n) (Fin n) K)
      = Matrix.toLin' (B (i + 1) : Matrix (Fin n) (Fin n) K) * Matrix.toLin' (H : Matrix (Fin n) (Fin n) K)
    rw [← hmat, ← hmat, ← hHB i]
    congr 2
    group
  have hdim : Module.finrank K (Fin n → K) ≤ 6 := by rw [Module.finrank_fin_fun]; exact hn
  have h2 := hb.two
  have hT01 := cycle7_eq h2 hdim T hT2 hTc Gm hGinj hG
  have : (B 0 : Matrix (Fin n) (Fin n) K) = B 1 := Matrix.toLin'.injective hT01
  exact hne (Units.ext this)

end Proj

end CFSG.GH74.Generic.BProg.B2.T4.T4ElimE8
