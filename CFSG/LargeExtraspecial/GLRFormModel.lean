module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure IsGoodForm (β : LinearMap.BilinForm (ZMod 2) V) : Prop where
  symm : ∀ a b, β a b = β b a
  nondeg : ∀ a, (∀ b, β a b = 0) → a = 0
  eq_id : ∀ g : V →ₗ[ZMod 2] V, Function.Injective g → (∀ w, β w w = 0 → g w = w) →
    (∀ a w, β w w = 0 → β (g a) w = β a w) → g = LinearMap.id
  card_le : Nat.card {a : V // β a a = 0} ≤ 2 ^ (2 * (finrank (ZMod 2) V / 2))
  exists_vectors : ∃ e e' v₁ v₂ v₃ : V, β e e = 0 ∧ β e' e' = 0 ∧ β v₁ v₁ = 0 ∧ β v₂ v₂ = 0 ∧
    β v₃ v₃ = 0 ∧ β e e' = 0 ∧ β v₁ e = 1 ∧ β v₂ e' = 1 ∧ β v₃ (e + e') = 1

namespace IsGoodForm

variable {β : LinearMap.BilinForm (ZMod 2) V}

theorem isSymm (h : IsGoodForm β) : β.IsSymm := ⟨h.symm⟩

theorem nondegenerate (h : IsGoodForm β) : β.Nondegenerate :=
  ⟨h.nondeg, fun y hy => h.nondeg y fun x => (h.symm y x).trans (hy x)⟩

theorem comap {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {β : LinearMap.BilinForm (ZMod 2) W}
    (h : IsGoodForm β) (e : V ≃ₗ[ZMod 2] W) :
    IsGoodForm (β.compl₁₂ (e : V →ₗ[ZMod 2] W) (e : V →ₗ[ZMod 2] W)) where
  symm a b := h.symm (e a) (e b)
  nondeg a ha := by
    have : e a = 0 := h.nondeg (e a) fun w => by
      have := ha (e.symm w)
      simpa using this
    exact (map_eq_zero_iff e e.injective).mp this
  eq_id g hg h1 h2 := by
    let g' : W →ₗ[ZMod 2] W := (e : V →ₗ[ZMod 2] W) ∘ₗ g ∘ₗ (e.symm : W →ₗ[ZMod 2] V)
    have hg' : g' = LinearMap.id := h.eq_id g'
      (e.injective.comp (hg.comp e.symm.injective))
      (fun w hw => by
        have := h1 (e.symm w) (by simpa using hw)
        simp [g', this])
      (fun a w hw => by
        have := h2 (e.symm a) (e.symm w) (by simpa using hw)
        simpa [g'] using this)
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hg' (e v)
    simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.id_apply] at this
    exact e.injective this
  card_le := by
    have hrank := e.finrank_eq
    rw [hrank]
    calc Nat.card {a : V // (β.compl₁₂ (e : V →ₗ[ZMod 2] W) (e : V →ₗ[ZMod 2] W)) a a = 0}
        = Nat.card {b : W // β b b = 0} :=
          Nat.card_congr (e.toEquiv.subtypeEquiv fun a => Iff.rfl)
      _ ≤ _ := h.card_le
  exists_vectors := by
    obtain ⟨a, b, c, d, f, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.exists_vectors
    refine ⟨e.symm a, e.symm b, e.symm c, e.symm d, e.symm f, ?_⟩
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      ← map_add]
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end IsGoodForm

abbrev Model (m r : ℕ) : Type := (Fin m → ZMod 2) × (Fin m → ZMod 2) × (Fin r → ZMod 2)

@[expose] noncomputable def modelForm (m r : ℕ) : LinearMap.BilinForm (ZMod 2) (Model m r) :=
  LinearMap.mk₂ (ZMod 2) (fun v w => v.1 ⬝ᵥ w.2.1 + v.2.1 ⬝ᵥ w.1 + v.2.2 ⬝ᵥ w.2.2)
    (fun v v' w => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct]; abel)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul]; ring)
    (fun v w w' => by simp only [Prod.fst_add, Prod.snd_add, dotProduct_add]; abel)
    (fun c v w => by
      simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul]; ring)

variable {m r : ℕ}

theorem modelForm_apply (v w : Model m r) :
    modelForm m r v w = v.1 ⬝ᵥ w.2.1 + v.2.1 ⬝ᵥ w.1 + v.2.2 ⬝ᵥ w.2.2 := rfl

theorem modelForm_self (v : Model m r) : modelForm m r v v = v.2.2 ⬝ᵥ v.2.2 := by
  rw [modelForm_apply, dotProduct_comm v.2.1 v.1, ZModModule.add_self, zero_add]

theorem modelForm_symm (v w : Model m r) : modelForm m r v w = modelForm m r w v := by
  rw [modelForm_apply, modelForm_apply, dotProduct_comm w.1, dotProduct_comm w.2.1,
    dotProduct_comm w.2.2]
  abel

theorem modelForm_nondeg (v : Model m r) (h : ∀ w, modelForm m r v w = 0) : v = 0 := by
  obtain ⟨x, y, s⟩ := v
  have hx : x = 0 := funext fun i => by simpa [modelForm_apply] using h (0, Pi.single i 1, 0)
  have hy : y = 0 := funext fun i => by simpa [modelForm_apply] using h (Pi.single i 1, 0, 0)
  have hs : s = 0 := funext fun i => by simpa [modelForm_apply] using h (0, 0, Pi.single i 1)
  rw [hx, hy, hs]
  rfl

theorem snd_snd_eq_zero (hr : r ≤ 1) {v : Model m r} (hv : modelForm m r v v = 0) :
    v.2.2 = 0 := by
  rw [modelForm_self] at hv
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · exact funext fun i => i.elim0
  · have h0 : v.2.2 0 * v.2.2 0 = 0 := by simpa [dotProduct] using hv
    funext i
    rw [Fin.fin_one_eq_zero i]
    exact mul_self_eq_zero.mp h0

theorem modelForm_eq_id (hr : r ≤ 1) (g : Model m r →ₗ[ZMod 2] Model m r)
    (hg : Function.Injective g) (h1 : ∀ w, modelForm m r w w = 0 → g w = w)
    (h2 : ∀ a w, modelForm m r w w = 0 → modelForm m r (g a) w = modelForm m r a w) :
    g = LinearMap.id := by
  obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
  · exact LinearMap.ext fun w => h1 w (by
      rw [modelForm_self]
      simp [dotProduct])
  · let u : Model m 1 := (0, 0, fun _ => 1)
    have hgu1 : (g u).1 = 0 := funext fun i => by
      have := h2 u (0, Pi.single i 1, 0) (by rw [modelForm_self]; simp [dotProduct])
      simpa [modelForm_apply, u] using this
    have hgu2 : (g u).2.1 = 0 := funext fun i => by
      have := h2 u (Pi.single i 1, 0, 0) (by rw [modelForm_self]; simp [dotProduct])
      simpa [modelForm_apply, u] using this
    have hgu3 : (g u).2.2 = fun _ => 1 := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) ((g u).2.2 0) with hc | hc
      · exfalso
        have hgu0 : g u = 0 := by
          refine Prod.ext hgu1 (Prod.ext hgu2 (funext fun i => ?_))
          rw [Fin.fin_one_eq_zero i]
          exact hc
        have : u = 0 := hg (hgu0.trans (map_zero g).symm)
        have := congrArg (fun v : Model m 1 => v.2.2 0) this
        simp [u] at this
      · exact hc
    have hgu : g u = u := Prod.ext hgu1 (Prod.ext hgu2 hgu3)
    refine LinearMap.ext fun v => ?_
    have hv : v = (v.1, v.2.1, 0) + (v.2.2 0) • u := by
      refine Prod.ext (by simp [u]) (Prod.ext (by simp [u]) (funext fun i => ?_))
      rw [Fin.fin_one_eq_zero i]
      simp [u]
    rw [hv, map_add, map_smul, hgu, h1 _ (by rw [modelForm_self]; simp [dotProduct])]
    rfl

theorem finrank_model (m r : ℕ) : finrank (ZMod 2) (Model m r) = m + (m + r) := by
  simp [Module.finrank_prod]

theorem modelForm_card_le (hr : r ≤ 1) :
    Nat.card {a : Model m r // modelForm m r a a = 0} ≤
      2 ^ (2 * (finrank (ZMod 2) (Model m r) / 2)) := by
  have hrank : 2 * (finrank (ZMod 2) (Model m r) / 2) = m + m := by
    rw [finrank_model]
    omega
  rw [hrank]
  let f : {a : Model m r // modelForm m r a a = 0} → (Fin m → ZMod 2) × (Fin m → ZMod 2) :=
    fun a => (a.1.1, a.1.2.1)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : a.1.2.2 = b.1.2.2 := by
      rw [snd_snd_eq_zero hr a.2, snd_snd_eq_zero hr b.2]
    have h0 : a.1.1 = b.1.1 := congrArg (fun p : (Fin m → ZMod 2) × (Fin m → ZMod 2) => p.1) hab
    have h2 : a.1.2.1 = b.1.2.1 :=
      congrArg (fun p : (Fin m → ZMod 2) × (Fin m → ZMod 2) => p.2) hab
    exact Subtype.ext (Prod.ext h0 (Prod.ext h2 h1))
  calc Nat.card {a : Model m r // modelForm m r a a = 0}
      ≤ Nat.card ((Fin m → ZMod 2) × (Fin m → ZMod 2)) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ (m + m) := by simp [pow_add]

theorem modelForm_exists_vectors (hm : 2 ≤ m) :
    ∃ e e' v₁ v₂ v₃ : Model m r, modelForm m r e e = 0 ∧ modelForm m r e' e' = 0 ∧
      modelForm m r v₁ v₁ = 0 ∧ modelForm m r v₂ v₂ = 0 ∧ modelForm m r v₃ v₃ = 0 ∧
      modelForm m r e e' = 0 ∧ modelForm m r v₁ e = 1 ∧ modelForm m r v₂ e' = 1 ∧
      modelForm m r v₃ (e + e') = 1 := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hne : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  refine ⟨(Pi.single i₀ 1, 0, 0), (Pi.single i₁ 1, 0, 0), (0, Pi.single i₀ 1, 0),
    (0, Pi.single i₁ 1, 0), (0, Pi.single i₀ 1, 0), ?_⟩
  simp [modelForm_apply, hne]

theorem isGoodForm_modelForm (hr : r ≤ 1) (hm : 2 ≤ m) : IsGoodForm (modelForm m r) where
  symm := modelForm_symm
  nondeg := modelForm_nondeg
  eq_id g hg h1 h2 := modelForm_eq_id hr g hg h1 h2
  card_le := modelForm_card_le hr
  exists_vectors := modelForm_exists_vectors hm

theorem exists_isGoodForm [FiniteDimensional (ZMod 2) V] (hn : 4 ≤ finrank (ZMod 2) V) :
    ∃ β : LinearMap.BilinForm (ZMod 2) V, IsGoodForm β := by
  have hdim : finrank (ZMod 2) V =
      finrank (ZMod 2) (Model (finrank (ZMod 2) V / 2) (finrank (ZMod 2) V % 2)) := by
    rw [finrank_model]
    omega
  let e := LinearEquiv.ofFinrankEq V (Model (finrank (ZMod 2) V / 2) (finrank (ZMod 2) V % 2))
    hdim
  exact ⟨_, (isGoodForm_modelForm (by omega) (by omega)).comap e⟩

section Transvection

variable {β : LinearMap.BilinForm (ZMod 2) V} (hβ : ∀ a b, β a b = β b a)

@[expose] noncomputable def transvMap (β : LinearMap.BilinForm (ZMod 2) V) (x : V) :
    V →ₗ[ZMod 2] V :=
  LinearMap.id + (β.flip x).smulRight x

theorem transvMap_apply (x a : V) : transvMap β x a = a + β a x • x := rfl

include hβ in
theorem transvMap_isometry {x : V} (hx : β x x = 0) (a b : V) :
    β (transvMap β x a) (transvMap β x b) = β a b := by
  simp only [transvMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hx, mul_zero, add_zero]
  rw [hβ x b]
  have : β a x * β b x + β a x * β b x = 0 := ZModModule.add_self _
  linear_combination this

theorem transvMap_transvMap {x : V} (hx : β x x = 0) (a : V) :
    transvMap β x (transvMap β x a) = a := by
  rw [transvMap_apply, transvMap_apply, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, hx, smul_zero, add_zero, add_assoc, ZModModule.add_self, add_zero]

include hβ in
theorem transvMap_comm {x y : V} (hxy : β x y = 0) (a : V) :
    transvMap β x (transvMap β y a) = transvMap β y (transvMap β x a) := by
  have hyx : β y x = 0 := by rw [hβ y x, hxy]
  rw [transvMap_apply, transvMap_apply, transvMap_apply, transvMap_apply, map_add, map_add,
    LinearMap.add_apply, LinearMap.add_apply, map_smul, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, hxy, hyx, smul_zero, smul_zero, add_zero, add_zero]
  abel

@[expose] noncomputable def transv {x : V} (hx : β x x = 0) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive (transvMap β x) (transvMap_transvMap hx)

theorem transv_apply {x : V} (hx : β x x = 0) (a : V) : transv hx a = a + β a x • x := rfl

end Transvection

end CFSG.LargeExtraspecial.GLR
