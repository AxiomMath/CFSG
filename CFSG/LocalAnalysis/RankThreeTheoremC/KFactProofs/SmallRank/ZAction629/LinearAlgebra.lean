module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
theorem linAlg_two_ne {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : (2 : ZMod f) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod f) = 0 := by exact_mod_cast h
  have hd : f ∣ 2 := (CharP.cast_eq_zero_iff (ZMod f) f 2).mp h'
  exact hf2 ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_two).mp hd)

theorem linAlg_neg_one_ne {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : (-1 : ZMod f) ≠ 1 := by
  intro h
  apply linAlg_two_ne hf hf2
  linear_combination (-1 : ZMod f) * h

theorem linAlg_sq_apply {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    {x : Module.End k V} (hx : x * x = -1) (w : V) : x (x w) = -w := by
  have := LinearMap.congr_fun hx w
  simpa [Module.End.mul_apply] using this

theorem linAlg_eig {k V : Type} [Field k] [AddCommGroup V] [Module k V] {x : Module.End k V}
    {v : V} (hv : v ≠ 0) (h : ¬ LinearIndependent k ![v, x v]) :
    ∃ c : k, x v = c • v := by
  by_contra hno
  push Not at hno
  apply h
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    have h' : s • v = 0 := by simpa using hst
    exact ⟨(smul_eq_zero.mp h').resolve_right hv, rfl⟩
  · exfalso
    apply hno (-s / t)
    have h1 : t • x v = (-s) • v := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact hst
    have h2 : x v = t⁻¹ • (t • x v) := by
      rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_smul]
    congr 1
    ring

theorem linAlg_eig_sq {k V : Type} [Field k] [AddCommGroup V] [Module k V] {x : Module.End k V}
    (hx : x * x = -1) {v : V} (hv : v ≠ 0) {c : k} (hc : x v = c • v) : c * c = -1 := by
  have h2 : x (x v) = (c * c) • v := by
    rw [hc, map_smul, hc, smul_smul]
  have h3 : (c * c + 1) • v = 0 := by
    rw [add_smul, one_smul, ← h2, linAlg_sq_apply hx, neg_add_cancel]
  have h4 : c * c + 1 = 0 := (smul_eq_zero.mp h3).resolve_right hv
  linear_combination h4

theorem linAlg_li_or {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (h2 : (2 : k) ≠ 0) {x y : Module.End k V} (hx : x * x = -1) (hy : y * y = -1)
    (hyx : y * x = -(x * y)) {v : V} (hv : v ≠ 0) :
    LinearIndependent k ![v, x v] ∨ LinearIndependent k ![v, y v] := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  obtain ⟨c, hc⟩ := linAlg_eig hv hn1
  obtain ⟨d, hd⟩ := linAlg_eig hv hn2
  have hcc : c * c = -1 := linAlg_eig_sq hx hv hc
  have hdd : d * d = -1 := linAlg_eig_sq hy hv hd
  have hxy : x (y v) = (d * c) • v := by
    rw [hd, map_smul, hc, smul_smul]
  have hyx' : y (x v) = (c * d) • v := by
    rw [hc, map_smul, hd, smul_smul]
  have hanti : y (x v) = -(x (y v)) := by
    have := LinearMap.congr_fun hyx v
    simpa [Module.End.mul_apply] using this
  have hsum : (c * d + d * c) • v = 0 := by
    rw [add_smul, ← hyx', ← hxy, hanti, neg_add_cancel]
  have hsum' : c * d + d * c = 0 := (smul_eq_zero.mp hsum).resolve_right hv
  have h2cd : (2 : k) * (c * d) = 0 := by linear_combination hsum'
  rcases mul_eq_zero.mp h2cd with h | h
  · exact h2 h
  rcases mul_eq_zero.mp h with h | h
  · have h1 : (1 : k) = 0 := by linear_combination hcc - c * h
    exact one_ne_zero h1
  · have h1 : (1 : k) = 0 := by linear_combination hdd - d * h
    exact one_ne_zero h1

theorem linAlg_scalar_of_li_x {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (h2 : (2 : k) ≠ 0) (hfin : Module.finrank k V = 2)
    {x y c : Module.End k V} (hx : x * x = -1) (hy : y * y = -1) (hyx : y * x = -(x * y))
    (hcx : c * x = x * c) (hcy : c * y = y * c) {v : V}
    (hli : LinearIndependent k ![v, x v]) : ∃ μ : k, c = μ • (1 : Module.End k V) := by
  have hv : v ≠ 0 := by
    intro h0
    exact one_ne_zero (LinearIndependent.pair_iff.mp hli 1 0 (by simp [h0])).1
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by
    rw [Fintype.card_fin, hfin]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin 2) k V, ⇑B = ![v, x v] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hB0 : B 0 = v := by simp [hB]
  have hB1 : B 1 = x v := by simp [hB]
  have hc1 : c (x v) = x (c v) := by
    have := LinearMap.congr_fun hcx v
    simpa [Module.End.mul_apply] using this
  obtain ⟨a, b, hcv⟩ : ∃ a b : k, c v = a • v + b • x v := by
    refine ⟨B.repr (c v) 0, B.repr (c v) 1, ?_⟩
    have hsum := B.sum_repr (c v)
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    exact hsum.symm
  have hc_eq : c = a • (1 : Module.End k V) + b • x := by
    refine B.ext (fun i => ?_)
    fin_cases i
    · simp [hB0, hcv]
    · simp [hB1, hc1, hcv, linAlg_sq_apply hx, map_add, map_smul]
  have hyv : y v ≠ 0 := by
    intro h0
    apply hv
    have := linAlg_sq_apply hy v
    rw [h0, map_zero] at this
    exact neg_eq_zero.mp this.symm
  have hxyv : x (y v) ≠ 0 := by
    intro h0
    apply hyv
    have := linAlg_sq_apply hx (y v)
    rw [h0, map_zero] at this
    exact neg_eq_zero.mp this.symm
  have hanti : y (x v) = -(x (y v)) := by
    have := LinearMap.congr_fun hyx v
    simpa [Module.End.mul_apply] using this
  have hb : b = 0 := by
    have e1 : c (y v) = y (c v) := by
      have := LinearMap.congr_fun hcy v
      simpa [Module.End.mul_apply] using this
    have e2 : c (y v) = a • y v + b • x (y v) := by
      rw [hc_eq]
      simp [map_add, map_smul]
    have e3 : y (c v) = a • y v + b • y (x v) := by
      rw [hcv]
      simp [map_add, map_smul]
    have e4 : b • x (y v) = b • y (x v) := by
      have h5 : a • y v + b • x (y v) = a • y v + b • y (x v) := by
        rw [← e2, ← e3]
        exact e1
      exact add_left_cancel h5
    rw [hanti, smul_neg] at e4
    have e5 : (b + b) • x (y v) = 0 := by
      rw [add_smul]
      exact eq_neg_iff_add_eq_zero.mp e4
    have e6 : b + b = 0 := (smul_eq_zero.mp e5).resolve_right hxyv
    have e7 : (2 : k) * b = 0 := by linear_combination e6
    exact (mul_eq_zero.mp e7).resolve_left h2
  exact ⟨a, by rw [hc_eq, hb]; simp⟩

theorem la_even {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : LAEven f := by
  intro V _ _ _ x y hx hy hyx
  haveI : Fact f.Prime := ⟨hf⟩
  have hneg_smul : ∀ g : Module.End (ZMod f) V, (-1 : ZMod f) • g = -g :=
    fun g => neg_one_smul (ZMod f) g
  have hdet_sq : ∀ g : Module.End (ZMod f) V, g * g = -1 →
      LinearMap.det g * LinearMap.det g = (-1 : ZMod f) ^ Module.finrank (ZMod f) V := by
    intro g hg
    calc LinearMap.det g * LinearMap.det g = LinearMap.det (g * g) :=
          (map_mul LinearMap.det g g).symm
      _ = LinearMap.det ((-1 : ZMod f) • (1 : Module.End (ZMod f) V)) := by
          rw [hneg_smul, hg]
      _ = (-1 : ZMod f) ^ Module.finrank (ZMod f) V := by
          rw [LinearMap.det_smul, map_one, mul_one]
  have hdet_yx : LinearMap.det y * LinearMap.det x =
      (-1 : ZMod f) ^ Module.finrank (ZMod f) V * (LinearMap.det x * LinearMap.det y) := by
    calc LinearMap.det y * LinearMap.det x = LinearMap.det (y * x) :=
          (map_mul LinearMap.det y x).symm
      _ = LinearMap.det (-(x * y)) := by rw [hyx]
      _ = LinearMap.det ((-1 : ZMod f) • (x * y)) := by rw [hneg_smul]
      _ = (-1 : ZMod f) ^ Module.finrank (ZMod f) V * LinearMap.det (x * y) :=
          LinearMap.det_smul _ _
      _ = (-1 : ZMod f) ^ Module.finrank (ZMod f) V * (LinearMap.det x * LinearMap.det y) := by
          rw [map_mul]
  have hsx := hdet_sq x hx
  have hsy := hdet_sq y hy
  have hneg1 : (-1 : ZMod f) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : ZMod f) ≠ 0)
  have hs : (-1 : ZMod f) ^ Module.finrank (ZMod f) V ≠ 0 := pow_ne_zero _ hneg1
  have hdx : LinearMap.det x ≠ 0 := by
    intro h0
    apply hs
    rw [← hsx, h0, zero_mul]
  have hdy : LinearMap.det y ≠ 0 := by
    intro h0
    apply hs
    rw [← hsy, h0, zero_mul]
  have hs1 : (-1 : ZMod f) ^ Module.finrank (ZMod f) V = 1 := by
    have hprod : LinearMap.det x * LinearMap.det y ≠ 0 := mul_ne_zero hdx hdy
    generalize (-1 : ZMod f) ^ Module.finrank (ZMod f) V = s at hdet_yx ⊢
    apply mul_left_cancel₀ hprod
    rw [mul_one]
    calc LinearMap.det x * LinearMap.det y * s = s * (LinearMap.det x * LinearMap.det y) :=
          mul_comm _ _
      _ = LinearMap.det y * LinearMap.det x := hdet_yx.symm
      _ = LinearMap.det x * LinearMap.det y := mul_comm _ _
  exact (neg_one_pow_eq_one_iff_even (linAlg_neg_one_ne hf hf2)).mp hs1

theorem la_scalar {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) : LAScalar f := by
  intro V _ _ _ hfin x y c hx hy hyx hcx hcy
  haveI : Fact f.Prime := ⟨hf⟩
  have h2 : (2 : ZMod f) ≠ 0 := linAlg_two_ne hf hf2
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hfin]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rcases linAlg_li_or h2 hx hy hyx hv with hli | hli
  · exact linAlg_scalar_of_li_x h2 hfin hx hy hyx hcx hcy hli
  · have hyx' : x * y = -(y * x) := by rw [hyx, neg_neg]
    exact linAlg_scalar_of_li_x h2 hfin hy hx hyx' hcy hcx hli
end

section
open Subgroup

variable {K : Type} [Group K] [Finite K]
variable {f : ℕ} {F : Subgroup K}

abbrev bridge_cg [h : Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a)] : CommGroup F :=
  { (inferInstance : Group F) with
    mul_comm := fun a b => Subtype.ext (h.out (a : K) a.2 (b : K) b.2) }

attribute [local instance] bridge_cg

theorem bridge_exp (hF : FData f F) (v : Additive F) : f • v = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  exact Subtype.ext (hF.exp _ (Additive.toMul v).2)

abbrev bridge_mod [Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a)]
    [h : Fact (∀ v : Additive F, f • v = 0)] : Module (ZMod f) (Additive F) :=
  AddCommGroup.zmodModule h.out

attribute [local instance] bridge_mod

def bridge_conjM (F : Subgroup K) (g : K) (hg : g ∈ normalizer (F : Set K)) : F →* F where
  toFun a := ⟨g * (a : K) * g⁻¹, (mem_set_normalizer_iff.mp hg (a : K)).mp a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

def bridge_conjAdd (F : Subgroup K) (g : K) (hg : g ∈ normalizer (F : Set K)) :
    Additive F →+ Additive F :=
  MonoidHom.toAdditive (bridge_conjM F g hg)

theorem bridge_card [Fact f.Prime] (V : Type) [AddCommGroup V] [Module (ZMod f) V] [Finite V] :
    Nat.card V = f ^ Module.finrank (ZMod f) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod f), Nat.card_zmod]

theorem bridge_smul [NeZero f] {V : Type} [AddCommGroup V] [Module (ZMod f) V] (μ : ZMod f)
    (v : V) : μ • v = μ.val • v := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod f), ZMod.natCast_zmod_val]

theorem bridge_endo [Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a)]
    [Fact (∀ v : Additive F, f • v = 0)] (g : K) (hg : g ∈ normalizer (F : Set K)) :
    ∃ X : Module.End (ZMod f) (Additive F), ∀ v : Additive F,
      ((Additive.toMul (X v) : F) : K) = g * ((Additive.toMul v : F) : K) * g⁻¹ :=
  ⟨(bridge_conjAdd F g hg).toZModLinearMap f, fun v => rfl⟩

theorem bridge_neg [Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a)] (v : Additive F) :
    ((Additive.toMul (-v) : F) : K) = ((Additive.toMul v : F) : K)⁻¹ :=
  rfl

theorem bridge_endos [Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a)]
    [Fact (∀ v : Additive F, f • v = 0)] {x y : K}
    (hx : x ∈ normalizer (F : Set K)) (hy : y ∈ normalizer (F : Set K))
    (hx2 : ∀ a ∈ F, x * x * a * (x * x)⁻¹ = a⁻¹) (hy2 : ∀ a ∈ F, y * y * a * (y * y)⁻¹ = a⁻¹)
    (hxy : ∀ a ∈ F, y * x * y⁻¹ * a * (y * x * y⁻¹)⁻¹ = (x * a * x⁻¹)⁻¹) :
    ∃ X Y : Module.End (ZMod f) (Additive F),
      (∀ v : Additive F, ((Additive.toMul (X v) : F) : K) = x * ((Additive.toMul v : F) : K) * x⁻¹) ∧
      (∀ v : Additive F, ((Additive.toMul (Y v) : F) : K) = y * ((Additive.toMul v : F) : K) * y⁻¹) ∧
      X * X = -1 ∧ Y * Y = -1 ∧ Y * X = -(X * Y) := by
  obtain ⟨X, hX⟩ := bridge_endo (f := f) x hx
  obtain ⟨Y, hY⟩ := bridge_endo (f := f) y hy
  refine ⟨X, Y, hX, hY, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [bridge_neg, hX, hX, ← hx2 _ (Additive.toMul v).2]
    group
  · apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.one_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [bridge_neg, hY, hY, ← hy2 _ (Additive.toMul v).2]
    group
  · apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    have hmem : y * ((Additive.toMul v : F) : K) * y⁻¹ ∈ F :=
      (mem_set_normalizer_iff.mp hy _).mp (Additive.toMul v).2
    rw [bridge_neg]
    simp only [hX, hY]
    rw [← hxy _ hmem]
    group

theorem FData.even_card_exponent_aux (hF : FData f F) (hLA : LAEven f) {x y : K}
    (hx : x ∈ normalizer (F : Set K)) (hy : y ∈ normalizer (F : Set K))
    (hx2 : ∀ a ∈ F, x * x * a * (x * x)⁻¹ = a⁻¹) (hy2 : ∀ a ∈ F, y * y * a * (y * y)⁻¹ = a⁻¹)
    (hxy : ∀ a ∈ F, y * x * y⁻¹ * a * (y * x * y⁻¹)⁻¹ = (x * a * x⁻¹)⁻¹) :
    ∃ k : ℕ, Nat.card F = f ^ (2 * k) := by
  haveI : Fact f.Prime := ⟨hF.prime⟩
  haveI : NeZero f := ⟨hF.prime.ne_zero⟩
  haveI : Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) := ⟨hF.comm⟩
  haveI : Fact (∀ v : Additive F, f • v = 0) := ⟨bridge_exp hF⟩
  haveI : Finite (Additive F) := Finite.of_equiv F Additive.ofMul
  obtain ⟨X, Y, -, -, hXX, hYY, hYX⟩ := bridge_endos (f := f) hx hy hx2 hy2 hxy
  obtain ⟨k, hk⟩ := hLA (Additive F) X Y hXX hYY hYX
  refine ⟨k, ?_⟩
  rw [Nat.card_congr (Additive.ofMul : F ≃ Additive F), bridge_card (f := f), hk, two_mul]

theorem FData.scalar_of_card_sq_aux (hF : FData f F) (hLA : LAScalar f) (hcard : Nat.card F = f ^ 2)
    {x y c : K} (hx : x ∈ normalizer (F : Set K)) (hy : y ∈ normalizer (F : Set K))
    (hc : c ∈ normalizer (F : Set K))
    (hx2 : ∀ a ∈ F, x * x * a * (x * x)⁻¹ = a⁻¹) (hy2 : ∀ a ∈ F, y * y * a * (y * y)⁻¹ = a⁻¹)
    (hxy : ∀ a ∈ F, y * x * y⁻¹ * a * (y * x * y⁻¹)⁻¹ = (x * a * x⁻¹)⁻¹)
    (hcx : ∀ a ∈ F, c * (x * a * x⁻¹) * c⁻¹ = x * (c * a * c⁻¹) * x⁻¹)
    (hcy : ∀ a ∈ F, c * (y * a * y⁻¹) * c⁻¹ = y * (c * a * c⁻¹) * y⁻¹) :
    ∃ n : ℕ, ∀ a ∈ F, c * a * c⁻¹ = a ^ n := by
  haveI : Fact f.Prime := ⟨hF.prime⟩
  haveI : NeZero f := ⟨hF.prime.ne_zero⟩
  haveI : Fact (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) := ⟨hF.comm⟩
  haveI : Fact (∀ v : Additive F, f • v = 0) := ⟨bridge_exp hF⟩
  haveI : Finite (Additive F) := Finite.of_equiv F Additive.ofMul
  obtain ⟨X, Y, hX, hY, hXX, hYY, hYX⟩ := bridge_endos (f := f) hx hy hx2 hy2 hxy
  obtain ⟨C, hC⟩ := bridge_endo (f := f) c hc
  have hCX : C * X = X * C := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hX, hC]
    exact hcx _ (Additive.toMul v).2
  have hCY : C * Y = Y * C := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, Module.End.mul_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [hY, hC]
    exact hcy _ (Additive.toMul v).2
  have hcardV : Nat.card F = f ^ Module.finrank (ZMod f) (Additive F) := by
    rw [Nat.card_congr (Additive.ofMul : F ≃ Additive F), bridge_card (f := f)]
  have hrank : Module.finrank (ZMod f) (Additive F) = 2 := by
    have h : f ^ Module.finrank (ZMod f) (Additive F) = f ^ 2 := by
      rw [← hcardV, hcard]
    exact Nat.pow_right_injective hF.prime.two_le h
  obtain ⟨μ, hμ⟩ := hLA (Additive F) hrank X Y C hXX hYY hYX hCX hCY
  refine ⟨μ.val, fun a ha => ?_⟩
  have h2 : C (Additive.ofMul (⟨a, ha⟩ : F)) = μ.val • Additive.ofMul (⟨a, ha⟩ : F) := by
    rw [hμ, LinearMap.smul_apply, Module.End.one_apply]
    exact bridge_smul μ _
  have h3 : ((Additive.toMul (C (Additive.ofMul (⟨a, ha⟩ : F))) : F) : K) = c * a * c⁻¹ :=
    hC _
  calc c * a * c⁻¹ = ((Additive.toMul (C (Additive.ofMul (⟨a, ha⟩ : F))) : F) : K) := h3.symm
    _ = ((Additive.toMul (μ.val • Additive.ofMul (⟨a, ha⟩ : F)) : F) : K) := by rw [h2]
    _ = a ^ μ.val := rfl
end

section
open Subgroup

variable {K : Type} [Group K] [Finite K] {f : ℕ} {F : Subgroup K}

theorem FData.even_card_exponent (hF : FData f F) {x y : K}
    (hx : x ∈ normalizer (F : Set K)) (hy : y ∈ normalizer (F : Set K))
    (hx2 : ∀ a ∈ F, x * x * a * (x * x)⁻¹ = a⁻¹) (hy2 : ∀ a ∈ F, y * y * a * (y * y)⁻¹ = a⁻¹)
    (hxy : ∀ a ∈ F, y * x * y⁻¹ * a * (y * x * y⁻¹)⁻¹ = (x * a * x⁻¹)⁻¹) :
    ∃ k : ℕ, Nat.card F = f ^ (2 * k) :=
  hF.even_card_exponent_aux (la_even hF.prime hF.odd) hx hy hx2 hy2 hxy

theorem FData.scalar_of_card_sq (hF : FData f F) (hcard : Nat.card F = f ^ 2) {x y c : K}
    (hx : x ∈ normalizer (F : Set K)) (hy : y ∈ normalizer (F : Set K))
    (hc : c ∈ normalizer (F : Set K))
    (hx2 : ∀ a ∈ F, x * x * a * (x * x)⁻¹ = a⁻¹) (hy2 : ∀ a ∈ F, y * y * a * (y * y)⁻¹ = a⁻¹)
    (hxy : ∀ a ∈ F, y * x * y⁻¹ * a * (y * x * y⁻¹)⁻¹ = (x * a * x⁻¹)⁻¹)
    (hcx : ∀ a ∈ F, c * (x * a * x⁻¹) * c⁻¹ = x * (c * a * c⁻¹) * x⁻¹)
    (hcy : ∀ a ∈ F, c * (y * a * y⁻¹) * c⁻¹ = y * (c * a * c⁻¹) * y⁻¹) :
    ∃ n : ℕ, ∀ a ∈ F, c * a * c⁻¹ = a ^ n :=
  hF.scalar_of_card_sq_aux (la_scalar hF.prime hF.odd) hcard hx hy hc hx2 hy2 hxy hcx hcy
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
