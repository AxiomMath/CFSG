module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSeries
public import Mathlib.RingTheory.Artinian.Instances

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V] [Finite V] [IsF2Space V]

private theorem linOf_mul_TB (f θ : MulAut V) : linOf (f * θ) = linOf f * linOf θ :=
  LinearMap.ext fun _ => rfl

private theorem linOf_pow_apply_TB (θ : MulAut V) (n : ℕ) (x : V) :
    (linOf θ ^ n) (Additive.ofMul x) = Additive.ofMul ((θ ^ n) x) := by
  induction n generalizing x with
  | zero => simp only [pow_zero, Module.End.one_apply, MulAut.one_apply]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, linOf_apply, pow_succ', MulAut.mul_apply]

private theorem polyAct_X_pow_TB (θ : MulAut V) (n : ℕ) (x : V) :
    polyAct θ (Polynomial.X ^ n) x = (θ ^ n) x := by
  unfold polyAct
  rw [map_pow, Polynomial.aeval_X]
  exact congrArg Additive.toMul (linOf_pow_apply_TB θ n x)

private theorem pow_apply_mem_TB {θ : MulAut V} {M : Subgroup V} (hθ : ∀ x ∈ M, θ x ∈ M)
    (n : ℕ) {x : V} (hx : x ∈ M) : (θ ^ n) x ∈ M := by
  induction n with
  | zero => simpa only [pow_zero, MulAut.one_apply] using hx
  | succ n ih => rw [pow_succ', MulAut.mul_apply]; exact hθ _ ih

theorem polyAct_add (θ : MulAut V) (p q : Polynomial (ZMod 2)) (x : V) :
    polyAct θ (p + q) x = polyAct θ p x * polyAct θ q x := by
  unfold polyAct
  rw [map_add, LinearMap.add_apply, toMul_add]

theorem polyAct_mul (θ : MulAut V) (p q : Polynomial (ZMod 2)) (x : V) :
    polyAct θ (p * q) x = polyAct θ p (polyAct θ q x) := by
  unfold polyAct
  rw [map_mul, Module.End.mul_apply]
  rfl

theorem polyAct_map_mul (θ : MulAut V) (p : Polynomial (ZMod 2)) (x y : V) :
    polyAct θ p (x * y) = polyAct θ p x * polyAct θ p y := by
  unfold polyAct
  rw [ofMul_mul, map_add, toMul_add]

theorem polyAct_one_apply (θ : MulAut V) (p : Polynomial (ZMod 2)) : polyAct θ p 1 = 1 := by
  unfold polyAct
  rw [ofMul_one, map_zero, toMul_zero]

@[expose] noncomputable def polyActHom (θ : MulAut V) (p : Polynomial (ZMod 2)) : V →* V where
  toFun := polyAct θ p
  map_one' := polyAct_one_apply θ p
  map_mul' := polyAct_map_mul θ p

theorem polyAct_comm {θ f : MulAut V} (hf : f * θ = θ * f) (p : Polynomial (ZMod 2)) (x : V) :
    f (polyAct θ p x) = polyAct θ p (f x) := by
  have hcomm : Commute (linOf f) (linOf θ) := by
    show linOf f * linOf θ = linOf θ * linOf f
    rw [← linOf_mul_TB, ← linOf_mul_TB, hf]
  have hc : Commute (linOf f) (Polynomial.aeval (linOf θ) p) :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute
      (Polynomial.aeval_mem_adjoin_singleton _ _) hcomm
  have h1 : linOf f (Polynomial.aeval (linOf θ) p (Additive.ofMul x)) =
      Polynomial.aeval (linOf θ) p (Additive.ofMul (f x)) := by
    have h := congrArg (fun F : Module.End (ZMod 2) (Additive V) => F (Additive.ofMul x)) hc.eq
    simp only [Module.End.mul_apply, linOf_apply] at h
    exact h
  exact congrArg Additive.toMul h1

theorem polyAct_mem {θ : MulAut V} {M : Subgroup V} (hθ : ∀ x ∈ M, θ x ∈ M)
    (p : Polynomial (ZMod 2)) {x : V} (hx : x ∈ M) : polyAct θ p x ∈ M := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [polyAct_add]
    exact M.mul_mem hp hq
  | monomial n c =>
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · have h0 : polyAct θ 0 x = 1 := by
        unfold polyAct
        rw [map_zero, LinearMap.zero_apply, toMul_zero]
      rw [Polynomial.monomial_zero_right, h0]
      exact M.one_mem
    · rw [← Polynomial.X_pow_eq_monomial, polyAct_X_pow_TB]
      exact pow_apply_mem_TB hθ n hx

private theorem exists_annihilator_gen (θ : MulAut V) (x : V) :
    ∃ g : Polynomial (ZMod 2), ∀ p : Polynomial (ZMod 2),
      Polynomial.aeval (linOf θ) p (Additive.ofMul x) = 0 ↔ g ∣ p := by
  let I : Ideal (Polynomial (ZMod 2)) :=
    { carrier := {p | Polynomial.aeval (linOf θ) p (Additive.ofMul x) = 0}
      add_mem' := by
        intro p q hp hq
        have hp' : Polynomial.aeval (linOf θ) p (Additive.ofMul x) = 0 := hp
        have hq' : Polynomial.aeval (linOf θ) q (Additive.ofMul x) = 0 := hq
        show Polynomial.aeval (linOf θ) (p + q) (Additive.ofMul x) = 0
        rw [map_add, LinearMap.add_apply, hp', hq', add_zero]
      zero_mem' := by
        show Polynomial.aeval (linOf θ) 0 (Additive.ofMul x) = 0
        rw [map_zero, LinearMap.zero_apply]
      smul_mem' := by
        intro c p hp
        have hp' : Polynomial.aeval (linOf θ) p (Additive.ofMul x) = 0 := hp
        show Polynomial.aeval (linOf θ) (c • p) (Additive.ofMul x) = 0
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, hp', map_zero] }
  obtain ⟨g, hg⟩ : ∃ g : Polynomial (ZMod 2), I = Ideal.span {g} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  refine ⟨g, fun p => ?_⟩
  have hI : Polynomial.aeval (linOf θ) p (Additive.ofMul x) = 0 ↔ p ∈ I := Iff.rfl
  rw [hI, hg, Ideal.mem_span_singleton]

theorem polyAct_semisimple {θ : MulAut V} {N : ℕ} (hN : Odd N) (hθN : θ ^ N = 1)
    (m : Polynomial (ZMod 2)) {x : V} (h : polyAct θ (m * m) x = 1) : polyAct θ m x = 1 := by
  obtain ⟨g, hg⟩ := exists_annihilator_gen θ x
  have hXN : Polynomial.aeval (linOf θ) (Polynomial.X ^ N - 1 : Polynomial (ZMod 2))
      (Additive.ofMul x) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply,
      linOf_pow_apply_TB, hθN, MulAut.one_apply, Module.End.one_apply, sub_self]
  have hN2 : (N : ZMod 2) ≠ 0 := by
    rw [ZMod.natCast_eq_one_iff_odd.mpr hN]
    exact one_ne_zero
  have hsep : (Polynomial.X ^ N - Polynomial.C (1 : ZMod 2)).Separable :=
    Polynomial.separable_X_pow_sub_C (1 : ZMod 2) hN2 one_ne_zero
  have hsq : Squarefree (Polynomial.X ^ N - 1 : Polynomial (ZMod 2)) := by
    have hs := hsep.squarefree
    rwa [Polynomial.C_1] at hs
  have hgsq : Squarefree g := Squarefree.squarefree_of_dvd ((hg _).1 hXN) hsq
  have hmm0 : Polynomial.aeval (linOf θ) (m * m) (Additive.ofMul x) = 0 := by
    have h' : Additive.toMul (Polynomial.aeval (linOf θ) (m * m) (Additive.ofMul x)) =
        Additive.toMul 0 := by
      rw [toMul_zero]
      exact h
    exact Additive.toMul.injective h'
  have hgm : g ∣ m := (Squarefree.dvd_pow_iff_dvd hgsq two_ne_zero).mp
    (by rw [sq]; exact (hg _).1 hmm0)
  have hm0 : Polynomial.aeval (linOf θ) m (Additive.ofMul x) = 0 := (hg m).2 hgm
  unfold polyAct
  rw [hm0, toMul_zero]

private theorem Y_stab_L {L D : Subgroup (MulAut V)} {U : Subgroup V}
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d) (hUL : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U) (k : ℕ) :
    ∀ g ∈ L, ∀ w ∈ U ⊓ socleSeries D k, g w ∈ U ⊓ socleSeries D k := by
  intro g hg w hw
  obtain ⟨hwU, hwS⟩ := Subgroup.mem_inf.mp hw
  have hgS := mem_stabSub_socleSeries (D := D) (g := g) (fun d hd => (hDL d hd g hg).symm) k
  exact Subgroup.mem_inf.mpr ⟨hUL g hg w hwU, (CFSG.Quasithin.mem_stabSub.1 hgS w).mpr hwS⟩

private theorem Y_stab_D {D : Subgroup (MulAut V)} {U : Subgroup V}
    (hDc : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (hUD : ∀ d ∈ D, ∀ u ∈ U, d u ∈ U) (k : ℕ) :
    ∀ d ∈ D, ∀ w ∈ U ⊓ socleSeries D k, d w ∈ U ⊓ socleSeries D k := by
  intro d hd w hw
  obtain ⟨hwU, hwS⟩ := Subgroup.mem_inf.mp hw
  have hdS := mem_stabSub_socleSeries (D := D) (g := d) (fun e he => hDc d hd e he) k
  exact Subgroup.mem_inf.mpr ⟨hUD d hd w hwU, (CFSG.Quasithin.mem_stabSub.1 hdS w).mpr hwS⟩

private theorem Y_mono {D : Subgroup (MulAut V)} (U : Subgroup V) {i j : ℕ} (h : i ≤ j) :
    U ⊓ socleSeries D i ≤ U ⊓ socleSeries D j := by
  have hmono : Monotone (socleSeries D) := monotone_nat_of_le_succ (socleSeries_le_succ D)
  intro w hw
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hw).1, hmono h (Subgroup.mem_inf.mp hw).2⟩

private theorem EE_apply_TB {c : ℕ} {Θi : Fin c → Subgroup (MulAut V)} (x : V) :
    EE Θi x = ∏ i, avgMap (Θi i) x := by
  unfold EE
  exact MonoidHom.finsetProd_apply _ _ _

private theorem avgMap_comm_of_comm {Θ' : Subgroup (MulAut V)} {θ : MulAut V}
    (hc : ∀ g ∈ Θ', θ * g = g * θ) (x : V) : avgMap Θ' (θ x) = θ (avgMap Θ' x) := by
  have := Fintype.ofFinite Θ'
  rw [avgMap_apply, avgMap_apply, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hcg := congrArg (fun φ : MulAut V => φ x) (hc _ g.2)
  simp only [MulAut.mul_apply] at hcg
  exact hcg.symm

private theorem dmul_mem_commSub_succ [IsF2Space V] {Θ D : Subgroup (MulAut V)}
    {U : Subgroup V} (hΘodd : Odd (Nat.card Θ))
    (hYΘ : ∀ k, ∀ g ∈ Θ, ∀ w ∈ U ⊓ socleSeries D k, g w ∈ U ⊓ socleSeries D k)
    (hYD : ∀ k, ∀ d ∈ D, ∀ w ∈ U ⊓ socleSeries D k, d w ∈ U ⊓ socleSeries D k)
    (hDΘ : ∀ d ∈ D, ∀ θ ∈ Θ, d * θ = θ * d) {j : ℕ} {x : V}
    (hx : x ∈ commSub (U ⊓ socleSeries D (j + 1 + 1)) Θ) {d : MulAut V} (hd : d ∈ D) :
    d x * x⁻¹ ∈ commSub (U ⊓ socleSeries D (j + 1)) Θ := by
  have hdΘ : ∀ θ ∈ Θ, d * θ * d⁻¹ ∈ Θ := fun θ hθ => by
    rw [hDΘ d hd θ hθ, mul_inv_cancel_right]
    exact hθ
  have h1 : d x ∈ commSub (U ⊓ socleSeries D (j + 1 + 1)) Θ :=
    commSub_stable hdΘ (hYD (j + 1 + 1) d hd) x hx
  have h1' : d x * x⁻¹ ∈ commSub (U ⊓ socleSeries D (j + 1 + 1)) Θ :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hx)
  have hxY : x ∈ U ⊓ socleSeries D (j + 1 + 1) := commSub_le_of_invariant (hYΘ (j + 1 + 1)) hx
  have hdxY : d x ∈ U ⊓ socleSeries D (j + 1 + 1) := hYD (j + 1 + 1) d hd x hxY
  have h2 : d x * x⁻¹ ∈ U ⊓ socleSeries D (j + 1) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp hdxY).1
        (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hxY).1)
    · exact mem_socleSeries_succ.mp (Subgroup.mem_inf.mp hxY).2 d hd
  have hle : U ⊓ socleSeries D (j + 1) ≤ U ⊓ socleSeries D (j + 1 + 1) := by
    intro w hw
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hw).1, socleSeries_le_succ D (j + 1) (Subgroup.mem_inf.mp hw).2⟩
  have h3 := commSub_inf_of_le hΘodd (hYΘ (j + 1 + 1)) (hYΘ (j + 1)) hle
  rw [← h3]
  exact Subgroup.mem_inf.mpr ⟨h1', h2⟩

theorem layerP {L D Θ Θ₁ : Subgroup (MulAut V)} {U : Subgroup V} {θ₀ : MulAut V}
    (hDcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (hD2 : ∀ d ∈ D, d * d = 1)
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d) (hΘL : Θ ≤ L) (hΘodd : Odd (Nat.card Θ))
    (hΘcomm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a) (hΘ₁ : Θ₁ ≤ Θ) (hθ₀ : θ₀ ∈ Θ)
    (hUL : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U) (hUD : ∀ d ∈ D, ∀ u ∈ U, d u ∈ U)
    (m : Polynomial (ZMod 2))
    (hss : ∀ x : V, polyAct θ₀ (m * m) x = 1 → polyAct θ₀ m x = 1)
    (hbase : ∀ x ∈ Rsub Θ Θ₁ (U ⊓ fixV D), polyAct θ₀ m x = 1) :
    ∀ x ∈ Rsub Θ Θ₁ U, polyAct θ₀ m x = 1 := by
  have hV : ∀ v : V, v ^ 2 = 1 := IsF2Space.sq_eq_one
  have hYL := Y_stab_L hDL hUL
  have hYΘ : ∀ k, ∀ g ∈ Θ, ∀ w ∈ U ⊓ socleSeries D k, g w ∈ U ⊓ socleSeries D k :=
    fun k g hg => hYL k g (hΘL hg)
  have hYD := Y_stab_D hDcomm hUD
  have hDΘ : ∀ d ∈ D, ∀ θ ∈ Θ, d * θ = θ * d := fun d hd θ hθ => hDL d hd θ (hΘL hθ)
  have hθ₀L : θ₀ ∈ L := hΘL hθ₀
  have hdθ₀ : ∀ d ∈ D, d * θ₀ = θ₀ * d := fun d hd => hDL d hd θ₀ hθ₀L
  have hgθ₀ : ∀ g ∈ Θ, g * θ₀ = θ₀ * g := fun g hg => hΘcomm g hg θ₀ hθ₀
  have hUθ₀ : ∀ w ∈ U, θ₀ w ∈ U := hUL θ₀ hθ₀L
  have hRsub : ∀ (M : Subgroup V) (y : V),
      y ∈ Rsub Θ Θ₁ M ↔ y ∈ commSub M Θ ∧ y ∈ fixV Θ₁ := fun _ _ => Iff.rfl
  have hbase' : ∀ y ∈ Rsub Θ Θ₁ (U ⊓ socleSeries D 1), polyAct θ₀ m y = 1 := by
    rw [socleSeries_one]
    exact hbase
  have hhom : ∀ a b : V, polyAct θ₀ m (a * b) = polyAct θ₀ m a * polyAct θ₀ m b :=
    polyAct_map_mul θ₀ m
  have hinv : ∀ a : V, polyAct θ₀ m a⁻¹ = (polyAct θ₀ m a)⁻¹ :=
    fun a => map_inv (polyActHom θ₀ m) a
  have hcommΘ : ∀ θ ∈ Θ, ∀ w : V, polyActHom θ₀ m (θ w) = θ (polyActHom θ₀ m w) :=
    fun θ hθ w => (polyAct_comm (hΘcomm θ hθ θ₀ hθ₀) m w).symm
  have claim : ∀ j, ∀ x ∈ Rsub Θ Θ₁ (U ⊓ socleSeries D (j + 1)), polyAct θ₀ m x = 1 := by
    intro j
    induction j with
    | zero =>
      intro x hx
      exact hbase' x hx
    | succ j ih =>
      intro x hx
      obtain ⟨hxc, hxf⟩ := (hRsub _ x).1 hx
      have hxY : x ∈ U ⊓ socleSeries D (j + 1 + 1) :=
        commSub_le_of_invariant (hYΘ (j + 1 + 1)) hxc
      have hxU : x ∈ U := (Subgroup.mem_inf.mp hxY).1
      have hda : ∀ d ∈ D, polyAct θ₀ m (d x * x⁻¹) = 1 := by
        intro d hd
        refine ih _ ((hRsub _ _).2 ⟨dmul_mem_commSub_succ hΘodd hYΘ hYD hDΘ hxc hd, ?_⟩)
        refine CFSG.Quasithin.mem_fixV.mpr fun g hg => ?_
        have hgd : g * d = d * g := (hDL d hd g (hΘL (hΘ₁ hg))).symm
        have h1 : g (d x) = d (g x) := by
          have h2 := congrArg (fun φ : MulAut V => φ x) hgd
          simpa only [MulAut.mul_apply] using h2
        rw [map_mul, map_inv, h1, CFSG.Quasithin.mem_fixV.mp hxf g hg]
      have hyD : ∀ d ∈ D, d (polyAct θ₀ m x) = polyAct θ₀ m x := by
        intro d hd
        have h1 := hda d hd
        rw [hhom, hinv, ← polyAct_comm (hdθ₀ d hd) m x] at h1
        exact mul_inv_eq_one.mp h1
      have hM : ∀ w ∈ U ⊓ socleSeries D (j + 1 + 1),
          polyActHom θ₀ m w ∈ U ⊓ socleSeries D (j + 1 + 1) :=
        fun w hw => polyAct_mem (hYΘ (j + 1 + 1) θ₀ hθ₀) m hw
      have hyc : polyAct θ₀ m x ∈ commSub (U ⊓ socleSeries D (j + 1 + 1)) Θ :=
        map_commSub_le (polyActHom θ₀ m) hcommΘ hM x hxc
      have hyf : polyAct θ₀ m x ∈ fixV Θ₁ := by
        refine CFSG.Quasithin.mem_fixV.mpr fun g hg => ?_
        rw [polyAct_comm (hgθ₀ g (hΘ₁ hg)) m x, CFSG.Quasithin.mem_fixV.mp hxf g hg]
      have hyY1 : polyAct θ₀ m x ∈ U ⊓ socleSeries D 1 := by
        refine Subgroup.mem_inf.mpr ⟨polyAct_mem hUθ₀ m hxU, ?_⟩
        rw [socleSeries_one]
        exact CFSG.Quasithin.mem_fixV.mpr fun d hd => hyD d hd
      have hY1Y2 : U ⊓ socleSeries D 1 ≤ U ⊓ socleSeries D (j + 1 + 1) := Y_mono U (by omega)
      have hyC1 : polyAct θ₀ m x ∈ commSub (U ⊓ socleSeries D 1) Θ := by
        have h3 := commSub_inf_of_le hΘodd (hYΘ (j + 1 + 1)) (hYΘ 1) hY1Y2
        rw [← h3]
        exact Subgroup.mem_inf.mpr ⟨hyc, hyY1⟩
      have hfin := hbase' (polyAct θ₀ m x) ((hRsub _ _).2 ⟨hyC1, hyf⟩)
      apply hss
      rw [polyAct_mul]
      exact hfin
  intro x hx
  obtain ⟨t, ht⟩ := exists_socleSeries_eq_top hV hD2 hDcomm
  have hT1 : socleSeries D (t + 1) = ⊤ := by
    apply top_le_iff.mp
    rw [← ht]
    exact socleSeries_le_succ D t
  have hU : U ⊓ socleSeries D (t + 1) = U := by
    rw [hT1, inf_top_eq]
  exact claim t x (by rw [hU]; exact hx)

theorem layerQ {L D Θ : Subgroup (MulAut V)} {U : Subgroup V} {c : ℕ}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi)
    (hDcomm : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d) (hD2 : ∀ d ∈ D, d * d = 1)
    (hDL : ∀ d ∈ D, ∀ l ∈ L, d * l = l * d) (hΘL : Θ ≤ L)
    (hUL : ∀ g ∈ L, ∀ u ∈ U, g u ∈ U) (hUD : ∀ d ∈ D, ∀ u ∈ U, d u ∈ U)
    (hbase : ∀ x ∈ commSub (U ⊓ fixV D) Θ, EE Θi x = x) :
    ∀ x ∈ commSub U Θ, EE Θi x = x := by
  have hV : ∀ v : V, v ^ 2 = 1 := IsF2Space.sq_eq_one
  have hΘodd : Odd (Nat.card Θ) := hT.odd
  have hYL := Y_stab_L hDL hUL
  have hYΘ : ∀ k, ∀ g ∈ Θ, ∀ w ∈ U ⊓ socleSeries D k, g w ∈ U ⊓ socleSeries D k :=
    fun k g hg => hYL k g (hΘL hg)
  have hYD := Y_stab_D hDcomm hUD
  have hDΘ : ∀ d ∈ D, ∀ θ ∈ Θ, d * θ = θ * d := fun d hd θ hθ => hDL d hd θ (hΘL hθ)
  have hEEd : ∀ d ∈ D, ∀ y : V, EE Θi (d y) = d (EE Θi y) := by
    intro d hd y
    rw [EE_apply_TB, EE_apply_TB, map_prod]
    exact Finset.prod_congr rfl fun i _ =>
      avgMap_comm_of_comm (Θ' := Θi i) (θ := d)
        (fun g hg => hDL d hd g (hΘL (hT.Θi_le i hg))) y
  have hbase1 : ∀ y ∈ commSub (U ⊓ socleSeries D 1) Θ, EE Θi y = y := by
    rw [socleSeries_one]
    exact hbase
  have claim : ∀ j, ∀ x ∈ commSub (U ⊓ socleSeries D (j + 1)) Θ, EE Θi x = x := by
    intro j
    induction j with
    | zero =>
      intro x hx
      exact hbase1 x hx
    | succ j ih =>
      intro x hx
      have hxV : x ∈ commV Θ := by
        rw [commV_eq_commSub]
        exact commSub_mono le_top (le_refl Θ) hx
      have hzC : EE Θi x * x⁻¹ ∈ commSub (U ⊓ socleSeries D (j + 1 + 1)) Θ :=
        Subgroup.mul_mem _ (EE_mem hT (hYΘ (j + 1 + 1)) hx) (Subgroup.inv_mem _ hx)
      have hzD : ∀ d ∈ D, d (EE Θi x * x⁻¹) = EE Θi x * x⁻¹ := by
        intro d hd
        have hw : d x * x⁻¹ ∈ commSub (U ⊓ socleSeries D (j + 1)) Θ :=
          dmul_mem_commSub_succ hΘodd hYΘ hYD hDΘ hx hd
        have hIH : EE Θi (d x * x⁻¹) = d x * x⁻¹ := ih _ hw
        have hid : d (EE Θi x * x⁻¹) * (EE Θi x * x⁻¹)⁻¹ =
            EE Θi (d x * x⁻¹) * (d x * x⁻¹)⁻¹ := by
          simp only [map_mul, map_inv, mul_inv, inv_inv, hEEd d hd x]
          simp only [mul_comm, mul_left_comm, mul_assoc]
        have h0 : d (EE Θi x * x⁻¹) * (EE Θi x * x⁻¹)⁻¹ = 1 := by
          rw [hid, hIH, mul_inv_cancel]
        exact mul_inv_eq_one.mp h0
      have hzY2 : EE Θi x * x⁻¹ ∈ U ⊓ socleSeries D (j + 1 + 1) :=
        commSub_le_of_invariant (hYΘ (j + 1 + 1)) hzC
      have hzY1 : EE Θi x * x⁻¹ ∈ U ⊓ socleSeries D 1 := by
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hzY2).1, ?_⟩
        rw [socleSeries_one]
        exact CFSG.Quasithin.mem_fixV.mpr hzD
      have hY1Y2 : U ⊓ socleSeries D 1 ≤ U ⊓ socleSeries D (j + 1 + 1) := Y_mono U (by omega)
      have hzC1 : EE Θi x * x⁻¹ ∈ commSub (U ⊓ socleSeries D 1) Θ := by
        have h3 := commSub_inf_of_le hΘodd (hYΘ (j + 1 + 1)) (hYΘ 1) hY1Y2
        rw [← h3]
        exact Subgroup.mem_inf.mpr ⟨hzC, hzY1⟩
      have hzfix : EE Θi (EE Θi x * x⁻¹) = EE Θi x * x⁻¹ := hbase1 _ hzC1
      have hz1 : EE Θi (EE Θi x * x⁻¹) = 1 := by
        rw [map_mul, map_inv, EE_idem hT hxV, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hzfix.symm.trans hz1)
  intro x hx
  obtain ⟨t, ht⟩ := exists_socleSeries_eq_top hV hD2 hDcomm
  have hT1 : socleSeries D (t + 1) = ⊤ := by
    apply top_le_iff.mp
    rw [← ht]
    exact socleSeries_le_succ D t
  have hU : U ⊓ socleSeries D (t + 1) = U := by
    rw [hT1, inf_top_eq]
  exact claim t x (by rw [hU]; exact hx)

end CFSG.LocalAnalysis.RankThreeUC
