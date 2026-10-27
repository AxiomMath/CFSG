module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.RankThree.FFModules.Offenders

import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderBasic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RepresentationTheory.Irreducible

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO

private theorem zmod2_add_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) :
    w + w = 0 := by
  rw [← two_smul (ZMod 2) w]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

private theorem zmod2_two_nsmul {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) :
    (2 : ℕ) • w = 0 := by
  rw [two_nsmul]; exact zmod2_add_self w

private theorem zmod2_two_zsmul {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) :
    (2 : ℤ) • w = 0 := by
  rw [two_zsmul]; exact zmod2_add_self w

private theorem zmod2_two_smul {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) :
    (2 : ZMod 2) • w = 0 := by
  rw [two_smul]; exact zmod2_add_self w

local macro "zmod2_norm" : tactic =>
  `(tactic| (module_nf; simp [zmod2_two_nsmul, zmod2_two_zsmul, zmod2_two_smul]))

private theorem exists_ne_zero_fixed_submodule {E M : Type*} [Group E] [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] (hE : IsPGroup 2 E) (σ : Representation (ZMod 2) E M)
    (N : Submodule (ZMod 2) M) (hN : N ≠ ⊥) (hinv : ∀ e : E, ∀ x ∈ N, σ e x ∈ N) :
    ∃ t ∈ N, t ≠ 0 ∧ ∀ e, σ e t = t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction E N :=
    { smul := fun e x => ⟨σ e x, hinv e x x.2⟩
      one_smul := fun x => Subtype.ext (by change σ 1 (x : M) = x; rw [map_one]; rfl)
      mul_smul := fun e e' x => Subtype.ext (by
        change σ (e * e') (x : M) = σ e (σ e' (x : M)); rw [map_mul]; rfl) }
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  have hdvd : 2 ∣ Nat.card N := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  have h0 : (0 : N) ∈ MulAction.fixedPoints E N := fun e => Subtype.ext (map_zero _)
  obtain ⟨b, hb, hb0⟩ := hE.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hdvd h0
  exact ⟨b, b.2, fun h => hb0 (Subtype.ext h.symm), fun e => congrArg Subtype.val (hb e)⟩

private theorem two_mul_card_le_of_card_fixed_le_two {E M : Type*} [Group E] [AddCommGroup M]
    [Module (ZMod 2) M] [Finite M] [Nontrivial M] (hcomm : ∀ x y : E, x * y = y * x)
    (hE : IsPGroup 2 E) (σ : Representation (ZMod 2) E M)
    (hfix : Nat.card {t : M // ∀ e, σ e t = t} ≤ 2) :
    2 * Nat.card E ≤ Nat.card M * Nat.card σ.ker := by
  classical
  obtain ⟨s, -, hs0, hsfix⟩ :=
    exists_ne_zero_fixed_submodule hE σ ⊤ top_ne_bot (fun e x _ => trivial)
  have hs : ∀ t : M, (∀ e, σ e t = t) → t = 0 ∨ t = s := by
    intro t ht
    by_contra hcon
    push Not at hcon
    have : Fintype {t : M // ∀ e, σ e t = t} := Fintype.ofFinite _
    have h3 : 2 < Fintype.card {t : M // ∀ e, σ e t = t} :=
      Fintype.two_lt_card_iff.2 ⟨⟨0, fun e => map_zero _⟩, ⟨s, hsfix⟩, ⟨t, ht⟩, ?_, ?_, ?_⟩
    · rw [← Nat.card_eq_fintype_card] at h3; omega
    · intro h; exact hs0 (congrArg Subtype.val h).symm
    · intro h; exact hcon.1 (congrArg Subtype.val h).symm
    · intro h; exact hcon.2 (congrArg Subtype.val h).symm
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) M, f s = 1 := by
    by_contra hcon
    push Not at hcon
    have : ∀ φ : Module.Dual (ZMod 2) M, φ s = 0 := by
      intro φ
      have := hcon φ
      revert this; generalize φ s = c; revert c; decide
    exact hs0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) s).1 this)
  have hL : ∀ k : E, f ∘ₗ σ k = f → σ k = 1 := by
    intro k hk
    by_contra hk1
    set N : Submodule (ZMod 2) M := LinearMap.range (σ k - 1) with hNdef
    have hNne : N ≠ ⊥ := by
      intro h
      rw [hNdef, LinearMap.range_eq_bot, sub_eq_zero] at h
      exact hk1 h
    have hinv : ∀ e : E, ∀ x ∈ N, σ e x ∈ N := by
      rintro e x ⟨y, rfl⟩
      refine ⟨σ e y, ?_⟩
      have hc : σ e * σ k = σ k * σ e := by rw [← map_mul, ← map_mul, hcomm]
      have := congrArg (fun T : Module.End (ZMod 2) M => T y) hc
      simp only [Module.End.mul_apply] at this
      simp [this]
    obtain ⟨t, htN, ht0, htfix⟩ := exists_ne_zero_fixed_submodule hE σ N hNne hinv
    have hts : t = s := (hs t htfix).resolve_left ht0
    rw [hts] at htN
    obtain ⟨y, hy⟩ := htN
    have hfs : f s = 0 := by
      rw [← hy]
      have := congrArg (fun φ : Module.Dual (ZMod 2) M => φ y) hk
      simp only [LinearMap.comp_apply] at this
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      have h2 : f ((σ k) y - y) = f ((σ k) y) - f y := map_sub f _ _
      rw [h2, this, sub_self]
    rw [hf] at hfs
    exact one_ne_zero hfs
  have : Finite (Module.Dual (ZMod 2) M) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod 2) M => (φ : M → ZMod 2)) DFunLike.coe_injective
  let : MulAction E (Module.Dual (ZMod 2) M) :=
    { smul := fun e φ => φ ∘ₗ σ e⁻¹
      one_smul := fun φ => by
        change φ ∘ₗ σ (1 : E)⁻¹ = φ
        rw [inv_one, map_one]; rfl
      mul_smul := fun e e' φ => by
        change φ ∘ₗ σ (e * e')⁻¹ = (φ ∘ₗ σ e'⁻¹) ∘ₗ σ e⁻¹
        rw [mul_inv_rev, map_mul]; rfl }
  have hstab : MulAction.stabilizer E f = σ.ker := by
    ext e
    rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : f ∘ₗ σ e⁻¹ = f := h
      have h2 := hL e⁻¹ h'
      have h1 : σ e * σ e⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [h2, mul_one] at h1
      exact h1
    · intro h
      change f ∘ₗ σ e⁻¹ = f
      have h2 : σ e⁻¹ = 1 := by
        have h1 : σ e⁻¹ * σ e = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        rwa [h, mul_one] at h1
      rw [h2]; rfl
  have hsub : MulAction.orbit E f ⊆ {φ : Module.Dual (ZMod 2) M | φ s = 1} := by
    rintro _ ⟨e, rfl⟩
    show (f ∘ₗ σ e⁻¹) s = 1
    simp [hsfix e⁻¹, hf]
  have h1 : Nat.card (MulAction.orbit E f) ≤ Nat.card {φ : Module.Dual (ZMod 2) M | φ s = 1} :=
    Nat.card_mono (Set.toFinite _) hsub
  have horb : Nat.card E = Nat.card (MulAction.orbit E f) * Nat.card σ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer E f),
      Nat.card_congr (MulAction.orbitEquivQuotientStabilizer E f), hstab]
  have h2 : 2 * Nat.card {φ : Module.Dual (ZMod 2) M | φ s = 1} ≤ Nat.card M := by
    have hDual : Nat.card (Module.Dual (ZMod 2) M) = Nat.card M := by
      have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) M),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M), Subspace.dual_finrank_eq]
    have hinj : Function.Injective
        (fun p : ZMod 2 × {φ : Module.Dual (ZMod 2) M | φ s = 1} => p.2.1 + p.1 • f) := by
      rintro ⟨c, φ, hφ⟩ ⟨c', φ', hφ'⟩ h
      simp only at h
      have hs := congrArg (fun ψ : Module.Dual (ZMod 2) M => ψ s) h
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hf, mul_one] at hs
      have hφ1 : φ s = 1 := hφ
      have hφ1' : φ' s = 1 := hφ'
      rw [hφ1, hφ1'] at hs
      have hc : c = c' := add_left_cancel hs
      subst hc
      have : φ = φ' := add_right_cancel h
      subst this
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, Nat.card_zmod, hDual] at this
    exact this
  calc 2 * Nat.card E = 2 * (Nat.card (MulAction.orbit E f) * Nat.card σ.ker) := by rw [horb]
    _ ≤ 2 * (Nat.card {φ : Module.Dual (ZMod 2) M | φ s = 1} * Nat.card σ.ker) := by gcongr
    _ = (2 * Nat.card {φ : Module.Dual (ZMod 2) M | φ s = 1}) * Nat.card σ.ker := by ring
    _ ≤ Nat.card M * Nat.card σ.ker := by gcongr

section Swap

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {τ : W →ₗ[ZMod 2] W}
  {I : Submodule (ZMod 2) W}

private theorem eq_of_add_eq_zero_zmod2 {x y : W} (h : x + y = 0) : x = y := by
  linear_combination (norm := zmod2_norm) h

private theorem mem_map_swap (hτ : ∀ w, τ (τ w) = w) {w : W} : w ∈ I.map τ ↔ τ w ∈ I := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [hτ]
  · intro h
    exact ⟨τ w, h, hτ w⟩

private theorem eq_zero_of_swap_fixed (hτ : ∀ w, τ (τ w) = w) (hdisj : Disjoint I (I.map τ))
    {d : W} (hd : d ∈ I) (hτd : τ d = d) : d = 0 :=
  Submodule.disjoint_def.1 hdisj d hd ((mem_map_swap hτ).2 (by rw [hτd]; exact hd))

private theorem exists_eq_add_swap (hτ : ∀ w, τ (τ w) = w) (hdisj : Disjoint I (I.map τ))
    {v : W} (hv : v ∈ I ⊔ I.map τ) (hτv : τ v = v) : ∃ x ∈ I, v = x + τ x := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨z, hz, rfl⟩ := hy
  have h1 : τ x + z = x + τ z := by rwa [map_add, hτ] at hτv
  have h2 : τ (x + z) = x + z := by
    rw [map_add]
    linear_combination (norm := zmod2_norm) h1
  have h3 : x + z = 0 := eq_zero_of_swap_fixed hτ hdisj (I.add_mem hx hz) h2
  have h4 : z = x := (eq_of_add_eq_zero_zmod2 h3).symm
  exact ⟨x, hx, by rw [h4]⟩

end Swap

private theorem eq_of_swap_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {τ : W →ₗ[ZMod 2] W} {I : Submodule (ZMod 2) W} (hτ : ∀ w, τ (τ w) = w)
    (hdisj : Disjoint I (I.map τ)) {β : W →ₗ[ZMod 2] W} (hβτ : ∀ w, β (τ w) = τ (β w))
    (hβI : ∀ w ∈ I, β w ∈ I) {x : W} (hx : x ∈ I) (hβ : β (x + τ x) = x + τ x) : β x = x := by
  have he : β x + x ∈ I := I.add_mem (hβI x hx) hx
  rw [map_add, hβτ] at hβ
  have h1 : τ (β x + x) = β x + x := by
    rw [map_add]
    linear_combination (norm := zmod2_norm) hβ
  exact eq_of_add_eq_zero_zmod2 (eq_zero_of_swap_fixed hτ hdisj he h1)

set_option linter.unusedVariables false in
open CFSG.RankThree.FFModules in
theorem card_le_two_of_swap {G : Type} [Group G] [Finite G] {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {ρ : Representation (ZMod 2) G W} {A A₀ : Subgroup G}
    (hAel : CFSG.IsElementaryAbelian 2 ↥A) (hA : IsBestOffender ρ A) (hA₀ : A₀ ≤ A) {a : G}
    (ha : a ∈ A) (haA₀ : a ∉ A₀) (hgen : A ≤ A₀ ⊔ Subgroup.zpowers a) (I : Submodule (ZMod 2) W)
    (hI : ∀ b ∈ A₀, ∀ w ∈ I, ρ b w ∈ I) (hdisj : Disjoint I (I.map (ρ a))) :
    Nat.card I ≤ 2 := by
  open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF in
  classical
  clear haA₀
  have := hAel
  have hsq : ∀ g ∈ A, g * g = 1 := fun g hg => by
    simpa [pow_two] using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) g hg
  have hcomm : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g := fun g hg h hh =>
    congrArg Subtype.val (hAel.toIsMulCommutative.is_comm.comm (⟨g, hg⟩ : A) ⟨h, hh⟩)
  have hτ : ∀ w, ρ a (ρ a w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, hsq a ha, map_one, Module.End.one_apply]
  have hρc : ∀ b ∈ A₀, ∀ w, ρ b (ρ a w) = ρ a (ρ b w) := fun b hb w => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      hcomm b (hA₀ hb) a ha]
  set V : Submodule (ZMod 2) W := I ⊔ I.map (ρ a)
  have hA2 : Nat.card A ≤ 2 * Nat.card A₀ := by
    have hc : ∀ x ∈ A₀, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := by
      intro x hx y hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_right (hcomm x (hA₀ hx) a ha) n)
    obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₀ (Subgroup.zpowers a) hc
    have h2 : Nat.card (Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq a ha))
    have h3 : 0 < Nat.card ↥(A₀ ⊓ Subgroup.zpowers a) := Nat.card_pos
    calc Nat.card A ≤ Nat.card ↥(A₀ ⊔ Subgroup.zpowers a) := Subgroup.card_le_of_le hgen
      _ ≤ Nat.card ↥(A₀ ⊔ Subgroup.zpowers a) * Nat.card ↥(A₀ ⊓ Subgroup.zpowers a) :=
          Nat.le_mul_of_pos_right _ h3
      _ = Nat.card A₀ * Nat.card (Subgroup.zpowers a) := h1
      _ ≤ Nat.card A₀ * 2 := Nat.mul_le_mul_left _ h2
      _ = 2 * Nat.card A₀ := mul_comm _ _
  have hVcard : Nat.card V = Nat.card I ^ 2 := by
    have hinj : Function.Injective (ρ a) := fun x y h => by
      have := congrArg (ρ a) h
      rwa [hτ, hτ] at this
    have hJ : Nat.card (I.map (ρ a)) = Nat.card I :=
      (Nat.card_congr (Submodule.equivMapOfInjective (ρ a) hinj I).toEquiv).symm
    have h1 := card_inf_mul_card_sup I (I.map (ρ a))
    rw [disjoint_iff.mp hdisj, hJ] at h1
    simpa [pow_two] using h1
  have hVinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ A V := by
    have hb : ∀ b ∈ A₀, ∀ v ∈ V, ρ b v ∈ V := by
      intro b hb v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨z, hz, rfl⟩ := hy
      rw [map_add, hρc b hb z]
      exact V.add_mem (Submodule.mem_sup_left (hI b hb x hx))
        (Submodule.mem_sup_right ⟨ρ b z, hI b hb z hz, rfl⟩)
    have ha' : ∀ v ∈ V, ρ a v ∈ V := by
      intro v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      obtain ⟨z, hz, rfl⟩ := hy
      rw [map_add, hτ]
      exact V.add_mem (Submodule.mem_sup_right ⟨x, hx, rfl⟩) (Submodule.mem_sup_left hz)
    let Stab : Subgroup G :=
      { carrier := {g | (∀ v ∈ V, ρ g v ∈ V) ∧ ∀ v ∈ V, ρ g⁻¹ v ∈ V}
        mul_mem' := fun {g h} hg hh =>
          ⟨fun v hv => by rw [map_mul, Module.End.mul_apply]; exact hg.1 _ (hh.1 v hv),
            fun v hv => by rw [mul_inv_rev, map_mul, Module.End.mul_apply]; exact hh.2 _ (hg.2 v hv)⟩
        one_mem' := ⟨fun v hv => by rwa [map_one, Module.End.one_apply],
          fun v hv => by rwa [inv_one, map_one, Module.End.one_apply]⟩
        inv_mem' := fun {g} hg => ⟨hg.2, by simpa using hg.1⟩ }
    have hA₀S : A₀ ≤ Stab := fun b hb' => ⟨hb b hb', hb b⁻¹ (A₀.inv_mem hb')⟩
    have haS : a ∈ Stab := ⟨ha', by
      rw [inv_eq_of_mul_eq_one_right (hsq a ha)]; exact ha'⟩
    exact fun g hg v hv => (hgen.trans (sup_le hA₀S (Subgroup.zpowers_le.2 haS)) hg).1 v hv
  have hbo : IsBestOffenderOn ρ A ⊤ := by
    refine ⟨fun g hg h hh => ⟨fun u _ => ?_, fun u _ => ?_⟩, fun B hB => ?_⟩
    · have : g * h * g⁻¹ * h⁻¹ = 1 := by rw [hcomm g hg h hh]; group
      rw [this, map_one, Module.End.one_apply]
    · rw [hsq g hg, map_one, Module.End.one_apply]
    · simpa only [fixOn_top] using hA B hB
  have hoff := (hbo.forall_isInvariant_isOffenderOn V hVinv).2
  have hcen : cenOn ρ A₀ I ≤ cenOn ρ A V := by
    intro g hg
    refine ⟨hA₀ hg.1, fun v hv => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨z, hz, rfl⟩ := hy
    rw [map_add, hρc g hg.1 z, hg.2 x hx, hg.2 z hz]
  have hFS : fixSub ρ A ≤ fixSub ρ A₀ := fixSub_antitone hA₀
  have hSF : Nat.card (fixSub ρ A₀) ≤ 2 * Nat.card (fixSub ρ A) := by
    have h1 := hA A₀ hA₀
    have h2 : Nat.card A₀ * Nat.card (fixSub ρ A₀) ≤
        Nat.card A₀ * (2 * Nat.card (fixSub ρ A)) :=
      h1.trans (by
        calc Nat.card A * Nat.card (fixSub ρ A)
            ≤ (2 * Nat.card A₀) * Nat.card (fixSub ρ A) := Nat.mul_le_mul_right _ hA2
          _ = Nat.card A₀ * (2 * Nat.card (fixSub ρ A)) := by ring)
    exact Nat.le_of_mul_le_mul_left h2 Nat.card_pos
  have hCF : fixOn ρ A₀ I ⊓ fixSub ρ A = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨⟨huI, -⟩, huF⟩
    exact eq_zero_of_swap_fixed hτ hdisj huI (huF a ha)
  have hfixI : Nat.card (fixOn ρ A₀ I) ≤ 2 := by
    have h1 := card_inf_mul_card_sup (fixOn ρ A₀ I) (fixSub ρ A)
    rw [hCF] at h1
    have h2 : Nat.card ↥(fixOn ρ A₀ I ⊔ fixSub ρ A) ≤ Nat.card (fixSub ρ A₀) :=
      card_le_of_le_submodule (sup_le inf_le_right hFS)
    have h3 : Nat.card ↥(fixOn ρ A₀ I) * Nat.card (fixSub ρ A) ≤
        2 * Nat.card (fixSub ρ A) := by
      rw [← h1]
      simp only [Nat.card_unique, one_mul]
      exact h2.trans hSF
    exact Nat.le_of_mul_le_mul_right h3 Nat.card_pos
  have hfixV : Nat.card (fixOn ρ A V) ≤ 2 := by
    have hVF : fixOn ρ A V ≤ (fixOn ρ A₀ I).map (ρ a + LinearMap.id) := by
      rintro v ⟨hvV, hvF⟩
      obtain ⟨x, hx, rfl⟩ := exists_eq_add_swap hτ hdisj hvV (hvF a ha)
      refine ⟨x, ⟨hx, fun b hb => ?_⟩, ?_⟩
      · exact eq_of_swap_fixed hτ hdisj (hρc b hb) (hI b hb) hx (hvF b (hA₀ hb))
      · simp [add_comm]
    have h1 : Nat.card ↥((fixOn ρ A₀ I).map (ρ a + LinearMap.id)) ≤ Nat.card (fixOn ρ A₀ I) :=
      Nat.card_le_card_of_surjective _ (LinearMap.submoduleMap_surjective _ _)
    exact (card_le_of_le_submodule hVF).trans (h1.trans hfixI)
  by_cases hI0 : I = ⊥
  · simp [hI0]
  have hkey : 2 * Nat.card A₀ ≤ Nat.card I * Nat.card (cenOn ρ A₀ I) := by
    let σ : Representation (ZMod 2) A₀ I :=
      { toFun := fun b => (ρ b).restrict (fun w hw => hI b b.2 w hw)
        map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
        map_mul' := fun b b' => LinearMap.ext fun x => Subtype.ext (by simp) }
    have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.2 hI0
    have hE : IsPGroup 2 A₀ := fun g => ⟨1, Subtype.ext (by
      simpa [pow_two] using (hsq g (hA₀ g.2)))⟩
    have hc₀ : ∀ x y : A₀, x * y = y * x := fun x y =>
      Subtype.ext (hcomm x (hA₀ x.2) y (hA₀ y.2))
    have hfix : Nat.card {t : I // ∀ e, σ e t = t} ≤ 2 := by
      refine le_trans (le_of_eq (Nat.card_congr
        { toFun := fun t => ⟨(t.1 : W), t.1.2, fun g hg => congrArg Subtype.val (t.2 ⟨g, hg⟩)⟩
          invFun := fun w => ⟨⟨w.1, w.2.1⟩, fun e => Subtype.ext (w.2.2 e e.2)⟩
          left_inv := fun t => rfl
          right_inv := fun w => rfl })) hfixI
    have h := two_mul_card_le_of_card_fixed_le_two hc₀ hE σ hfix
    have hker : Nat.card σ.ker = Nat.card (cenOn ρ A₀ I) :=
      Nat.card_congr
        { toFun := fun e => ⟨(e.1 : G), e.1.2, fun u hu =>
            congrArg Subtype.val (LinearMap.congr_fun e.2 ⟨u, hu⟩)⟩
          invFun := fun g => ⟨⟨g.1, g.2.1⟩, LinearMap.ext fun x => Subtype.ext (g.2.2 x x.2)⟩
          left_inv := fun e => rfl
          right_inv := fun g => rfl }
    rwa [hker] at h
  have hcle : Nat.card (cenOn ρ A₀ I) ≤ Nat.card (cenOn ρ A V) := Subgroup.card_le_of_le hcen
  have h1 : Nat.card I ^ 2 * Nat.card (cenOn ρ A₀ I) ≤
      2 * (Nat.card I * Nat.card (cenOn ρ A₀ I)) :=
    calc Nat.card I ^ 2 * Nat.card (cenOn ρ A₀ I)
        = Nat.card V * Nat.card (cenOn ρ A₀ I) := by rw [hVcard]
      _ ≤ Nat.card V * Nat.card (cenOn ρ A V) := Nat.mul_le_mul_left _ hcle
      _ ≤ Nat.card A * Nat.card (fixOn ρ A V) := hoff
      _ ≤ (2 * Nat.card A₀) * 2 := Nat.mul_le_mul hA2 hfixV
      _ = 2 * (2 * Nat.card A₀) := by ring
      _ ≤ 2 * (Nat.card I * Nat.card (cenOn ρ A₀ I)) := Nat.mul_le_mul_left _ hkey
  have h2 : Nat.card I * (Nat.card I * Nat.card (cenOn ρ A₀ I)) ≤
      2 * (Nat.card I * Nat.card (cenOn ρ A₀ I)) := by
    calc Nat.card I * (Nat.card I * Nat.card (cenOn ρ A₀ I))
        = Nat.card I ^ 2 * Nat.card (cenOn ρ A₀ I) := by ring
      _ ≤ _ := h1
  exact Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos Nat.card_pos Nat.card_pos)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO
