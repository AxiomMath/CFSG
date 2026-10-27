module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnOrbit

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

section Duality

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
  {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] [Module (ZMod p) V] [IsScalarTower (ZMod p) K V]

@[expose] noncomputable def bilinDual (τ : K →ₗ[ZMod p] ZMod p) (β : LinearMap.BilinForm K V) :
    V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p :=
  LinearMap.mk₂ (ZMod p) (fun y x => τ (β x y))
    (fun y y' x => by simp)
    (fun a y x => by
      rw [← algebraMap_smul K a y, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul])
    (fun y x x' => by simp)
    (fun a y x => by
      rw [← algebraMap_smul K a x, map_smul, LinearMap.smul_apply, smul_eq_mul, ← Algebra.smul_def,
        map_smul])

theorem bilinDual_apply (τ : K →ₗ[ZMod p] ZMod p) (β : LinearMap.BilinForm K V) (y x : V) :
    bilinDual τ β y x = τ (β x y) := rfl

theorem eq_zero_of_trace_mul {τ : K →ₗ[ZMod p] ZMod p} (hτ : τ ≠ 0) {z : K}
    (h : ∀ c, τ (c * z) = 0) : z = 0 := by
  by_contra hz
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hτ (LinearMap.ext h')
  apply ha
  have := h (a / z)
  rwa [div_mul_cancel₀ _ hz] at this

theorem bilinDual_nondegenerate {τ : K →ₗ[ZMod p] ZMod p} (hτ : τ ≠ 0)
    {β : LinearMap.BilinForm K V} (hβ : β.Nondegenerate) : (bilinDual τ β).Nondegenerate := by
  refine ⟨fun y hy => hβ.2 y fun x => ?_, fun x hx => hβ.1 x fun y => ?_⟩
  · refine eq_zero_of_trace_mul hτ fun c => ?_
    have := hy (c • x)
    rwa [bilinDual_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  · refine eq_zero_of_trace_mul hτ fun c => ?_
    have := hx (c • y)
    rwa [bilinDual_apply, map_smul, smul_eq_mul] at this

theorem exists_smul_of_ker_eq_gen {F U : Type} [Field F] [AddCommGroup U] [Module F U]
    (B : U →ₗ[F] U →ₗ[F] F) (hsep : ∀ w, (∀ c, B w c = 0) → w = 0) {w w' : U} (hw : w ≠ 0)
    (h : ∀ c, B w c = 0 ↔ B w' c = 0) : ∃ a : F, a ≠ 0 ∧ w' = a • w := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, B w c₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (hsep w hcon)
  have hc₀' : B w' c₀ ≠ 0 := fun h0 => hc₀ ((h c₀).2 h0)
  set a : F := B w' c₀ / B w c₀ with ha
  have hform : ∀ c, B w' c = a * B w c := by
    intro c
    set t : F := B w c / B w c₀ with ht
    have h1 : B w (c - t • c₀) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hc₀, sub_self]
    have h2 := (h _).1 h1
    rw [map_sub, map_smul, smul_eq_mul] at h2
    have h3 : B w' c = t * B w' c₀ := sub_eq_zero.1 h2
    rw [h3, ht, ha]
    field_simp
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply hc₀'
    rw [hform c₀, h0, zero_mul]
  · apply sub_eq_zero.1
    apply hsep
    intro c
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hform c, smul_eq_mul,
      sub_self]

theorem exists_hyperplane_formB {τ : K →ₗ[ZMod p] ZMod p} (hτ : τ ≠ 0)
    {β : LinearMap.BilinForm K V} (hβ : β.Nondegenerate)
    (D' : AddSubgroup V) (hD : D'.index = p) :
    ∃ y : V, y ≠ 0 ∧ ∀ c, c ∈ D' ↔ bilinDual τ β y c = 0 := by
  classical
  have hFV : Finite V := Module.finite_of_finite K
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).one_lt.ne'
  have hne : D' ≠ ⊤ := by
    intro h
    rw [h, AddSubgroup.index_top] at hD
    exact hp1 hD.symm
  obtain ⟨x, hx⟩ : ∃ x, x ∉ D' := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.2 fun y _ => hcon y)
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := (AddSubgroup.toZModSubmodule p D')) (x := x) hx inferInstance
  have hDker : ∀ d ∈ D', f d = 0 := by
    intro d hd
    have hmem : f d ∈ Submodule.map f (AddSubgroup.toZModSubmodule p D') :=
      Submodule.mem_map_of_mem (show d ∈ AddSubgroup.toZModSubmodule p D' from hd)
    rw [hf] at hmem
    exact (Submodule.mem_bot (ZMod p)).1 hmem
  let Kf : AddSubgroup V := f.toAddMonoidHom.ker
  have hDK : D' ≤ Kf := fun d hd => hDker d hd
  have hrange : f.toAddMonoidHom.range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    refine ⟨(a / f x) • x, ?_⟩
    show f ((a / f x) • x) = a
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfx]
  have hKfidx : Kf.index = p := by
    rw [AddSubgroup.index_ker, hrange, Nat.card_congr AddSubgroup.topEquiv.toEquiv]
    simp
  have hcardD := AddSubgroup.card_mul_index D'
  have hcardK := AddSubgroup.card_mul_index Kf
  have hpos : 0 < p := (Fact.out : p.Prime).pos
  have hcard : Nat.card Kf = Nat.card D' := by
    rw [hD] at hcardD
    rw [hKfidx] at hcardK
    exact Nat.eq_of_mul_eq_mul_right hpos (hcardK.trans hcardD.symm)
  have hDeq : D' = Kf := AddSubgroup.eq_of_le_of_card_ge hDK hcard.le
  obtain ⟨y, hy⟩ := (LinearMap.BilinForm.toDual (bilinDual τ β)
    (bilinDual_nondegenerate hτ hβ)).surjective f
  have hyf : ∀ c, bilinDual τ β y c = f c := fun c => by rw [← hy]; rfl
  refine ⟨y, ?_, fun c => ?_⟩
  · rintro rfl
    apply hfx
    rw [← hyf x]
    simp
  · rw [hDeq, hyf c]
    rfl

@[expose] def kerSubB (B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p) (y : V) :
    Subgroup (Multiplicative V) where
  carrier := {c | B y c.toAdd = 0}
  mul_mem' {a b} ha hb := by
    show B y (a * b).toAdd = 0
    rw [toAdd_mul, map_add, ha, hb, add_zero]
  one_mem' := by
    show B y (1 : Multiplicative V).toAdd = 0
    rw [toAdd_one, map_zero]
  inv_mem' {a} ha := by
    show B y (a⁻¹).toAdd = 0
    rw [toAdd_inv, map_neg, ha]
    exact neg_zero

theorem mem_kerSubB {B : V →ₗ[ZMod p] V →ₗ[ZMod p] ZMod p} {y : V} {c : Multiplicative V} :
    c ∈ kerSubB B y ↔ B y c.toAdd = 0 := Iff.rfl

end Duality

section Orbit

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Module.Finite K V]
  {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] [Module (ZMod p) V] [IsScalarTower (ZMod p) K V]
  {S : Type} [Group S] {G : Type} [Group G]

theorem conjSub_map_kerSubB (τ : K →ₗ[ZMod p] ZMod p) (β : LinearMap.BilinForm K V)
    (u : Multiplicative V →* S) (t : G →* S) (ρ σ : G → V →ₗ[K] V)
    (hβρσ : ∀ g x y, β (ρ g x) (σ g y) = β x y)
    (htu : ∀ g v, t g * u (Multiplicative.ofAdd v) * (t g)⁻¹ = u (Multiplicative.ofAdd (ρ g v)))
    (hρ : ∀ g, Function.Surjective (ρ g)) (y : V) (g : G) :
    conjSub (t g) ((kerSubB (bilinDual τ β) y).map u) =
      (kerSubB (bilinDual τ β) (σ g y)).map u := by
  ext s
  unfold conjSub
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨Multiplicative.ofAdd (ρ g c.toAdd), ?_, ?_⟩
    · rw [mem_kerSubB, toAdd_ofAdd, bilinDual_apply, hβρσ]
      have h1 := mem_kerSubB.1 hc
      rwa [bilinDual_apply] at h1
    · have := htu g c.toAdd
      rw [ofAdd_toAdd] at this
      simpa [MulAut.conj_apply] using this.symm
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨v, hv⟩ := hρ g c'.toAdd
    refine ⟨u (Multiplicative.ofAdd v), ⟨Multiplicative.ofAdd v, ?_, rfl⟩, ?_⟩
    · rw [mem_kerSubB, toAdd_ofAdd]
      have h1 : bilinDual τ β (σ g y) c'.toAdd = 0 := hc'
      rw [← hv, bilinDual_apply, hβρσ] at h1
      rw [bilinDual_apply]
      exact h1
    · have := htu g v
      rw [hv, ofAdd_toAdd] at this
      simpa [MulAut.conj_apply] using this

end Orbit

section Main

theorem two_pow_le_card_of_bilinear_root_aux {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K V : Type} [Field K] [Finite K] [CharP K p] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Nontrivial V] [Algebra (ZMod p) K] [Module (ZMod p) V]
    [IsScalarTower (ZMod p) K V] (τ : K →ₗ[ZMod p] ZMod p) (hτ : τ ≠ 0)
    (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate)
    (u : Multiplicative V →* S) (hu : Function.Injective u)
    {G : Type} [Group G] (t : G →* S) (ρ σ : G → V →ₗ[K] V)
    (hβρσ : ∀ g x y, β (ρ g x) (σ g y) = β x y)
    (htu : ∀ g v, t g * u (Multiplicative.ofAdd v) * (t g)⁻¹ = u (Multiplicative.ofAdd (ρ g v)))
    {m : ℕ} (horb : ∀ y : V, y ≠ 0 → m ≤ Nat.card (Set.range fun g : G => σ g y)) :
    2 ^ (orderOf (2 : ZMod p) * (m / (p - 1))) ≤ Nat.card W := by
  classical
  have hFV : Finite V := Module.finite_of_finite K
  have : Fintype V := Fintype.ofFinite V
  have : Finite S := Finite.of_surjective π hπ
  have hBnd := bilinDual_nondegenerate hτ hβ
  have hUc : ∀ a ∈ u.range, ∀ b ∈ u.range, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨r, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hUp : ∀ a ∈ u.range, a ^ p = 1 := by
    rintro _ ⟨r, rfl⟩
    rw [← map_pow]
    have : r ^ p = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul K p, CharP.cast_eq_zero, zero_smul]
    rw [this, map_one]
  have hU1 : u.range ≠ ⊥ := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hm : u (Multiplicative.ofAdd v) ∈ u.range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot, ← map_one u] at hm
    exact hv (by simpa using hu hm)
  have hTN : t.range ≤ Subgroup.normalizer (u.range : Set S) := by
    rintro _ ⟨g, rfl⟩
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨Multiplicative.ofAdd (ρ g s.toAdd), ?_⟩
      rw [← htu g s.toAdd, ofAdd_toAdd]
    · rintro ⟨s', hs'⟩
      have e : h = t g⁻¹ * u s' * (t g⁻¹)⁻¹ := by rw [map_inv, hs']; group
      refine ⟨Multiplicative.ofAdd (ρ g⁻¹ s'.toAdd), ?_⟩
      rw [← htu g⁻¹ s'.toAdd, ofAdd_toAdd, ← e]
  have hρinj : ∀ g, Function.Injective (ρ g) := by
    intro g
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 := htu g v
    rw [hv, ofAdd_zero, map_one] at h1
    have h2 : u (Multiplicative.ofAdd v) = 1 := by
      calc u (Multiplicative.ofAdd v)
          = (t g)⁻¹ * (t g * u (Multiplicative.ofAdd v) * (t g)⁻¹) * t g := by group
        _ = 1 := by rw [h1]; group
    simpa using hu (h2.trans (map_one u).symm)
  have hρsurj : ∀ g, Function.Surjective (ρ g) := fun g =>
    LinearMap.injective_iff_surjective.1 (hρinj g)
  have hσne : ∀ g y, y ≠ 0 → σ g y ≠ 0 := by
    intro g y hy h0
    apply hy
    refine hβ.2 y fun x => ?_
    rw [← hβρσ g x y, h0, map_zero]
  have horb' : ∀ D : Subgroup S, D ≤ u.range → D.relIndex u.range = p →
      m / (p - 1) ≤ (t.range ⊓ Subgroup.normalizer (D : Set S)).relIndex t.range := by
    intro D hDU hrel
    obtain ⟨D'', hDD⟩ : ∃ D'' : Subgroup (Multiplicative V), D''.map u = D :=
      ⟨D.comap u, Subgroup.map_comap_eq_self hDU⟩
    have hidx : D''.index = p := by
      rw [← Subgroup.relIndex_top_right, ← Subgroup.relIndex_map_map_of_injective D'' ⊤ hu, hDD,
        ← MonoidHom.range_eq_map]
      exact hrel
    have hD'idx : (addOfMulGen D'').index = p := (index_addOfMulGen D'').trans hidx
    obtain ⟨y₀, hy₀, hform⟩ := exists_hyperplane_formB hτ hβ (addOfMulGen D'') hD'idx
    have hD'' : D'' = kerSubB (bilinDual τ β) y₀ := by
      ext c
      exact hform c.toAdd
    have hD₀eq : D = (kerSubB (bilinDual τ β) y₀).map u := by rw [← hDD, hD'']
    let Y : Finset V := (Set.toFinite (Set.range fun g : G => σ g y₀)).toFinset
    have hY : m ≤ Y.card := by
      have := horb y₀ hy₀
      rwa [Nat.card_eq_card_finite_toFinset (Set.toFinite _)] at this
    have hYne : ∀ y ∈ Y, y ≠ 0 := by
      intro y hy
      obtain ⟨g, rfl⟩ := (Set.Finite.mem_toFinset _).1 hy
      exact hσne g y₀ hy₀
    let 𝓢 : Finset (Subgroup S) := Y.image (fun y => (kerSubB (bilinDual τ β) y).map u)
    have hconj : ∀ E ∈ 𝓢, ∃ s ∈ t.range, conjSub s D = E := by
      intro E hE
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hE
      obtain ⟨g, rfl⟩ := (Set.Finite.mem_toFinset _).1 hy
      refine ⟨t g, ⟨g, rfl⟩, ?_⟩
      rw [hD₀eq]
      exact conjSub_map_kerSubB τ β u t ρ σ hβρσ htu hρsurj y₀ g
    refine le_trans ?_ (card_le_relIndex_of_conj hconj)
    have hfiber : ∀ a ∈ Y.image (fun y => (kerSubB (bilinDual τ β) y).map u),
        (Y.filter (fun y => (kerSubB (bilinDual τ β) y).map u = a)).card ≤ p - 1 := by
      intro a ha
      obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.1 ha
      have hy₁0 := hYne y₁ hy₁
      have hsub : (Y.filter (fun y => (kerSubB (bilinDual τ β) y).map u =
          (kerSubB (bilinDual τ β) y₁).map u)) ⊆
          (Finset.univ : Finset (ZMod p)ˣ).image (fun a : (ZMod p)ˣ => (a : ZMod p) • y₁) := by
        intro y' hy'
        obtain ⟨hy'Y, hy'eq⟩ := Finset.mem_filter.1 hy'
        have hker' := Subgroup.map_injective hu hy'eq
        obtain ⟨a, ha0, rfl⟩ := exists_smul_of_ker_eq_gen (bilinDual τ β) hBnd.1 hy₁0
          (w' := y') fun c =>
          (SetLike.ext_iff.1 hker' (Multiplicative.ofAdd c)).symm
        exact Finset.mem_image.2 ⟨Units.mk0 a ha0, Finset.mem_univ _, rfl⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
      rw [Finset.card_univ, ZMod.card_units]
    have hs := Finset.card_le_mul_card_image Y (p - 1) hfiber
    exact Nat.div_le_of_le_mul (le_trans hY hs)
  have h := two_pow_le_card_of_lift_orbit hW hp2 π hπ hker hZ hUc hUp hU1 hTN horb'
  rwa [mul_comm] at h

theorem two_pow_le_card_of_bilinear_root {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {S : Type} [Group S] (π : ↥L →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K V : Type} [Field K] [Finite K] [CharP K p] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Nontrivial V] (β : LinearMap.BilinForm K V) (hβ : β.Nondegenerate)
    (u : Multiplicative V →* S) (hu : Function.Injective u)
    {G : Type} [Group G] (t : G →* S) (ρ σ : G → V →ₗ[K] V)
    (hβρσ : ∀ g x y, β (ρ g x) (σ g y) = β x y)
    (htu : ∀ g v, t g * u (Multiplicative.ofAdd v) * (t g)⁻¹ = u (Multiplicative.ofAdd (ρ g v)))
    {m : ℕ} (horb : ∀ y : V, y ≠ 0 → m ≤ Nat.card (Set.range fun g : G => σ g y)) :
    2 ^ (orderOf (2 : ZMod p) * (m / (p - 1))) ≤ Nat.card W := by
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  let _ : Module (ZMod p) V := Module.compHom V (algebraMap (ZMod p) K)
  have : IsScalarTower (ZMod p) K V :=
    ⟨fun a c v => by
      show (a • c) • v = algebraMap (ZMod p) K a • (c • v)
      rw [Algebra.smul_def, mul_smul]⟩
  have hτ : Algebra.trace (ZMod p) K ≠ 0 := Algebra.trace_ne_zero (ZMod p) K
  exact two_pow_le_card_of_bilinear_root_aux hW hp2 π hπ hker hZ (Algebra.trace (ZMod p) K) hτ β hβ
    u hu t ρ σ hβρσ htu horb

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
