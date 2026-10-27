module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LargeExtraspecial.S4Restrict

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {K : Type*} [Group K]

structure CEHyp (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K) (a : V)
    (X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  range_eq : π.range = X
  ker_le_center : π.ker ≤ center K
  inf_ker_eq_bot : E ⊓ π.ker = ⊥
  map_eq : E.map π = E₀
  closure_conj_eq_top : closure {k | ∃ x : K, ∃ e ∈ E, k = x * e * x⁻¹} = ⊤
  le_normalizer : ∀ x : K, π x a = a → x ∈ normalizer (E : Set K)

theorem inv_apply_self' (g : V ≃ₗ[ZMod 2] V) (v : V) : g⁻¹ (g v) = v :=
  g.symm_apply_apply v

theorem apply_inv_self' (g : V ≃ₗ[ZMod 2] V) (v : V) : g (g⁻¹ v) = v :=
  g.apply_symm_apply v

@[expose] def Eb (E : Subgroup K) (k : K) : Subgroup K :=
  E.map (MulAut.conj k).toMonoidHom

theorem mem_Eb {E : Subgroup K} {k e : K} : e ∈ Eb E k ↔ k⁻¹ * e * k ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro he
    exact ⟨k⁻¹ * e * k, he, by simp [mul_assoc]⟩

theorem Eb_one (E : Subgroup K) : Eb E 1 = E := by
  ext e
  simp [mem_Eb]

theorem conj_mem_Eb {E : Subgroup K} {k e : K} (he : e ∈ E) : k * e * k⁻¹ ∈ Eb E k :=
  mem_Eb.mpr (by simpa [mul_assoc] using he)

theorem mul_conj_mem_Eb {E : Subgroup K} {k e : K} (he : e ∈ Eb E k) (x : K) :
    x * e * x⁻¹ ∈ Eb E (x * k) := by
  rw [mem_Eb] at he ⊢
  simpa [mul_assoc] using he

namespace CEHyp

variable {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

section Basic

variable (h : CEHyp π E a X E₀)
include h

theorem conj_mem_of_apply_eq {x e : K} (hx : π x a = a) (he : e ∈ E) : x * e * x⁻¹ ∈ E :=
  (mem_normalizer_iff.mp (h.le_normalizer x hx) e).mp he

theorem mem_center_of_mem_ker {z : K} (hz : π z = 1) : z ∈ center K :=
  h.ker_le_center (MonoidHom.mem_ker.mpr hz)

theorem Eb_eq_of_apply_eq {k k' : K} (hk : π k a = π k' a) : Eb E k = Eb E k' := by
  have hn : π (k⁻¹ * k') a = a := by
    rw [map_mul, LinearEquiv.mul_apply, ← hk, map_inv, inv_apply_self']
  ext e
  rw [mem_Eb, mem_Eb]
  have key := mem_normalizer_iff.mp (h.le_normalizer _ hn) (k'⁻¹ * e * k')
  rw [show k⁻¹ * k' * (k'⁻¹ * e * k') * (k⁻¹ * k')⁻¹ = k⁻¹ * e * k by group] at key
  exact key.symm

theorem Eb_inf_ker (k : K) : Eb E k ⊓ π.ker = ⊥ := by
  rw [eq_bot_iff]
  intro e hmem
  obtain ⟨he, hz⟩ := mem_inf.mp hmem
  rw [mem_Eb] at he
  rw [MonoidHom.mem_ker] at hz
  have h1 : k⁻¹ * e * k ∈ E ⊓ π.ker := mem_inf.mpr
    ⟨he, by rw [MonoidHom.mem_ker, map_mul, map_mul, hz, mul_one, map_inv, inv_mul_cancel]⟩
  rw [h.inf_ker_eq_bot, mem_bot] at h1
  rw [mem_bot]
  calc e = k * (k⁻¹ * e * k) * k⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem map_Eb (k : K) : (Eb E k).map π = E₀.map (MulAut.conj (π k)).toMonoidHom := by
  rw [← h.map_eq, Eb, map_map, map_map]
  congr 1
  ext x
  simp

theorem mem_normalizer_Eb {k x : K} (hx : π x (π k a) = π k a) :
    x ∈ normalizer (Eb E k : Set K) := by
  have hn : π (k⁻¹ * x * k) a = a := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hx, map_inv,
      inv_apply_self']
  rw [mem_normalizer_iff]
  intro e
  simp only [mem_Eb]
  have key := mem_normalizer_iff.mp (h.le_normalizer _ hn) (k⁻¹ * e * k)
  rw [show k⁻¹ * x * k * (k⁻¹ * e * k) * (k⁻¹ * x * k)⁻¹ = k⁻¹ * (x * e * x⁻¹) * k by group]
    at key
  exact key

theorem eq_of_mem_Eb {k e e' : K} (he : e ∈ Eb E k) (he' : e' ∈ Eb E k) (hπ : π e = π e') :
    e = e' := by
  have hmem : e * e'⁻¹ ∈ Eb E k ⊓ π.ker := mem_inf.mpr
    ⟨mul_mem he (inv_mem he'), by rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, mul_inv_cancel]⟩
  rw [h.Eb_inf_ker, mem_bot, mul_inv_eq_one] at hmem
  exact hmem

end Basic

end CEHyp

open Classical in
@[expose] noncomputable def Ept (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K) (a p : V) :
    Subgroup K :=
  if hp : ∃ k, π k a = p then Eb E hp.choose else E

open Classical in
@[expose] noncomputable def liftPt (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K) (a p : V)
    (g : V ≃ₗ[ZMod 2] V) : K :=
  if hg : ∃ e ∈ Ept π E a p, π e = g then hg.choose else 1

variable {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem liftPt_spec {p : V} {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ (Ept π E a p).map π) :
    liftPt π E a p g ∈ Ept π E a p ∧ π (liftPt π E a p g) = g := by
  have hg' : ∃ e ∈ Ept π E a p, π e = g := hg
  rw [liftPt, dite_eq_left hg']
  exact hg'.choose_spec

theorem liftPt_mem {p : V} {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ (Ept π E a p).map π) :
    liftPt π E a p g ∈ Ept π E a p :=
  (liftPt_spec hg).1

theorem apply_liftPt {p : V} {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ (Ept π E a p).map π) :
    π (liftPt π E a p g) = g :=
  (liftPt_spec hg).2

namespace CEHyp

variable (h : CEHyp π E a X E₀)
include h

theorem Ept_eq {k : K} {p : V} (hk : π k a = p) : Ept π E a p = Eb E k := by
  have hp : ∃ k, π k a = p := ⟨k, hk⟩
  rw [Ept, dite_eq_left hp]
  exact h.Eb_eq_of_apply_eq (hp.choose_spec.trans hk.symm)

theorem Ept_self : Ept π E a a = E := by
  rw [h.Ept_eq (k := 1) (by rw [map_one]; rfl), Eb_one]

theorem map_Ept {k : K} {p : V} (hk : π k a = p) :
    (Ept π E a p).map π = E₀.map (MulAut.conj (π k)).toMonoidHom := by
  rw [h.Ept_eq hk, h.map_Eb]

theorem Ept_inf_ker {p : V} (hp : ∃ k, π k a = p) : Ept π E a p ⊓ π.ker = ⊥ := by
  obtain ⟨k, hk⟩ := hp
  rw [h.Ept_eq hk, h.Eb_inf_ker]

theorem conj_mem_Ept {p : V} (hp : ∃ k, π k a = p) {e : K} (he : e ∈ Ept π E a p) (x : K) :
    x * e * x⁻¹ ∈ Ept π E a (π x p) := by
  obtain ⟨k, hk⟩ := hp
  rw [h.Ept_eq hk] at he
  rw [h.Ept_eq (k := x * k) (by rw [map_mul, LinearEquiv.mul_apply, hk])]
  exact mul_conj_mem_Eb he x

theorem mem_normalizer_Ept {p : V} (hp : ∃ k, π k a = p) {x : K} (hx : π x p = p) :
    x ∈ normalizer (Ept π E a p : Set K) := by
  obtain ⟨k, hk⟩ := hp
  rw [h.Ept_eq hk]
  exact h.mem_normalizer_Eb (by rw [hk]; exact hx)

theorem commutatorElement_mem_Ept {p : V} (hp : ∃ k, π k a = p) {e x : K}
    (he : e ∈ Ept π E a p) (hx : π x p = p) : ⁅e, x⁆ ∈ Ept π E a p := by
  rw [commutatorElement_def,
    show e * x * e⁻¹ * x⁻¹ = e * (x * e⁻¹ * x⁻¹) by group]
  exact mul_mem he ((mem_normalizer_iff.mp (h.mem_normalizer_Ept hp hx) _).mp (inv_mem he))

theorem commutatorElement_mem_Ept' {p : V} (hp : ∃ k, π k a = p) {e x : K}
    (he : e ∈ Ept π E a p) (hx : π x p = p) : ⁅x, e⁆ ∈ Ept π E a p := by
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp (h.mem_normalizer_Ept hp hx) _).mp he) (inv_mem he)

theorem eq_of_mem_Ept {p : V} (hp : ∃ k, π k a = p) {e e' : K} (he : e ∈ Ept π E a p)
    (he' : e' ∈ Ept π E a p) (hπ : π e = π e') : e = e' := by
  obtain ⟨k, hk⟩ := hp
  rw [h.Ept_eq hk] at he he'
  exact h.eq_of_mem_Eb he he' hπ

theorem eq_one_of_mem_Ept {p : V} (hp : ∃ k, π k a = p) {e : K} (he : e ∈ Ept π E a p)
    (hπ : π e = 1) : e = 1 :=
  h.eq_of_mem_Ept hp he (one_mem _) (by rw [hπ, map_one])

theorem liftPt_eq {p : V} (hp : ∃ k, π k a = p) {e : K} (he : e ∈ Ept π E a p) :
    liftPt π E a p (π e) = e :=
  h.eq_of_mem_Ept hp (liftPt_mem ⟨e, he, rfl⟩) he (apply_liftPt ⟨e, he, rfl⟩)

theorem liftPt_eq_of_apply_eq {p : V} (hp : ∃ k, π k a = p) {e : K} {g : V ≃ₗ[ZMod 2] V}
    (he : e ∈ Ept π E a p) (hg : π e = g) : liftPt π E a p g = e := by
  rw [← hg, h.liftPt_eq hp he]

theorem liftPt_one {p : V} (hp : ∃ k, π k a = p) : liftPt π E a p 1 = 1 := by
  rw [← map_one π, h.liftPt_eq hp (one_mem _)]

theorem liftPt_mul {p : V} (hp : ∃ k, π k a = p) {g g' : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ (Ept π E a p).map π) (hg' : g' ∈ (Ept π E a p).map π) :
    liftPt π E a p (g * g') = liftPt π E a p g * liftPt π E a p g' :=
  h.liftPt_eq_of_apply_eq hp (mul_mem (liftPt_mem hg) (liftPt_mem hg'))
    (by rw [map_mul, apply_liftPt hg, apply_liftPt hg'])

theorem conj_mem_map_Ept {p : V} (hp : ∃ k, π k a = p) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ (Ept π E a p).map π) (x : K) :
    π x * g * (π x)⁻¹ ∈ (Ept π E a (π x p)).map π := by
  obtain ⟨e, he, rfl⟩ := hg
  exact ⟨x * e * x⁻¹, h.conj_mem_Ept hp he x, by rw [map_mul, map_mul, map_inv]⟩

theorem liftPt_conj {p : V} (hp : ∃ k, π k a = p) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ (Ept π E a p).map π) (x : K) :
    liftPt π E a (π x p) (π x * g * (π x)⁻¹) = x * liftPt π E a p g * x⁻¹ := by
  obtain ⟨k, hk⟩ := hp
  refine h.liftPt_eq_of_apply_eq ⟨x * k, by rw [map_mul, LinearEquiv.mul_apply, hk]⟩
    (h.conj_mem_Ept ⟨k, hk⟩ (liftPt_mem hg) x) ?_
  rw [map_mul, map_mul, map_inv, apply_liftPt hg]

theorem commutatorElement_liftPt {p : V} (hp : ∃ k, π k a = p) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ (Ept π E a p).map π) {x : K} (hx : π x p = p) :
    ⁅liftPt π E a p g, x⁆ = liftPt π E a p ⁅g, π x⁆ :=
  (h.liftPt_eq_of_apply_eq hp (h.commutatorElement_mem_Ept hp (liftPt_mem hg) hx)
    (by rw [map_commutatorElement, apply_liftPt hg])).symm

theorem commutatorElement_liftPt' {p : V} (hp : ∃ k, π k a = p) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ (Ept π E a p).map π) {x : K} (hx : π x p = p) :
    ⁅x, liftPt π E a p g⁆ = liftPt π E a p ⁅π x, g⁆ :=
  (h.liftPt_eq_of_apply_eq hp (h.commutatorElement_mem_Ept' hp (liftPt_mem hg) hx)
    (by rw [map_commutatorElement, apply_liftPt hg])).symm

theorem exists_mem_inv_mul_mem_ker {H : Subgroup K} (hHX : X ≤ H.map π) (x : K) :
    ∃ y ∈ H, y⁻¹ * x ∈ π.ker := by
  have hx : π x ∈ X := h.range_eq ▸ ⟨x, rfl⟩
  obtain ⟨y, hy, hπ⟩ := hHX hx
  exact ⟨y, hy, by rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]⟩

theorem normal_of_le_map {H : Subgroup K} (hHX : X ≤ H.map π) : H.Normal := by
  refine ⟨fun y hy x => ?_⟩
  obtain ⟨y', hy', hz⟩ := h.exists_mem_inv_mul_mem_ker hHX x
  have hzy := (mem_center_iff.mp (h.ker_le_center hz)) y
  have e : x * y * x⁻¹ = y' * y * y'⁻¹ := by
    calc x * y * x⁻¹ = y' * ((y'⁻¹ * x) * y) * x⁻¹ := by group
      _ = y' * (y * (y'⁻¹ * x)) * x⁻¹ := by rw [hzy]
      _ = y' * y * y'⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hy' hy) (inv_mem hy')

theorem ker_sup_eq_top_of_le_map {H : Subgroup K} (hHX : X ≤ H.map π) : π.ker ⊔ H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hz⟩ := h.exists_mem_inv_mul_mem_ker hHX x
  have := mul_mem (mem_sup_right (S := π.ker) hy) (mem_sup_left (T := H) hz)
  rwa [mul_inv_cancel_left] at this

theorem eq_top_of_normal {D : Subgroup K} [D.Normal] {k : K} (hE : Eb E k ≤ D) : D = ⊤ := by
  have hEH : E ≤ D := by
    intro e he
    have := ‹D.Normal›.conj_mem _ (hE (conj_mem_Eb (k := k) he)) k⁻¹
    rwa [show k⁻¹ * (k * e * k⁻¹) * k⁻¹⁻¹ = e by group] at this
  rw [eq_top_iff, ← h.closure_conj_eq_top, closure_le]
  rintro _ ⟨x, e, he, rfl⟩
  exact ‹D.Normal›.conj_mem e (hEH he) x

theorem ker_eq_bot_of_le {H : Subgroup K} (hHZ : H ⊓ π.ker = ⊥) (hHX : X ≤ H.map π) {k : K}
    (hE : Eb E k ≤ H) : π.ker = ⊥ := by
  have := h.normal_of_le_map hHX
  rw [← hHZ, h.eq_top_of_normal hE, top_inf_eq]

theorem ker_eq_bot_of_hom {G : Type*} [Group G] (σ : G →* K)
    (hinj : Function.Injective (π.comp σ)) (hX : X ≤ (π.comp σ).range) {p : V}
    (hp : ∃ k, π k a = p) (hE : Ept π E a p ≤ σ.range) : π.ker = ⊥ := by
  obtain ⟨k, hk⟩ := hp
  refine h.ker_eq_bot_of_le (H := σ.range) ?_ (by rwa [MonoidHom.map_range]) (k := k)
    (by rwa [← h.Ept_eq hk])
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨g, rfl⟩, hz⟩ := mem_inf.mp hy
  rw [MonoidHom.mem_ker] at hz
  have hg : g = 1 := hinj (by rw [MonoidHom.comp_apply, hz, MonoidHom.comp_apply, map_one,
    map_one])
  rw [hg, map_one]
  exact one_mem _

theorem Ept_le_range {p : V} (hp : ∃ k, π k a = p) {G : Type*} [Group G] (σ : G →* K)
    {S : Set (V ≃ₗ[ZMod 2] V)} (hS : (Ept π E a p).map π ≤ closure S)
    (hσ : ∀ s ∈ S, ∃ y ∈ σ.range, y ∈ Ept π E a p ∧ π y = s) : Ept π E a p ≤ σ.range := by
  have hT : closure S ≤ (σ.range ⊓ Ept π E a p).map π := by
    rw [closure_le]
    intro s hs
    obtain ⟨y, hy, hyE, hys⟩ := hσ s hs
    exact ⟨y, ⟨hy, hyE⟩, hys⟩
  intro e he
  obtain ⟨y, ⟨hy, hyE⟩, hye⟩ := hT (hS ⟨e, he, rfl⟩)
  rw [← h.eq_of_mem_Ept hp hyE he hye]
  exact hy

end CEHyp

theorem exists_linearEquiv_apply_eq_of_ne {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] {x y : W} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : W ≃ₗ[F] W, g x = y := by
  let f : (F ∙ x) ≃ₗ[F] (F ∙ y) :=
    (LinearEquiv.toSpanNonzeroSingleton F W x hx).symm ≪≫ₗ
      (LinearEquiv.toSpanNonzeroSingleton F W y hy)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, ?_⟩
  have h1 := hg ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [← h1]
  have h2 : (LinearEquiv.toSpanNonzeroSingleton F W x hx).symm
      ⟨x, Submodule.mem_span_singleton_self x⟩ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp
  simp [f, h2]

end CFSG.LargeExtraspecial.S4
