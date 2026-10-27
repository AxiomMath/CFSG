module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LieType.SeitzGeneration.UnitaryHyperRad

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def qPerp (X : Submodule K V) : Submodule K V where
  carrier := {v | ∀ x ∈ X, polar Q x v = 0}
  add_mem' := fun {a b} ha hb x hx => by rw [polar_add_right, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => polar_zero_right Q x
  smul_mem' := fun c v hv x hx => by rw [polar_smul_right_eq, hv x hx, mul_zero]

theorem mem_qPerp {X : Submodule K V} {v : V} : v ∈ qPerp Q X ↔ ∀ x ∈ X, polar Q x v = 0 :=
  Iff.rfl

theorem le_qPerp_of_singular {X : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) : X ≤ qPerp Q X :=
  fun x hx y hy => by
    have h := hX (y + x) (X.add_mem hy hx)
    rw [polar, h, hX y hy, hX x hx]
    ring

theorem apply_mem_qPerp {X : Submodule K V} {a : V ≃ₗ[K] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (haX : ∀ x ∈ X, a⁻¹ x ∈ X) {v : V}
    (hv : v ∈ qPerp Q X) : a v ∈ qPerp Q X := by
  intro x hx
  calc polar Q x (a v) = polar Q (a (a⁻¹ x)) (a v) := by rw [LinearEquiv.apply_inv_apply']
    _ = polar Q (a⁻¹ x) v := polar_map_of_mem ha _ _
    _ = 0 := hv _ (haX x hx)

@[expose] def autToEnd (K V : Type) [Field K] [AddCommGroup V] [Module K V] :
    (V ≃ₗ[K] V) →* Module.End K V where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

theorem autToEnd_apply (g : V ≃ₗ[K] V) (v : V) : autToEnd K V g v = g v := rfl

variable (Q) in
@[expose] def qRad (X : Submodule K V) (hX : ∀ x ∈ X, Q x = 0) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | (∀ x, g x - x ∈ qPerp Q X) ∧ (∀ x ∈ qPerp Q X, g x - x ∈ X) ∧ ∀ x ∈ X, g x = x}
  mul_mem' := by
    rintro g h ⟨hg1, hg2, hg3⟩ ⟨hh1, hh2, hh3⟩
    have hXP := le_qPerp_of_singular hX
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [LinearEquiv.mul_apply]
      have := (qPerp Q X).add_mem (hg1 (h x)) (hh1 x)
      simpa using this
    · have hhx : h x ∈ qPerp Q X := by
        have := (qPerp Q X).add_mem hx (hXP (hh2 x hx))
        simpa using this
      rw [LinearEquiv.mul_apply]
      have := X.add_mem (hg2 _ hhx) (hh2 x hx)
      simpa using this
    · rw [LinearEquiv.mul_apply, hh3 x hx, hg3 x hx]
  one_mem' := ⟨fun x => by simp, fun x _ => by simp, fun x _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2, hg3⟩
    have hy : ∀ x, g⁻¹ x - x = -(g (g⁻¹ x) - g⁻¹ x) := fun x => by
      rw [LinearEquiv.apply_inv_apply']
      abel
    refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hy]
      exact (qPerp Q X).neg_mem (hg1 _)
    · have hyP : g⁻¹ x ∈ qPerp Q X := by
        have h1 : g⁻¹ x = x - (g (g⁻¹ x) - g⁻¹ x) := by
          rw [LinearEquiv.apply_inv_apply']
          abel
        rw [h1]
        exact (qPerp Q X).sub_mem hx (hg1 _)
      rw [hy]
      exact X.neg_mem (hg2 _ hyP)
    · conv_lhs => rw [← hg3 x hx]
      exact LinearEquiv.inv_apply_apply' g x

theorem mem_qRad {X : Submodule K V} {hX : ∀ x ∈ X, Q x = 0} {g : V ≃ₗ[K] V} :
    g ∈ qRad Q X hX ↔ (∀ x, g x - x ∈ qPerp Q X) ∧ (∀ x ∈ qPerp Q X, g x - x ∈ X) ∧
      ∀ x ∈ X, g x = x := Iff.rfl

theorem eichler_mem_qRad {X : Submodule K V} {hX : ∀ x ∈ X, Q x = 0} {e w : V} (he : e ∈ X)
    (hw : w ∈ qPerp Q X) : eichler Q e w ∈ qRad Q X hX := by
  have hXP := le_qPerp_of_singular hX
  have hQe : Q e = 0 := hX e he
  have hew : polar Q e w = 0 := hw e he
  have hdiff : ∀ x, eichler Q e w x - x = polar Q x e • w - (polar Q x w + Q w * polar Q x e) • e :=
    fun x => by rw [eichler_apply hQe hew]; abel
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hdiff]
    exact (qPerp Q X).sub_mem ((qPerp Q X).smul_mem _ hw) ((qPerp Q X).smul_mem _ (hXP he))
  · have hxe : polar Q x e = 0 := by rw [polar_comm]; exact hx e he
    rw [hdiff, hxe, zero_smul, zero_sub]
    exact X.neg_mem (X.smul_mem _ he)
  · have hxe : polar Q x e = 0 := hXP he x hx
    have hxw : polar Q x w = 0 := hw x hx
    rw [eichler_apply hQe hew, hxe, hxw]
    simp

theorem qRad_conj_mem {X : Submodule K V} {hX : ∀ x ∈ X, Q x = 0} {a g : V ≃ₗ[K] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (haX : ∀ x ∈ X, a x ∈ X)
    (haX' : ∀ x ∈ X, a⁻¹ x ∈ X) (hg : g ∈ qRad Q X hX) : a * g * a⁻¹ ∈ qRad Q X hX := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hP' : ∀ v ∈ qPerp Q X, a⁻¹ v ∈ qPerp Q X := fun v hv =>
    apply_mem_qPerp (a := a⁻¹) ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem ha)
      (by simpa using haX) hv
  have hmul : ∀ x, (a * g * a⁻¹) x = a (g (a⁻¹ x)) := fun x => by
    simp only [LinearEquiv.mul_apply]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := apply_mem_qPerp ha haX' (hg1 (a⁻¹ x))
    rw [map_sub, LinearEquiv.apply_inv_apply'] at h1
    rw [hmul]
    exact h1
  · have h1 := haX _ (hg2 _ (hP' x hx))
    rw [map_sub, LinearEquiv.apply_inv_apply'] at h1
    rw [hmul]
    exact h1
  · rw [hmul, hg3 _ (haX' x hx), LinearEquiv.apply_inv_apply']

theorem eq_one_of_pow_eq_one_qRad {X : Submodule K V} {hX : ∀ x ∈ X, Q x = 0} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {g : V ≃ₗ[K] V} (hg : g ∈ qRad Q X hX)
    (hgp : g ^ p = 1) : g = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  set N : Module.End K V := autToEnd K V g - 1 with hNdef
  have hNx : ∀ x, N x = g x - x := fun x => by simp [hNdef, autToEnd_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ qPerp Q X := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ X := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : autToEnd K V g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg (autToEnd K V) hgp
  rw [map_pow, map_one, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 p] at hpow
  set c : K := (((p - 1) / 2 : ℕ) : K) with hc
  have hchoose : (p.choose 2 : K) = (p : K) * c := by
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (even_iff_two_dvd.1 (hp.even_sub_one hp2))]
    push_cast
    rfl
  have h1 : (p : K) • (N + c • (N * N)) = 0 := by
    have h0 : (p : K) • N + (p.choose 2 : K) • (N * N) = 0 := by
      have := hpow
      rw [add_assoc] at this
      exact add_eq_left.1 this
    rw [hchoose, mul_smul] at h0
    rw [smul_add]
    exact h0
  have h2 : N + c • (N * N) = 0 := (smul_eq_zero.1 h1).resolve_left hpK
  have h3 : N * N = 0 := by
    have h := congrArg (fun X => N * X) h2
    simp only [mul_add, mul_zero, mul_smul_comm, ← mul_assoc, hN3, smul_zero, add_zero] at h
    exact h
  have h4 : N = 0 := by
    rw [h3, smul_zero, add_zero] at h2
    exact h2
  have h5 : autToEnd K V g = 1 := by rw [hg1', h4, add_zero]
  refine LinearEquiv.ext fun v => ?_
  have := LinearMap.congr_fun h5 v
  simpa [autToEnd_apply] using this

theorem not_dvd_card_comap_qRad [Finite (V ≃ₗ[K] V)] {X : Submodule K V}
    {hX : ∀ x ∈ X, Q x = 0} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (G : Subgroup (V ≃ₗ[K] V)) : ¬ p ∣ Nat.card ((qRad Q X hX).comap G.subtype) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 : ((g : G) : V ≃ₗ[K] V) ^ p = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg (fun y : G => (y : V ≃ₗ[K] V)) (congrArg Subtype.val this)
  have h2 : ((g : G) : V ≃ₗ[K] V) = 1 := eq_one_of_pow_eq_one_qRad (hX := hX) hp hp2 hpK g.2 h1
  have h3 : g = 1 := Subtype.ext (Subtype.ext h2)
  rw [h3, orderOf_one] at hg
  exact hp.one_lt.ne hg

end CFSG.LieType.SeitzGeneration
