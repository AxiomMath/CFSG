module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

open Module Subgroup
open LinearMap (BilinForm)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {W : Type} [AddCommGroup W] [Module (ZMod 3) W]

theorem isometry_of_similitude_of_odd_prime_power {B : BilinForm (ZMod 3) W}
    (hB : B ≠ 0) {d k : ℕ} (hd : d.Prime) (hd2 : d ≠ 2)
    {x : (Module.End (ZMod 3) W)ˣ} (hx : orderOf x = d ^ k) {c : ZMod 3}
    (hc : ∀ u v : W, B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) =
      c * B u v) :
    ∀ u v : W, B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) = B u v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : Module.End (ZMod 3) W := x
  have hpow : ∀ m : ℕ, ∀ u v : W, B ((f ^ m) u) ((f ^ m) v) = c ^ m * B u v := by
    intro m
    induction m with
    | zero => intro u v; simp
    | succ m ih =>
        intro u v
        have hstep : B ((f ^ (m + 1)) u) ((f ^ (m + 1)) v) =
            B ((f ^ m) (f u)) ((f ^ m) (f v)) := by
          rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [hstep, ih, hc, pow_succ]
        ring
  have hfix : f ^ (d ^ k) = 1 := by
    have h : x ^ (d ^ k) = 1 := hx ▸ pow_orderOf_eq_one x
    simpa [f] using congrArg Units.val h
  have hc1 : c ^ (d ^ k) = 1 := by
    by_contra hne
    apply hB
    refine BilinForm.ext fun u v => ?_
    have h := hpow (d ^ k) u v
    rw [hfix, Module.End.one_apply] at h
    have hzero : (c ^ (d ^ k) - 1) * B u v = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr h.symm
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (pow_pos hd.pos k).ne'] at hc1
    exact zero_ne_one hc1
  have hc2 : c ^ 2 = 1 := by simpa using ZMod.pow_card_sub_one_eq_one hc0
  obtain ⟨a, ha⟩ := (hd.odd_of_ne_two hd2).pow (n := k)
  have hcpow : c ^ (d ^ k) = c := by
    rw [ha, pow_add, pow_mul, hc2, one_pow, pow_one, one_mul]
  have heq : c = 1 := hcpow.symm.trans hc1
  intro u v
  rw [hc, heq, one_mul]

theorem card_dvd_symplectic_of_odd_prime [Module.Finite (ZMod 3) W]
    (hdim : finrank (ZMod 3) W = 4) (B : BilinForm (ZMod 3) W)
    (hnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (halt : ∀ w : W, B w w = 0)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) {D : Subgroup (Module.End (ZMod 3) W)ˣ}
    (hD : IsPGroup d D)
    (hsim : ∀ x ∈ D, ∃ c : ZMod 3, ∀ u v : W,
      B ((x : Module.End (ZMod 3) W) u) ((x : Module.End (ZMod 3) W) v) = c * B u v) :
    Nat.card D ∣ Nat.card ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) := by
  classical
  have : Fact d.Prime := ⟨hd⟩
  have hB : B ≠ 0 := by
    intro hB0
    have : Subsingleton W := ⟨fun u v => by
      have hu : u = 0 := hnd u (by simp [hB0])
      have hv : v = 0 := hnd v (by simp [hB0])
      rw [hu, hv]⟩
    have h0 : finrank (ZMod 3) W = 0 := Module.finrank_zero_of_subsingleton
    omega
  have hBnd : B.Nondegenerate := BilinForm.Nondegenerate.ofSeparatingLeft hnd
  obtain ⟨m, b, hdim', hbJ⟩ := exists_symplectic_basis B (show B.IsAlt from halt) hBnd
  obtain rfl : m = 2 := by omega
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W
  have hDiso : ∀ x ∈ D, e x ∈ isometryGroup B := by
    intro x hx
    obtain ⟨c, hc⟩ := hsim x hx
    obtain ⟨k, hk⟩ := hD.exists_orderOf_eq_pow (⟨x, hx⟩ : D)
    have hord : orderOf x = d ^ k := (Subgroup.orderOf_coe ⟨x, hx⟩).trans hk
    exact (mem_isometryGroup_iff B (e x)).mpr
      (isometry_of_similitude_of_odd_prime_power hB hd hd2 hord hc)
  let ψ : D →* isometryGroup B :=
    { toFun := fun x => ⟨e x, hDiso x x.2⟩
      map_one' := Subtype.ext e.map_one
      map_mul' x y := Subtype.ext (e.map_mul x y) }
  have hψ : Function.Injective ψ := by
    intro x y h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  let E : isometryGroup B ≃* ↥(Matrix.symplecticGroup (Fin 2) (ZMod 3)) :=
    (isometryMatrixEquiv b B hbJ).trans (TauCeti.GLSymplectic.mulEquivSymplecticGroup _ _)
  exact Subgroup.card_dvd_of_injective (E.toMonoidHom.comp ψ) (E.injective.comp hψ)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.SmallSympDLeK

end
