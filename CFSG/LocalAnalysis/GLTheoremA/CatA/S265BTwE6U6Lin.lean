module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BBigAb
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructNonab

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem abelian_exp_three_of_invariant [Finite K] (hK : Nat.card K = 4)
    [FiniteDimensional K V] {Q : Subgroup (V ≃ₗ[K] V)} (hQ : IsGoodIn (scalars K V) Q)
    (W : Submodule K V) (hW : ∀ x ∈ Q, ∀ w ∈ W, x w ∈ W) (h3 : ¬ 3 ∣ Module.finrank K W) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  let ρ : Q →* (W ≃ₗ[K] W) :=
    CFSG.LargeExtraspecial.S4.restrictHom Q.subtype W (fun x w hw => hW x x.2 w hw)
  let δ : Q →* Kˣ := LinearEquiv.det.comp ρ
  have key : ∀ z : Q, δ z = 1 → (z : V ≃ₗ[K] V) ∈ scalars K V → (z : V ≃ₗ[K] V) = 1 := by
    intro z hz hs
    obtain ⟨c, hc⟩ := mem_scalars_iff.1 hs
    have hρ : ((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) = (c : K) • LinearMap.id :=
      LinearMap.ext fun w => Subtype.ext (hc w)
    have hdet : c ^ Module.finrank K W = 1 := by
      have h1 : LinearMap.det ((ρ z : W ≃ₗ[K] W) : W →ₗ[K] W) = 1 := by
        rw [← LinearEquiv.coe_det]
        exact (congrArg Units.val hz).trans Units.val_one
      rw [hρ, LinearMap.det_smul, LinearMap.det_id, mul_one] at h1
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have hc1 : c = 1 := by
      have h := pow_gcd_eq_one.2 ⟨units_pow_three hK c, hdet⟩
      rwa [show Nat.gcd 3 (Module.finrank K W) = 1 from
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3, pow_one] at h
    refine LinearEquiv.ext fun v => ?_
    rw [hc v, hc1, Units.val_one, one_smul]
    rfl
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h := key ⁅(⟨x, hx⟩ : Q), ⟨y, hy⟩⁆ (by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _) (hQ.1 x hx y hy)
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  · have h := key ((⟨x, hx⟩ : Q) ^ 3) (by rw [map_pow]; exact units_pow_three hK _) (hQ.2 x hx)
    simpa using h

theorem abelian_exp_three_of_commute_involution [Finite K] (hK : Nat.card K = 4)
    [FiniteDimensional K V] (hV : Module.finrank K V = 6) {Q : Subgroup (V ≃ₗ[K] V)}
    (hQ : IsGoodIn (scalars K V) Q) (hcard : 3 ^ 4 ≤ Nat.card Q) {u : V ≃ₗ[K] V}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hcomm : ∀ x ∈ Q, x * u = u * x) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  classical
  have hZ := scalarLike_scalars (V := V) hK
  have h2 : ∀ v : V, v + v = 0 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    intro v
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  have huu : ∀ v, u (u v) = v := fun v => by
    have := congrArg (fun e : V ≃ₗ[K] V => e v) hu2
    simpa [pow_two] using this
  let N : V →ₗ[K] V := (u : V →ₗ[K] V) - LinearMap.id
  have hNv : ∀ v, N v = u v - v := fun v => rfl
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    rw [hNv, hNv, map_sub, huu, show v - u v - (u v - v) = (v + v) - (u v + u v) by abel, h2, h2,
      sub_zero]
  have hxN : ∀ x ∈ Q, ∀ v, x (N v) = N (x v) := by
    intro x hx v
    have h1 : x (u v) = u (x v) := by
      have := congrArg (fun e : V ≃ₗ[K] V => e v) (hcomm x hx)
      simpa using this
    rw [hNv, hNv, map_sub, h1]
  set W : Submodule K V := LinearMap.range N
  have hWle : W ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.2 (hNN v)
  have hWQ : ∀ x ∈ Q, ∀ w ∈ W, x w ∈ W := by
    rintro x hx _ ⟨v, rfl⟩
    exact ⟨x v, (hxN x hx v).symm⟩
  have hW0 : Module.finrank K W ≠ 0 := by
    intro h0
    apply hu1
    refine LinearEquiv.ext fun v => ?_
    have hmem : N v ∈ W := LinearMap.mem_range_self N v
    rw [Submodule.finrank_eq_zero.1 h0, Submodule.mem_bot, hNv, sub_eq_zero] at hmem
    simpa using hmem
  have hdim : Module.finrank K W + Module.finrank K (LinearMap.ker N) = 6 := by
    rw [← hV]
    exact LinearMap.finrank_range_add_finrank_ker N
  have hle := Submodule.finrank_mono hWle
  by_cases hW3 : Module.finrank K W = 3
  swap
  · exact abelian_exp_three_of_invariant hK hQ W hWQ (by omega)
  have hWk : W = LinearMap.ker N := Submodule.eq_of_le_of_finrank_eq hWle (by omega)
  let ρ : Q →* (W ≃ₗ[K] W) :=
    CFSG.LargeExtraspecial.S4.restrictHom Q.subtype W (fun x w hw => hWQ x x.2 w hw)
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hfix : ∀ w ∈ W, (q : V ≃ₗ[K] V) w = w :=
      (CFSG.LargeExtraspecial.S4.restrictHom_eq_one_iff _ _ _ q).1 hq
    have hq2 : ∀ v, (q : V ≃ₗ[K] V) ((q : V ≃ₗ[K] V) v) = v := by
      intro v
      have hmem : (q : V ≃ₗ[K] V) v - v ∈ W := by
        rw [hWk, LinearMap.mem_ker, map_sub, ← hxN q q.2 v, hfix _ ⟨v, rfl⟩, sub_self]
      have h1 := hfix _ hmem
      rw [map_sub] at h1
      refine sub_eq_zero.1 ?_
      calc (q : V ≃ₗ[K] V) ((q : V ≃ₗ[K] V) v) - v
          = ((q : V ≃ₗ[K] V) ((q : V ≃ₗ[K] V) v) - (q : V ≃ₗ[K] V) v) +
            ((q : V ≃ₗ[K] V) v - v) := by abel
        _ = ((q : V ≃ₗ[K] V) v - v) + ((q : V ≃ₗ[K] V) v - v) := by rw [h1]
        _ = 0 := h2 _
    have hsq : (q : V ≃ₗ[K] V) ^ 2 = 1 :=
      LinearEquiv.ext fun v => by simpa [pow_two] using hq2 v
    have h9 := hQ.pow_nine hZ q.2
    apply Subtype.ext
    calc (q : V ≃ₗ[K] V) = (q : V ≃ₗ[K] V) ^ 9 * ((q : V ≃ₗ[K] V) ^ 2)⁻¹ ^ 4 := by group
      _ = 1 := by rw [h9, hsq]; group
  set R : Subgroup (W ≃ₗ[K] W) := ρ.range with hRdef
  have hRcard : 3 ^ 4 ≤ Nat.card R := by
    rw [hRdef, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact hcard
  have hsc : ∀ z : Q, (z : V ≃ₗ[K] V) ∈ scalars K V → ρ z ∈ scalars K W := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars_iff.1 hz
    exact mem_scalars_iff.2 ⟨c, fun w => Subtype.ext (hc w)⟩
  have hRgood : IsGoodIn (scalars K W) R := by
    constructor
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_commutatorElement]
      exact hsc _ (hQ.1 x x.2 y y.2)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      exact hsc _ (hQ.2 x x.2)
  haveI : Finite (W ≃ₗ[K] W) := finite_linearEquiv
  have hR : (∀ x ∈ R, ∀ y ∈ R, x * y = y * x) ∧ ∀ x ∈ R, x ^ 3 = 1 := by
    by_cases hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
    · refine ⟨hab, fun x hx => ?_⟩
      by_contra hx3
      have h1 := BBig.card_le_of_abelian_cube hK hRgood hab hx hx3
      rw [hW3] at h1
      norm_num at h1
      omega
    · exfalso
      obtain ⟨g, hg, h, hh, hg3, hgh⟩ :=
        exists_pow_three_eq_one_noncomm (scalarLike_scalars (V := W) hK) hRgood hab
      obtain ⟨n, hn3, hcardn⟩ := card_le_of_nonab hK hRgood hg hh hg3 hgh
      rw [hW3] at hn3
      have h1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hRcard.trans hcardn)
      omega
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := hR.1 (ρ ⟨x, hx⟩) ⟨_, rfl⟩ (ρ ⟨y, hy⟩) ⟨_, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hρinj h1)
  · have h1 := hR.2 (ρ ⟨x, hx⟩) ⟨_, rfl⟩
    rw [← map_pow] at h1
    simpa using congrArg Subtype.val ((injective_iff_map_eq_one ρ).1 hρinj _ h1)

end CFSG.LocalAnalysis.GLTheoremA.S265.BTwE6

end
