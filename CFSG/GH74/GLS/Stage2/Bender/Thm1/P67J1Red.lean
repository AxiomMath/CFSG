module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67AltRed
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint

theorem not_sq_dvd_card_J1 (r : ℕ) (hr : r.Prime) (hr2 : Odd r) : ¬ r ^ 2 ∣ 175560 := by
  intro h
  have hdv : r ∣ 175560 := (dvd_pow_self r two_ne_zero).trans h
  have h175 : (175560 : ℕ) = 2 * 2 * 2 * 3 * 5 * 7 * 11 * 19 := by norm_num
  rw [h175] at hdv
  simp only [Nat.Prime.dvd_mul hr, or_assoc] at hdv
  have hp : ∀ p : ℕ, p.Prime → r ∣ p → r = p := fun p hp hd => (Nat.prime_dvd_prime_iff_eq hr hp).1 hd
  rcases hdv with h2 | h2 | h2 | h3 | h5 | h7 | h11 | h19
  · obtain rfl := hp 2 (by norm_num) h2
    exact absurd hr2 (by decide)
  · obtain rfl := hp 2 (by norm_num) h2
    exact absurd hr2 (by decide)
  · obtain rfl := hp 2 (by norm_num) h2
    exact absurd hr2 (by decide)
  · obtain rfl := hp 3 (by norm_num) h3
    omega
  · obtain rfl := hp 5 (by norm_num) h5
    omega
  · obtain rfl := hp 7 (by norm_num) h7
    omega
  · obtain rfl := hp 11 (by norm_num) h11
    omega
  · obtain rfl := hp 19 (by norm_num) h19
    omega

theorem centralizes_of_quotAut_eq_one {N : Type} [Group N] {J : Subgroup N} (hJ : Group.IsPerfect ↥J)
    (g : ↥(normalizer (J : Set N))) (h : quotAut (J.normalizerMonoidHom g) = 1) :
    ∀ x ∈ J, (g : N) * x * (g : N)⁻¹ = x := by
  have h3 : J.normalizerMonoidHom g = 1 := by
    apply eq_one_of_forall_mem_center hJ
    intro x
    have := congrArg (fun φ : MulAut (↥J ⧸ center ↥J) => φ (x : ↥J ⧸ center ↥J)) h
    simp only [quotAut_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.1 this.symm
  intro x hx
  have := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : N)) h3
  simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using this

theorem cf67_j1
    {N : Type} [Group N] (J : Subgroup N) (hJ : IsComponent J)
    (θ : ↥J ⧸ center ↥J ≃* NativeSporadic.J1) {r : ℕ} (hr : r.Prime) (hr2 : Odd r)
    (V : Subgroup N) (hVc : Nat.card ↥V = r ^ 2) (hVn : V ≤ normalizer (J : Set N))
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N)) : False := by
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  let Ψ : ↥(normalizer (J : Set N)) →* MulAut NativeSporadic.J1 :=
    (MulAut.congr θ).toMonoidHom.comp ((quotAut (J := ↥J)).comp J.normalizerMonoidHom)
  let ΨV : ↥V →* MulAut NativeSporadic.J1 := Ψ.comp (Subgroup.inclusion hVn)
  have hinj : Function.Injective ΨV := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra hne
    have h1 : (a : N) ≠ 1 := fun h => hne (Subtype.ext h)
    refine hfaith _ a.2 h1 fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : quotAut (J.normalizerMonoidHom (Subgroup.inclusion hVn a)) = 1 := by
      apply (MulAut.congr θ).injective
      exact ha.trans (map_one _).symm
    exact (mul_inv_eq_iff_eq_mul.1 (centralizes_of_quotAut_eq_one hperf _ h2 x hx)).symm
  have hsurj : Function.Surjective (MulAut.conj : NativeSporadic.J1 →* MulAut NativeSporadic.J1) :=
    fun φ => (Sporadic.Schreier.at_j1_schreier.2.1 φ).imp fun g hg => hg.symm
  have h1 : Nat.card ↥V ∣ Nat.card (MulAut NativeSporadic.J1) :=
    Subgroup.card_dvd_of_injective ΨV hinj
  have h2 : Nat.card (MulAut NativeSporadic.J1) ∣ Nat.card NativeSporadic.J1 :=
    Subgroup.card_dvd_of_surjective hsurj
  rw [Sporadic.J1.card_J1] at h2
  rw [hVc] at h1
  exact not_sq_dvd_card_J1 r hr hr2 (h1.trans h2)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
