module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup
open scoped Pointwise

@[expose] def conjHom {K : Type*} [Group K] (A H : Subgroup K)
    (hAH : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) : ↥A →* MulAut ↥H where
  toFun a :=
    { toFun := fun h => ⟨(a : K) * h * (a : K)⁻¹, hAH a a.2 h h.2⟩
      invFun := fun h => ⟨(a : K)⁻¹ * h * (a : K), by
        have := hAH (a : K)⁻¹ (A.inv_mem a.2) h h.2
        simpa using this⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext h
    simp
  map_mul' a b := by
    ext h
    simp [mul_assoc]

theorem exists_normalizing_sylow {K : Type*} [Group K] [Finite K] {p q : ℕ} [Fact p.Prime]
    (A H : Subgroup K) (hA : IsPGroup q A) (hq : q.Prime)
    (hAH : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H) (hH : ¬ q ∣ Nat.card H) :
    ∃ P : Sylow p ↥H, A ≤ Subgroup.normalizer (((P : Subgroup ↥H).map H.subtype : Subgroup K) :
      Set K) := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI : MulDistribMulAction ↥A ↥H := MulDistribMulAction.compHom ↥H (conjHom A H hAH)
  have hcard : ¬ q ∣ Nat.card (Sylow p ↥H) := by
    intro h
    obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
    exact hH (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p ↥H) hcard
  have key : ∀ b ∈ A, ∀ x : K, x ∈ ((P : Subgroup ↥H).map H.subtype : Subgroup K) →
      b * x * b⁻¹ ∈ ((P : Subgroup ↥H).map H.subtype : Subgroup K) := by
    intro b hb
    have hfix := hP ⟨b, hb⟩
    have hfix' : (⟨b, hb⟩ : ↥A) • (P : Subgroup ↥H) = (P : Subgroup ↥H) := by
      have := congrArg (fun Q : Sylow p ↥H => (Q : Subgroup ↥H)) hfix
      exact this
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (⟨b, hb⟩ : ↥A) • y ∈ (⟨b, hb⟩ : ↥A) • (P : Subgroup ↥H) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hy
    rw [hfix'] at hy'
    exact ⟨_, hy', rfl⟩
  refine ⟨P, fun a ha => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hx
  simpa [mul_assoc] using this

theorem exists_lift_normalizing {J : Type*} [Group J] [Finite J] {M : Type*} [Group M]
    (π : J →* M) (hk3 : ¬ 3 ∣ Nat.card π.ker) {E₀ U₀ : Subgroup M}
    (hE : IsPGroup 3 E₀) (hU : IsPGroup 2 U₀) (hEπ : E₀ ≤ π.range) (hUπ : U₀ ≤ π.range)
    (hEU : E₀ ≤ Subgroup.normalizer (U₀ : Set M)) :
    ∃ W P : Subgroup J, IsPGroup 3 W ∧ W.map π = E₀ ∧ Function.Injective (π.comp W.subtype) ∧
      IsPGroup 2 P ∧ P.map π = U₀ ∧ W ≤ Subgroup.normalizer (P : Set J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥π.range :=
    Finite.of_surjective (MonoidHom.rangeRestrict π) (MonoidHom.rangeRestrict_surjective π)
  haveI : Finite ↥U₀ := Finite.of_injective (Subgroup.inclusion hUπ) (Subgroup.inclusion_injective hUπ)
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_three π hk3 hE hEπ
  let H : Subgroup J := U₀.comap π
  have hAH : ∀ a ∈ W, ∀ h ∈ H, a * h * a⁻¹ ∈ H := by
    intro a ha h hh
    have hπa : π a ∈ Subgroup.normalizer (U₀ : Set M) := hEU (hWmap ▸ Subgroup.mem_map_of_mem π ha)
    rw [Subgroup.mem_normalizer_iff] at hπa
    have hh' : π h ∈ U₀ := hh
    show π (a * h * a⁻¹) ∈ U₀
    rw [map_mul, map_mul, map_inv]
    exact (hπa (π h)).1 hh'
  have hH3 : ¬ 3 ∣ Nat.card H := by
    let ψ : ↥H →* M := π.comp H.subtype
    have hrange : ψ.range = U₀ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact (Subgroup.map_comap_eq π U₀).trans (inf_eq_right.2 hUπ)
    have h1 : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [h1, Nat.Prime.dvd_mul Nat.prime_three]
    rintro (h | h)
    · rw [hrange] at h
      obtain ⟨n, hn⟩ := hU.exists_card_eq
      rw [hn] at h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      omega
    · exact hk3 (h.trans (card_ker_comp_subtype_dvd π H))
  obtain ⟨S, hS⟩ := exists_normalizing_sylow (p := 2) W H hWp Nat.prime_three hAH hH3
  let P : Subgroup J := (S : Subgroup ↥H).map H.subtype
  refine ⟨W, P, hWp, hWmap, hWinj, S.2.map H.subtype, ?_, hS⟩
  let ψU : ↥H →* ↥U₀ := π.subgroupComap U₀
  have hψU : Function.Surjective ψU := by
    intro u
    obtain ⟨j, hj⟩ := hUπ u.2
    exact ⟨⟨j, by simp [H, Subgroup.mem_comap, hj]⟩, Subtype.ext hj⟩
  have htop : IsPGroup 2 (⊤ : Subgroup ↥U₀) := hU.of_equiv Subgroup.topEquiv.symm
  have hSU : (S.mapSurjective hψU : Subgroup ↥U₀) = ⊤ :=
    ((S.mapSurjective hψU).3 htop le_top).symm
  have hmap : P.map π = ((S : Subgroup ↥H).map ψU).map U₀.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hmap]
  have : (S : Subgroup ↥H).map ψU = ⊤ := hSU
  rw [this, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.LocalAnalysis.GLTheoremA.CatB
