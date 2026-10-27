module

public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.LocalAnalysis.ComponentInitial

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

private theorem coe_reflect_comp_subtype {U : Submodule F V} (x u : U) :
    ((reflect (Q.comp U.subtype) x u : U) : V) = reflect Q (x : V) (u : V) := by
  by_cases hx : Q (x : V) = 0
  · have hx' : (Q.comp U.subtype) x = 0 := hx
    rw [reflect_of_map_eq_zero hx, reflect_of_map_eq_zero hx']
    rfl
  · have hx' : (Q.comp U.subtype) x ≠ 0 := hx
    rw [reflect_apply hx, reflect_apply hx']
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rfl

private theorem extendHom_reflect {U : Submodule F V} (hR : IsCompl U (orthPerp Q U)) (x : U) :
    extendHom hR ⟨reflect (Q.comp U.subtype) x, reflect_mem_orthogonalGroup _ x⟩ =
      reflect Q (x : V) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨u, w, rfl⟩ := exists_add_of_isCompl hR v
  rw [extendHom_apply, map_add, reflect_apply_of_polar_eq_zero (mem_orthPerp.1 w.2 x x.2)]
  exact congrArg (· + (w : V)) (coe_reflect_comp_subtype x u)

theorem exists_orderOf_reflect_mul_reflect_eq [Finite F] [CharP F 2] [FiniteDimensional F V]
    {U : Submodule F V}
    (hU : finrank F U = 2) (han : ∀ x ∈ U, Q x = 0 → x = 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    ∃ x ∈ U, ∃ y ∈ U, Q x ≠ 0 ∧ Q y ≠ 0 ∧ orderOf (reflect Q x * reflect Q y) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hani : ∀ x : U, x ≠ 0 → (Q.comp U.subtype) x ≠ 0 := fun x hx h =>
    hx (Subtype.ext (han x x.2 h))
  have hani' : ∀ x : U, (Q.comp U.subtype) x = 0 → x = 0 := fun x h => Subtype.ext (han x x.2 h)
  have hreg : (polarBilin (Q.comp U.subtype)).Nondegenerate :=
    finite_anisotropic_plane_regular (by rw [hU]) hani
  have hR : IsCompl U (orthPerp Q U) := isCompl_orthPerp hreg
  have hcard := CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_of_anisotropic hU hani
  haveI : Finite (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p (by rw [hcard]; exact Dvd.dvd.mul_left hpq 2)
  obtain ⟨l, hl2, hl0, hgl⟩ := orthogonal_char_two_anisotropic_plane_generation hU hreg hani' g.2
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · have h1 : g = 1 := Subtype.ext (by simpa using hgl)
    rw [h1, orderOf_one] at hg
    exact absurd hg hp.one_lt.ne
  · have h1 : (g : U ≃ₗ[F] U) = reflect (Q.comp U.subtype) x := by simpa using hgl
    have h2 : g * g = 1 := Subtype.ext (by rw [Subgroup.coe_mul, h1, reflect_mul_self]; rfl)
    have h3 : p ∣ 2 := hg ▸ orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2
  · have h1 : (g : U ≃ₗ[F] U) = reflect (Q.comp U.subtype) x * reflect (Q.comp U.subtype) y := by
      simpa using hgl
    have hxne : x ≠ 0 := hl0 x (by simp)
    have hyne : y ≠ 0 := hl0 y (by simp)
    refine ⟨x, x.2, y, y.2, fun h => hxne (Subtype.ext (han _ x.2 h)),
      fun h => hyne (Subtype.ext (han _ y.2 h)), ?_⟩
    have h2 : g = ⟨reflect (Q.comp U.subtype) x, reflect_mem_orthogonalGroup _ x⟩ *
        ⟨reflect (Q.comp U.subtype) y, reflect_mem_orthogonalGroup _ y⟩ := Subtype.ext h1
    have h3 : extendHom hR g = reflect Q (x : V) * reflect Q (y : V) := by
      rw [h2, map_mul, extendHom_reflect, extendHom_reflect]
    rw [← h3, orderOf_injective (extendHom hR) (extendHom_injective hR) g, hg]
  · simp at hl2

end CFSG.LocalAnalysis.GLTheoremA.S172C.Rank

end
