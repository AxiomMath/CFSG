module

public import CFSG.GH74.Generic.S45.LQSmall
public import CFSG.GH74.Generic.S45.LOddPSU
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

theorem QData.psl_source {S X : Type} [Group S] [Group X] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) (L' : Subgroup X) (eLb : Lb ≃* L') :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧
      StatedClassicalModel (L' ⧸ Subgroup.center L') .PSL 2 p f ∧
      Subgroup.center L' = ⊥ := by
  obtain ⟨p, f, hp, hf, hP, hmodel⟩ := hQ.model (fun x => x % 8 = 3 ∨ x % 8 = 5) hQ.mod8
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have : IsSimpleGroup ↥Lb := hQ.simple
  have hs' : IsSimpleGroup ↥L' := eLb.symm.isSimpleGroup
  have hnab' : ∃ a b : ↥L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hQ.nonab
    refine ⟨eLb a, eLb b, fun h => hab (eLb.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hZ : Subgroup.center ↥L' = ⊥ := center_eq_bot_of_simple_nonab hs' hnab'
  let e : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥Lb :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eLb.symm
  exact ⟨p, f, hp, hp2, hf, hP,
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm (LQ.stated_of_lieModel_PSL hmodel), hZ⟩

theorem linear_selector_five_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (hp2 : p ≠ 2) (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f)
    (hrank : Odd (Nat.card (center L)))
    {m ℓ e : ℕ} (hm : 5 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL m k) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hZ := center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  obtain ⟨-, -, -, hL₁⟩ := socle_images φ hinj hρW hLW hL
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  have hsrc' : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := Or.inl hsrc
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨-, -, -, hm4'⟩ :=
        inner_case_reduction ha hm4 hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc' (fun _ => Or.inr hrank)
      omega
    · exact field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc'
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut m k B * dualAut m k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact orthogonal_case_false hm hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc'
      · exact symplectic_case_false hm4 hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc'
    · exact graph_field_case_false ha hm4 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc'

theorem psl_ge_five_false {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f m : ℕ} (hr2 : r ≠ 2) (hm : 5 ≤ m)
    (hmodel : StatedClassicalModel S .PSL m r f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : False := by
  classical
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple_nonab hS hnab
  obtain ⟨L', hL', ⟨eLb⟩⟩ := exists_component_conj hZ ya hQ.le hQ.sub hQ.simple hQ.nonab
  have hι : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro g g' h
    have hc : g'⁻¹ * g ∈ Subgroup.center S := Subgroup.mem_center_iff.2 fun x => by
      have hx := congrArg (fun φ : MulAut S => φ x) h
      simp only [MulAut.conj_apply] at hx
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [hx]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  let e : S ≃* ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S) :=
    MonoidHom.ofInjective hι
  have hconj : ∀ (α : MulAut S) (s : S), α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := fun α s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hCW : Subgroup.centralizer
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner S : Subgroup (MulAut S)) :
        Set (MulAut S)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    ext s
    have h1 : MulAut.conj s * α = α * MulAut.conj s :=
      Subgroup.mem_centralizer_iff.1 hα (MulAut.conj s) ⟨s, rfl⟩
    have h2 : MulAut.conj (α s) = MulAut.conj s := by
      rw [← hconj α s, ← h1]
      group
    simpa using hι h2
  have ha : orderOf ya = 2 := orderOf_eq_prime (by rw [pow_two]; exact hQ.sq) hQ.ne
  have hLW : L' ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S := hL'.1.trans inf_le_left
  have hL : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({ya} : Set (MulAut S))) :=
    isComponentOf_of_normal_inf' (inner_normal S) hL'
  obtain ⟨p, f', -, hp2, -, -, hsrc, hZL⟩ := hQ.psl_source L' eLb
  obtain ⟨⟨hr, hf, -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have hodd : Odd (Nat.card (center L')) := by rw [hZL]; simp
  let φ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S) ≃* projectiveSL m F :=
    e.symm.trans (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj m F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL m F)))
  exact linear_selector_five_false (W := CFSG.ComponentClassification.OuterAutomorphisms.inner S)
    hCW ha hLW hL hp2 hsrc hodd hm hr hr2 hf hF φ

end CFSG.GH74.Generic.S45
