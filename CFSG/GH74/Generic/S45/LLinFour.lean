module

public import CFSG.GH74.Generic.S45.LLinSel
public import CFSG.GH74.Generic.S45.LPsl2Field

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)
open scoped Matrix

theorem psl_four_symm_or_false {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {r f : ℕ} (hr2 : r ≠ 2)
    (hmodel : StatedClassicalModel S .PSL 4 r f) {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : ringChar F ≠ 2) (ψ : S ≃* projectiveSL 4 F)
      (B : GL (Fin 4) F), (B : Matrix (Fin 4) (Fin 4) F)ᵀ = B ∧
        ∀ s, ψ (ya s) = (conjAut 4 F B * dualAut 4 F) (ψ s) := by
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
  have hLW : L' ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S :=
    hL'.1.trans inf_le_left
  have hL : CFSG.Assembly.IsComponentOf L' (Subgroup.centralizer ({ya} : Set (MulAut S))) :=
    isComponentOf_of_normal_inf' (inner_normal S) hL'
  obtain ⟨p, f', hp, hp2, -, hmod8, hsrc, hZL⟩ := hQ.psl_source L' eLb
  have hodd : Odd (Nat.card (center L')) := by rw [hZL]; simp
  obtain ⟨⟨hr, hf, -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hr.ne_zero)
  have hk2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hr hr2 hF
  have htwo : (2 : F) ≠ 0 := Ring.two_ne_zero hk2
  let ψ : S ≃* projectiveSL 4 F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 F))
  let φ : ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner S) ≃* projectiveSL 4 F :=
    e.symm.trans ψ
  have hm3 : 3 ≤ 4 := by norm_num
  have hZP := center_projectiveSL_eq_bot (k := F) hm3
  obtain ⟨ρ, hinj, hρW, -, hρφ⟩ :=
    socle_extension (W := CFSG.ComponentClassification.OuterAutomorphisms.inner S) hCW φ hZP
  obtain ⟨-, hCA, hCW', hL₁⟩ := socle_images φ hinj hρW hLW hL
  have hψ : ∀ s, ψ (ya s) = ρ ya (ψ s) := by
    intro s
    have h1 := hρφ ya (e s)
    have h2 : MulAut.conjNormal ya (e s) = e (ya s) := Subtype.ext (hconj ya s)
    rw [h2] at h1
    have h3 : ∀ t, φ (e t) = ψ t := fun t => by
      simp [φ]
    rw [h3, h3] at h1
    exact h1.symm
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ ya)
  have hsrc' : StatedClassicalModel (L' ⧸ center L') .PSL 2 p f' ∨
      Nonempty (L' ⧸ center L' ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L' ⧸ center L') .PSL 3 2 2 := Or.inl hsrc
  have hrank : StatedClassicalModel (L' ⧸ center L') .PSL 2 p f' →
      2 ≤ CFSG.pRank 2 L' ∨ Odd (Nat.card (center L')) := fun _ => Or.inr hodd
  refine ⟨F, inferInstance, inferInstance, hk2, ψ, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      exfalso
      obtain ⟨μ, hμ, hsq, -⟩ := inner_case_reduction ha (le_refl 4) hr hr2 hf hF hinj hL₁ hρa hp2
        hsrc' hrank
      obtain ⟨-, E, _, _, hEc, ⟨eL⟩⟩ := selectorRowS_of_inner htwo hinj hCA hCW' hL₁ hρa hμ hsq
      have hE : Nat.card E = r ^ (2 * f) := by rw [hEc, hF, ← pow_mul, mul_comm]
      have h4 : 4 ≤ r ^ (2 * f) := by
        have h3 : 3 ≤ r := by have := hr.two_le; omega
        calc 4 ≤ r ^ 2 := by nlinarith
          _ ≤ r ^ (2 * f) := Nat.pow_le_pow_right hr.pos (by omega)
      have hX := statedClassicalModel_of_mulEquiv_projectiveSL_two hr (by omega) hE h4 eL
      obtain ⟨hpl, hfe, -⟩ := source_parameters hr2 hX hp2 hsrc'
      have hsq8 : (r ^ f * r ^ f) % 8 = 1 :=
        odd_sq_mod_eight ((hr.odd_of_ne_two hr2).pow)
      rw [hpl, hfe, two_mul, pow_add] at hmod8
      generalize r ^ f * r ^ f = N at hsq8 hmod8
      omega
    · exfalso
      exact field_case_false ha hm3 hr hr2 hf hF hinj hL₁ hτ hρa hp2 hsrc'
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut 4 F B * dualAut 4 F) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact ⟨B, hB, fun s => by rw [hψ, hρa]⟩
      · exfalso
        exact symplectic_case_false (le_refl 4) hr hr2 hf hF hinj hL₁ hρa hB hp2 hsrc'
    · exfalso
      exact graph_field_case_false ha (le_refl 4) hr hr2 hf hF hinj hL₁ hτ hρa hp2 hsrc'

end CFSG.GH74.Generic.S45
