module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Conj

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.Generic.S45 CFSG.GH74.GLS.IVK
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem centralizer_inner_eq_bot_of_center_eq_bot {K : Type} [Group K] (hZ : center K = ⊥) :
    Subgroup.centralizer ((inner K : Subgroup (MulAut K)) : Set (MulAut K)) = ⊥ := by
  have hι := conj_injective_of_center_eq_bot hZ
  have hconj : ∀ (α : MulAut K) (s : K), α * MulAut.conj s * α⁻¹ = MulAut.conj (α s) := fun α s => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
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

theorem linear_selector_five_false_alt7 {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    (hsrc : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)))
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
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hsrc' : StatedClassicalModel (L ⧸ center L) .PSL 2 3 1 ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := Or.inr (Or.inl hsrc)
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

theorem ivk714_psl_ge_five {m p f : ℕ} (hm : 5 ≤ m) (hp2 : p ≠ 2) :
    Ivk714Empty (fun X _ => LieModel X .PSL m p f) := by
  intro K _ _ hs hK z hz h
  have hmodel := LQ.stated_of_lieModel_PSL hK
  have hZ : center K = ⊥ := center_eq_bot_of_simple_of_nonab hs h.nonabelian
  obtain ⟨L, hLW, hL, hq, hodd⟩ := h.exists_inner_component hZ
  have hCW := centralizer_inner_eq_bot_of_center_eq_bot hZ
  let e : K ≃* ↥(inner K) := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)
  obtain ⟨⟨hr, hf', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hmodel
  let φ : ↥(inner K) ≃* projectiveSL m F :=
    e.symm.trans (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj m F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL m F)))
  exact linear_selector_five_false_alt7 (W := inner K) hCW hz hLW hL hq hodd hm hr hp2 hf' hF φ

theorem ivk714_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk714Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f _ hf hmod
  refine ivk714_psl_ge_five (by norm_num) ?_
  rintro rfl
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

end CFSG.GH74.GLS.IVK.Proofs2
