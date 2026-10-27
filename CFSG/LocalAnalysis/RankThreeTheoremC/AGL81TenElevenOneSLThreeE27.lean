module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeIrred
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement

variable {K : Type} [Field K] {p f : ℕ}

theorem apply_tau_eq {f₀ : ℕ} (hq₀ : ModThree true (p ^ f₀)) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard true (p ^ f₀)) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2) {τ : K}
    (hτ : τ ^ 3 = 1) : ψ τ = τ := by
  obtain ⟨r, hr, hψr⟩ := exists_pow_mod_three hq₀ hφ hψ
  rw [hψr, ← Nat.div_add_mod r 3, hr, pow_add, pow_mul, hτ, one_pow, one_mul, pow_one]

theorem exists_apply_ne {φ : K ≃+* K} (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) : ∃ c, ψ c ≠ c := by
  by_contra h
  push Not at h
  have h1 : ψ = 1 := RingEquiv.ext h
  rcases hψ with rfl | rfl
  · rw [h1, orderOf_one] at hφ3
    norm_num at hφ3
  · have := orderOf_dvd_of_pow_eq_one h1
    rw [hφ3] at this
    norm_num at this

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]

theorem exists_commute_slThree
    [Group.IsPerfect L] (hK : PiField true p f K) (hq : ModThree true (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) (hq₀ : ModThree true (p ^ f₀))
    (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* slPi true 3 (p ^ f) K) {a : G} (ha3 : a ^ 3 = 1) {σ : K ≃+* K}
    (hσ : (∀ c, σ c = c ^ piCard true (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard true (p ^ f₀) ^ 2))
    {g : GL (Fin 3) K}
    (haσ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨a, mem_normalizer_of_normal a⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        g * frobGL σ s * g⁻¹) :
    ∃ z : G, orderOf z = 3 ∧ L ⊓ centralizer (L : Set G) = zpowers z ∧
      ∀ x : G, x ^ 3 = 1 → x ∉ zpowers z →
        ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers z := by
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hψ := eq_or_eq_sq_of_pow hφ hσ
  obtain ⟨e₁, ha₁, -⟩ := exists_normalized_field_of_pow hK hq hf hφ hφ3 hψ e
    (slAct_pow_three e ha3) (mem_glPi_true _ g) haσ
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨t, ht⟩ := exists_scalar_tau hK hq hτ
  obtain ⟨hzo, hLC⟩ := inf_centralizer_eq_zpowers hK hq e₁ hτ hτ1 ht
  have hψτ := apply_tau_eq hq₀ hφ hψ hτ
  obtain ⟨c, hc⟩ := exists_apply_ne hφ3 hψ
  have haLC := not_mem_sup_of_frob e₁ hc ha₁
  have haL : a ∉ L := fun h => haLC (mem_sup_left h)
  have hq2 : 2 < p ^ f := by
    have := hK.one_le
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ f := Nat.pow_le_pow_left hK.prime.two_le f
  refine ⟨(e₁.symm t : G), hzo, hLC, fun x hx3 hxz => ?_⟩
  by_cases hxL : x ∈ L
  · exact exists_w_of_mem hK hq e₁ hτ hτ1 ht ha3 haL hψτ ha₁ hxL hx3 hxz
  have hx3' : (⟨x, mem_normalizer_of_normal x⟩ : normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hx3, Subgroup.coe_one])
  rcases slAct_pgl_or_field hK hq2 hθ e₁ ⟨x, mem_normalizer_of_normal x⟩ hx3' with
    ⟨y, -, hy⟩ | ⟨-, f₀', hf₀', σ', hσ', g', -, hg'⟩
  · have hyP : IsPGLAt e₁ x y := ⟨mem_glPi_true _ _, hy⟩
    have h3 : IsPGLAt e₁ (x * x * x) (y * y * y) := isPGLAt_mul e₁ (isPGLAt_mul e₁ hyP hyP) hyP
    have hxxx : x * x * x = 1 := by rw [← hx3, pow_succ, pow_two]
    rw [hxxx] at h3
    obtain ⟨c', hc'⟩ := isPGLAt_inv_mul_mem hK hq
      (isPGLAt_of_mem_centralizer e₁ (one_mem (centralizer (L : Set G)))) h3
    rw [inv_one, one_mul] at hc'
    by_cases hcube : ∃ μ : K, μ ^ 3 = c'
    · obtain ⟨μ, hμ⟩ := hcube
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        exact c'.ne_zero (by rw [← hμ]; ring)
      have hy3 : y ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
        rw [pow_succ, pow_two, ← hc']
        congr 1
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ])
      obtain ⟨u, huL, hus, hu3, huy⟩ := exists_commute_diagTau_conj hK hq hτ hτ1 hy3
      exact exists_w_of_not_mem_of_commute hK hq e₁ hτ hτ1 ht hx3 hxL hyP huL hus hu3 huy
    · push Not at hcube
      have hyℓ : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = (c' : K) • 1 := by
        rw [← Units.val_pow_eq_pow_val, pow_succ, pow_two, ← hc', coe_scalar_eq_smul]
      exact exists_w_of_irred hK hq hf hq₀ hφ hφ3 hψ e₁ hτ hτ1 ht ha3 haLC ha₁ hx3 hyP hcube hyℓ
  · have hf₀ : f₀' = f₀ := by omega
    subst hf₀
    have hψ' := eq_or_eq_sq_of_pow hφ hσ'
    obtain ⟨e₂, hx₂, -⟩ := exists_normalized_field_of_pow hK hq hf hφ hφ3 hψ' e₁
      (slAct_pow_three e₁ hx3) (mem_glPi_true _ g') hg'
    obtain ⟨c'', hc''⟩ := exists_apply_ne hφ3 hψ'
    exact exists_w_of_frob hK hq e₂ hτ hτ1 hLC hx3 (apply_tau_eq hq₀ hφ hψ' hτ) hc'' hx₂

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
