module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolSix
public import CFSG.ClassicalGroups.Alternating.RT1SpFaithful

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

section Simple

variable {K : Type} [Field K] [CharP K 2] [Finite K] {N : Type*} [AddCommGroup N] [Module K N]
  {BN : BilinForm K N}

theorem isSimpleGroup_Gsp_of_six_le (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h6 : 6 ≤ finrank K N) : IsSimpleGroup (Gsp BN) := by
  have : FiniteDimensional K N := Module.finite_of_finrank_pos (by omega)
  by_cases hq : 4 ≤ Nat.card K
  · exact isSimpleGroup_Gsp hq hBN hBNnd (by omega)
  · have hK2 : Nat.card K = 2 := by
      have := Fintype.ofFinite K
      obtain ⟨n, -, hn⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card] at hq ⊢
      rw [hn] at hq ⊢
      have hn2 : (n : ℕ) < 2 := by
        by_contra h
        push Not at h
        exact hq (calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h)
      rw [show (n : ℕ) = 1 by have := n.pos; omega, pow_one]
    have hQ := CFSG.RankThree.PartOne.KCSpIsotypic.isQuasisimple_sesqUnitaryGroup_of_alt hBN hBNnd
      (by omega) (Or.inr (Or.inr ⟨hK2, h6⟩))
    rw [← CFSG.RankThree.PartOne.KCSpIsotypic.bilinIsometryGroup_eq_sesqUnitaryGroup] at hQ
    have : IsSimpleGroup (Gsp BN ⧸ Subgroup.center (Gsp BN)) := hQ.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq (center_Gsp_eq_bot hBN hBNnd)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup

end Simple

section Transvection

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem exists_form_ne_zero_of_mem_orthogonal (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {X : Submodule K N} (hX : X ⊔ BN.orthogonal X = ⊤) {y : N} (hy : y ∈ BN.orthogonal X)
    (hy0 : y ≠ 0) : ∃ e ∈ BN.orthogonal X, BN y e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hy0 (hBNnd.1 y fun z => ?_)
  obtain ⟨x, hx, e, he, rfl⟩ := Submodule.mem_sup.mp (hX ▸ Submodule.mem_top (x := z))
  rw [map_add, hcon e he, add_zero, ← hBN.neg_eq x y, mem_orthogonal_iff_form.mp hy x hx, neg_zero]

theorem exists_form_ne_zero_pair (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {X : Submodule K N} (hX : X ⊔ BN.orthogonal X = ⊤) {b b' : N} (hb : b ∈ BN.orthogonal X)
    (hb' : b' ∈ BN.orthogonal X) (hb0 : b ≠ 0) (hb'0 : b' ≠ 0) :
    ∃ e ∈ BN.orthogonal X, BN b e ≠ 0 ∧ BN b' e ≠ 0 := by
  obtain ⟨e₁, he₁, h₁⟩ := exists_form_ne_zero_of_mem_orthogonal hBN hBNnd hX hb hb0
  obtain ⟨e₂, he₂, h₂⟩ := exists_form_ne_zero_of_mem_orthogonal hBN hBNnd hX hb' hb'0
  by_cases h₃ : BN b' e₁ = 0
  · by_cases h₄ : BN b e₂ = 0
    · refine ⟨e₁ + e₂, Submodule.add_mem _ he₁ he₂, ?_, ?_⟩
      · rw [map_add, h₄, add_zero]
        exact h₁
      · rw [map_add, h₃, zero_add]
        exact h₂
    · exact ⟨e₂, he₂, h₄, h₂⟩
  · exact ⟨e₁, he₁, h₁, h₃⟩

theorem exists_orthogonal_not_mem_span (B : BilinForm K N) {Y : Submodule K N}
    (h4 : 4 ≤ finrank K Y) {b : N} (hb : b ∈ Y) (hb0 : b ≠ 0) :
    ∃ b' ∈ Y, B b b' = 0 ∧ ∀ s : K, b' ≠ s • b := by
  have : Module.Finite K Y := Module.finite_of_finrank_pos (by omega)
  let f : Y →ₗ[K] K := (B b).comp Y.subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hr : finrank K (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have hbY : (⟨b, hb⟩ : Y) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
  have hS : finrank K (Submodule.span K {(⟨b, hb⟩ : Y)}) = 1 := finrank_span_singleton hbY
  have hnle : ¬ LinearMap.ker f ≤ Submodule.span K {(⟨b, hb⟩ : Y)} := fun hle => by
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨w, hw, hwS⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨w, w.2, hw, fun s hs => hwS ?_⟩
  rw [Submodule.mem_span_singleton]
  exact ⟨s, Subtype.ext hs.symm⟩

theorem Tsp_ne_Tsp_of_forall_ne_smul (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {b b' : N} {c : K}
    (hc : c ≠ 0) (h : ∀ s : K, b' ≠ s • b) : Tsp hBN b' c ≠ Tsp hBN b c := by
  intro heq
  have hb'0 : b' ≠ 0 := by simpa using h 0
  obtain ⟨x, hx⟩ : ∃ x, BN x b' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hb'0 (hBNnd.2 b' hcon)
  have h1 := congrArg (fun g : Gsp BN => g.app x) heq
  simp only [Tsp_app, add_right_inj] at h1
  have hne : c * BN x b' ≠ 0 := mul_ne_zero hc hx
  refine h ((c * BN x b')⁻¹ * (c * BN x b)) ?_
  rw [mul_smul, ← h1, inv_smul_smul₀ hne]

theorem exists_conj_commute_of_transvection_of_four_le [CharP K 2] [Finite K]
    {X : Submodule K N} (h4 : 4 ≤ finrank K (BN.orthogonal X)) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (hX : X ⊔ BN.orthogonal X = ⊤) {u : Gsp BN} (hu : u * u = 1)
    (hfix : ∀ x ∈ X, u.app x = x) (hβ : ∀ z, u.ft z = 0 → u.phi z = 0) {z₀ : N}
    (hz₀ : u.phi z₀ ≠ 0) :
    ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧ k * u * k⁻¹ ≠ u ∧ Commute u (k * u * k⁻¹) := by
  obtain ⟨hζ, hutsp⟩ := eq_Tsp_of_ft_eq_zero_imp hBN hu hβ hz₀
  set b := u.phi z₀ with hb
  set c := (u.ft z₀)⁻¹ with hc
  have hbX : b ∈ BN.orthogonal X := by
    rw [mem_orthogonal_iff_form]
    intro x hx
    rw [hb, ← Gsp.form_phi_left hu, Gsp.phi_eq_zero_of_app_eq (hfix x hx), map_zero,
      LinearMap.zero_apply]
  have hc0 : c ≠ 0 := inv_ne_zero hζ
  obtain ⟨b', hb'X, hbb', hb'span⟩ := exists_orthogonal_not_mem_span BN h4 hbX hz₀
  have hb'0 : b' ≠ 0 := by simpa using hb'span 0
  obtain ⟨e, heX, hbe, hb'e⟩ := exists_form_ne_zero_pair hBN hBNnd hX hbX hb'X hz₀ hb'0
  obtain ⟨s₁, -, hs₁b, hs₁fix⟩ := exists_Tsp_swap hBN hbe (one_ne_zero (α := K))
  have heb' : BN e b' ≠ 0 := by rw [form_comm_charTwo hBN e b']; exact hb'e
  obtain ⟨s₂, -, hs₂e, hs₂fix⟩ := exists_Tsp_swap hBN heb' (one_ne_zero (α := K))
  rw [one_smul] at hs₁b hs₂e
  have hXb := mem_orthogonal_iff_form.mp hbX
  have hXe := mem_orthogonal_iff_form.mp heX
  have hXb' := mem_orthogonal_iff_form.mp hb'X
  have hkb : (s₂ * s₁).app b = b' := by rw [Gsp.app_mul, hs₁b, hs₂e]
  have hconj : s₂ * s₁ * u * (s₂ * s₁)⁻¹ = Tsp hBN b' c := by
    rw [hutsp, Tsp_conj, hkb]
  refine ⟨s₂ * s₁, fun x hx => ?_, ?_, ?_⟩
  · rw [Gsp.app_mul, hs₁fix x (hXb x hx) (hXe x hx), hs₂fix x (hXe x hx) (hXb' x hx)]
  · rw [hconj]
    nth_rewrite 1 [hutsp]
    exact Tsp_ne_Tsp_of_forall_ne_smul hBN hBNnd hc0 hb'span
  · rw [hconj]
    nth_rewrite 1 [hutsp]
    exact Tsp_comm hBN hbb' c c

end Transvection

section Six

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem Gsp.Block.ft_tau_mul_eq_zero [CharP K 2] (hBN : BN.IsAlt) {t τ h : Gsp BN}
    {X : Submodule K N} (hb : t.Block X τ h) (ht : t * t = 1) (hf : ∀ x, t.ft x = 0) (z : N) :
    (τ * t).ft z = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp
    (hb.isCompl.sup_eq_top ▸ Submodule.mem_top (x := z))
  rw [Gsp.ft_add hBN (hb.mul_self_tau_mul ht), Gsp.ft_eq_zero_of_app_eq hBN (hb.fixes x hx),
    zero_add]
  have hty : t.app y ∈ BN.orthogonal X := by
    rw [mem_orthogonal_iff_form]
    intro n hn
    have h1 := Gsp.form_app t n (t.app y)
    rw [Gsp.app_app_of_mul_self ht] at h1
    rw [← h1]
    exact mem_orthogonal_iff_form.mp hy _ (hb.maps n hn)
  rw [Gsp.ft, Gsp.app_mul, hb.tau_orth _ hty]
  exact hf y

theorem Gsp.exists_phi_ne_zero {u : Gsp BN} (hu1 : u ≠ 1) : ∃ z, u.phi z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hu1 (Gsp.ext' fun x => ?_)
  have := hcon x
  rw [Gsp.phi_apply, sub_eq_zero] at this
  rw [this, Gsp.app_one]

theorem exists_conj_orderOf_eq_six_of_six_le [CharP K 2] [Finite K] (h6 : 6 ≤ finrank K N)
    (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {t : Gsp BN} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hT : finrank K (LinearMap.range
      (((t : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1)) ≠ 1)
    (hA2 : ¬ ∃ a c, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ t = lineElt hBN a c) :
    ∃ g : Gsp BN, orderOf (t * (g * t * g⁻¹)) = 6 := by
  have : FiniteDimensional K N := Module.finite_of_finrank_pos (by omega)
  by_cases hf : ∀ x, t.ft x = 0
  · obtain ⟨X, τ, h, hb, hty⟩ := exists_block_of_ft_eq_zero hBN hBNnd ht ht1 hf
    obtain ⟨z, hz⟩ := Gsp.exists_phi_ne_zero (fun h1 => hA2 (hty h1) : τ * t ≠ 1)
    obtain ⟨k, hkfix, hkne, hkcomm⟩ := exists_conj_commute_of_exists_ft_eq_zero hBN hBNnd
      hb.isCompl.sup_eq_top (hb.mul_self_tau_mul ht) (fun x hx => hb.fixes x hx)
      ⟨z, hb.ft_tau_mul_eq_zero hBN ht hf z, hz⟩
    exact ⟨h * k, orderOf_mul_conj_eq_six_of_block hb ht hkfix hkne hkcomm⟩
  · push Not at hf
    obtain ⟨v, hv⟩ := hf
    obtain ⟨X, τ, h, hb, hdim, hty⟩ := exists_block_of_ft_ne_zero hBN ht hv
    obtain ⟨z, hz⟩ := Gsp.exists_phi_ne_zero (fun h1 => hT (hty h1) : τ * t ≠ 1)
    have huu := hb.mul_self_tau_mul ht
    have hufix : ∀ x ∈ X, (τ * t).app x = x := fun x hx => hb.fixes x hx
    obtain ⟨k, hkfix, hkne, hkcomm⟩ : ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧
        k * (τ * t) * k⁻¹ ≠ τ * t ∧ Commute (τ * t) (k * (τ * t) * k⁻¹) := by
      by_cases hα : ∃ z, (τ * t).ft z = 0 ∧ (τ * t).phi z ≠ 0
      · exact exists_conj_commute_of_exists_ft_eq_zero hBN hBNnd hb.isCompl.sup_eq_top huu hufix hα
      · push Not at hα
        have h4 : 4 ≤ finrank K (BN.orthogonal X) := by
          have := LinearMap.BilinForm.finrank_orthogonal hBNnd X
          omega
        exact exists_conj_commute_of_transvection_of_four_le h4 hBN hBNnd hb.isCompl.sup_eq_top
          huu hufix hα hz
    exact ⟨h * k, orderOf_mul_conj_eq_six_of_block hb ht hkfix hkne hkcomm⟩

end Six

end CFSG.ClassicalGroups.Alternating
