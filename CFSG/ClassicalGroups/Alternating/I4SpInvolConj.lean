module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolBasic
public import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem mem_orthogonal_iff_form {X : Submodule K N} {x : N} :
    x ∈ BN.orthogonal X ↔ ∀ n ∈ X, BN n x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]

theorem Tsp_mem_fixator (hBN : BN.IsAlt) {S : Set N} {x : N} (hx : ∀ y ∈ S, BN y x = 0) (c : K) :
    Tsp hBN x c ∈ Gsp.fixator S := fun y hy => Tsp_app_of_form_eq_zero hBN c (hx y hy)

theorem exists_Tsp_swap [CharP K 2] (hBN : BN.IsAlt) {a b : N} (hab : BN a b ≠ 0) {l : K}
    (hl : l ≠ 0) :
    ∃ s : Gsp BN, s * s = 1 ∧ s.app a = l • b ∧ ∀ x, BN x a = 0 → BN x b = 0 → s.app x = x := by
  set ζ := BN a b with hζ
  set l' : K := l * ζ⁻¹ with hl'
  set α : K := (l * ζ)⁻¹ with hα
  have hrel : α * l' * BN a b ^ 2 = 1 := by
    rw [hα, hl', ← hζ]
    field_simp
  refine ⟨Tsp hBN a α * Tsp hBN b l' * Tsp hBN a α, ?_, ?_, ?_⟩
  · have h1 := Tsp_mul_self hBN a α
    have h2 := Tsp_mul_self hBN b l'
    calc (Tsp hBN a α * Tsp hBN b l' * Tsp hBN a α) * (Tsp hBN a α * Tsp hBN b l' * Tsp hBN a α)
        = Tsp hBN a α * Tsp hBN b l' * (Tsp hBN a α * Tsp hBN a α) * Tsp hBN b l' *
            Tsp hBN a α := by group
      _ = Tsp hBN a α * (Tsp hBN b l' * Tsp hBN b l') * Tsp hBN a α := by
        rw [h1, mul_one]
        group
      _ = 1 := by rw [h2, mul_one, h1]
  · rw [app_Tsp_mul_Tsp_mul_Tsp_left hBN hrel]
    congr 1
    rw [hl', ← hζ]
    field_simp
  · intro x hxa hxb
    simp only [Gsp.app_mul, Tsp_app_of_form_eq_zero hBN _ hxa, Tsp_app_of_form_eq_zero hBN _ hxb]

theorem Gsp.phi_eq_zero_of_app_eq {u : Gsp BN} {z : N} (h : u.app z = z) : u.phi z = 0 := by
  rw [Gsp.phi_apply, h, sub_self]

theorem Gsp.ft_eq_zero_of_app_eq (hBN : BN.IsAlt) {u : Gsp BN} {z : N} (h : u.app z = z) :
    u.ft z = 0 := by
  rw [Gsp.ft, h, hBN.self_eq_zero]

theorem eq_Tsp_of_ft_eq_zero_imp [CharP K 2] [Finite K] (hBN : BN.IsAlt) {u : Gsp BN}
    (hu : u * u = 1) (h : ∀ z, u.ft z = 0 → u.phi z = 0) {z₀ : N} (hz₀ : u.phi z₀ ≠ 0) :
    u.ft z₀ ≠ 0 ∧ u = Tsp hBN (u.phi z₀) (u.ft z₀)⁻¹ := by
  have hζ : u.ft z₀ ≠ 0 := fun h0 => hz₀ (h z₀ h0)
  refine ⟨hζ, Gsp.ext' fun x => ?_⟩
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (u.ft x * (u.ft z₀)⁻¹)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hy : u.ft (x + (-r) • z₀) = 0 := by
    rw [Gsp.ft_add hBN hu, Gsp.ft_smul, neg_sq, sq, ← hr]
    field_simp
    linear_combination (u.ft x) * h2
  have hphi := h _ hy
  rw [map_add, map_smul] at hphi
  have hx : u.phi x = r • u.phi z₀ := by
    have : u.phi x + (-r) • u.phi z₀ = 0 := hphi
    rw [neg_smul] at this
    exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact this)
  have hBx : BN x (u.phi z₀) = r * u.ft z₀ := by
    rw [← Gsp.form_phi_left hu, hx, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Gsp.form_phi_left hu, ← Gsp.ft_eq_form_phi hBN]
  rw [Tsp_app]
  have hrx : (u.ft z₀)⁻¹ * BN x (u.phi z₀) = r := by
    rw [hBx]
    field_simp
  rw [hrx, ← hx]
  have : u.app x = x + u.phi x := by rw [Gsp.phi_apply]; abel
  exact this

theorem exists_conj_commute_of_exists_ft_eq_zero [CharP K 2] (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {X : Submodule K N} (hX : X ⊔ BN.orthogonal X = ⊤) {u : Gsp BN}
    (hu : u * u = 1) (hfix : ∀ x ∈ X, u.app x = x) (hα : ∃ z, u.ft z = 0 ∧ u.phi z ≠ 0) :
    ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧ k * u * k⁻¹ ≠ u ∧ Commute u (k * u * k⁻¹) := by
  obtain ⟨z, hz0, hzphi⟩ := hα
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp (hX ▸ Submodule.mem_top (x := z))
  have hphi : u.phi z₂ ≠ 0 := by
    rw [map_add, Gsp.phi_eq_zero_of_app_eq (hfix z₁ hz₁), zero_add] at hzphi
    exact hzphi
  have hft : u.ft z₂ = 0 := by
    rw [Gsp.ft_add hBN hu, Gsp.ft_eq_zero_of_app_eq hBN (hfix z₁ hz₁), zero_add] at hz0
    exact hz0
  have hz₂' := mem_orthogonal_iff_form.mp hz₂
  set k : Gsp BN := Tsp hBN z₂ 1 with hk
  set k' : Gsp BN := Tsp hBN (u.app z₂) 1 with hk'
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hki : k⁻¹ = k := inv_eq_of_mul_eq_one_right (Tsp_mul_self hBN z₂ 1)
  have hukuk : u * k * u = k' := by
    have h := Tsp_conj hBN u z₂ 1
    rwa [hui] at h
  have hxy : BN (u.app z₂) z₂ = 0 := by
    rw [form_comm_charTwo hBN]
    exact hft
  refine ⟨k, fun x hx => Tsp_app_of_form_eq_zero hBN 1 (hz₂' x hx), ?_, ?_⟩
  · intro h
    rw [hki] at h
    have h1 : u * (k * u * k) = u * u := by rw [h]
    have e1 : u * (k * u * k) = k' * k := by rw [← hukuk]; group
    rw [e1, hu] at h1
    have h2 : k' = k := by
      have : k' = k⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this, hki]
    have h3 := Tsp_injective_one hBN hBNnd h2
    apply hphi
    rw [Gsp.phi_apply, h3, sub_self]
  · rw [hki]
    have e1 : u * (k * u * k) = (u * k * u) * k := by group
    have e2 : (k * u * k) * u = k * (u * k * u) := by group
    show u * (k * u * k) = (k * u * k) * u
    rw [e1, e2, hukuk]
    exact Tsp_comm hBN hxy 1 1

theorem exists_conj_commute_of_transvection [CharP K 2] [Finite K] (hq : 3 ≤ Nat.card K)
    (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {X : Submodule K N}
    (hX : X ⊔ BN.orthogonal X = ⊤) {u : Gsp BN} (hu : u * u = 1) (hfix : ∀ x ∈ X, u.app x = x)
    (hβ : ∀ z, u.ft z = 0 → u.phi z = 0) {z₀ : N} (hz₀ : u.phi z₀ ≠ 0) :
    ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧ k * u * k⁻¹ ≠ u ∧ Commute u (k * u * k⁻¹) := by
  obtain ⟨hζ, hutsp⟩ := eq_Tsp_of_ft_eq_zero_imp hBN hu hβ hz₀
  set a₂ := u.phi z₀ with ha₂
  set ζ := u.ft z₀ with hζdef
  have ha₂X : ∀ x ∈ X, BN x a₂ = 0 := fun x hx => by
    rw [ha₂, ← Gsp.form_phi_left hu, Gsp.phi_eq_zero_of_app_eq (hfix x hx), map_zero,
      LinearMap.zero_apply]
  have ha₂z : BN a₂ z₀ = ζ := by
    rw [ha₂, Gsp.form_phi_left hu, ← Gsp.ft_eq_form_phi hBN]
  obtain ⟨z₁, hz₁, b₂, hb₂, hz⟩ := Submodule.mem_sup.mp (hX ▸ Submodule.mem_top (x := z₀))
  have hb₂X := mem_orthogonal_iff_form.mp hb₂
  have hab : BN a₂ b₂ = ζ := by
    have h1 : BN a₂ z₁ = 0 := by rw [form_comm_charTwo hBN]; exact ha₂X z₁ hz₁
    rw [← hz, map_add, h1, zero_add] at ha₂z
    exact ha₂z
  have ha₂0 : a₂ ≠ 0 := hz₀
  obtain ⟨μ, hμ0, hμ1⟩ := exists_ne_zero_ne_one_of_two_lt_card hq
  have hX0 : ∀ x ∈ X, BN x a₂ = 0 ∧ BN x b₂ = 0 := fun x hx => ⟨ha₂X x hx, hb₂X x hx⟩
  obtain ⟨s₁, hs₁sq, hs₁a, hs₁fix⟩ := exists_Tsp_swap hBN (hab ▸ hζ : BN a₂ b₂ ≠ 0) one_ne_zero
  obtain ⟨s₂, hs₂sq, hs₂a, hs₂fix⟩ := exists_Tsp_swap hBN (hab ▸ hζ : BN a₂ b₂ ≠ 0) hμ0
  have hs₁b : s₁.app b₂ = a₂ := by
    have := Gsp.app_app_of_mul_self hs₁sq a₂
    rw [hs₁a, one_smul] at this
    exact this
  set k : Gsp BN := s₁ * s₂ with hk
  have hka : k.app a₂ = μ • a₂ := by
    rw [hk, Gsp.app_mul, hs₂a, Gsp.map_smul, hs₁b]
  refine ⟨k, fun x hx => ?_, ?_, ?_⟩
  · rw [hk, Gsp.app_mul, hs₂fix x (hX0 x hx).1 (hX0 x hx).2, hs₁fix x (hX0 x hx).1 (hX0 x hx).2]
  · have hconj : k * u * k⁻¹ = Tsp hBN a₂ (μ ^ 2 * ζ⁻¹) := by
      rw [hutsp, Tsp_conj, hka, Tsp_smul]
    rw [hconj]
    intro h
    have h1 : Tsp hBN a₂ (μ ^ 2 * ζ⁻¹) * Tsp hBN a₂ ζ⁻¹ = 1 := by
      conv_lhs => rw [h]
      conv_lhs => rw [hutsp]
      exact Tsp_mul_self hBN _ _
    rw [Tsp_mul_Tsp] at h1
    rcases (Tsp_eq_one_iff hBN hBNnd a₂ _).mp h1 with h2 | h2
    · exact ha₂0 h2
    · have h3 : μ ^ 2 = 1 := by
        have hz' : ζ⁻¹ ≠ 0 := inv_ne_zero hζ
        have : (μ ^ 2 + 1) * ζ⁻¹ = 0 := by linear_combination h2
        have h4 := (mul_eq_zero.mp this).resolve_right hz'
        have h5 : (1 : K) = -1 := (CharTwo.neg_eq 1).symm
        linear_combination h4 - h5
      exact hμ1 (CharTwo.sq_inj.mp (by rw [h3, one_pow]))
  · have hconj : k * u * k⁻¹ = Tsp hBN a₂ (μ ^ 2 * ζ⁻¹) := by
      rw [hutsp, Tsp_conj, hka, Tsp_smul]
    rw [hconj]
    nth_rewrite 1 [hutsp]
    show Tsp hBN a₂ ζ⁻¹ * Tsp hBN a₂ (μ ^ 2 * ζ⁻¹) = Tsp hBN a₂ (μ ^ 2 * ζ⁻¹) * Tsp hBN a₂ ζ⁻¹
    rw [Tsp_mul_Tsp, Tsp_mul_Tsp, add_comm]

theorem exists_conj_commute [CharP K 2] [Finite K] (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {X : Submodule K N} (hX : IsCompl X (BN.orthogonal X))
    {u : Gsp BN} (hu : u * u = 1) (hu1 : u ≠ 1) (hfix : ∀ x ∈ X, u.app x = x) :
    ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧ k * u * k⁻¹ ≠ u ∧ Commute u (k * u * k⁻¹) := by
  by_cases hα : ∃ z, u.ft z = 0 ∧ u.phi z ≠ 0
  · exact exists_conj_commute_of_exists_ft_eq_zero hBN hBNnd hX.sup_eq_top hu hfix hα
  · push Not at hα
    obtain ⟨z₀, hz₀⟩ : ∃ z, u.phi z ≠ 0 := by
      by_contra h
      push Not at h
      apply hu1
      refine Gsp.ext' fun x => ?_
      have := h x
      rw [Gsp.phi_apply, sub_eq_zero] at this
      rw [this, Gsp.app_one]
    exact exists_conj_commute_of_transvection (by omega) hBN hBNnd hX.sup_eq_top hu hfix hα hz₀

theorem exists_conj_commute_sq [CharP K 2] [Finite K] (hq : 4 ≤ Nat.card K) (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) {X : Submodule K N} (hX : IsCompl X (BN.orthogonal X))
    {u : Gsp BN} (hu : u * u = 1) (hu1 : u ≠ 1) (hfix : ∀ x ∈ X, u.app x = x) :
    ∃ k : Gsp BN, (∀ x ∈ X, k.app x = x) ∧ k * u * k⁻¹ ≠ u ∧
      (u * (k * u * k⁻¹)) ^ 2 = 1 := by
  obtain ⟨k, hk, hne, hcomm⟩ := exists_conj_commute hq hBN hBNnd hX hu hu1 hfix
  refine ⟨k, hk, hne, ?_⟩
  have hu'sq : (k * u * k⁻¹) * (k * u * k⁻¹) = 1 := by
    calc (k * u * k⁻¹) * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
      _ = 1 := by rw [hu]; group
  rw [sq]
  calc u * (k * u * k⁻¹) * (u * (k * u * k⁻¹)) = u * ((k * u * k⁻¹) * u) * (k * u * k⁻¹) := by
        group
    _ = u * (u * (k * u * k⁻¹)) * (k * u * k⁻¹) := by rw [← hcomm.eq]
    _ = (u * u) * ((k * u * k⁻¹) * (k * u * k⁻¹)) := by group
    _ = 1 := by rw [hu, hu'sq, one_mul]

end CFSG.ClassicalGroups.Alternating
