module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagAdapted
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaLagrangian

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_apply_of_singular {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (x : V) : eichler Q u w x = x + polar Q x u • w - polar Q x w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero]

theorem omegaInvRadical_mul_apply {W : Submodule K V}
    (hW : ∀ v ∈ W, ∀ w ∈ W, polar Q v w = 0) {g g' : V ≃ₗ[K] V}
    (hg : g ∈ omegaInvRadical Q W) (hg' : g' ∈ omegaInvRadical Q W) (x : V) :
    (g * g') x = g x + g' x - x := by
  have hS : g (g' x - x) = g' x - x := hg.2.2 _ fun w hw => by
    rw [polar_comm]
    exact hW w hw _ (hg'.2.1 x)
  rw [map_sub] at hS
  rw [LinearEquiv.mul_apply, show g (g' x) = (g (g' x) - g x) + g x by abel, hS]
  abel

theorem eichler_mem_omegaO2Cent_of_partner [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {x y u : V}
    (hxy : polar Q (omegaInvNil s x) y = 1) (hNx : Q (omegaInvNil s x) = 0)
    (hNy : Q (omegaInvNil s y) = 0) (hu : u ∈ omegaInvSpace s) (hux : polar Q u x = 0)
    (huy : polar Q u y = 0) : eichler Q u (omegaInvNil s x) ∈ omegaO2Cent Q s := by
  have hNx0 : omegaInvNil s x ≠ 0 := by
    intro h
    rw [h, polar_zero_left] at hxy
    exact zero_ne_one hxy
  obtain ⟨w₁, hw₁, hxw₁⟩ : ∃ w₁ ∈ omegaInvSpace s, polar Q x w₁ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hNx0 ((omegaInvNil_eq_zero_iff hQ hs hss).2 hc)
  set c := (1 - polar Q x y) / polar Q x w₁ with hc
  set y' := y + c • w₁ with hy'
  have hNy' : omegaInvNil s y' = omegaInvNil s y := by
    rw [hy', map_add, map_smul, omegaInvNil_of_mem_omegaInvSpace hss hw₁, smul_zero, add_zero]
  have hxy' : polar Q x y' = 1 := by
    rw [hy', polar_add_right, polar_smul_right_eq, hc, div_mul_cancel₀ _ hxw₁]
    ring
  have hxNy' : polar Q x (omegaInvNil s y') = 1 := by
    rw [hNy', ← polar_omegaInvNil_left hs hss, hxy]
  have huy' : polar Q u y' = 0 := by
    rw [hy', polar_add_right, polar_smul_right_eq, huy,
      polar_of_mem_omegaInvSpace hs hss hu hw₁]
    ring
  exact eichler_mem_omegaO2Cent_of_doubled hK hs hss hxy' hxNy' hNx (by rw [hNy']; exact hNy) hu
    hux huy'

theorem polar_omegaInvNil_comm {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hss : s * s = 1) (x y : V) :
    polar Q (omegaInvNil s x) y = polar Q (omegaInvNil s y) x := by
  rw [polar_omegaInvNil_left hs hss, polar_comm]

theorem polar_omegaInvNil_self [CharP K 2] {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    polar Q (omegaInvNil s x) x = Q (omegaInvNil s x) := by
  rw [polar_comm, ← map_omegaInvNil hs]

theorem eichler_mul_eichler_mem_omegaO2Cent [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) {x₁ y₁ x₂ y₂ : V}
    (h11 : polar Q (omegaInvNil s x₁) y₁ = 1) (h22 : polar Q (omegaInvNil s x₂) y₂ = 1)
    (h12 : polar Q (omegaInvNil s x₁) y₂ = 0) (h21 : polar Q (omegaInvNil s x₂) y₁ = 0)
    (hxx : polar Q (omegaInvNil s x₁) x₂ = 0) :
    eichler Q (omegaInvNil s x₁) (omegaInvNil s y₁) *
      eichler Q (omegaInvNil s x₂) (omegaInvNil s y₂) ∈ omegaO2Cent Q s := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  set W := omegaInvSpace s with hWdef
  have hWiso : ∀ v ∈ W, ∀ w ∈ W, polar Q v w = 0 := fun v hv w hw =>
    polar_of_mem_omegaInvSpace hs hss hv hw
  have hmem : ∀ z, omegaInvNil s z ∈ W := omegaInvNil_mem_omegaInvSpace s
  have hNN : ∀ z, Q (omegaInvNil s z) = 0 := fun z => hW _ (hmem z)
  have hsym := polar_omegaInvNil_comm hs hss
  have hself : ∀ z, polar Q (omegaInvNil s z) z = 0 := fun z => by
    rw [polar_omegaInvNil_self hs, hNN]
  have g1 : eichler Q (omegaInvNil s (x₁ + x₂)) (omegaInvNil s (y₁ + y₂)) ∈ omegaO2Cent Q s := by
    refine eichler_mem_omegaO2Cent_of_partner hK hQ hs hss (y := x₁) ?_ (hNN _) (hNN _) (hmem _)
      ?_ ?_
    · rw [map_add, polar_add_left, hsym y₁, hsym y₂, h11, h12, add_zero]
    · rw [map_add, polar_add_left, polar_add_right, polar_add_right, h11, h12, h21, h22]
      linear_combination h2
    · rw [map_add, polar_add_left, hself, hsym x₂ x₁, hxx, add_zero]
  have g2 : eichler Q (omegaInvNil s x₁) (omegaInvNil s y₂) ∈ omegaO2Cent Q s :=
    eichler_mem_omegaO2Cent_of_partner hK hQ hs hss (y := x₂) (by rw [hsym, h22]) (hNN _)
      (hNN _) (hmem _) h12 hxx
  have g3 : eichler Q (omegaInvNil s x₂) (omegaInvNil s y₁) ∈ omegaO2Cent Q s :=
    eichler_mem_omegaO2Cent_of_partner hK hQ hs hss (y := x₁) (by rw [hsym, h11]) (hNN _)
      (hNN _) (hmem _) h21 (by rw [hsym, hxx])
  set a := omegaInvNil s x₁
  set b := omegaInvNil s y₁
  set a' := omegaInvNil s x₂
  set b' := omegaInvNil s y₂
  have hE : ∀ u ∈ W, ∀ w ∈ W, ∀ z, eichler Q u w z = z + polar Q z u • w - polar Q z w • u :=
    fun u hu w hw z => eichler_apply_of_singular (hW u hu) (hW w hw) (hWiso u hu w hw) z
  have hR : ∀ u ∈ W, ∀ w ∈ W, eichler Q u w ∈ omegaInvRadical Q W := fun u hu w hw =>
    eichler_mem_omegaInvRadical hu hw
  have ha := hmem x₁
  have hb := hmem y₁
  have ha' := hmem x₂
  have hb' := hmem y₂
  have hid : eichler Q a b * eichler Q a' b' =
      eichler Q (a + a') (b + b') * eichler Q a (-b') * eichler Q a' (-b) := by
    refine LinearEquiv.ext fun z => ?_
    rw [omegaInvRadical_mul_apply hWiso (hR a ha b hb) (hR a' ha' b' hb'),
      omegaInvRadical_mul_apply hWiso (mul_mem (hR _ (W.add_mem ha ha') _ (W.add_mem hb hb'))
        (hR a ha _ (W.neg_mem hb'))) (hR a' ha' _ (W.neg_mem hb)),
      omegaInvRadical_mul_apply hWiso (hR _ (W.add_mem ha ha') _ (W.add_mem hb hb'))
        (hR a ha _ (W.neg_mem hb')),
      hE a ha b hb, hE a' ha' b' hb', hE _ (W.add_mem ha ha') _ (W.add_mem hb hb'),
      hE a ha _ (W.neg_mem hb'), hE a' ha' _ (W.neg_mem hb)]
    simp only [polar_add_right, polar_neg_right]
    module
  have hmap : ∀ z z', omegaInvNil s (z + z') = omegaInvNil s z + omegaInvNil s z' :=
    fun z z' => map_add _ z z'
  rw [hid, ← eichler_inv (hWiso a ha b' hb'), ← eichler_inv (hWiso a' ha' b hb)]
  refine mul_mem (mul_mem ?_ (inv_mem g2)) (inv_mem g3)
  rw [← hmap, ← hmap]
  exact g1

theorem exists_pair_of_lagAdapted [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    {s' : V ≃ₗ[K] V} (h : LagAdapted Q s s') (hne : omegaInvSpace s' ≠ ⊥) :
    ∃ x y, omegaInvNil s x ∈ omegaInvSpace s' ∧ omegaInvNil s y ∈ omegaInvSpace s' ∧
      polar Q (omegaInvNil s x) y = 1 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 (h.2.2.1 hu)
  obtain ⟨b, hb, hub⟩ := exists_polar_ne_zero_of_lagAdapted hQ hs hss h hu hu0
  refine ⟨x, (polar Q (omegaInvNil s x) b)⁻¹ • b, hu, ?_, ?_⟩
  · rw [map_smul]
    exact (omegaInvSpace s').smul_mem _ hb
  · rw [polar_smul_right_eq, inv_mul_cancel₀ hub]

theorem lagAdapted_eichler_typeA [CharP K 2] [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) {x y : V} (hxy : polar Q (omegaInvNil s x) y = 1) :
    LagAdapted Q s (eichler Q (omegaInvNil s x) (omegaInvNil s y)) ∧
      omegaInvSpace (eichler Q (omegaInvNil s x) (omegaInvNil s y)) =
        Submodule.span K {omegaInvNil s x, omegaInvNil s y} ∧
      finrank K (omegaInvSpace (eichler Q (omegaInvNil s x) (omegaInvNil s y))) = 2 := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  set a := omegaInvNil s x with ha
  set b := omegaInvNil s y with hb
  have haW : a ∈ omegaInvSpace s := omegaInvNil_mem_omegaInvSpace s x
  have hbW : b ∈ omegaInvSpace s := omegaInvNil_mem_omegaInvSpace s y
  have hQa : Q a = 0 := hW a haW
  have hQb : Q b = 0 := hW b hbW
  have hab : polar Q a b = 0 := polar_of_mem_omegaInvSpace hs hss haW hbW
  have hsym := polar_omegaInvNil_comm hs hss
  have hxx : polar Q a x = 0 := by rw [ha, polar_omegaInvNil_self hs, ← ha, hQa]
  have hyy : polar Q b y = 0 := by rw [hb, polar_omegaInvNil_self hs, ← hb, hQb]
  have hyx : polar Q b x = 1 := by rw [hb, ← hsym, hxy]
  set E := eichler Q a b with hE
  have hEz : ∀ z, E z = z + polar Q z a • b - polar Q z b • a := fun z =>
    eichler_apply_of_singular hQa hQb hab z
  have hNE : ∀ z, omegaInvNil E z = polar Q z a • b + polar Q z b • a := fun z => by
    rw [omegaInvNil_apply, hEz, omegaInv_sub_eq_add K (z + polar Q z a • b)]
    abel
  have hEE : E * E = 1 := by
    rw [hE, eichler_mul hab hab, omegaInv_add_self K, eichler_zero_right]
  have hEO : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q a b
  have hspan : omegaInvSpace E = Submodule.span K {a, b} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨z, rfl⟩ := mem_omegaInvSpace_iff.1 hv
      rw [hNE]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | hv
      · refine mem_omegaInvSpace_iff.2 ⟨x, ?_⟩
        rw [hNE, polar_comm Q x a, polar_comm Q x b, hxx, hyx, zero_smul, zero_add, one_smul]
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        refine mem_omegaInvSpace_iff.2 ⟨y, ?_⟩
        rw [hNE, polar_comm Q y a, polar_comm Q y b, hxy, hyy, one_smul, zero_smul, add_zero]
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, polar_zero_left] at hxy
    exact zero_ne_one hxy
  have hli : LinearIndependent K ![a, b] := by
    refine (LinearIndependent.pair_iff' ha0).2 fun c hc => ?_
    have e := congrArg (fun z => polar Q z x) hc
    simp only [polar_smul_left_eq, hxx, mul_zero, hyx] at e
    exact zero_ne_one e
  have hfin := finrank_span_eq_card hli
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at hfin
  refine ⟨⟨hEO, hEE, ?_, fun v hv => ?_⟩, hspan, by rw [hspan, hfin]⟩
  · rw [hspan, Submodule.span_le]
    rintro v (rfl | hv)
    · exact haW
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hbW
  · rw [hspan] at hv
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hv
    have e1 : polar Q v a = β := by
      rw [ha, polar_comm, polar_omegaInvNil_left hs hss, ← hαβ, polar_add_right,
        polar_smul_right_eq, polar_smul_right_eq, polar_comm Q x a, polar_comm Q x b, hxx, hyx]
      ring
    have e2 : polar Q v b = α := by
      rw [hb, polar_comm, polar_omegaInvNil_left hs hss, ← hαβ, polar_add_right,
        polar_smul_right_eq, polar_smul_right_eq, polar_comm Q y a, polar_comm Q y b, hxy, hyy]
      ring
    rw [hNE, e1, e2, ← hαβ, add_comm]

theorem mem_omegaO2Cent_of_lagAdapted_typeA [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) (r : ℕ) :
    ∀ s' : V ≃ₗ[K] V, LagAdapted Q s s' → finrank K (omegaInvSpace s') = 4 * r →
      s' ∈ omegaO2Cent Q s := by
  have hsym := polar_omegaInvNil_comm hs hss
  have hpair : ∀ {x y : V} {U : Submodule K V}, omegaInvNil s x ∈ U → omegaInvNil s y ∈ U →
      Submodule.span K {omegaInvNil s x, omegaInvNil s y} ≤ U := fun hx hy => by
    rw [Submodule.span_le]
    rintro v (rfl | hv)
    · exact hx
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hy
  have hin1 : ∀ x y : V, omegaInvNil s x ∈ Submodule.span K {omegaInvNil s x, omegaInvNil s y} :=
    fun _ _ => Submodule.subset_span (by simp)
  have hin2 : ∀ x y : V, omegaInvNil s y ∈ Submodule.span K {omegaInvNil s x, omegaInvNil s y} :=
    fun _ _ => Submodule.subset_span (by simp)
  induction r with
  | zero =>
    intro s' _ hr
    rw [eq_one_of_finrank_omegaInvSpace_eq_zero (s' := s') (by omega)]
    exact Subgroup.one_mem _
  | succ r ih =>
    intro s' h hr
    have hne : omegaInvSpace s' ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hr
      omega
    obtain ⟨x₁, y₁, hx₁, hy₁, h11⟩ := exists_pair_of_lagAdapted hQ hs hss h hne
    obtain ⟨hg₁, hsp₁, hd₁⟩ := lagAdapted_eichler_typeA hs hss hW h11
    set E₁ := eichler Q (omegaInvNil s x₁) (omegaInvNil s y₁) with hE₁
    obtain ⟨hs₁, -, horth₁, -, hdim₁, he₁⟩ :=
      lagAdapted_mul hQ hs hss h hg₁ (hsp₁ ▸ hpair hx₁ hy₁)
    set s₁ := s' * E₁ with hs₁def
    have hne₁ : omegaInvSpace s₁ ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hdim₁
      omega
    obtain ⟨x₂, y₂, hx₂, hy₂, h22⟩ := exists_pair_of_lagAdapted hQ hs hss hs₁ hne₁
    obtain ⟨hg₂, hsp₂, hd₂⟩ := lagAdapted_eichler_typeA hs hss hW h22
    set E₂ := eichler Q (omegaInvNil s x₂) (omegaInvNil s y₂) with hE₂
    obtain ⟨hs₂, -, -, -, hdim₂, he₂⟩ :=
      lagAdapted_mul hQ hs hss hs₁ hg₂ (hsp₂ ▸ hpair hx₂ hy₂)
    have hmem₂ : s₁ * E₂ ∈ omegaO2Cent Q s := ih _ hs₂ (by omega)
    have h21 : polar Q (omegaInvNil s x₂) y₁ = 0 :=
      horth₁ _ hx₂ y₁ (by rw [hsp₁]; exact hin2 x₁ y₁)
    have h12 : polar Q (omegaInvNil s x₁) y₂ = 0 := by
      rw [hsym]
      exact horth₁ _ hy₂ x₁ (by rw [hsp₁]; exact hin1 x₁ y₁)
    have hxx : polar Q (omegaInvNil s x₂) x₁ = 0 :=
      horth₁ _ hx₂ x₁ (by rw [hsp₁]; exact hin1 x₁ y₁)
    have hC : E₂ * E₁ ∈ omegaO2Cent Q s :=
      eichler_mul_eichler_mem_omegaO2Cent hK hQ hs hss hW h22 h11 h21 h12 hxx
    have key : s' = (s₁ * E₂) * (E₂ * E₁) := by
      calc s' = s₁ * E₁ := he₁
        _ = (s₁ * E₂ * E₂) * E₁ := by rw [← he₂]
        _ = (s₁ * E₂) * (E₂ * E₁) := by group
    rw [key]
    exact mul_mem hmem₂ hC

theorem mem_omegaO2Cent_of_typeA_four_dvd [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) (h4 : 4 ∣ finrank K (omegaInvSpace s)) :
    s ∈ omegaO2Cent Q s := by
  obtain ⟨r, hr⟩ := h4
  exact mem_omegaO2Cent_of_lagAdapted_typeA hK hQ hs hss hW r s (lagAdapted_self hs hss) hr

end CFSG.SeitzReduction.SymplecticPilot
