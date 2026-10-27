module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowDoubled
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowO2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_mul_eichler_mem_omegaO2Cent_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    {s : V ≃ₗ[K] V}
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
    refine eichler_mem_omegaO2Cent_of_partner_two hs hss (y := x₁) ?_ (hNN _) (hNN _)
      (omegaInvNil_of_mem_omegaInvSpace hss (hmem _)) ?_ ?_
    · rw [map_add, polar_add_left, hsym y₁, hsym y₂, h11, h12, add_zero]
    · rw [map_add, polar_add_left, polar_add_right, polar_add_right, h11, h12, h21, h22]
      linear_combination h2
    · rw [map_add, polar_add_left, hself, hsym x₂ x₁, hxx, add_zero]
  have g2 : eichler Q (omegaInvNil s x₁) (omegaInvNil s y₂) ∈ omegaO2Cent Q s :=
    eichler_mem_omegaO2Cent_of_partner_two hs hss (y := x₂) (by rw [hsym, h22]) (hNN _)
      (hNN _) (omegaInvNil_of_mem_omegaInvSpace hss (hmem _)) h12 hxx
  have g3 : eichler Q (omegaInvNil s x₂) (omegaInvNil s y₁) ∈ omegaO2Cent Q s :=
    eichler_mem_omegaO2Cent_of_partner_two hs hss (y := x₁) (by rw [hsym, h11]) (hNN _)
      (hNN _) (omegaInvNil_of_mem_omegaInvSpace hss (hmem _)) h21 (by rw [hsym, hxx])
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

theorem mem_omegaO2Cent_of_lagAdapted_typeA_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
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
      eichler_mul_eichler_mem_omegaO2Cent_two hs hss hW h22 h11 h21 h12 hxx
    have key : s' = (s₁ * E₂) * (E₂ * E₁) := by
      calc s' = s₁ * E₁ := he₁
        _ = (s₁ * E₂ * E₂) * E₁ := by rw [← he₂]
        _ = (s₁ * E₂) * (E₂ * E₁) := by group
    rw [key]
    exact mul_mem hmem₂ hC

theorem mem_omegaO2Cent_of_typeA_four_dvd_two [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) (h4 : 4 ∣ finrank K (omegaInvSpace s)) :
    s ∈ omegaO2Cent Q s := by
  obtain ⟨r, hr⟩ := h4
  exact mem_omegaO2Cent_of_lagAdapted_typeA_two hQ hs hss hW r s (lagAdapted_self hs hss) hr


theorem eichler_inv_eq_swap {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    (eichler Q u w)⁻¹ = eichler Q w u := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  rw [eichler_inv huw]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply_of_singular hu (by rw [QuadraticMap.map_neg, hw])
      (by rw [polar_neg_right, huw, neg_zero]),
    eichler_apply_of_singular hw hu hwu, polar_neg_right]
  module

theorem eichler_mem_omegaO2Cent_of_mem_ker [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) {x₁ : V} (hx₁ : omegaInvNil s x₁ = 0)
    (hx₁W : x₁ ∉ omegaInvSpace s) {w : V} (hw : w ∈ omegaInvSpace s) :
    eichler Q x₁ w ∈ omegaO2Cent Q s := by
  by_cases hw0 : w = 0
  · rw [hw0, eichler_zero_right]
    exact Subgroup.one_mem _
  obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hw
  obtain ⟨y, hy⟩ := omegaInv_exists_polar_eq_one hQ hw0
  obtain ⟨z, hz, hx₁z⟩ := exists_partner_of_not_mem hQ hs hss hx₁W
  set x' := x - polar Q x₁ x • z with hx'
  set y' := y - polar Q x₁ y • z with hy'
  have hNx' : omegaInvNil s x' = omegaInvNil s x := by
    rw [hx', map_sub, map_smul, hz, smul_zero, sub_zero]
  have hNy' : omegaInvNil s y' = omegaInvNil s y := by
    rw [hy', map_sub, map_smul, hz, smul_zero, sub_zero]
  have hNxz : polar Q (omegaInvNil s x) z = 0 := by
    rw [polar_omegaInvNil_left hs hss, hz, polar_zero_right]
  have hxy' : polar Q (omegaInvNil s x') y' = 1 := by
    rw [hNx', hy', polar_sub_right, polar_smul_right_eq, hNxz, mul_zero, sub_zero, polar_comm, hy]
  have hux' : polar Q x₁ x' = 0 := by
    rw [hx', polar_sub_right, polar_smul_right_eq, hx₁z, mul_one, sub_self]
  have huy' : polar Q x₁ y' = 0 := by
    rw [hy', polar_sub_right, polar_smul_right_eq, hx₁z, mul_one, sub_self]
  have h := eichler_mem_omegaO2Cent_of_partner_two hs hss hxy'
    (by rw [hNx']; exact hW _ (omegaInvNil_mem_omegaInvSpace s x))
    (by rw [hNy']; exact hW _ (omegaInvNil_mem_omegaInvSpace s y)) hx₁ hux' huy'
  rwa [hNx'] at h

theorem mem_omegaO2Cent_of_typeA_of_singular [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hW : ∀ w ∈ omegaInvSpace s, Q w = 0) {x₁ : V} (hx₁ : omegaInvNil s x₁ = 0)
    (hx₁W : x₁ ∉ omegaInvSpace s) (hQx₁ : Q x₁ = 0) : s ∈ omegaO2Cent Q s := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have hev : Even (finrank K (omegaInvSpace s)) :=
    CFSG.RankThree.OrthogonalInvolutions.even_finrank_commSpace_of_forall_eq_zero hQ hs hss hW
  obtain ⟨z, hz, hx₁z⟩ := exists_partner_of_not_mem hQ hs hss hx₁W
  set x₂ := z - Q z • x₁ with hx₂
  have hx₂N : omegaInvNil s x₂ = 0 := by rw [hx₂, map_sub, map_smul, hz, hx₁, smul_zero, sub_zero]
  have hx₁x₁ : polar Q x₁ x₁ = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hx₁x₂ : polar Q x₁ x₂ = 1 := by
    rw [hx₂, polar_sub_right, polar_smul_right_eq, hx₁x₁, mul_zero, sub_zero, hx₁z]
  have hQx₂ : Q x₂ = 0 := by
    rw [hx₂, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, hQx₁, mul_zero,
      add_zero, polar_smul_right_eq, polar_comm, hx₁z, mul_one]
    ring
  have hx₂W : x₂ ∉ omegaInvSpace s := by
    intro h
    have h0 := polar_eq_zero_of_mem_of_nil hQ hs hss h hx₁
    rw [polar_comm, hx₁x₂] at h0
    exact one_ne_zero h0
  refine mem_omegaO2Cent_of_forall_eichler hQ hs hss hev fun u hu w hw => ?_
  have hux₁ : polar Q u x₁ = 0 := polar_eq_zero_of_mem_of_nil hQ hs hss hu hx₁
  have hux₂ : polar Q u x₂ = 0 := polar_eq_zero_of_mem_of_nil hQ hs hss hu hx₂N
  have hwx₁ : polar Q w x₁ = 0 := polar_eq_zero_of_mem_of_nil hQ hs hss hw hx₁
  have hwx₂ : polar Q w x₂ = 0 := polar_eq_zero_of_mem_of_nil hQ hs hss hw hx₂N
  have hx₁w : polar Q x₁ w = 0 := by rw [polar_comm, hwx₁]
  have huw : polar Q u w = 0 := polar_of_mem_omegaInvSpace hs hss hu hw
  have g1 : eichler Q x₁ w ∈ omegaO2Cent Q s :=
    eichler_mem_omegaO2Cent_of_mem_ker hQ hs hss hW hx₁ hx₁W hw
  have g2 : eichler Q u x₂ ∈ omegaO2Cent Q s := by
    have h := inv_mem (eichler_mem_omegaO2Cent_of_mem_ker hQ hs hss hW hx₂N hx₂W hu)
    rwa [eichler_inv_eq_swap hQx₂ (hW u hu) (by rw [polar_comm, hux₂])] at h
  have hgu : eichler Q x₁ w u = u := by
    rw [eichler_apply hQx₁ hx₁w, hux₁, huw]
    simp
  have hgx₂ : eichler Q x₁ w x₂ - x₂ = w := by
    rw [eichler_apply hQx₁ hx₁w, polar_comm Q x₂ x₁, hx₁x₂, polar_comm Q x₂ w, hwx₂, hW w hw]
    simp
  have hc := commutatorElement_eichler (eichler_mem_orthogonalGroup Q x₁ w) hgu hux₂
  rw [hgx₂] at hc
  rw [← hc, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem g1 g2) (inv_mem g1)) (inv_mem g2)

end CFSG.SeitzReduction.SymplecticPilot
