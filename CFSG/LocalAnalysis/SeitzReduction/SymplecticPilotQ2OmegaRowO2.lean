module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowPlane
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaO2Even
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagC

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.OrthogonalInvolutions (two_mul_finrank_commSpace_le mem_omegaGroup)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem omegaTwo_eq_zero_or_eq_one (hK : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, _root_.sq] at h
  rcases eq_or_ne c 0 with h0 | h0
  · exact Or.inl h0
  · right
    have h1 : c * c = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ h0 h1

theorem omegaTwo_eq_one_of_ne_zero (hK : Nat.card K = 2) {c : K} (hc : c ≠ 0) : c = 1 :=
  (omegaTwo_eq_zero_or_eq_one hK c).resolve_left hc

theorem exists_partner_of_not_mem [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {p : V}
    (hpW : p ∉ omegaInvSpace s) : ∃ p', omegaInvNil s p' = 0 ∧ polar Q p p' = 1 := by
  obtain ⟨z', hz', hzz'⟩ : ∃ z', omegaInvNil s z' = 0 ∧ polar Q p z' ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hpW (mem_omegaInvSpace_of_forall_polar hQ hs hss hc)
  refine ⟨(polar Q p z')⁻¹ • z', ?_, ?_⟩
  · rw [map_smul, hz', smul_zero]
  · rw [polar_smul_right_eq, inv_mul_cancel₀ hzz']

theorem polar_eq_zero_of_mem_of_nil (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {u p : V}
    (hu : u ∈ omegaInvSpace s) (hp : omegaInvNil s p = 0) : polar Q u p = 0 := by
  rw [polar_comm]
  exact (omegaInvNil_eq_zero_iff hQ hs hss).1 hp u hu

theorem eichler_mem_omegaO2Cent_of_good [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {u : V}
    (hu : u ∈ omegaInvSpace s) {p p' : V} (hp : omegaInvNil s p = 0)
    (hp' : omegaInvNil s p' = 0) (hpp' : polar Q p p' = 1) (h1 : Q p = 1) (h2 : Q p' = 1) :
    eichler Q u p ∈ omegaO2Cent Q s := by
  refine eichler_mem_omegaO2Cent_of_plane_two hQ hs hss hu hp hp' hpp' (by rw [h1]; exact
    one_ne_zero) ?_
  rw [QuadraticMap.map_add Q, h1, h2, hpp', CharTwo.add_self_eq_zero, zero_add]
  exact one_ne_zero

theorem eichler_mem_omegaO2Cent_of_aniso [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hani : ∀ y, omegaInvNil s y = 0 → y ∉ omegaInvSpace s → Q y ≠ 0) {u : V}
    (hu : u ∈ omegaInvSpace s) {p : V} (hp : omegaInvNil s p = 0) (hpW : p ∉ omegaInvSpace s) :
    eichler Q u p ∈ omegaO2Cent Q s := by
  obtain ⟨p', hp', hpp'⟩ := exists_partner_of_not_mem hQ hs hss hpW
  have hsum : omegaInvNil s (p + p') = 0 := by rw [map_add, hp, hp', add_zero]
  have hsumW : p + p' ∉ omegaInvSpace s := by
    intro hW
    have h0 := polar_eq_zero_of_mem_of_nil hQ hs hss hW hp
    rw [polar_add_left, polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul, zero_add,
      polar_comm, hpp'] at h0
    exact one_ne_zero h0
  exact eichler_mem_omegaO2Cent_of_plane_two hQ hs hss hu hp hp' hpp' (hani p hp hpW)
    (hani _ hsum hsumW)

theorem polar_proj_left [CharP K 2] {p p' : V} (hpp' : polar Q p p' = 1) (y : V) :
    polar Q p (y - polar Q y p' • p - polar Q y p • p') = 0 := by
  rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul, mul_zero, hpp', mul_one, sub_zero,
    polar_comm, sub_self]

theorem polar_proj_right [CharP K 2] {p p' : V} (hpp' : polar Q p p' = 1) (y : V) :
    polar Q p' (y - polar Q y p' • p - polar Q y p • p') = 0 := by
  rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_self_eq_two_mul (Q := Q) p', omegaInv_two_eq_zero, zero_mul, mul_zero, sub_zero,
    polar_comm Q p' p, hpp', mul_one, polar_comm Q p' y, sub_self]

theorem exists_perp_not_mem [CharP K 2] [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hl : 2 * finrank K (omegaInvSpace s) + 4 ≤ finrank K V) {p p' : V}
    (hp : omegaInvNil s p = 0) (hp' : omegaInvNil s p' = 0) (hpp' : polar Q p p' = 1) :
    ∃ a, omegaInvNil s a = 0 ∧ polar Q p a = 0 ∧ polar Q p' a = 0 ∧ a ∉ omegaInvSpace s := by
  classical
  by_contra hc
  push Not at hc
  have hle : LinearMap.ker (omegaInvNil s) ≤
      omegaInvSpace s ⊔ Submodule.span K ({p, p'} : Set V) := by
    intro y hy
    have hy0 : omegaInvNil s y = 0 := LinearMap.mem_ker.1 hy
    set a := y - polar Q y p' • p - polar Q y p • p' with ha
    have ha0 : omegaInvNil s a = 0 := by
      rw [ha, map_sub, map_sub, map_smul, map_smul, hy0, hp, hp', smul_zero, smul_zero, sub_zero,
        sub_zero]
    have haW := hc a ha0 (polar_proj_left hpp' y) (polar_proj_right hpp' y)
    have hy' : y = a + (polar Q y p' • p + polar Q y p • p') := by rw [ha]; abel
    rw [hy']
    refine Submodule.add_mem_sup haW ?_
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (omegaInvSpace s)
    (Submodule.span K ({p, p'} : Set V))
  have h3 : finrank K (Submodule.span K ({p, p'} : Set V)) ≤ 2 := by
    have e : ({p, p'} : Set V) = (({p, p'} : Finset V) : Set V) := by simp
    rw [e]
    refine (finrank_span_finset_le_card _).trans ?_
    exact (Finset.card_insert_le _ _).trans (by simp)
  have h4 := LinearMap.finrank_range_add_finrank_ker (omegaInvNil s)
  change finrank K (omegaInvSpace s) + _ = _ at h4
  omega

theorem omegaTwo_map_eq_one_or [CharP K 2] (hK : Nat.card K = 2) {x c : V} (hc : Q c = 1)
    (hxc : polar Q x c = 0) : Q x = 1 ∨ Q (x + c) = 1 := by
  rcases omegaTwo_eq_zero_or_eq_one hK (Q x) with h | h
  · right
    rw [QuadraticMap.map_add Q, h, hc, hxc, zero_add, add_zero]
  · exact Or.inl h

theorem exists_nonsingular_pair_perp [CharP K 2] [FiniteDimensional K V] (hK : Nat.card K = 2)
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hl : 2 * finrank K (omegaInvSpace s) + 4 ≤ finrank K V) {p p' : V}
    (hp : omegaInvNil s p = 0) (hp' : omegaInvNil s p' = 0) (hpp' : polar Q p p' = 1) :
    ∃ c d, omegaInvNil s c = 0 ∧ omegaInvNil s d = 0 ∧ polar Q p c = 0 ∧ polar Q p' c = 0 ∧
      polar Q p d = 0 ∧ polar Q p' d = 0 ∧ polar Q c d = 1 ∧ Q c = 1 := by
  obtain ⟨a, ha, hpa, hp'a, haW⟩ := exists_perp_not_mem hl hp hp' hpp'
  obtain ⟨y, hy, hay⟩ := exists_partner_of_not_mem hQ hs hss haW
  set b := y - polar Q y p' • p - polar Q y p • p' with hb
  have hb0 : omegaInvNil s b = 0 := by
    rw [hb, map_sub, map_sub, map_smul, map_smul, hy, hp, hp', smul_zero, smul_zero, sub_zero,
      sub_zero]
  have hpb : polar Q p b = 0 := polar_proj_left hpp' y
  have hp'b : polar Q p' b = 0 := polar_proj_right hpp' y
  have hab : polar Q a b = 1 := by
    rw [hb, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_comm Q a p, hpa, polar_comm Q a p', hp'a, mul_zero, mul_zero, sub_zero, sub_zero, hay]
  have hba : polar Q b a = 1 := by rw [polar_comm, hab]
  rcases omegaTwo_eq_zero_or_eq_one hK (Q a) with hQa | hQa
  · rcases omegaTwo_eq_zero_or_eq_one hK (Q b) with hQb | hQb
    · refine ⟨a + b, a, by rw [map_add, ha, hb0, add_zero], ha,
        by rw [polar_add_right, hpa, hpb, add_zero], by rw [polar_add_right, hp'a, hp'b, add_zero],
        hpa, hp'a, ?_, ?_⟩
      · rw [polar_add_left, polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul, zero_add, hba]
      · rw [QuadraticMap.map_add Q, hQa, hQb, hab, zero_add, zero_add]
    · exact ⟨b, a, hb0, ha, hpb, hp'b, hpa, hp'a, hba, hQb⟩
  · exact ⟨a, b, ha, hb0, hpa, hp'a, hpb, hp'b, hab, hQa⟩

theorem eichler_mem_omegaO2Cent_of_four_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hl : 2 * finrank K (omegaInvSpace s) + 4 ≤ finrank K V) {u : V}
    (hu : u ∈ omegaInvSpace s) {p : V} (hp : omegaInvNil s p = 0) (hpW : p ∉ omegaInvSpace s) :
    eichler Q u p ∈ omegaO2Cent Q s := by
  obtain ⟨p', hp', hpp'⟩ := exists_partner_of_not_mem hQ hs hss hpW
  obtain ⟨c, d, hc, hd, hpc, hp'c, hpd, hp'd, hcd, hQc⟩ :=
    exists_nonsingular_pair_perp hK hQ hs hss hl hp hp' hpp'
  have hgood : ∀ {x x' : V}, omegaInvNil s x = 0 → omegaInvNil s x' = 0 → polar Q x x' = 1 →
      Q x = 1 → Q x' = 1 → eichler Q u x ∈ omegaO2Cent Q s := fun hx hx' hxx' h1 h2 =>
    eichler_mem_omegaO2Cent_of_good hQ hs hss hu hx hx' hxx' h1 h2
  have hp'cnil : omegaInvNil s (p' + c) = 0 := by rw [map_add, hp', hc, add_zero]
  rcases omegaTwo_eq_zero_or_eq_one hK (Q p) with hQp | hQp
  ·
    have hpcnil : omegaInvNil s (p + c) = 0 := by rw [map_add, hp, hc, add_zero]
    have hQpc : Q (p + c) = 1 := by
      rw [QuadraticMap.map_add Q, hQp, hQc, hpc, zero_add, add_zero]
    have e1 : eichler Q u (p + c) ∈ omegaO2Cent Q s := by
      rcases omegaTwo_map_eq_one_or hK hQc hp'c with h | h
      · exact hgood hpcnil hp' (by rw [polar_add_left, hpp', polar_comm, hp'c, add_zero]) hQpc h
      · refine hgood hpcnil hp'cnil ?_ hQpc h
        rw [polar_add_left, polar_add_right, polar_add_right, hpp', hpc, polar_comm Q c p', hp'c,
          polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul]
        simp
    have e2 : eichler Q u c ∈ omegaO2Cent Q s := by
      have hdp'nil : omegaInvNil s (d + p') = 0 := by rw [map_add, hd, hp', add_zero]
      have hdpp'nil : omegaInvNil s (d + p' + p) = 0 := by
        rw [map_add, map_add, hd, hp', hp, add_zero, add_zero]
      have hQ1 : Q (d + p') = Q d + Q p' := by
        rw [QuadraticMap.map_add Q, polar_comm Q d p', hp'd, add_zero]
      have hQ2 : Q (d + p' + p) = Q d + Q p' + 1 := by
        rw [QuadraticMap.map_add Q (d + p') p, hQ1, hQp, add_zero, polar_add_left,
          polar_comm Q d p, hpd, polar_comm Q p' p, hpp', zero_add]
      have hc1 : polar Q c (d + p') = 1 := by
        rw [polar_add_right, hcd, polar_comm, hp'c, add_zero]
      have hc2 : polar Q c (d + p' + p) = 1 := by
        rw [polar_add_right, hc1, polar_comm, hpc, add_zero]
      rcases omegaTwo_eq_zero_or_eq_one hK (Q d + Q p') with h | h
      · refine hgood hc hdpp'nil hc2 hQc ?_
        rw [hQ2, h, zero_add]
      · exact hgood hc hdp'nil hc1 hQc (hQ1.trans h)
    have e3 := mul_mem e1 e2
    rwa [eichler_mul (polar_eq_zero_of_mem_of_nil hQ hs hss hu hpcnil)
      (polar_eq_zero_of_mem_of_nil hQ hs hss hu hc), add_assoc, omegaInv_add_self K c,
      add_zero] at e3
  · rcases omegaTwo_map_eq_one_or hK hQc hp'c with h | h
    · exact hgood hp hp' hpp' hQp h
    · refine hgood hp hp'cnil ?_ hQp h
      rw [polar_add_right, hpp', hpc, add_zero]

theorem eichler_mem_omegaO2Cent_of_forall_out [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hl : 2 * finrank K (omegaInvSpace s) < finrank K V) {u : V} (hu : u ∈ omegaInvSpace s)
    (h : ∀ p, omegaInvNil s p = 0 → p ∉ omegaInvSpace s → eichler Q u p ∈ omegaO2Cent Q s)
    {z : V} (hz : z ∈ omegaInvSpace s) : eichler Q u z ∈ omegaO2Cent Q s := by
  have hzn : omegaInvNil s z = 0 := omegaInvNil_of_mem_omegaInvSpace hss hz
  obtain ⟨e, he, heW⟩ : ∃ e, omegaInvNil s e = 0 ∧ e ∉ omegaInvSpace s := by
    by_contra hc
    push Not at hc
    have hle : LinearMap.ker (omegaInvNil s) ≤ omegaInvSpace s := fun x hx =>
      hc x (LinearMap.mem_ker.1 hx)
    have h1 := Submodule.finrank_mono hle
    have h2 := LinearMap.finrank_range_add_finrank_ker (omegaInvNil s)
    change finrank K (omegaInvSpace s) + _ = _ at h2
    omega
  have hez : omegaInvNil s (e + z) = 0 := by rw [map_add, he, hzn, add_zero]
  have hezW : e + z ∉ omegaInvSpace s := fun h' => heW (by
    have := (omegaInvSpace s).sub_mem h' hz
    rwa [add_sub_cancel_right] at this)
  have hne : omegaInvNil s (-e) = 0 := by rw [map_neg, he, neg_zero]
  have hneW : -e ∉ omegaInvSpace s := fun h' => heW (by simpa using (omegaInvSpace s).neg_mem h')
  have e3 := mul_mem (h _ hez hezW) (h _ hne hneW)
  rwa [eichler_mul (polar_eq_zero_of_mem_of_nil hQ hs hss hu hez)
    (polar_eq_zero_of_mem_of_nil hQ hs hss hu hne), add_neg_cancel_comm] at e3

theorem mem_omegaO2Cent_of_forall_eichler [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hev : Even (finrank K (omegaInvSpace s)))
    (h : ∀ u ∈ omegaInvSpace s, ∀ z ∈ omegaInvSpace s, eichler Q u z ∈ omegaO2Cent Q s) :
    s ∈ omegaO2Cent Q s := by
  have h1 : s ∈ omegaEichlerGroup Q (omegaInvSpace s) :=
    mem_omegaEichlerGroup_of_even hQ _ s hs hss le_rfl hev rfl
  refine (Subgroup.closure_le _).2 ?_ h1
  rintro g ⟨u, hu, w, hw, rfl⟩
  exact h u hu w hw

theorem mem_omegaO2Cent_two_of_four_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hev : Even (finrank K (omegaInvSpace s)))
    (hl : 2 * finrank K (omegaInvSpace s) + 4 ≤ finrank K V) : s ∈ omegaO2Cent Q s :=
  mem_omegaO2Cent_of_forall_eichler hQ hs hss hev fun _ hu _ hz =>
    eichler_mem_omegaO2Cent_of_forall_out hQ hs hss (by omega) hu
      (fun _ hp hpW => eichler_mem_omegaO2Cent_of_four_le hK hQ hs hss hl hu hp hpW) hz

theorem mem_omegaO2Cent_two_of_aniso [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hev : Even (finrank K (omegaInvSpace s)))
    (hl : 2 * finrank K (omegaInvSpace s) < finrank K V)
    (hani : ∀ y, omegaInvNil s y = 0 → y ∉ omegaInvSpace s → Q y ≠ 0) : s ∈ omegaO2Cent Q s :=
  mem_omegaO2Cent_of_forall_eichler hQ hs hss hev fun _ hu _ hz =>
    eichler_mem_omegaO2Cent_of_forall_out hQ hs hss hl hu
      (fun _ hp hpW => eichler_mem_omegaO2Cent_of_aniso hQ hs hss hani hu hp hpW) hz

@[expose] def OmegaTwoHighTypeA (Q : QuadraticForm K V) (s : V ≃ₗ[K] V) : Prop :=
  (∀ w ∈ omegaInvSpace s, Q w = 0) ∧ finrank K V < 2 * finrank K (omegaInvSpace s) + 4 ∧
    (2 * finrank K (omegaInvSpace s) = finrank K V ∨
      ∃ y, omegaInvNil s y = 0 ∧ y ∉ omegaInvSpace s ∧ Q y = 0)

theorem mem_omegaO2Cent_two_of_mem_omega [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1) (hdim : 10 ≤ finrank K V) (hexc : ¬ OmegaTwoHighTypeA Q s) :
    s ∈ omegaO2Cent Q s := by
  have hs := omega_le_orthogonalGroup hsΩ
  have hev : Even (finrank K (omegaInvSpace s)) := (mem_omegaGroup.1 (omega_le_omegaGroup hQ hsΩ)).2
  have hle : 2 * finrank K (omegaInvSpace s) ≤ finrank K V := two_mul_finrank_commSpace_le hss
  by_cases h4 : 2 * finrank K (omegaInvSpace s) + 4 ≤ finrank K V
  · exact mem_omegaO2Cent_two_of_four_le hK hQ hs hss hev h4
  by_cases hC : ∃ w ∈ omegaInvSpace s, Q w ≠ 0
  · exact mem_omegaO2Cent_of_typeC_four_le hQ hs hss hC hev (by omega)
  push Not at hC
  have hlt : 2 * finrank K (omegaInvSpace s) < finrank K V := by
    by_contra hge
    exact hexc ⟨hC, by omega, Or.inl (by omega)⟩
  refine mem_omegaO2Cent_two_of_aniso hQ hs hss hev hlt fun y hy hyW hQy => ?_
  exact hexc ⟨hC, by omega, Or.inr ⟨y, hy, hyW, hQy⟩⟩

end CFSG.SeitzReduction.SymplecticPilot
