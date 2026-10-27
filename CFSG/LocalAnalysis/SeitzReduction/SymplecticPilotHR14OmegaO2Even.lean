module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaO2
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace natCast_finrank_commSpace_mul
  natCast_finrank_commSpace_one natCast_finrank_commSpace_inv omegaGroup mem_omegaGroup
  suzukiLetter suzukiLetter_eq_b_iff)
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem omegaInvSpace_eq_commSpace (s : V ≃ₗ[K] V) : omegaInvSpace s = commSpace s :=
  rfl

theorem omegaInv_exists_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {u : V} (hu : u ≠ 0) :
    ∃ x, polar Q x u = 1 := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu
  refine ⟨(polar Q u y)⁻¹ • y, ?_⟩
  rw [polar_smul_left_eq, polar_comm Q y u, inv_mul_cancel₀ hy]

theorem omegaInv_exists_polar_eq_zero_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {u w : V}
    (hu : u ≠ 0) (hw : ∀ c : K, w ≠ c • u) : ∃ x, polar Q x u = 0 ∧ polar Q x w = 1 := by
  obtain ⟨x₀, hx₀⟩ := omegaInv_exists_polar_eq_one hQ hu
  by_contra hc
  push Not at hc
  have hc' : ∀ x, polar Q x u = 0 → polar Q x w = 0 := by
    intro x hx
    by_contra hxw
    apply hc ((polar Q x w)⁻¹ • x) (by rw [polar_smul_left_eq, hx, mul_zero])
    rw [polar_smul_left_eq, inv_mul_cancel₀ hxw]
  apply hw (polar Q x₀ w)
  have h0 : w - polar Q x₀ w • u = 0 := by
    apply eq_zero_of_polar_eq_zero hQ
    intro x
    have h1 := hc' (x - polar Q x u • x₀)
      (by rw [polar_sub_left, polar_smul_left_eq, hx₀, mul_one, sub_self])
    rw [polar_sub_left, polar_smul_left_eq] at h1
    rw [polar_sub_left, polar_smul_left_eq, polar_comm Q w x, polar_comm Q u x]
    linear_combination h1
  exact sub_eq_zero.1 h0

theorem omegaInv_even_finrank_commSpace_one : Even (finrank K (commSpace (1 : V ≃ₗ[K] V))) := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  exact natCast_finrank_commSpace_one

theorem even_finrank_commSpace_eichler [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (u w : V) :
    Even (finrank K (commSpace (eichler Q u w))) := by
  by_cases hu : Q u = 0
  swap
  · rw [eichler_of_map_ne_zero hu]
    exact omegaInv_even_finrank_commSpace_one
  by_cases huw : polar Q u w = 0
  swap
  · rw [eichler_of_polar_ne_zero huw]
    exact omegaInv_even_finrank_commSpace_one
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact omegaInv_even_finrank_commSpace_one
  by_cases hwu : ∃ c : K, w = c • u
  · obtain ⟨c, rfl⟩ := hwu
    rw [show c • u = 0 + c • u by rw [zero_add], eichler_add_smul_self hu, eichler_zero_right]
    exact omegaInv_even_finrank_commSpace_one
  push Not at hwu
  obtain ⟨x, hxu, hxw⟩ := omegaInv_exists_polar_eq_zero_polar_eq_one hQ hu0 hwu
  obtain ⟨x₀, hx₀⟩ := omegaInv_exists_polar_eq_one hQ hu0
  obtain ⟨x', hx'u, hx'w⟩ : ∃ x', polar Q x' u = 1 ∧ polar Q x' w = 0 :=
    ⟨x₀ - polar Q x₀ w • x, by
      rw [polar_sub_left, polar_smul_left_eq, hxu, hx₀, mul_zero, sub_zero], by
      rw [polar_sub_left, polar_smul_left_eq, hxw, mul_one, sub_self]⟩
  have huC : u ∈ commSpace (eichler Q u w) := by
    refine mem_commSpace.2 ⟨-x, ?_⟩
    rw [map_neg, eichler_apply hu huw, hxu, hxw]
    module
  have hwC : w - Q w • u ∈ commSpace (eichler Q u w) := by
    refine mem_commSpace.2 ⟨x', ?_⟩
    rw [eichler_apply hu huw, hx'u, hx'w]
    module
  have hspan : commSpace (eichler Q u w) = Submodule.span K {u, w} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨z, rfl⟩ := mem_commSpace.1 hv
      rw [eichler_apply hu huw,
        show z + polar Q z u • w - (polar Q z w + Q w * polar Q z u) • u - z =
          polar Q z u • w - (polar Q z w + Q w * polar Q z u) • u by abel]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · rw [Submodule.span_le]
      intro v hv
      rcases hv with rfl | hv
      · exact huC
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        have := (commSpace (eichler Q u v)).add_mem hwC
          ((commSpace (eichler Q u v)).smul_mem (Q v) huC)
        rwa [sub_add_cancel] at this
  have hli : LinearIndependent K ![u, w] :=
    (LinearIndependent.pair_iff' hu0).2 fun a h => hwu a h.symm
  have h2 := finrank_span_eq_card hli
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at h2
  rw [hspan, h2, Fintype.card_fin]
  exact even_two

theorem omegaInv_exists_ne_zero_singular [Finite K] [CharP K 2] [FiniteDimensional K V]
    {W : Submodule K V} (hW : ∀ v ∈ W, ∀ w ∈ W, polar Q v w = 0) (h2 : 2 ≤ finrank K W) :
    ∃ u ∈ W, u ≠ 0 ∧ Q u = 0 := by
  obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W) (by
    intro h
    rw [h, finrank_bot] at h2
    omega)
  obtain ⟨v₂, hv₂, hv₂'⟩ : ∃ v₂ ∈ W, v₂ ∉ K ∙ v₁ := by
    by_contra hc
    push Not at hc
    have h1 := Submodule.finrank_mono (show W ≤ K ∙ v₁ from hc)
    rw [finrank_span_singleton hv₁0] at h1
    omega
  by_cases hQ1 : Q v₁ = 0
  · exact ⟨v₁, hv₁, hv₁0, hQ1⟩
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v₂ / Q v₁)
  refine ⟨v₂ + c • v₁, W.add_mem hv₂ (W.smul_mem c hv₁), ?_, ?_⟩
  · intro h
    apply hv₂'
    have e : v₂ = (-c) • v₁ := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, h]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₁)
  · rw [QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, hW _ hv₂ _ hv₁, mul_zero,
      add_zero, _root_.sq, ← hc, div_mul_cancel₀ _ hQ1]
    exact CharTwo.add_self_eq_zero _

theorem exists_eichler_reduction [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1) {u : V}
    (huW : u ∈ omegaInvSpace s) (hu0 : u ≠ 0) (hQu : Q u = 0) :
    ∃ w ∈ omegaInvSpace s, s * eichler Q u w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (s * eichler Q u w) * (s * eichler Q u w) = 1 ∧
      (∀ x, omegaInvNil (s * eichler Q u w) x =
        omegaInvNil s x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u) ∧
      omegaInvSpace (s * eichler Q u w) < omegaInvSpace s ∧
      ((finrank K (omegaInvSpace (s * eichler Q u w)) : ZMod 2) =
        finrank K (omegaInvSpace s)) ∧
      s = (s * eichler Q u w) * eichler Q u w := by
  obtain ⟨x₂, h21⟩ := omegaInv_exists_polar_eq_one hQ hu0
  have h12 : polar Q u x₂ = 1 := by rw [polar_comm, h21]
  set w := omegaInvNil s x₂ with hw
  have hwW : w ∈ omegaInvSpace s := omegaInvNil_mem_omegaInvSpace s x₂
  have hpuw : polar Q u w = 0 := polar_of_mem_omegaInvSpace hs hss huW hwW
  set E := eichler Q u w with hE
  have hEO : E ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q u w
  have hsE : s * E = E * s := by
    have e := eichler_conj hs u w
    rw [apply_of_mem_omegaInvSpace hss huW, apply_of_mem_omegaInvSpace hss hwW] at e
    calc s * E = (s * E * s⁻¹) * s := by group
      _ = E * s := by rw [e]
  have hEE : E * E = 1 := by
    rw [hE, eichler_mul hpuw hpuw, omegaInv_add_self K, eichler_zero_right]
  have hs's' : (s * E) * (s * E) = 1 := by
    calc (s * E) * (s * E) = s * (E * s) * E := by group
      _ = s * (s * E) * E := by rw [hsE]
      _ = (s * s) * (E * E) := by group
      _ = 1 := by rw [hss, hEE, one_mul]
  have hs'O : s * E ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hs hEO
  have hpar : ((finrank K (omegaInvSpace (s * E)) : ZMod 2) = finrank K (omegaInvSpace s)) := by
    have hd := natCast_finrank_commSpace_mul hQ hs hEO
    rw [← omegaInvSpace_eq_commSpace, ← omegaInvSpace_eq_commSpace,
      ZMod.natCast_eq_zero_iff_even.2 (even_finrank_commSpace_eichler hQ u w), add_zero] at hd
    exact hd
  have hN' : ∀ x, omegaInvNil (s * E) x =
      omegaInvNil s x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u := by
    intro x
    rw [omegaInvNil_apply, omegaInvNil_apply, LinearEquiv.mul_apply, hE,
      eichler_apply hQu hpuw, map_sub, map_add, map_smul, map_smul,
      apply_of_mem_omegaInvSpace hss huW, apply_of_mem_omegaInvSpace hss hwW]
    abel
  have hle : omegaInvSpace (s * E) ≤ omegaInvSpace s := by
    intro v hv
    obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hv
    rw [hN']
    exact (omegaInvSpace s).sub_mem ((omegaInvSpace s).add_mem
      (omegaInvNil_mem_omegaInvSpace s x) ((omegaInvSpace s).smul_mem _ hwW))
      ((omegaInvSpace s).smul_mem _ huW)
  have hx₂' : omegaInvNil (s * E) x₂ = 0 := by
    have h22 : polar Q x₂ w = Q w := by
      rw [hw, ← map_omegaInvNil hs]
    rw [hN', h21, h22, one_smul, mul_one, ← hw, CharTwo.add_self_eq_zero, zero_smul, sub_zero,
      omegaInv_add_self K]
  have hu' : u ∉ omegaInvSpace (s * E) := by
    intro hu'
    obtain ⟨y, hy⟩ := mem_omegaInvSpace_iff.1 hu'
    have e := polar_omegaInvNil_left hs'O hs's' y x₂
    rw [hx₂', polar_zero_right, hy, h12] at e
    exact one_ne_zero e
  refine ⟨w, hwW, hs'O, hs's', hN', lt_of_le_of_ne hle fun h => hu' (h ▸ huW), hpar, ?_⟩
  rw [mul_assoc, hEE, mul_one]

theorem two_le_finrank_of_even_of_ne [FiniteDimensional K V] {s : V ≃ₗ[K] V}
    (hev : Even (finrank K (omegaInvSpace s)))
    {x : V} (hx : omegaInvNil s x ≠ 0) : 2 ≤ finrank K (omegaInvSpace s) := by
  have hpos : finrank K (omegaInvSpace s) ≠ 0 := by
    intro h
    rw [Submodule.finrank_eq_zero] at h
    have := omegaInvNil_mem_omegaInvSpace s x
    rw [h, Submodule.mem_bot] at this
    exact hx this
  obtain ⟨j, hj⟩ := hev
  omega

theorem mem_omegaEichlerGroup_of_even [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {W : Submodule K V} (r : ℕ) :
    ∀ s : V ≃ₗ[K] V, s ∈ TauCeti.QuadraticMap.orthogonalGroup Q → s * s = 1 →
      omegaInvSpace s ≤ W → Even (finrank K (omegaInvSpace s)) →
        finrank K (omegaInvSpace s) = r → s ∈ omegaEichlerGroup Q W := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro s hs hss hsW hev hr
  by_cases h0 : ∀ x, omegaInvNil s x = 0
  · rw [eq_one_of_omegaInvNil_eq_zero h0]
    exact Subgroup.one_mem _
  push Not at h0
  obtain ⟨x₁, hx₁⟩ := h0
  obtain ⟨u, huW, hu0, hQu⟩ := omegaInv_exists_ne_zero_singular
    (fun v hv w hw => polar_of_mem_omegaInvSpace hs hss hv hw)
    (two_le_finrank_of_even_of_ne hev hx₁)
  obtain ⟨w, hwW, hs'O, hs's', -, hlt', hpar, he⟩ := exists_eichler_reduction hQ hs hss huW hu0 hQu
  have hev' : Even (finrank K (omegaInvSpace (s * eichler Q u w))) := by
    rw [← ZMod.natCast_eq_zero_iff_even, hpar, ZMod.natCast_eq_zero_iff_even]
    exact hev
  have hlt : finrank K (omegaInvSpace (s * eichler Q u w)) < r := by
    rw [← hr]
    exact Submodule.finrank_lt_finrank_of_lt hlt'
  have hs'W := ih _ hlt _ hs'O hs's' (hlt'.le.trans hsW) hev' rfl
  rw [he]
  exact mul_mem hs'W (eichler_mem_omegaEichlerGroup (hsW huW) (hsW hwW))

theorem mem_omegaO2Cent_of_even [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hev : Even (finrank K (omegaInvSpace s)))
    (hl : 2 * finrank K (omegaInvSpace s) < finrank K V) : s ∈ omegaO2Cent Q s := by
  have h1 : s ∈ omegaEichlerGroup Q (omegaInvSpace s) :=
    mem_omegaEichlerGroup_of_even hQ _ s hs hss le_rfl hev rfl
  refine (Subgroup.closure_le _).2 ?_ h1
  rintro g ⟨u, hu, w, hw, rfl⟩
  exact eichler_mem_omegaO2Cent hK hQ hs hss hl hu (omegaInvNil_of_mem_omegaInvSpace hss hw)

theorem omega_le_omegaGroup [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      omegaGroup Q hQ := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  refine ⟨Subgroup.commutator_mem_commutator hg hh |> omega_le_orthogonalGroup, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, commutatorElement_def,
    natCast_finrank_commSpace_mul hQ (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    natCast_finrank_commSpace_mul hQ (mul_mem hg hh) (inv_mem hg),
    natCast_finrank_commSpace_mul hQ hg hh, natCast_finrank_commSpace_inv hQ hg,
    natCast_finrank_commSpace_inv hQ hh]
  have e1 : ((finrank K (commSpace g) : ℕ) : ZMod 2) + finrank K (commSpace g) = 0 :=
    CharTwo.add_self_eq_zero _
  have e2 : ((finrank K (commSpace h) : ℕ) : ZMod 2) + finrank K (commSpace h) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination e1 + e2

theorem mem_omegaO2Cent_of_mem_omega [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1) (hl : 2 * finrank K (omegaInvSpace s) < finrank K V) :
    s ∈ omegaO2Cent Q s :=
  mem_omegaO2Cent_of_even hK hQ (omega_le_orthogonalGroup hsΩ) hss
    (mem_omegaGroup.1 (omega_le_omegaGroup hQ hsΩ)).2 hl

theorem mem_closure_odd_centralizer_of_mem_omega [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hK : 4 ≤ Nat.card K) (hQ : (polarBilin Q).Nondegenerate)
    (s : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1)
    (hl : 2 * finrank K (omegaInvSpace (s : V ≃ₗ[K] V)) < finrank K V) :
    s ∈ Subgroup.closure {x | x ∈ Subgroup.centralizer {s} ∧ Odd (orderOf x)} :=
  mem_closure_odd_centralizer_omega s.2
    (mem_omegaO2Cent_of_mem_omega hK hQ s.2 (congrArg Subtype.val hss) hl)

end CFSG.SeitzReduction.SymplecticPilot
