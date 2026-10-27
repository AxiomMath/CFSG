module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Position

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {fr fr' frY : OFrame Q}

theorem position_of_commutator_eq {t t' : V ≃ₗ[F] V} (ht : t * t = 1) (ht' : t' * t' = 1)
    (h : t * t' * t⁻¹ * t'⁻¹ = 1 ∨ t * t' * t⁻¹ * t'⁻¹ = LinearEquiv.neg F) :
    (∀ x, t' (t x) = t (t' x)) ∨ (∀ x, t' (t x) = -t (t' x)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hti' : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'
  rw [hti, hti'] at h
  rcases h with h | h
  · left
    intro x
    have h1 : t * t' = t' * t := by
      have h2 : (t * t') * (t * t') = 1 := by
        rw [← h]
        group
      rw [eq_inv_of_mul_eq_one_left h2, mul_inv_rev, hti, hti']
    have := congrArg (fun T : V ≃ₗ[F] V => T x) h1
    exact this.symm
  · right
    intro y
    have h1 : ∀ x, t (t' (t (t' x))) = -x := fun x => by
      have := congrArg (fun T : V ≃ₗ[F] V => T x) h
      simpa [LinearEquiv.mul_apply] using this
    have h2 : ∀ x, t (t x) = x := fun x => by
      have := congrArg (fun T : V ≃ₗ[F] V => T x) ht
      exact this
    have h3 : ∀ x, t' (t (t' x)) = -t x := fun x => by
      have := congrArg t (h1 x)
      rw [h2, map_neg] at this
      exact this
    have h4 : ∀ x, t' (t' x) = x := fun x => by
      have := congrArg (fun T : V ≃ₗ[F] V => T x) ht'
      exact this
    have := h3 (t' y)
    rwa [h4] at this

theorem elementaryGroup_le_of_position [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V = 8) (hY : frY.span = fr.perp) {G : Subgroup (V ≃ₗ[F] V)}
    (h₁ : omegaGrp fr ≤ G) (h₃ : omegaGrp frY ≤ G) (h' : omegaGrp fr' ≤ G)
    (hne1 : fr'.span ≠ fr.span) (hne2 : fr'.span ≠ fr.perp)
    (hpos : (∀ x, fr'.La (-1) (fr.La (-1) x) = fr.La (-1) (fr'.La (-1) x)) ∨
      (∀ x, fr'.La (-1) (fr.La (-1) x) = -fr.La (-1) (fr'.La (-1) x))) :
    elementaryGroup Q ≤ G :=
  hpos.elim (case_comm h2 hdim hY h₁ h₃ h' hne1 hne2) (case_swap h2 hY h₁ h₃ h')

end Position

section Model

variable {F : Type} [Field F] [Finite F]

theorem D4Facts.mul_self_eq_one_of_central (hF : D4Facts F)
    {R : Subgroup (spinGroup (quadPlus 4 F))} (hR : R ∈ fundD4 F) {fr : OFrame (quadPlus 4 F)}
    (hfr : R.map (spinAction (quadPlus 4 F)) = fr.La.range) {c : spinGroup (quadPlus 4 F)}
    (hc : c ∈ R) (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) : c * c = 1 := by
  have hθc := hF.theta_central hR hfr hc hz h1
  have h0 : spinAction (quadPlus 4 F) (c * c) = 1 := by
    rw [map_mul, hθc]
    exact Frame.La_neg_one_mul_self fr
  exact spinAction_injOn_fund hF.odd (by norm_num) hF.single hF.perf hF.long hF.sl2 hR
    (R.mul_mem hc hc) h0

theorem sq_commutator_eq_one {G : Type*} [Group G] {c c' : G} (hcc : c * c = 1)
    (hcc' : c' * c' = 1) (hz : c * c' * c⁻¹ * c'⁻¹ ∈ Subgroup.center G) :
    (c * c' * c⁻¹ * c'⁻¹) * (c * c' * c⁻¹ * c'⁻¹) = 1 := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hci' : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right hcc'
  rw [hci, hci'] at hz ⊢
  have hc' := Subgroup.mem_center_iff.mp hz c'
  have h1 : c' * (c * c' * c * c') * c' = c' * c * c' * c := by
    calc c' * (c * c' * c * c') * c' = c' * c * c' * c * (c' * c') := by group
      _ = c' * c * c' * c := by rw [hcc', mul_one]
  have h2 : c' * (c * c' * c * c') * c' = c * c' * c * c' := by
    calc c' * (c * c' * c * c') * c' = (c * c' * c * c') * c' * c' := by rw [hc']
      _ = c * c' * c * c' := by rw [mul_assoc, hcc', mul_one]
  have h3 : c * c' * c * c' = c' * c * c' * c := h2.symm.trans h1
  calc (c * c' * c * c') * (c * c' * c * c') = (c * c' * c * c') * (c' * c * c' * c) := by
        rw [← h3]
    _ = c * c' * c * (c' * c') * c * c' * c := by group
    _ = c * c' * (c * c) * c' * c := by rw [hcc']; group
    _ = c * (c' * c') * c := by rw [hcc]; group
    _ = 1 := by rw [hcc', mul_one, hcc]

theorem D4Facts.generate_of_comm (hF : D4Facts F)
    {R R' : Subgroup (spinGroup (quadPlus 4 F))} (hR : R ∈ fundD4 F) (hR' : R' ∈ fundD4 F)
    (hne : R' ≠ R) (hnc : ¬ Commutes R R') {c c' : spinGroup (quadPlus 4 F)} (hc : c ∈ R)
    (hcz : ∀ r ∈ R, c * r = r * c) (hc1 : c ≠ 1) (hc' : c' ∈ R') (hcz' : ∀ r ∈ R', c' * r = r * c')
    (hc1' : c' ≠ 1) (hcomm : c * c' * c⁻¹ * c'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 F))) :
    (⨆ S ∈ {S : Subgroup (spinGroup (quadPlus 4 F)) |
      S ∈ fundD4 F ∧ (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S) = ⊤ := by
  classical
  have h2 := hF.two_ne_zero
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hdim := finrank_quadPlus_four (F := F)
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup (quadPlus 4 F)) := isPerfect_spinGroup_quadPlus hn3
  obtain ⟨fr, hfr⟩ := hF.exists_frame hR
  obtain ⟨fr', hfr'⟩ := hF.exists_frame hR'
  obtain ⟨frY, hY⟩ := exists_frame_span_eq_perp hF.odd fr
  obtain ⟨R₁, hR₁, hθR₁⟩ := hF.exists_fund_of_frame fr.swap
  obtain ⟨R₂, hR₂, hθR₂⟩ := hF.exists_fund_of_frame frY
  obtain ⟨R₃, hR₃, hθR₃⟩ := hF.exists_fund_of_frame frY.swap
  obtain ⟨R₄, hR₄, hθR₄⟩ := hF.exists_fund_of_frame fr'.swap
  have horth : ∀ X Y, polar (quadPlus 4 F) (fr.incl X) (frY.incl Y) = 0 := fun X Y =>
    polar_eq_zero_of_span_eq_perp hY ⟨X, rfl⟩ ⟨Y, rfl⟩
  have horth' : ∀ X Y, polar (quadPlus 4 F) (fr.incl X) (frY.swap.incl Y) = 0 := fun X Y => by
    rw [Frame.incl_swap]
    exact horth X _
  have hC₁ : Commutes R₁ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₁] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_La_swap fr A B).symm
  have hC₂ : Commutes R₂ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₂] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_of_orth horth A B).symm
  have hC₃ : Commutes R₃ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₃] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_of_orth horth' A B).symm
  have hC₄ : Commutes R₄ R' := hF.commutes_of_map_commute hR' fun a ha b hb => by
    rw [hθR₄] at ha
    rw [hfr'] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_La_swap fr' A B).symm
  have hθc := hF.theta_central hR hfr hc hcz hc1
  have hθc' := hF.theta_central hR' hfr' hc' hcz' hc1'
  have hcc := hF.mul_self_eq_one_of_central hR hfr hc hcz hc1
  have hcc' := hF.mul_self_eq_one_of_central hR' hfr' hc' hcz' hc1'
  have hw2 := sq_commutator_eq_one hcc hcc' hcomm
  have hθw : spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) =
      fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hθc, hθc']
  have hmemE : spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) ∈
      elementaryGroup (quadPlus 4 F) := by
    rw [← range_spinAction_quadPlus (by norm_num)]
    exact ⟨_, rfl⟩
  let zz : ↥(elementaryGroup (quadPlus 4 F)) := ⟨_, hmemE⟩
  have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 F)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hu : (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) ∈
        (spinAction (quadPlus 4 F)).range := by
      rw [range_spinAction_quadPlus (by norm_num)]
      exact u.2
    obtain ⟨y, hy⟩ := hu
    apply Subtype.ext
    show (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) *
      spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) =
        spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) *
          (u : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F))
    rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hcomm y)]
  have hz2 : zz * zz = 1 := Subtype.ext (by
    show spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) *
      spinAction (quadPlus 4 F) (c * c' * c⁻¹ * c'⁻¹) = 1
    rw [← map_mul, hw2, map_one])
  have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := F)
    (n := 4) (by norm_num)
  have hcomm' : fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ = 1 ∨
      fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ = LinearEquiv.neg F := by
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · left
      rw [← hθw]
      exact congrArg Subtype.val h
    · right
      rw [← hθw]
      exact h
  have hpos := position_of_commutator_eq (Frame.La_neg_one_mul_self fr)
    (Frame.La_neg_one_mul_self fr') hcomm'
  have hne1 : fr'.span ≠ fr.span := by
    intro hs
    rcases Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hs) with h | h
    · exact hne (hF.eq_of_map_eq hR' hR (hfr'.trans (h.trans hfr.symm)))
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_La_swap fr A B).symm
  have hne2 : fr'.span ≠ fr.perp := by
    intro hs
    rw [← hY] at hs
    rcases Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hs) with h | h
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_of_orth horth A B).symm
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_of_orth horth' A B).symm
  set T : Subgroup (spinGroup (quadPlus 4 F)) := ⨆ S ∈ {S : Subgroup (spinGroup (quadPlus 4 F)) |
      S ∈ fundD4 F ∧ (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S with hT
  have hmemT : ∀ S ∈ fundD4 F, (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R') → S ≤ T :=
    fun S hS hS' => le_iSup₂_of_le S ⟨hS, hS'⟩ le_rfl
  have hle : ∀ (fr₀ : OFrame (quadPlus 4 F)) (S : Subgroup (spinGroup (quadPlus 4 F))),
      S.map (spinAction (quadPlus 4 F)) = fr₀.La.range → S ≤ T →
      fr₀.La.range ≤ T.map (spinAction (quadPlus 4 F)) := fun fr₀ S hS hST =>
    hS ▸ Subgroup.map_mono hST
  have h₁ : omegaGrp fr ≤ T.map (spinAction (quadPlus 4 F)) :=
    sup_le (hle fr R hfr (hmemT R hR (Or.inl rfl)))
      (hle fr.swap R₁ hθR₁ (hmemT R₁ hR₁ (Or.inr (Or.inl hC₁))))
  have h₃ : omegaGrp frY ≤ T.map (spinAction (quadPlus 4 F)) :=
    sup_le (hle frY R₂ hθR₂ (hmemT R₂ hR₂ (Or.inr (Or.inl hC₂))))
      (hle frY.swap R₃ hθR₃ (hmemT R₃ hR₃ (Or.inr (Or.inl hC₃))))
  have h' : omegaGrp fr' ≤ T.map (spinAction (quadPlus 4 F)) :=
    sup_le (hle fr' R' hfr' (hmemT R' hR' (Or.inr (Or.inr (Or.inl rfl)))))
      (hle fr'.swap R₄ hθR₄ (hmemT R₄ hR₄ (Or.inr (Or.inr (Or.inr hC₄)))))
  have hE := elementaryGroup_le_of_position h2 hdim hY h₁ h₃ h' hne1 hne2 hpos
  exact eq_top_of_range_le_map (spinAction (quadPlus 4 F)) (ker_spinAction_le_center _)
    ((range_spinAction_quadPlus hn3).le.trans hE)

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
