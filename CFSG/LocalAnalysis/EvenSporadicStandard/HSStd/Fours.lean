module

public import CFSG.Sporadic.SmallOddCore.HSAut
public import Certificates.Certificate25370

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier CFSG.EvenSporadicStandard.HypOne

theorem center_hsP :
    center hsP = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 3850)) ∈
      Subgroup.centralizer (hsP : Set (Equiv.Perm (Fin 3850))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [hs_centralizer_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem class_data_hs :
    tp 3850 rho0 ∈ hsP ∧ tp 3850 rho1 ∈ hsP ∧ tp 3850 rho2 ∈ hsR ∧ tp 3850 rho2 ∉ hsP ∧
      tp 3850 rho3 ∈ hsR ∧ tp 3850 rho3 ∉ hsP ∧
      ∀ v ∈ hsR, orderOf v = 2 → ∃ g ∈ hsP, v = g * tp 3850 rho0 * g⁻¹ ∨
        v = g * tp 3850 rho1 * g⁻¹ ∨ v = g * tp 3850 rho2 * g⁻¹ ∨ v = g * tp 3850 rho3 * g⁻¹ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨-, -, h0o, -⟩ := hrows _ List.mem_cons_self
  obtain ⟨-, -, h1o, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨h2R, -, h2o, -⟩ := hrows _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨h3R, -, h3o, -⟩ := hrows _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  dsimp only at h0o h1o h2R h2o h3R h3o
  have h0 : tp 3850 rho0 ∈ hsP := by
    by_contra h
    exact Bool.false_ne_true (h0o.2 h)
  have h1 : tp 3850 rho1 ∈ hsP := by
    by_contra h
    exact Bool.false_ne_true (h1o.2 h)
  refine ⟨h0, h1, h2R, h2o.1 rfl, h3R, h3o.1 rfl, fun v hv hv2 => ?_⟩
  obtain ⟨r, hr, g, hg, hv'⟩ := hcover v hv hv2
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr
  · exact ⟨g, hg, Or.inl (by rw [hv', hr])⟩
  · exact ⟨g, hg, Or.inr (Or.inl (by rw [hv', hr]))⟩
  · exact ⟨g, hg, Or.inr (Or.inr (Or.inl (by rw [hv', hr])))⟩
  · exact ⟨g, hg, Or.inr (Or.inr (Or.inr (by rw [hv', hr])))⟩

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.HS := by
  obtain ⟨e, he, -, -, -⟩ := hs_full_automorphism_model
  obtain ⟨h0, h1, hR2, hP2, hR3, hP3, hcover⟩ := class_data_hs
  have h4 := Certificates.certificate25370
  simp only [foursData, Bool.and_eq_true] at h4
  obtain ⟨h2, h3⟩ := h4
  obtain ⟨l2, hl2P, hl2⟩ := foursWit_spec hs_groupData h2
  obtain ⟨l3, hl3P, hl3⟩ := foursWit_spec hs_groupData h3
  refine foursGroupCondition_of_outTwo hsPermEquiv center_hsP le_sup_left e he
    [⟨tp 3850 rho2, hR2⟩, ⟨tp 3850 rho3, hR3⟩] (fun τ hτ hτP => ?_) (fun ρ hρ => ?_)
  · obtain ⟨g, hg, hv⟩ := hcover τ τ.2 hτ
    rcases hv with hv | hv | hv | hv
    · exfalso
      apply hτP
      rw [hv]
      exact hsP.mul_mem (hsP.mul_mem hg h0) (hsP.inv_mem hg)
    · exfalso
      apply hτP
      rw [hv]
      exact hsP.mul_mem (hsP.mul_mem hg h1) (hsP.inv_mem hg)
    · exact ⟨⟨tp 3850 rho2, hR2⟩, List.mem_cons_self, g, hg, hv⟩
    · exact ⟨⟨tp 3850 rho3, hR3⟩, List.mem_cons_of_mem _ List.mem_cons_self, g, hg, hv⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · exact ⟨l2, hl2P, hl2⟩
    · exact ⟨l3, hl3P, hl3⟩

theorem foursGroupCondition_of_isSporadic_hs
    {Y : Type} [Group Y] (h : IsSporadic Y .HS) :
    CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

end CFSG.EvenSporadicStandard.HSStd
