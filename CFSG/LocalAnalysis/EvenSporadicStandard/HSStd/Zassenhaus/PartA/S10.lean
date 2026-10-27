module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Lower
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10X

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd
  CFSG.Open

section Main

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem s10_false (hHiS : Harris311HiS) (hb : PAB G L t E W z) (a : PA9 L t E z)
    (he4 : a.dcase = DCase.e4) : False := by
  have hub : a.ub = a.u := a.ub_eq
  have S : FusionSetup G L a.Abar t a.u := PA0.fusionSetup hb a.toPA0
  have hn : ¬ IsConj t a.u := by
    have := a.ub_nconj
    rwa [hub] at this
  have h5760 : Nat.card ↥(centralizer ((Vsub t a.u : Subgroup G) : Set G)) = 5760 :=
    PA0.card_cent_V hb a.toPA0
  have hTo : orderOf (t * a.u) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact S.tu_sq) ?_
    intro h1
    apply hn
    have hu : a.u = t := by
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right S.t_sq]
    rw [hu]
  have hOH : fusionOddCore ↥(Cen (t * a.u)) = ⊥ := hb.setting.1.oddCore (t * a.u) hTo
  have hKX : CFSG.SectionRank.IsKGroupCat (QuotT (t * a.u)) :=
    (hb.setting.1.isKGroupCat_centralizer_of_orderOf (n := 2) (by norm_num) hTo).quotient _
  obtain ⟨σ, hσswap, hσι⟩ := a.ub_base
  have hσ2 : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσswap.orderOf, pow_two] at this
  have hy3 : a.y * a.y * a.y = 1 := by
    have := pow_orderOf_eq_one a.y
    rw [a.y_ord] at this
    simpa [pow_succ, mul_assoc] using this
  have hty : t * a.y = a.y * t := mem_Cen.1 a.t_cy
  have huy : a.u * a.y = a.y * a.u := mem_Cen.1 (a.K₀_le a.u_mem).2
  have hrange : a.ι.range = DE4 := by
    rcases a.ι_range with h | h
    · exfalso
      have : a.dcase = DCase.d8 := a.dcase_iff.2 h
      rw [he4] at this
      exact absurd this (by decide)
    · exact h
  have hιu : a.ι (oMk (Cen a.y) ⟨a.u, mem_Cen.2 huy⟩) = base σ σ := by
    have e : (⟨a.ub, a.ub_cy⟩ : ↥(Cen a.y)) = ⟨a.u, mem_Cen.2 huy⟩ := Subtype.ext hub
    rw [← e]
    exact hσι
  let F : Five G t a.u a.y σ :=
    { tu := S.tu
      t_sq := S.t_sq
      u_sq := S.u_sq
      T_ne := by
        intro h1
        apply hn
        have hu : a.u = t := by
          rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right S.t_sq]
        rw [hu]
      y_cube := hy3
      ty := hty
      uy := huy
      σ_sq := hσ2
      ι := a.ι
      ι_inj := a.ι_inj
      ι_t := a.ι_t
      ι_u := hιu
      ι_range := hrange }
  have hyA : a.y ∈ a.Abar := derivedIn_le a.Abar a.y_J
  have hy1 : a.y ≠ 1 := by
    intro h
    have := a.y_ord
    rw [h, orderOf_one] at this
    omega
  have hnc : ∃ h : ↥(Cen (t * a.u)), (h : G) * a.y ≠ a.y * h := by
    by_contra hcon0
    have hcon : ∀ h : ↥(Cen (t * a.u)), (h : G) * a.y = a.y * h := fun h => by
      by_contra hh
      exact hcon0 ⟨h, hh⟩
    have hz : (⟨a.y, hyA⟩ : ↥a.Abar) ∈ Subgroup.center ↥a.Abar := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcon ⟨g, S.A_mem_Cen_tu g.2⟩)
    have hz' : a.eAbar ⟨a.y, hyA⟩ ∈ Subgroup.center (MulAut (alternatingGroup (Fin 6))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := Subgroup.mem_center_iff.1 hz (a.eAbar.symm g)
      have h2 := congrArg a.eAbar this
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rw [center_mulAut_eq_bot s10_nonab6, mem_bot] at hz'
    have : (⟨a.y, hyA⟩ : ↥a.Abar) = 1 := a.eAbar.injective (by rw [hz', map_one])
    exact hy1 (congrArg Subtype.val this)
  obtain ⟨hH, hup⟩ := upper_bound hHiS S hn a.eAbar hKX hOH F hnc h5760
  exact lower_contra hb a he4 hH hup

end Main

theorem s10
    (hHiS : Harris311HiS) : StepS10 := by
  intro G _ _ L t E W z hb a
  by_cases hd8 : a.dcase = DCase.d8
  · exact ⟨⟨a, hd8⟩⟩
  · exfalso
    have he4 : a.dcase = DCase.e4 := by
      cases h : a.dcase
      · exact absurd h hd8
      · rfl
    exact s10_false hHiS hb a he4

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
