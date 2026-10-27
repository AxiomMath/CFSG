module

public import CFSG.LargeExtraspecial.AS35IAbs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.Timmesfeld.Bridge.SchurNarrow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {X : Type} [Group X] {Q M : Subgroup X}

namespace AbsTI

variable (h : AbsTI X Q M)
include h

theorem mem_of_comm_classQ {x y : X} (hx : x ∈ Q) (hx1 : x ≠ 1)
    (hy : ∃ g : X, ∃ q ∈ Q, q ≠ 1 ∧ y = g * q * g⁻¹) (hc : Commute x y) : y ∈ Q ∧ y ≠ 1 := by
  obtain ⟨g, q, hq, hq1, rfl⟩ := hy
  refine ⟨h.mem_of_comm_conj hx hx1 hq hq1 hc.eq, fun h1 => hq1 ?_⟩
  calc q = g⁻¹ * (g * q * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group


theorem stronglyEmbedded [Finite X] (hQ1 : Q ≠ ⊥) (hM : M ≠ ⊤)
    (hcl : normalClosure (Q : Set X) = ⊤) : fusionStronglyEmbedded M := by
  set D : Set X := {y : X | ∃ g : X, ∃ q ∈ Q, q ≠ 1 ∧ y = g * q * g⁻¹} with hDdef
  have hN : IsNormalSet D := by
    rintro g _ ⟨k, q, hq, hq1, rfl⟩
    exact ⟨g * k, q, hq, hq1, by group⟩
  have hInv : Bridge.IsInvolutionSet D := by
    rintro _ ⟨k, q, hq, hq1, rfl⟩
    have h2 : orderOf q = 2 := orderOf_eq_prime (by rw [pow_two, h.sq q hq]) hq1
    rw [← h2]
    simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj k) q
  have hgen : closure D = ⊤ := by
    rw [eq_top_iff, ← hcl, normalClosure, closure_le]
    intro y hy
    obtain ⟨q, hq, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    by_cases hq1 : q = 1
    · rw [hq1]
      simp
    · exact subset_closure ⟨c, q, hq, hq1, rfl⟩
  have hnp : Moufang.NoPolar D := by
    rintro x ⟨g, q, hq, hq1, rfl⟩ y hy hxy hne
    have hy' : g⁻¹ * y * g ∈ D := by simpa using hN g⁻¹ y hy
    have hc : Commute q (g⁻¹ * y * g) := by
      have := (Commute.conj_iff g⁻¹).2 hxy
      simpa [mul_assoc] using this
    obtain ⟨hyQ, hy1⟩ := h.mem_of_comm_classQ hq hq1 hy' hc
    have hqy1 : q * (g⁻¹ * y * g) ≠ 1 := by
      intro h1
      apply hne
      have h2 : g⁻¹ * y * g = q := by
        have h3 : q * (g⁻¹ * y * g) = q * q := by rw [h1, h.sq q hq]
        exact mul_left_cancel h3
      calc g * q * g⁻¹ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [h2]
        _ = y := by group
    exact ⟨g, q * (g⁻¹ * y * g), Q.mul_mem hq hyQ, hqy1, by group⟩
  obtain ⟨⟨q, hq⟩, hq1⟩ := (ne_bot_iff_exists_ne_one).1 hQ1
  have hq1' : q ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
  have hqD : q ∈ D := ⟨1, q, hq, hq1', by group⟩
  have hreach : ∀ y, Reach D q y → y ∈ Q ∧ y ≠ 1 := by
    intro y hy
    refine mem_of_reach (S := {w | w ∈ Q ∧ w ≠ 1}) ?_ ⟨hq, hq1'⟩ hy
    intro w hw y' hy' hc
    exact h.mem_of_comm_classQ hw.1 hw.2 hy' hc
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hM (eq_top_iff.2 fun g _ => hcon g)
  have hdisc : Disconnected D := by
    refine ⟨q, hqD, g * q * g⁻¹, ⟨g, q, hq, hq1', rfl⟩, fun hr => ?_⟩
    exact hg (h.ti g q hq hq1' (hreach _ hr).1)
  have hSE := Bridge.asc73For_of CFSG.ShultStronglyClosedTI.theoremTwo
    Bridge.schurNarrowInput X D hN hInv hgen hnp hdisc q hqD
  have hstab : compStab hN q = M := by
    ext k
    rw [mem_compStab_iff]
    constructor
    · intro hk
      exact h.ti k q hq hq1' (hreach _ hk).1
    · intro hk
      have hkq : k * q * k⁻¹ ∈ Q := h.norm k hk q hq
      exact reach_of_commute hqD ⟨k, q, hq, hq1', rfl⟩ (h.comm q hq _ hkq)
  rw [hstab] at hSE
  exact (Bridge.fusionStronglyEmbedded_iff M).2 hSE

end AbsTI

end CFSG.LargeExtraspecial.Asc22
