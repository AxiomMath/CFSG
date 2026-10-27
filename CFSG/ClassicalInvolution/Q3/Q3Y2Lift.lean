module

public import CFSG.ClassicalInvolution.Balance.BootstrapGeneration

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG.Open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Balance (oddCoreIn)
open CFSG.ClassicalInvolution.Balance.Bootstrap (map_inf_centralizer_eq isPGroup_two_of_sq_eq_one)

section Lift

variable {G : Type} [Group G] [Finite G] (Y : Subgroup G)

theorem odd_card_ker_mk :
    Odd (Nat.card (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)).ker) := by
  rw [QuotientGroup.ker_mk']
  exact CFSG.ComponentClassification.OddCore.odd_card ↥Y

theorem centralizer_mk_le {f : G} (hf : f ∈ Y) (hf2 : f * f = 1)
    {q : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hq : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hf⟩ * q =
      q * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hf⟩) :
    ∃ y : ↥Y, (y : G) * f = f * (y : G) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y = q := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set E : Subgroup ↥Y := Subgroup.zpowers (⟨f, hf⟩ : ↥Y) with hE
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hsq : (⟨f, hf⟩ : ↥Y) * ⟨f, hf⟩ = 1 := Subtype.ext hf2
    have hcomm : Commute ((⟨f, hf⟩ : ↥Y) ^ k) ((⟨f, hf⟩ : ↥Y) ^ k) := Commute.refl _
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hsq, one_zpow]
  have hnorm : E ≤ Subgroup.normalizer ((⊤ : Subgroup ↥Y) : Set ↥Y) := fun x _ =>
    (Subgroup.mem_normalizer_iff).mpr fun h => by simp
  have key := map_inf_centralizer_eq π (odd_card_ker_mk Y) E ⊤ (isPGroup_two_of_sq_eq_one hE2)
    hnorm
  have hqmem : q ∈ (⊤ : Subgroup ↥Y).map π ⊓ Subgroup.centralizer (E.map π : Set _) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨y, trivial, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hq' : q * π ⟨f, hf⟩ = π ⟨f, hf⟩ * q := hq.symm
      have : q * π ⟨f, hf⟩ ^ k = π ⟨f, hf⟩ ^ k * q :=
        ((Commute.zpow_right (show Commute q (π ⟨f, hf⟩) from hq') k))
      rw [map_zpow]
      exact this.symm
  rw [← key] at hqmem
  obtain ⟨y, ⟨-, hyE⟩, hyq⟩ := hqmem
  refine ⟨y, ?_, hyq⟩
  have := Subgroup.mem_centralizer_iff.mp hyE ⟨f, hf⟩ (Subgroup.mem_zpowers _)
  have h2 : (⟨f, hf⟩ : ↥Y) * y = y * ⟨f, hf⟩ := this
  exact (congrArg Subtype.val h2).symm

omit [Finite G] in
theorem oddCoreIn_sup_of_range_le {J : Subgroup G}
    (h : ∀ y : ↥Y, ∃ j : ↥Y, (j : G) ∈ J ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) j =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y) :
    Y ≤ oddCoreIn Y ⊔ J := by
  intro y hy
  obtain ⟨j, hjJ, hj⟩ := h ⟨y, hy⟩
  have h1 : (j⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ classicalInvolutionOddCore ↥Y :=
    QuotientGroup.eq.mp hj
  have hodd : (j : G)⁻¹ * y ∈ oddCoreIn Y := ⟨_, h1, rfl⟩
  have hmem : (j : G) * ((j : G)⁻¹ * y) ∈ J ⊔ oddCoreIn Y := Subgroup.mul_mem_sup hjJ hodd
  rwa [mul_inv_cancel_left, sup_comm] at hmem

end Lift

end CFSG.ClassicalInvolution.Q3.Q3Y2
