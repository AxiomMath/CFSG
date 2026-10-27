module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness

public section

namespace CFSG.ClassicalInvolution.Hat2A7E5

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

variable {X : Type*} [Group X] [Finite X]

theorem natCard_center_quotient_of_witness {L : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hw : A7Witness L) :
    Nat.card (↥L ⧸ Subgroup.center ↥L) = 2520 := by
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hZ0 : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot _
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq)
  set O : Subgroup ↥L := classicalInvolutionOddCore ↥L with hOdef
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  have h5040 : Nat.card (↥L ⧸ O) = 5040 := by
    obtain ⟨π, z, hcov, -⟩ := exists_cover_of_witness hw
    exact hcov.card_E
  have hZcen : Nat.card (Subgroup.center (↥L ⧸ O)) = 2 := hw.2.1
  have hOZ : O ≤ Z := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq O with h | h
    · exact h
    · exfalso
      have h1 : Nat.card ↥L = Nat.card (↥L ⧸ O) * Nat.card O :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup O
      have h2 : Nat.card O = Nat.card ↥L := by rw [h, Subgroup.card_top]
      have hpos : 0 < Nat.card ↥L := Nat.card_pos
      rw [h5040, h2] at h1
      omega
  let π : (↥L ⧸ O) →* (↥L ⧸ Z) := QuotientGroup.map O Z (MonoidHom.id ↥L) (fun x hx => hOZ hx)
  have hπ : ∀ x : ↥L, π (QuotientGroup.mk x) = QuotientGroup.mk x := fun x => rfl
  have hsurj : Function.Surjective π := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk x, hπ x⟩
  have hkerc : π.ker ≤ Subgroup.center (↥L ⧸ O) := by
    intro q hq1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ Z := by
      have : (QuotientGroup.mk x : ↥L ⧸ Z) = 1 := by rw [← hπ]; exact hq1
      exact (QuotientGroup.eq_one_iff x).mp this
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subgroup.mem_center_iff.mp hx w)
  have hcard : Nat.card (↥L ⧸ O) = Nat.card (↥L ⧸ Z) * Nat.card π.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker]
    exact congrArg (· * Nat.card π.ker)
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hsurj).toEquiv)
  have hkdvd : Nat.card π.ker ∣ 2 := hZcen ▸ Subgroup.card_dvd_of_le hkerc
  rcases (Nat.dvd_prime Nat.prime_two).mp hkdvd with h1 | h2
  ·
    exfalso
    have hker1 : π.ker = ⊥ := Subgroup.card_eq_one.mp h1
    have hne : Subgroup.center (↥L ⧸ O) ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hZcen
      omega
    obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hcz : π (c : ↥L ⧸ O) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := hsurj y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp c.2 w).symm]
    rw [hZ0, Subgroup.mem_bot] at hcz
    have : (c : ↥L ⧸ O) ∈ π.ker := hcz
    rw [hker1, Subgroup.mem_bot] at this
    exact hc1 (Subtype.ext this)
  · rw [h2, h5040] at hcard
    omega

end CFSG.ClassicalInvolution.Hat2A7E5
