module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInvol

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKM

variable {X : Type} [Group X] [Finite X]

theorem exists_center_mul_of_involution
    {L : Subgroup X} (hset : HeldEndSetting X L) {a : X} (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X)) {u : X} (hu : HeldTwoA L u) {n : X} (hn : n * n = 1)
    (hna : n ∈ centralizer ({a} : Set X)) (hnK : ∀ k ∈ gsFixedLayer L u, n * k = k * n) :
    ∃ y ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype,
      y⁻¹ * n ∈ centralizer (L : Set X) := by
  obtain ⟨-, -, hstd, ⟨e⟩, -⟩ := hset
  set K := gsFixedLayer L u with hK
  set CL := centralizer (L : Set X) with hCL
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have haL : a ∈ CL :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLa hl)
  have hCN := HeZ.centralizer_le_normalizer hstd haL ha
  have hcard : Nat.card K = 80640 :=
    HeZ.card_gsFixedLayer heldTwoALayerFact heldTwoAKFact ⟨e⟩ hu
  obtain ⟨-, -, hAK⟩ := heldTwoAKFact X L ⟨e⟩ u hu
  by_cases hnC : n ∈ CL
  · exact ⟨1, one_mem _, by rwa [inv_one, one_mul]⟩
  rcases heldInvolAutFact X L ⟨e⟩ n (hCN hna) (by rw [hn]; exact one_mem _) hnC with
    ⟨y, hyL, -, hyc⟩ | ⟨-, -, hS, -⟩
  · refine ⟨y, ?_, hyc⟩
    have hyK : ∀ k ∈ K, y * k = k * y := by
      intro k hk
      have hck : Commute k (y⁻¹ * n) := mem_centralizer_iff.mp hyc k (hKL hk)
      have hnk : Commute k n := (hnK k hk).symm
      have hy : y = n * (y⁻¹ * n)⁻¹ := by group
      have h' : Commute k y := by
        rw [hy]
        exact hnk.mul_right hck.inv_right
      exact h'.eq.symm
    rcases hAK y hyL hyK with rfl | ⟨-, h⟩
    · exact one_mem _
    · exact h
  · have h := hS K hKL fun k hk => mem_centralizer_singleton_iff.mpr (hnK k hk).symm
    omega

end HeKM

end CFSG.ComponentClassification.GrSLit
