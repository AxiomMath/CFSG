module

public import CFSG.LieType.Steinberg.Bruhat

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

def negIndices (D : UniversalRootDatum K) (A : Subgroup K) : Set (Fin D.rank) :=
  {i | D.rootGroup (-Pi.single i 1) ≤ A}

theorem rankOne_le_of_mem_negIndices {A : Subgroup K} (hBA : borel D H ≤ A) {i : Fin D.rank}
    (hi : i ∈ negIndices D A) : rankOne D.rootGroup i ≤ A :=
  sup_le ((rootGroup_le_borel ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
    (ht_single_pos i)).trans hBA) hi

theorem rootGroup_neg_single_le_of_nrep_mem
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {A : Subgroup K} (hBA : borel D H ≤ A) {w : (coxeterMatrix D.isFiniteType).Group}
    (hw : nrep hct w ∈ A) {i : Fin D.rank}
    (hi : (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsLeftDescent w i) :
    D.rootGroup (-Pi.single i 1) ≤ A := by
  intro x hx
  have hdesc : (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w⁻¹ i :=
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.isRightDescent_inv_iff).2 hi
  have hneg := ht_weylAction_single_neg hdesc
  have hαr : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  set β : Fin D.rank → ℤ := weylAction D.isFiniteType w⁻¹ (Pi.single i 1) with hβ
  have hβr : β ∈ D.roots := weylAction_mem_roots D.isFiniteType w⁻¹ hαr
  have hγr : -β ∈ D.roots := (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem β hβr
  have hγpos : 0 < ht (-β) := by
    rw [ht_neg]
    omega
  have hmem : (nrep hct w)⁻¹ * x * nrep hct w ∈ D.rootGroup (-β) := by
    have h1 := nrep_inv_conj_mem hct w ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem
      _ hαr) hx
    have h2 : weylAction D.isFiniteType w⁻¹ (-Pi.single i 1) = -β := by
      rw [map_neg]
    rwa [h2] at h1
  have hyB : (nrep hct w)⁻¹ * x * nrep hct w ∈ borel D H :=
    posUnipotent_le_borel (rootGroup_le_posUnipotent hγr hγpos hmem)
  have := mul_mem (mul_mem hw (hBA hyB)) (inv_mem hw)
  simpa [mul_assoc] using this

theorem eq_borel_sup_rankOne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {A : Subgroup K} (hBA : borel D H ≤ A) :
    A = borel D H ⊔ ⨆ i ∈ negIndices D A, rankOne D.rootGroup i := by
  set P : Subgroup K := borel D H ⊔ ⨆ i ∈ negIndices D A, rankOne D.rootGroup i with hP
  have hPA : P ≤ A :=
    sup_le hBA (iSup₂_le fun i hi => rankOne_le_of_mem_negIndices hBA hi)
  have key : ∀ m : ℕ, ∀ w : (coxeterMatrix D.isFiniteType).Group,
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w = m → nrep hct w ∈ A →
        nrep hct w ∈ P := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro w hlen hwA
      by_cases hw1 : w = 1
      · rw [hw1, nrep_one]
        exact one_mem _
      · obtain ⟨i, hi⟩ :=
          (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one hw1
        have hneg := rootGroup_neg_single_le_of_nrep_mem hct hBA hwA hi
        have hiI : i ∈ negIndices D A := hneg
        have hLi : rankOne D.rootGroup i ≤ P :=
          le_sup_of_le_right (le_iSup₂_of_le (f := fun i (_ : i ∈ negIndices D A) =>
            rankOne D.rootGroup i) i hiI le_rfl)
        have hn : n i ∈ P := hLi (hct.n_mem i)
        obtain ⟨w', hw'⟩ : ∃ w' : (coxeterMatrix D.isFiniteType).Group, w' =
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w := ⟨_, rfl⟩
        have hlt : (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w' <
            (coxeterMatrix D.isFiniteType).toCoxeterSystem.length w := by
          have := ((coxeterMatrix D.isFiniteType).toCoxeterSystem.isLeftDescent_iff).1 hi
          rw [← hw'] at this
          omega
        have hww : w = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * w' := by
          rw [hw', ← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
        have hnd : ¬ (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsLeftDescent w' i := by
          rw [CoxeterSystem.isLeftDescent_iff, ← hww]
          omega
        have hnw : nrep hct w = n i * nrep hct w' := by
          rw [hww]
          exact nrep_simple_mul hct hnd
        have hnw'A : nrep hct w' ∈ A := by
          have : nrep hct w' = (n i)⁻¹ * nrep hct w := by rw [hnw]; group
          rw [this]
          exact mul_mem (inv_mem (hPA hn)) hwA
        have := ih _ (by omega) w' rfl hnw'A
        rw [hnw]
        exact mul_mem hn this
  have hBP : borel D H ≤ P := le_sup_left
  refine le_antisymm (fun g hg => ?_) hPA
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_bruhatCell hct hext g
  have hnw : nrep hct w ∈ A := by
    have := mul_mem (mul_mem (inv_mem (hBA hb₁)) hg) (inv_mem (hBA hb₂))
    simpa [mul_assoc] using this
  exact mul_mem (mul_mem (hBP hb₁) (key _ w rfl hnw)) (hBP hb₂)

theorem negIndices_nonempty_of_ne
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) {A : Subgroup K} (hBA : borel D H ≤ A)
    (hne : A ≠ borel D H) : (negIndices D A).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  apply hne
  rw [eq_borel_sup_rankOne hct hext hBA, h]
  simp

end CFSG.AGLEmbedding.ParabPrime
