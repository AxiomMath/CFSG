module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut


section General

theorem mem_of_pow_two_pow_eq_one_of_mem_sup {G : Type*} [Group G] {N T' : Subgroup G}
    (hT : T' ≤ Subgroup.normalizer (N : Set G)) {M : ℕ} (hM : Odd M)
    (hTM : ∀ t ∈ T', t ^ M = 1) {a : G} (ha : a ∈ N ⊔ T') {k : ℕ} (hk : a ^ 2 ^ k = 1) :
    a ∈ N := by
  have hNT : N ⊔ T' ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hT
  haveI : (N.subgroupOf (N ⊔ T')).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hNT
  obtain ⟨x, hx, t, ht, rfl⟩ : ∃ x ∈ N, ∃ t ∈ T', a = x * t := by
    have h := ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hT, Set.mem_mul] at h
    obtain ⟨x, hx, t, ht, e⟩ := h
    exact ⟨x, hx, t, ht, e.symm⟩
  set q := QuotientGroup.mk' (N.subgroupOf (N ⊔ T')) with hq
  have htm : t ∈ N ⊔ T' := Subgroup.mem_sup_right ht
  have hxm : x ∈ N ⊔ T' := Subgroup.mem_sup_left hx
  have hqa : q ⟨x * t, ha⟩ = q ⟨t, htm⟩ := by
    have : (⟨x * t, ha⟩ : ↥(N ⊔ T')) = ⟨x, hxm⟩ * ⟨t, htm⟩ := rfl
    rw [this, map_mul]
    have hx1 : q ⟨x, hxm⟩ = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_subgroupOf).2 hx
    rw [hx1, one_mul]
  have h1 : q ⟨x * t, ha⟩ ^ M = 1 := by
    rw [hqa, ← map_pow]
    have : (⟨t, htm⟩ : ↥(N ⊔ T')) ^ M = 1 := Subtype.ext (hTM t ht)
    rw [this, map_one]
  have h2 : q ⟨x * t, ha⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x * t, ha⟩ : ↥(N ⊔ T')) ^ 2 ^ k = 1 := Subtype.ext hk
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) M := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hM)
  have h3 : orderOf (q ⟨x * t, ha⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  have h4 : q ⟨x * t, ha⟩ = 1 := orderOf_eq_one_iff.1 h3
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact (Subgroup.mem_subgroupOf).1 h4

end General


section K

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

@[expose] def parJ (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K)
    (J : Set (Fin D.rank)) : Subgroup K :=
  borel D H ⊔ ⨆ j ∈ J, rankOne D.rootGroup j

@[expose] def unipJ (D : UniversalRootDatum K) (J : Set (Fin D.rank)) : Subgroup K :=
  posUnipotent D ⊔ ⨆ j ∈ J, rankOne D.rootGroup j

theorem borel_le_parJ (J : Set (Fin D.rank)) : borel D H ≤ parJ D H J := le_sup_left

theorem rankOne_le_parJ {J : Set (Fin D.rank)} {j : Fin D.rank} (hj : j ∈ J) :
    rankOne D.rootGroup j ≤ parJ D H J :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => rankOne D.rootGroup j) j hj le_rfl)

theorem posUnipotent_le_unipJ (J : Set (Fin D.rank)) : posUnipotent D ≤ unipJ D J := le_sup_left

theorem rankOne_le_unipJ {J : Set (Fin D.rank)} {j : Fin D.rank} (hj : j ∈ J) :
    rankOne D.rootGroup j ≤ unipJ D J :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => rankOne D.rootGroup j) j hj le_rfl)

theorem rootGroup_neg_single_le_of_actsAs {X : Subgroup K} (hU : posUnipotent D ≤ X) {m : K}
    (hm : m ∈ X) {w : (coxeterMatrix D.isFiniteType).Group} (hact : ActsAs D m w)
    {i : Fin D.rank}
    (hi : (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsLeftDescent w i) :
    D.rootGroup (-Pi.single i 1) ≤ X := by
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
  have hmem : m⁻¹ * x * m ∈ D.rootGroup (-β) := by
    have h1 := hact.inv_conj_mem ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem
      _ hαr) hx
    have h2 : weylAction D.isFiniteType w⁻¹ (-Pi.single i 1) = -β := by
      rw [map_neg]
    rwa [h2] at h1
  have hyU : m⁻¹ * x * m ∈ posUnipotent D := rootGroup_le_posUnipotent hγr hγpos hmem
  have := mul_mem (mul_mem hm (hU hyU)) (inv_mem hm)
  simpa [mul_assoc] using this

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem exists_negIndex_of_not_le_borel {X : Subgroup K} (hU : posUnipotent D ≤ X)
    (hX : ¬ X ≤ borel D H) : ∃ i, D.rootGroup (-Pi.single i 1) ≤ X := by
  obtain ⟨g, hgX, hgB⟩ := Set.not_subset.1 hX
  obtain ⟨w, hgw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hgw
  have huU : u ∈ posUnipotent D := inversionUnipotent_le_posUnipotent w hu
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hgB
    rw [nrep_one, mul_one]
    exact mul_mem hb (posUnipotent_le_borel huU)
  obtain ⟨i, hi⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one hw1
  have hbn : b * nrep hct w ∈ X := by
    have := mul_mem hgX (inv_mem (hU huU))
    simpa [mul_assoc] using this
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  have htB : t ∈ borel D H := iSup_le_borel ht
  have hv' : t * v * t⁻¹ ∈ posUnipotent D := by
    have := (Subgroup.mem_normalizer_iff.1
      (borel_le_normalizer_posUnipotent hct htB) v).1 hv
    exact this
  have hm : t * nrep hct w ∈ X := by
    have h1 := mul_mem (inv_mem (hU hv')) hbn
    simpa [mul_assoc] using h1
  have hact : ActsAs D (t * nrep hct w) (1 * w) :=
    (actsAs_of_mem_iSup hct ht).mul (actsAs_nrep hct w)
  rw [one_mul] at hact
  exact ⟨i, rootGroup_neg_single_le_of_actsAs hU hm hact hi⟩

include hct hext in
theorem not_rankOne_le_normalizer_radical (k : Fin D.rank) :
    ¬ rankOne D.rootGroup k ≤ Subgroup.normalizer (radical D k : Set K) := by
  intro hle
  have hα : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
  have hα' : (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hnk : n k ∈ rankOne D.rootGroup k := hct.n_mem k
  have hneg : D.rootGroup (-Pi.single k 1) ≤ posUnipotent D := by
    intro y hy
    have h1 := (actsAs_n hct k).inv_conj_mem hα' hy
    have h2 : weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k)⁻¹
        (-(Pi.single k 1 : Fin D.rank → ℤ)) = Pi.single k 1 := by
      rw [CoxeterSystem.inv_simple, map_neg,
        weylAction_simple_single D.isFiniteType, neg_neg]
    rw [h2] at h1
    have h3 : (n k)⁻¹ * y * n k ∈ radical D k := rootGroup_le_radical hα (by simp) h1
    have h4 : n k * ((n k)⁻¹ * y * n k) * (n k)⁻¹ ∈ radical D k :=
      (Subgroup.mem_normalizer_iff.1 (hle hnk) _).1 h3
    have h5 : n k * ((n k)⁻¹ * y * n k) * (n k)⁻¹ = y := by group
    rw [h5] at h4
    exact radical_le_posUnipotent k h4
  apply hext.ne_bot _ hα'
  rw [eq_bot_iff, ← posUnipotent_inf_negUnipotent hext]
  exact le_inf hneg (rootGroup_le_negUnipotent hα' (by
    rw [ht_neg]; have := ht_single_pos (D := D) k; omega))

include hct hext in
theorem parJ_le_normalizer_radical {J : Set (Fin D.rank)} {k : Fin D.rank} (hk : k ∉ J) :
    parJ D H J ≤ Subgroup.normalizer (radical D k : Set K) :=
  sup_le (borel_le_normalizer_radical hct hext k) (iSup₂_le fun j hj =>
    rankOne_le_normalizer_radical hext (fun e => hk (e ▸ hj)))

include hct hext in
theorem mem_of_rankOne_le_parJ {J : Set (Fin D.rank)} {k : Fin D.rank}
    (h : rankOne D.rootGroup k ≤ parJ D H J) : k ∈ J := by
  by_contra hk
  exact not_rankOne_le_normalizer_radical hct hext k (h.trans (parJ_le_normalizer_radical hct hext hk))

include hct in
theorem torus_le_normalizer_unipJ (J : Set (Fin D.rank)) :
    ⨆ i, H i ≤ Subgroup.normalizer (unipJ D J : Set K) := by
  refine le_normalizer_sup (iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct)) ?_
  refine le_normalizer_iSup fun j => le_normalizer_iSup fun _ => ?_
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hα' : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  exact le_normalizer_sup (iSup_le_normalizer_rootGroup hct hα) (iSup_le_normalizer_rootGroup hct hα')

theorem parJ_eq_sup (J : Set (Fin D.rank)) : parJ D H J = unipJ D J ⊔ ⨆ i, H i := by
  rw [parJ, unipJ, LieType.Steinberg.borel]
  simp only [sup_assoc, sup_comm, sup_left_comm]

include hct hext in
theorem not_rankOne_le_borel (i : Fin D.rank) : ¬ rankOne D.rootGroup i ≤ borel D H := fun h => by
  have h1 : nrep hct ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) ∈ borel D H := by
    rw [nrep_simple hct i]
    exact h (hct.n_mem i)
  exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_ne_one i
    ((nrep_mem_borel_iff hct hext).1 h1)

include hct hext in
theorem borel_lt_parJ {J : Set (Fin D.rank)} (hJ : J.Nonempty) : borel D H < parJ D H J := by
  obtain ⟨i, hi⟩ := hJ
  refine lt_of_le_of_ne (borel_le_parJ J) fun h => ?_
  exact not_rankOne_le_borel hct hext i ((rankOne_le_parJ hi).trans h.symm.le)

include hct hext in
theorem eq_parJ_negIndices {A : Subgroup K} (hBA : borel D H ≤ A) :
    A = parJ D H (negIndices D A) := eq_borel_sup_rankOne hct hext hBA

include hct hext in
theorem eq_borel_or_eq_parJ_singleton {A : Subgroup K} {i : Fin D.rank} (hBA : borel D H ≤ A)
    (hA : A ≤ parJ D H {i}) : A = borel D H ∨ A = parJ D H {i} := by
  have hsub : negIndices D A ⊆ {i} := fun k hk =>
    mem_of_rankOne_le_parJ hct hext ((rankOne_le_of_mem_negIndices hBA hk).trans hA)
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · left
    rw [eq_parJ_negIndices hct hext hBA, h]
    simp [parJ]
  · right
    rw [eq_parJ_negIndices hct hext hBA, h]

end K

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
