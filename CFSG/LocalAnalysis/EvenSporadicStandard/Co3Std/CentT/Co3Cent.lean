module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Elementary
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint CFSG.Blueprint.NativeSporadic

private theorem factorization_2903040_two : Nat.factorization 2903040 2 = 10 := by
  have h : (2903040 : ℕ) = 2 ^ 10 * 2835 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 10) Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 2835), add_zero]

private theorem factorization_95040_two : Nat.factorization 95040 2 = 6 := by
  have h : (95040 : ℕ) = 2 ^ 6 * 1485 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 6) Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 1485), add_zero]

private theorem sylow_relIndex_map_of_injective {R D : Type} [Group R] [Group D]
    (f : R →* D) (hf : Function.Injective f) {S : Subgroup R}
    (hS : ∀ M : Subgroup R, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S) :
    ∀ M : Subgroup D, M ≤ S.map f → IsCyclic ↥M → 2 < M.relIndex (S.map f) := by
  intro M hM hcyc
  have hMrange : M ≤ f.range := hM.trans (Subgroup.map_le_range (f := f) S)
  have hmap : (M.comap f).map f = M := Subgroup.map_comap_eq_self (f := f) hMrange
  have hcomap : (S.map f).comap f = S := Subgroup.comap_map_eq_self_of_injective hf S
  have hMle : M.comap f ≤ S := by
    rw [← hcomap]
    exact Subgroup.comap_mono hM
  have hcyc' : IsCyclic ↥(M.comap f) := by
    have e := Subgroup.equivMapOfInjective (M.comap f) f hf
    rw [hmap] at e
    exact (e.isCyclic).mpr hcyc
  rw [← hmap, Subgroup.relIndex_map_map_of_injective (f := f) (M.comap f) S hf]
  exact hS (M.comap f) hMle hcyc'

private theorem centFacts_of_isoCore {D R : Type} [Group D] [Finite D] [Group R] [Finite R]
    {N : Subgroup D} [N.Normal] (e : ↥N ≃* R) {c idx : ℕ}
    (hD : Nat.card D = idx * Nat.card R) (hconst : idx * c = 4)
    (hnotdvd : ¬ 2 ^ 12 ∣ Nat.card D)
    (hproperR : ∀ K : Subgroup R, K.Normal → K ≠ ⊤ → Nat.card K ≤ c)
    (hbig : c * 23040 < Nat.card R)
    (hSylow : ∃ S : Subgroup R, IsPGroup 2 S ∧
      ∀ M : Subgroup R, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S)
    (hprime : 7 ∣ Nat.card R ∨ 11 ∣ Nat.card R) : CentFacts D := by
  have hNcard : Nat.card ↥N = Nat.card R := Nat.card_congr e.toEquiv
  have hidx : N.index = idx := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hD] at h
    have h' : Nat.card R * N.index = Nat.card R * idx := by
      rw [h, mul_comm idx]
    exact mul_left_cancel₀ (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) h'
  have hpropN : ∀ K : Subgroup ↥N, K.Normal → K ≠ ⊤ → Nat.card K ≤ c := by
    intro K hK hKne
    have hKmap : (K.map e.toMonoidHom).Normal := hK.map e.toMonoidHom e.surjective
    have hKmapNe : K.map e.toMonoidHom ≠ ⊤ := by
      intro htop
      apply hKne
      have hc : (K.map e.toMonoidHom).comap e.toMonoidHom = K :=
        Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective K
      rw [htop, Subgroup.comap_top] at hc
      exact hc.symm
    have hle := hproperR (K.map e.toMonoidHom) hKmap hKmapNe
    rwa [Subgroup.card_map_of_injective (K := K) e.injective] at hle
  refine ⟨hnotdvd, ?_⟩
  refine ⟨N, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro R' _ _ hR' f'
    exact hom_eq_one_of_normal_small hpropN (by rwa [hNcard]) R' hR' f'
  · obtain ⟨S_R, hSR_grp, hSR_rel⟩ := hSylow
    let f : R →* D := N.subtype.comp e.symm.toMonoidHom
    have hf : Function.Injective f := by
      intro a b hab
      exact e.symm.injective (N.subtype_injective hab)
    refine ⟨S_R.map f, ?_, hSR_grp.map f, sylow_relIndex_map_of_injective f hf hSR_rel⟩
    rintro y ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rwa [hNcard]
  · intro M hMnorm hMcard
    haveI : M.Normal := hMnorm
    refine le_of_normal_of_card_gt (c := c) ?_ ?_
    · intro K hKN hKnorm hKne
      have hmapN : ((K.subgroupOf N).map e.toMonoidHom).Normal :=
        hKnorm.map e.toMonoidHom e.surjective
      have hmapNe : (K.subgroupOf N).map e.toMonoidHom ≠ ⊤ := by
        intro htop
        apply hKne
        have hsub : K.subgroupOf N = ⊤ := by
          have hc : ((K.subgroupOf N).map e.toMonoidHom).comap e.toMonoidHom = K.subgroupOf N :=
            Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective
              (K.subgroupOf N)
          rw [htop, Subgroup.comap_top] at hc
          exact hc.symm
        rw [← Subgroup.map_subgroupOf_eq_of_le hKN, hsub, Subgroup.map_top,
          Subgroup.range_subtype]
      have hle := hproperR _ hmapN hmapNe
      have hcard : Nat.card K = Nat.card ((K.subgroupOf N).map e.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (K := K.subgroupOf N) e.injective]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv).symm
      exact hcard.trans_le hle
    · have hindexc : N.index * c = 4 := by rw [hidx, hconst]
      rw [hindexc]
      exact hMcard

section TypeA


theorem co3M_proper_normal_card_le :
    ∀ K : Subgroup ↥co3M, K.Normal → K ≠ ⊤ → Nat.card K ≤ 2 := by
  intro K hK hproper
  haveI : K.Normal := hK
  have hq : CFSG.Open.IsQuasisimple ↥co3M := isTwoSp62_co3M.isSp62Cover.isQuasisimple
  have hle : K ≤ Subgroup.center ↥co3M :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq K hproper
  calc Nat.card K ≤ Nat.card (Subgroup.center ↥co3M) := Subgroup.card_le_of_le hle
    _ = 2 := card_co3M_center

private theorem sylow_co3M :
    ∃ S : Subgroup ↥co3M, IsPGroup 2 S ∧
      ∀ M : Subgroup ↥co3M, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S := by
  let S₀ : Sylow 2 ↥co3M := default
  have hS : Nat.card (S₀ : Subgroup ↥co3M) = 2 ^ 10 := by
    rw [Sylow.card_eq_multiplicity S₀, card_co3M, factorization_2903040_two]
  refine ⟨(S₀ : Subgroup ↥co3M), S₀.isPGroup', ?_⟩
  intro M hM hcyc
  exact lt_relIndex_of_perm (E := ↥co3M) (n := 276) co3M.subtype co3M.subtype_injective
    (S := (S₀ : Subgroup ↥co3M)) (k := 10) (by norm_num) hS (by norm_num) M hM hcyc

theorem centFacts_of_typeA {D : Type} [Group D] [Finite D] {N : Subgroup D} [N.Normal]
    (e : ↥N ≃* ↥co3M) (hD : Nat.card D = 2 * 2903040) : CentFacts D := by
  have hD' : Nat.card D = 2 * Nat.card ↥co3M := by rw [card_co3M]; exact hD
  exact centFacts_of_isoCore (D := D) (R := ↥co3M) (N := N) e (c := 2) (idx := 2)
    hD' (by norm_num) (by rw [hD]; norm_num) co3M_proper_normal_card_le
    (by rw [card_co3M]; norm_num) sylow_co3M
    (Or.inl (by rw [card_co3M]; exact ⟨414720, by norm_num⟩))

end TypeA

section TypeB


private theorem sylow_M12 :
    ∃ S : Subgroup ↥NativeSporadic.M12, IsPGroup 2 S ∧
      ∀ M : Subgroup ↥NativeSporadic.M12, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S := by
  let S₀ : Sylow 2 ↥NativeSporadic.M12 := default
  have hS : Nat.card (S₀ : Subgroup ↥NativeSporadic.M12) = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity S₀, CFSG.Sporadic.Mathieu.card_M12, factorization_95040_two]
  refine ⟨(S₀ : Subgroup ↥NativeSporadic.M12), S₀.isPGroup', ?_⟩
  intro M hM hcyc
  exact lt_relIndex_of_perm (E := ↥NativeSporadic.M12) (n := 12) NativeSporadic.M12.subtype
    NativeSporadic.M12.subtype_injective (S := (S₀ : Subgroup ↥NativeSporadic.M12)) (k := 6)
    (by norm_num) hS (by norm_num) M hM hcyc

theorem centFacts_of_typeB {D : Type} [Group D] [Finite D] {N : Subgroup D} [N.Normal]
    (e : ↥N ≃* ↥NativeSporadic.M12) (hD : Nat.card D = 4 * 95040) : CentFacts D := by
  have hD' : Nat.card D = 4 * Nat.card ↥NativeSporadic.M12 := by
    rw [CFSG.Sporadic.Mathieu.card_M12]; exact hD
  have hproper : ∀ K : Subgroup ↥NativeSporadic.M12, K.Normal → K ≠ ⊤ →
      Nat.card K ≤ 1 := by
    intro K hK hne
    haveI : IsSimpleGroup ↥NativeSporadic.M12 :=
      (CFSG.Sporadic.Mathieu.fam_m12_simplicity).2.2
    haveI : K.Normal := hK
    rcases Subgroup.Normal.eq_bot_or_eq_top K with hbot | htop
    · rw [hbot, Subgroup.card_bot]
    · exact absurd htop hne
  exact centFacts_of_isoCore (D := D) (R := ↥NativeSporadic.M12) (N := N) e (c := 1) (idx := 4)
    hD' (by norm_num) (by rw [hD]; norm_num) hproper
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) sylow_M12
    (Or.inr (by rw [CFSG.Sporadic.Mathieu.card_M12]; exact ⟨8640, by norm_num⟩))

end TypeB

end CFSG.EvenSporadicStandard.Co3Std.CentT
