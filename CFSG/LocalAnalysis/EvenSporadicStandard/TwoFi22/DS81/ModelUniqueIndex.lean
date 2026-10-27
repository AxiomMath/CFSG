module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section


theorem frameT_conj {T : Subgroup J} (hT : ∀ x ∈ D23, x ∈ T ↔ ∃ i, fjHom (eVec i) = x) {t : J}
    (ht : t ∈ T) (w : Multiplicative Word) : ∃ w' : Multiplicative Word,
      fjHom w' = t * fjHom w * t⁻¹ := by
  have key : ∀ v : Word, ∃ w' : Multiplicative Word,
      fjHom w' = t * fjHom (Multiplicative.ofAdd v) * t⁻¹ := by
    intro v
    rw [← Finset.univ_sum_single v]
    refine Finset.sum_induction _ (fun v : Word => ∃ w' : Multiplicative Word,
      fjHom w' = t * fjHom (Multiplicative.ofAdd v) * t⁻¹) ?_ ?_ ?_
    · rintro a b ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
      refine ⟨w₁ * w₂, ?_⟩
      rw [map_mul, h₁, h₂, ofAdd_add, map_mul]
      group
    · exact ⟨1, by simp⟩
    · rintro i -
      have hv : v i = 0 ∨ v i = 1 := by
        have : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        exact this _
      rcases hv with h | h
      · rw [h]
        exact ⟨1, by simp⟩
      · rw [h]
        have hp : fjHom (Multiplicative.ofAdd (Pi.single i 1)) = fjPt i := fjHom_eVec i
        rw [hp]
        have hpT : fjPt i ∈ T := (hT _ (fjPt_mem i)).2 ⟨i, fjHom_eVec i⟩
        have hconj : t * fjPt i * t⁻¹ ∈ D23 :=
          (show IsConj d (fjPt i) from fjPt_mem i).trans (isConj_iff.2 ⟨t, rfl⟩)
        obtain ⟨j, hj⟩ := (hT _ hconj).1 (T.mul_mem (T.mul_mem ht hpT) (T.inv_mem ht))
        exact ⟨eVec j, hj.symm ▸ rfl⟩
  have := key (Multiplicative.toAdd w)
  rwa [ofAdd_toAdd] at this

theorem frameT_le_normalizer {T : Subgroup J}
    (hT : ∀ x ∈ D23, x ∈ T ↔ ∃ i, fjHom (eVec i) = x) {t : Cd} (ht : (t : J) ∈ T) :
    t ∈ normalizer (E0 : Set ↥Cd) := by
  have hone : ∀ {s : Cd}, (s : J) ∈ T → ∀ h : Cd, h ∈ E0 → s * h * s⁻¹ ∈ E0 := by
    intro s hs h hh
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.1 hh
    obtain ⟨w', hw'⟩ := frameT_conj hT hs w
    refine Subgroup.mem_subgroupOf.2 ⟨w', ?_⟩
    rw [hw', hw]
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hone ht h, fun hh => ?_⟩
  have htinv : ((t⁻¹ : Cd) : J) ∈ T := T.inv_mem ht
  have h1 := hone htinv _ hh
  have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
  rwa [e] at h1

end

section


theorem exists_frameT :
    ∃ T : Subgroup J, T ≤ Subgroup.centralizer {d} ∧ Nat.card T = 2 ^ 18 ∧
      ∀ x ∈ D23, x ∈ T ↔ ∃ i, fjHom (eVec i) = x := by
  have hE : IsPGroup 2 fjProj.range :=
    isPGroup_word.of_surjective fjProj.rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  have hSi : ∀ i : Fin 23, piC (fjQ i) ∈ (S : Subgroup CFSG.Sporadic.Fi22.J) := fun i =>
    hES ⟨eVec i, fjProj_eVec i⟩
  refine ⟨((S : Subgroup CFSG.Sporadic.Fi22.J).comap piC).map Cd.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have h1 := Subgroup.card_mul_index ((S : Subgroup CFSG.Sporadic.Fi22.J).comap piC)
    have h2 := Subgroup.card_mul_index (S : Subgroup CFSG.Sporadic.Fi22.J)
    rw [Subgroup.index_comap_of_surjective _ piC_surjective, card_centralizer_d] at h1
    rw [card_sylow_fi22 S, CFSG.Sporadic.Fi22.card_J] at h2
    have hidx : (S : Subgroup CFSG.Sporadic.Fi22.J).index = 492567075 := by omega
    rw [hidx] at h1
    omega
  · intro x hx
    constructor
    · intro hxT
      obtain ⟨c, hcS, hcx⟩ := Subgroup.mem_map.1 hxT
      have hcx' : (c : J) = x := hcx
      by_cases hcd : (c : J) = d
      · exact ⟨0, by rw [fjHom_eVec, fjPt_zero, ← hcx', hcd]⟩
      · have hstar : (c : J) ∈ star := ⟨hcx' ▸ hx, hcd, mem_Cd.1 c.2⟩
        obtain ⟨i, -, hi⟩ := exists_pt_of_image_mem hSi hstar hcS
        exact ⟨i, by rw [fjHom_eVec, hi, hcx']⟩
    · rintro ⟨i, rfl⟩
      rw [fjHom_eVec]
      refine Subgroup.mem_map.2 ⟨fjQ i, ?_, rfl⟩
      exact hSi i

theorem E0_odd_index : Odd (normalizer (E0 : Set ↥Cd)).index := by
  obtain ⟨T, hTle, hTcard, hT⟩ := exists_frameT
  have hTN : T.subgroupOf Cd ≤ normalizer (E0 : Set ↥Cd) := fun t ht =>
    frameT_le_normalizer hT (Subgroup.mem_subgroupOf.1 ht)
  have hT'card : Nat.card (T.subgroupOf Cd) = 2 ^ 18 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv).trans hTcard
  obtain ⟨c, hc⟩ := hT'card ▸ Subgroup.card_dvd_of_le hTN
  have h := Subgroup.card_mul_index (normalizer (E0 : Set ↥Cd))
  rw [hc, show Nat.card ↥Cd = 129123503308800 from card_centralizer_d, mul_assoc] at h
  have h' : c * (normalizer (E0 : Set ↥Cd)).index = 492567075 := by
    refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ 18 by norm_num) ?_
    rw [h]
    norm_num
  have hodd : Odd (c * (normalizer (E0 : Set ↥Cd)).index) := by
    rw [h']
    exact ⟨246283537, by norm_num⟩
  exact (Nat.odd_mul.1 hodd).2

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81
