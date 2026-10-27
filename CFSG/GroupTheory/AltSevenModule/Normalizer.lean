module

public import CFSG.GroupTheory.AltSevenModule.Offender
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GroupTheory.AltSevenModule

open CFSG.Quasithin
open CFSG.RankThree.PartTwo.KFacts

private def sevenCycle : Equiv.Perm (Fin 7) := List.formPerm [0, 4, 1, 5, 2, 6, 3]

private theorem sevenCycle_conj_cOne :
    sevenCycle * KP2.cOne * sevenCycle⁻¹ = Equiv.swap 4 5 * Equiv.swap 5 6 := by
  decide +kernel

private theorem sevenCycle_conj_cTwo :
    sevenCycle * KP2.cTwo * sevenCycle⁻¹ = Equiv.swap 0 1 * Equiv.swap 1 2 := by
  decide +kernel

private theorem card_kleinRegular7 :
    Nat.card (kleinRegular7 : Subgroup (Equiv.Perm (Fin 7))) = 4 := by
  simpa only [kleinRegular7, CFSG.QuasithinUnique.B42A57.V0] using
    CFSG.QuasithinUnique.B42A57.card_V0

private theorem eNine_eq_closure :
    KP2.eNine = Subgroup.closure ({KP2.cOne, KP2.cTwo} : Set (Equiv.Perm (Fin 7))) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨i, j, rfl⟩ := hx
    show KP2.eNineF i j ∈ Subgroup.closure _
    rw [show KP2.eNineF i j = KP2.cOne ^ (i : ℕ) * KP2.cTwo ^ (j : ℕ) from rfl]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact KP2.cOne_mem_eNine
    · exact KP2.cTwo_mem_eNine

private def eNineConj : Subgroup (Equiv.Perm (Fin 7)) :=
  KP2.eNine.map (MulAut.conj sevenCycle).toMonoidHom

private theorem eNineConj_eq :
    eNineConj = Subgroup.closure
      ({Equiv.swap 4 5 * Equiv.swap 5 6, Equiv.swap 0 1 * Equiv.swap 1 2} :
        Set (Equiv.Perm (Fin 7))) := by
  unfold eNineConj
  rw [eNine_eq_closure, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl), rfl⟩
    · left
      simpa [MulAut.conj_apply] using sevenCycle_conj_cOne
    · right
      simpa [MulAut.conj_apply] using sevenCycle_conj_cTwo
  · rintro (rfl | rfl)
    · exact ⟨KP2.cOne, Or.inl rfl, by simpa [MulAut.conj_apply] using sevenCycle_conj_cOne⟩
    · exact ⟨KP2.cTwo, Or.inr rfl, by simpa [MulAut.conj_apply] using sevenCycle_conj_cTwo⟩

private theorem eNineConj_le_alternatingGroup : eNineConj ≤ alternatingGroup (Fin 7) := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hx
  simpa [MulAut.conj_apply] using
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem e
      (KP2.eNine_le_alternatingGroup he) sevenCycle

private theorem threeCycle456_mem_normalizer :
    Equiv.swap 4 5 * Equiv.swap 5 6 ∈
      Subgroup.normalizer (kleinRegular7 : Set (Equiv.Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    unfold kleinRegular7
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · apply Subgroup.mem_comap.2
      change MulAut.conj (Equiv.swap 4 5 * Equiv.swap 5 6)
        (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ kleinRegular7
      rw [MulAut.conj_apply,
        show (Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6) * (Equiv.swap 0 1 * Equiv.swap 2 3) *
            (Equiv.swap 4 5 * Equiv.swap 5 6)⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 from by
          decide +kernel]
      exact Subgroup.subset_closure (by simp)
    · apply Subgroup.mem_comap.2
      change MulAut.conj (Equiv.swap 4 5 * Equiv.swap 5 6)
        (Equiv.swap 0 2 * Equiv.swap 1 3) ∈ kleinRegular7
      rw [MulAut.conj_apply,
        show (Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6) * (Equiv.swap 0 2 * Equiv.swap 1 3) *
            (Equiv.swap 4 5 * Equiv.swap 5 6)⁻¹ = Equiv.swap 0 2 * Equiv.swap 1 3 from by
          decide +kernel]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, card_kleinRegular7]

private theorem threeCycle012_mem_normalizer :
    Equiv.swap 0 1 * Equiv.swap 1 2 ∈
      Subgroup.normalizer (kleinRegular7 : Set (Equiv.Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    unfold kleinRegular7
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · apply Subgroup.mem_comap.2
      change MulAut.conj (Equiv.swap 0 1 * Equiv.swap 1 2)
        (Equiv.swap 0 1 * Equiv.swap 2 3) ∈ kleinRegular7
      rw [MulAut.conj_apply,
        show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 2 3) *
            (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ =
              (Equiv.swap 0 1 * Equiv.swap 2 3) * (Equiv.swap 0 2 * Equiv.swap 1 3) from by
          decide +kernel]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · apply Subgroup.mem_comap.2
      change MulAut.conj (Equiv.swap 0 1 * Equiv.swap 1 2)
        (Equiv.swap 0 2 * Equiv.swap 1 3) ∈ kleinRegular7
      rw [MulAut.conj_apply,
        show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap 0 2 * Equiv.swap 1 3) *
            (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 3 from by
          decide +kernel]
      exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, card_kleinRegular7]

private theorem eNineConj_le_normalizer :
    eNineConj ≤ Subgroup.normalizer (kleinRegular7 : Set (Equiv.Perm (Fin 7))) := by
  rw [eNineConj_eq, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact threeCycle456_mem_normalizer
  · exact threeCycle012_mem_normalizer

private theorem eNineConj_map_conj_le_normalizer (c : Equiv.Perm (Fin 7)) :
    eNineConj.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.normalizer ((kleinRegular7.map (MulAut.conj c).toMonoidHom :
        Subgroup (Equiv.Perm (Fin 7))) : Set (Equiv.Perm (Fin 7))) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono eNineConj_le_normalizer

private theorem eNineConj_map_conj_le_alternatingGroup (c : Equiv.Perm (Fin 7)) :
    eNineConj.map (MulAut.conj c).toMonoidHom ≤ alternatingGroup (Fin 7) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  simpa [MulAut.conj_apply] using
    (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem y
      (eNineConj_le_alternatingGroup hy) c

theorem exists_elemAbelian_three_le_normalizer {T : Subgroup ↥(alternatingGroup (Fin 7))}
    (hT : IsPGroup 2 T) (hT8 : Nat.card T ≠ 8) {c : Equiv.Perm (Fin 7)}
    (hc : c ∈ alternatingGroup (Fin 7))
    (hcT : kleinRegular7.map (MulAut.conj c).toMonoidHom ≤
      T.map (alternatingGroup (Fin 7)).subtype) :
    ∃ E : Subgroup ↥(alternatingGroup (Fin 7)),
      E ≤ Subgroup.normalizer (T : Set ↥(alternatingGroup (Fin 7))) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have hKc_card : Nat.card (kleinRegular7.map (MulAut.conj c).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_kleinRegular7]
  have hTmap_card : Nat.card (T.map (alternatingGroup (Fin 7)).subtype) = Nat.card T :=
    Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective
  have h4dvd : 4 ∣ Nat.card T := by
    have h := Subgroup.card_dvd_of_le hcT
    rwa [hKc_card, hTmap_card] at h
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hk2 : 2 ≤ k := by
    have h : 2 ^ 2 ∣ 2 ^ k := by
      rw [← hk]
      exact h4dvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp h
  have hkdvd : 2 ^ k ∣ 2520 := by
    rw [← hk, ← CFSG.QuasithinUnique.L246.C123.card_A7]
    exact Subgroup.card_subgroup_dvd_card T
  have hk3 : k ≤ 3 := by
    have hfac : (2520 : ℕ).factorization 2 = 3 := by
      have h := CFSG.QuasithinUnique.L246.C123.fac_card_A7
      rwa [CFSG.QuasithinUnique.L246.C123.card_A7] at h
    have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (by norm_num : (2520 : ℕ) ≠ 0)).mp hkdvd
    omega
  have hkne : k ≠ 3 := by
    rintro rfl
    exact hT8 (by rw [hk]; norm_num)
  have hk2' : k = 2 := by omega
  have hT_card : Nat.card T = 4 := by
    rw [hk, hk2']
    norm_num
  have hTmap_eq :
      T.map (alternatingGroup (Fin 7)).subtype =
        kleinRegular7.map (MulAut.conj c).toMonoidHom := by
    refine (Subgroup.eq_of_le_of_card_ge hcT ?_).symm
    rw [hTmap_card, hT_card, hKc_card]
  let E₂ : Subgroup (Equiv.Perm (Fin 7)) :=
    eNineConj.map (MulAut.conj c).toMonoidHom
  have hE₂_alt : E₂ ≤ alternatingGroup (Fin 7) :=
    eNineConj_map_conj_le_alternatingGroup c
  have hE₂_norm : E₂ ≤ Subgroup.normalizer
      ((kleinRegular7.map (MulAut.conj c).toMonoidHom : Subgroup (Equiv.Perm (Fin 7))) :
        Set (Equiv.Perm (Fin 7))) :=
    eNineConj_map_conj_le_normalizer c
  have hE₂_range : E₂ ≤ (alternatingGroup (Fin 7)).subtype.range := by
    rw [Subgroup.range_subtype]
    exact hE₂_alt
  let E : Subgroup ↥(alternatingGroup (Fin 7)) :=
    E₂.comap (alternatingGroup (Fin 7)).subtype
  have hE_map : E.map (alternatingGroup (Fin 7)).subtype = E₂ :=
    Subgroup.map_comap_eq_self hE₂_range
  refine ⟨E, ?_, ?_, ?_⟩
  ·
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxE₂ : (alternatingGroup (Fin 7)).subtype x ∈ E₂ := hx
    have hy : y ∈ T ↔ (alternatingGroup (Fin 7)).subtype y ∈
        kleinRegular7.map (MulAut.conj c).toMonoidHom := by
      rw [← hTmap_eq,
        Subgroup.mem_map_iff_mem (alternatingGroup (Fin 7)).subtype_injective]
    have hconj : (alternatingGroup (Fin 7)).subtype y ∈
          kleinRegular7.map (MulAut.conj c).toMonoidHom ↔
        (alternatingGroup (Fin 7)).subtype (x * y * x⁻¹) ∈
          kleinRegular7.map (MulAut.conj c).toMonoidHom := by
      have h := (Subgroup.mem_normalizer_iff.mp (hE₂_norm hxE₂))
        ((alternatingGroup (Fin 7)).subtype y)
      have heq : (alternatingGroup (Fin 7)).subtype (x * y * x⁻¹) =
          (alternatingGroup (Fin 7)).subtype x * (alternatingGroup (Fin 7)).subtype y *
            ((alternatingGroup (Fin 7)).subtype x)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [heq]
      exact h
    have hz : (alternatingGroup (Fin 7)).subtype (x * y * x⁻¹) ∈
          kleinRegular7.map (MulAut.conj c).toMonoidHom ↔ x * y * x⁻¹ ∈ T := by
      rw [← hTmap_eq,
        Subgroup.mem_map_iff_mem (alternatingGroup (Fin 7)).subtype_injective]
    exact hy.trans (hconj.trans hz)
  ·
    have hE₂_class : CFSG.IsElementaryAbelian 3 ↥E₂ := by
      have h₁ : CFSG.IsElementaryAbelian 3 ↥eNineConj :=
        CFSG.IsElementaryAbelian.map (p := 3) (A := KP2.eNine)
          (MulAut.conj sevenCycle).toMonoidHom
      exact CFSG.IsElementaryAbelian.map (p := 3) (A := eNineConj)
        (MulAut.conj c).toMonoidHom
    constructor
    · haveI : IsMulCommutative ↥E₂ := hE₂_class.toIsMulCommutative
      exact Subgroup.comap_injective_isMulCommutative E₂
        (f := (alternatingGroup (Fin 7)).subtype)
        (alternatingGroup (Fin 7)).subtype_injective
    · intro x hx
      apply (alternatingGroup (Fin 7)).subtype_injective
      rw [map_pow, map_one]
      have hxE₂ : (alternatingGroup (Fin 7)).subtype x ∈ E₂ := hx
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian
        ((alternatingGroup (Fin 7)).subtype x) hxE₂
  ·
    have hE₂_card : Nat.card E₂ = 9 := by
      change Nat.card (eNineConj.map (MulAut.conj c).toMonoidHom) = 9
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      change Nat.card (KP2.eNine.map (MulAut.conj sevenCycle).toMonoidHom) = 9
      rw [Subgroup.card_map_of_injective (MulAut.conj sevenCycle).injective, KP2.card_eNine]
    calc Nat.card E = Nat.card (E.map (alternatingGroup (Fin 7)).subtype) :=
          (Subgroup.card_map_of_injective
            (alternatingGroup (Fin 7)).subtype_injective).symm
      _ = Nat.card E₂ := by rw [hE_map]
      _ = 9 := hE₂_card

theorem exists_elemAbelian_three_le_normalizer_of_offender {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (ρ : ↥(alternatingGroup (Fin 7)) →* MulAut V)
    (hρ : Function.Injective ρ) (h16 : Nat.card (commV ρ.range) = 16)
    {T A : Subgroup ↥(alternatingGroup (Fin 7))} (hT : IsPGroup 2 T) (hT8 : Nat.card T ≠ 8)
    (hAT : A ≤ T) (hA1 : A ≠ ⊥) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV (A.map ρ))) :
    ∃ E : Subgroup ↥(alternatingGroup (Fin 7)),
      E ≤ Subgroup.normalizer (T : Set ↥(alternatingGroup (Fin 7))) ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨c, hc, hle⟩ := exists_conj_kleinRegular7_le hV ρ hρ h16 hA1 hA2 hoff
  exact exists_elemAbelian_three_le_normalizer hT hT8 hc (hle.trans (Subgroup.map_mono hAT))

end CFSG.GroupTheory.AltSevenModule
