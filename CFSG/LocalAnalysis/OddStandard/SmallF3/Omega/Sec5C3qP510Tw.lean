module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def sec5p510_twist (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => v i + ∑ j, v j

theorem sec5p510_twist_twist (v : Fin 6 → ZMod 2) :
    sec5p510_twist (sec5p510_twist v) = v := by
  revert v
  decide +kernel

theorem sec5p510_twist_add (v w : Fin 6 → ZMod 2) :
    sec5p510_twist (v + w) = sec5p510_twist v + sec5p510_twist w := by
  revert v w
  decide +kernel

theorem sec5p510_twist_perm (σ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    sec5p510_twist (permVec σ v) = permVec σ (sec5p510_twist v) := by
  funext i
  simp only [sec5p510_twist, permVec, Function.comp_apply]
  rw [Equiv.sum_comp σ.symm v]

theorem sec5p510_twist_even (v : Fin 6 → ZMod 2) :
    IsEvenVec (sec5p510_twist v) ↔ IsEvenVec v := by
  unfold IsEvenVec sec5p510_twist
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h6 : (6 : ZMod 2) = 0 := by decide
  push_cast
  rw [h6, zero_mul, add_zero]

theorem sec5p510_weight_twist (v : Fin 6 → ZMod 2) :
    vecWeight (sec5p510_twist v) = if ∑ i, v i = 0 then vecWeight v else 6 - vecWeight v := by
  revert v
  decide +kernel

theorem sec5p510_twist_one : sec5p510_twist (fun _ => (1 : ZMod 2)) = fun _ => 1 := by
  decide +kernel

variable {G : Type} [Group G] {t : G} {L : Subgroup G} {z ρ : G} {A : Subgroup G}
  {φ : (Fin 6 → ZMod 2) → G}

theorem sec5p510_model_twist (hm : Sec5Model58 t L z ρ A φ) :
    Sec5Model58 t L z (ρ * t) A (fun v => φ (sec5p510_twist v)) := by
  have htau_inj : Function.Injective sec5p510_twist := by
    intro v w h
    have := congrArg sec5p510_twist h
    simpa only [sec5p510_twist_twist] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v w _ _
      change φ (sec5p510_twist (v + w)) =
        φ (sec5p510_twist v) * φ (sec5p510_twist w)
      rw [sec5p510_twist_add, hm.perm.map_add]
    · intro v w _ _ h
      exact htau_inj (hm.perm.injective h)
    · intro x
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := (hm.perm.mem_iff x).mp hx
        refine ⟨sec5p510_twist u, trivial, ?_⟩
        show φ (sec5p510_twist (sec5p510_twist u)) = x
        rw [sec5p510_twist_twist, hu]
      · rintro ⟨v, -, rfl⟩
        exact hm.perm.mem (sec5p510_twist v)
    · intro h hh
      obtain ⟨σ, hσ, hσv⟩ := hm.perm.2.2.2.1 h hh
      refine ⟨σ, hσ, fun v _ => ?_⟩
      rw [hσv (sec5p510_twist v) trivial]
      change φ (permVec σ (sec5p510_twist v)) = φ (sec5p510_twist (permVec σ v))
      rw [sec5p510_twist_perm]
    · intro σ hσ
      obtain ⟨h, hh, hσv⟩ := hm.perm.2.2.2.2 σ hσ
      refine ⟨h, hh, fun v _ => ?_⟩
      rw [hσv (sec5p510_twist v) trivial]
      change φ (permVec σ (sec5p510_twist v)) = φ (sec5p510_twist (permVec σ v))
      rw [sec5p510_twist_perm]
  · rw [sec5p510_twist_one, hm.map_one]
  · obtain ⟨i, hi⟩ := hm.r_mem
    refine ⟨i, ?_⟩
    have hsingle : sec5p510_twist (Pi.single i 1) = Pi.single i 1 + (fun _ => 1) := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [sec5p510_twist]
      · simp [sec5p510_twist, Pi.single_eq_of_ne hji]
    rw [hsingle, hm.perm.map_add, hi, hm.map_one]
  · obtain ⟨v, hv, hvz⟩ := hm.z_mem
    refine ⟨v, hv, ?_⟩
    have heven : IsEvenVec v :=
      (sec5b6_isEvenVec_iff v).mpr (by rw [hv]; norm_num)
    have hfix : sec5p510_twist v = v := by
      ext j
      simp only [sec5p510_twist]
      rw [show (∑ i, v i) = 0 from heven]
      simp
    rw [hfix, hvz]
  · intro w
    rw [hm.mem_L (sec5p510_twist w), sec5p510_twist_even]
  · intro w hw
    rcases hw with hw | hw
    · have hsum : (∑ i, w i) ≠ 0 := by
        intro h0
        have he : Even (vecWeight w) :=
          (sec5b6_isEvenVec_iff w).mp (by simpa [IsEvenVec] using h0)
        rw [hw] at he
        norm_num at he
      refine hm.type_one (sec5p510_twist w) (Or.inr ?_)
      rw [sec5p510_weight_twist, if_neg hsum, hw]
    · have hsum : (∑ i, w i) ≠ 0 := by
        intro h0
        have he : Even (vecWeight w) :=
          (sec5b6_isEvenVec_iff w).mp (by simpa [IsEvenVec] using h0)
        rw [hw] at he
        norm_num at he
      refine hm.type_one (sec5p510_twist w) (Or.inl ?_)
      rw [sec5p510_weight_twist, if_neg hsum, hw]
  · intro w hw
    have hsum : (∑ i, w i) ≠ 0 := by
      intro h0
      have he : Even (vecWeight w) :=
        (sec5b6_isEvenVec_iff w).mp (by simpa [IsEvenVec] using h0)
      rw [hw] at he
      norm_num at he
    refine hm.type_three (sec5p510_twist w) ?_
    rw [sec5p510_weight_twist, if_neg hsum, hw]

theorem sec5p510_wclass_twist_one (φ : (Fin 6 → ZMod 2) → G) :
    wclass (fun v => φ (sec5p510_twist v)) 1 = wclass φ 5 := by
  rw [wclass, wclass, ← Set.image_image]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : vecWeight v = 1 := hv
    have hsum : (∑ i, v i) ≠ 0 := by
      intro h0
      have he : Even (vecWeight v) :=
        (sec5b6_isEvenVec_iff v).mp (by simpa [IsEvenVec] using h0)
      rw [hv'] at he
      norm_num at he
    show vecWeight (sec5p510_twist v) = 5
    rw [sec5p510_weight_twist, if_neg hsum, hv']
  · intro hu
    have hu' : vecWeight u = 5 := hu
    refine ⟨sec5p510_twist u, ?_, sec5p510_twist_twist u⟩
    have hsum : (∑ i, u i) ≠ 0 := by
      intro h0
      have he : Even (vecWeight u) :=
        (sec5b6_isEvenVec_iff u).mp (by simpa [IsEvenVec] using h0)
      rw [hu'] at he
      norm_num at he
    show vecWeight (sec5p510_twist u) = 1
    rw [sec5p510_weight_twist, if_neg hsum, hu']

theorem sec5p510_wclass_twist_six (φ : (Fin 6 → ZMod 2) → G) :
    wclass (fun v => φ (sec5p510_twist v)) 6 = wclass φ 6 := by
  have h1 : sec5p510_twist (1 : Fin 6 → ZMod 2) = 1 := sec5p510_twist_one
  rw [wclass, wclass, ← Set.image_image]
  congr 1
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv1 : v = 1 := sec5b6_eq_one_of_weight_six hv
    show vecWeight (sec5p510_twist v) = 6
    rw [hv1, h1, sec5b6_vecWeight_one]
  · intro hu
    have hu1 : u = 1 := sec5b6_eq_one_of_weight_six hu
    refine ⟨sec5p510_twist u, ?_, sec5p510_twist_twist u⟩
    show vecWeight (sec5p510_twist u) = 6
    rw [hu1, h1, sec5b6_vecWeight_one]

end CFSG.OddStandard.SmallF3.Omega
