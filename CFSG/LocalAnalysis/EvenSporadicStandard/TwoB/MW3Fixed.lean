module

public import CFSG.Sporadic.Co1.Module.Transfer

public section

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Monster CFSG.Monster.VisCert CFSG.Monster.SpinLattice CFSG.Monster.Existence.Co1Bridge
  CFSG.Sporadic.Co1.Module Matrix

theorem not_dvd_card_orbit
    (i : Fin 3) :
    ¬ (2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) * (MulAction.orbit J24 (reps i)).ncard ∣ Nat.card J24 := by
  rw [natCard_J24]
  fin_cases i
  · have h : (MulAction.orbit J24 v₂).ncard = 98280 := J24_orbit_ncard_v₂
    change ¬ _ * (MulAction.orbit J24 v₂).ncard ∣ _
    rw [h]
    norm_num
  · have h : (MulAction.orbit J24 v₃).ncard = 8386560 := J24_orbit_ncard_v₃
    change ¬ _ * (MulAction.orbit J24 v₃).ncard ∣ _
    rw [h]
    norm_num
  · have h : (MulAction.orbit J24 v₄).ncard = 8292375 := J24_orbit_ncard_v₄
    change ¬ _ * (MulAction.orbit J24 v₄).ncard ∣ _
    rw [h]
    norm_num

theorem eq_zero_of_fixed_J24
    (P : Subgroup J24)
    (hcard : Nat.card P = 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) {u : Vec24}
    (hu : ∀ g ∈ P, g • u = u) : u = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := (J24_exists_unique_orbit hne).exists
  have horb : MulAction.orbit J24 u = MulAction.orbit J24 (reps i) := MulAction.orbit_eq_iff.2 hi
  have hPle : P ≤ MulAction.stabilizer J24 u := fun g hg => MulAction.mem_stabilizer_iff.2 (hu g hg)
  have hdvd : Nat.card P ∣ Nat.card (MulAction.stabilizer J24 u) := Subgroup.card_dvd_of_le hPle
  have hmul : Nat.card (MulAction.stabilizer J24 u) * (MulAction.orbit J24 u).ncard =
      Nat.card J24 := by
    rw [← MulAction.index_stabilizer J24 u]
    exact Subgroup.card_mul_index _
  rw [horb] at hmul
  rw [hcard] at hdvd
  exact not_dvd_card_orbit i (by rw [← hmul]; exact Nat.mul_dvd_mul_right hdvd _)

theorem exists_fixing_subgroup
    (K : Subgroup (GL (Fin 24) (ZMod 2))) (hK : K.map conjHom = Hvis)
    (P : Subgroup GLV) (hP : P ≤ Hvis) {v : L2} (hv : ∀ g ∈ P, (g : L2 →ₗ[ZMod 2] L2) v = v) :
    ∃ P' : Subgroup K, Nat.card P' = Nat.card P ∧
      ∀ g ∈ P', ((g : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ theta.symm v =
        theta.symm v := by
  let f : K →* GLV := conjHom.comp K.subtype
  have hf : Function.Injective f := conjHom_injective.comp K.subtype_injective
  have hPf : P ≤ f.range := by
    intro x hx
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 (hK ▸ hP hx)
    exact ⟨⟨g, hg⟩, hgx⟩
  refine ⟨P.comap f, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self hPf]
  · intro g hg
    have h1 := hv _ hg
    have h2 : (f g : GLV) = conjHom (g : GL (Fin 24) (ZMod 2)) := rfl
    rw [h2, conjHom_apply] at h1
    have h3 := congrArg theta.symm h1
    rwa [LinearEquiv.symm_apply_apply] at h3

theorem eq_zero_of_fixed
    (P : Subgroup GLV) (hP : P ≤ Hvis) (hcard : Nat.card P = 2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) {v : L2}
    (hv : ∀ g ∈ P, (g : L2 →ₗ[ZMod 2] L2) v = v) : v = 0 := by
  obtain ⟨P', hP', hfix⟩ := exists_fixing_subgroup J24 map_J24_eq_Hvis P hP hv
  have hz := eq_zero_of_fixed_J24 P' (hP'.trans hcard) hfix
  exact (LinearEquiv.map_eq_zero_iff theta.symm).1 hz

end CFSG.EvenSporadicStandard.TwoB.MW3
