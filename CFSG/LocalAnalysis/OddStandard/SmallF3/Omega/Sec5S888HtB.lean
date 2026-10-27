module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartLift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private instance instDecidableIsEvenVecHtB (v : Fin 8 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private instance instDecidableIsFirstBlockVecHtB (v : Fin 8 → ZMod 2) :
    Decidable (IsFirstBlockVec v) := by
  unfold IsFirstBlockVec
  infer_instance

private instance instDecidableIsSecondBlockVecHtB (v : Fin 8 → ZMod 2) :
    Decidable (IsSecondBlockVec v) := by
  unfold IsSecondBlockVec
  infer_instance

theorem heart_class_pair {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : alternatingGroup (Fin 8) ≤ Alt)
    (hd : HeartData φ A M Alt) {t : G} (htA : t ∈ A) (ht1 : t ≠ 1)
    (hcard : Set.ncard (conjClassIn M t) = 28) :
    ∀ x ∈ conjClassIn M t, ∃ w, IsEvenVec w ∧ φ w = x ∧ vecWeight w = 2 := by
  obtain ⟨a, haE, hat, haw⟩ := sec5b_weight_rep hd htA ht1
  have ha2 : vecWeight a = 2 :=
    sec5b_pair_of_card hAlt hd haE haw (by rw [hat]; exact hcard)
  intro x hx
  rw [← hat] at hx
  obtain ⟨σ, -, hσ⟩ := (sec5b_mem_conj_iff hd haE).mp hx
  exact ⟨permVec σ a, isEvenVec_permVec σ haE, hσ.symm, by rw [vecWeight_permVec, ha2]⟩

theorem heart_z_weight_four {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hAlt : alternatingGroup (Fin 8) ≤ Alt)
    (hd : HeartData φ A M Alt) {t z : G} (htA : t ∈ A) (hzA : z ∈ A) (ht1 : t ≠ 1) (hz1 : z ≠ 1)
    (hcard : Set.ncard (conjClassIn M t) = 28) (hzt : z ∉ conjClassIn M t) :
    ∃ w, IsEvenVec w ∧ φ w = z ∧ vecWeight w = 4 := by
  obtain ⟨a, haE, hat, haw⟩ := sec5b_weight_rep hd htA ht1
  have ha2 : vecWeight a = 2 :=
    sec5b_pair_of_card hAlt hd haE haw (by rw [hat]; exact hcard)
  obtain ⟨c, hcE, hcz, hcw⟩ := sec5b_weight_rep hd hzA hz1
  refine ⟨c, hcE, hcz, ?_⟩
  rcases hcw with hc2 | hc4
  · exfalso
    apply hzt
    rw [← hat, ← hcz]
    exact sec5b_conj_of_weight hAlt hd haE hcE (by rw [ha2, hc2])
  · exact hc4

theorem vecWeight_heartZVec : vecWeight heartZVec = 4 := by
  decide +kernel

theorem isEvenVec_heartZVec : IsEvenVec heartZVec := by
  decide +kernel

@[expose] def heartSwap : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7

theorem heartSwap_mem_alternatingGroup : heartSwap ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem heartSwap_mul_self : heartSwap * heartSwap = 1 := by
  decide +kernel

theorem permVec_heartSwap_zVec : permVec heartSwap heartZVec = heartZVec + 1 := by
  decide +kernel

theorem isFirstBlockVec_permVec_heartSwap (v : Fin 8 → ZMod 2) :
    IsFirstBlockVec (permVec heartSwap v) ↔ IsSecondBlockVec v := by
  revert v
  decide +kernel

theorem isSecondBlockVec_permVec_heartSwap (v : Fin 8 → ZMod 2) :
    IsSecondBlockVec (permVec heartSwap v) ↔ IsFirstBlockVec v := by
  revert v
  decide +kernel

theorem heart_image_swap_firstBlock (φ : (Fin 8 → ZMod 2) → G) :
    (fun v => φ (permVec heartSwap v)) '' {v | IsFirstBlockVec v} =
      φ '' {v | IsSecondBlockVec v} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨permVec heartSwap v, (isSecondBlockVec_permVec_heartSwap v).mpr hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨permVec heartSwap u, (isFirstBlockVec_permVec_heartSwap u).mpr hu, ?_⟩
    show φ (permVec heartSwap (permVec heartSwap u)) = φ u
    rw [← sec5b_permVec_mul, heartSwap_mul_self, heart_permVec_one]

theorem heart_image_swap_secondBlock (φ : (Fin 8 → ZMod 2) → G) :
    (fun v => φ (permVec heartSwap v)) '' {v | IsSecondBlockVec v} =
      φ '' {v | IsFirstBlockVec v} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨permVec heartSwap v, (isFirstBlockVec_permVec_heartSwap v).mpr hv, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨permVec heartSwap u, (isSecondBlockVec_permVec_heartSwap u).mpr hu, ?_⟩
    show φ (permVec heartSwap (permVec heartSwap u)) = φ u
    rw [← sec5b_permVec_mul, heartSwap_mul_self, heart_permVec_one]

theorem heart_ncard_firstBlock {φ : (Fin 8 → ZMod 2) → G}
    (hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → w = v ∨ w = v + 1) :
    Set.ncard (φ '' {v | IsFirstBlockVec v}) = 8 := by
  have hI : Set.InjOn φ {v | IsFirstBlockVec v} := by
    intro v hv w hw h
    rcases hinj v w hv.1 hw.1 h with h1 | h1
    · exact h1.symm
    · exfalso
      have h4 : w 4 = 0 := hw.2 4 (by decide)
      have h5 : v 4 = 0 := hv.2 4 (by decide)
      rw [h1] at h4
      simp [h5] at h4
  rw [hI.ncard_image]
  have hset : {v : Fin 8 → ZMod 2 | IsFirstBlockVec v} =
      ↑(Finset.univ.filter fun v : Fin 8 → ZMod 2 => IsFirstBlockVec v) := by
    ext v
    simp
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

theorem heart_ncard_secondBlock {φ : (Fin 8 → ZMod 2) → G}
    (hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → w = v ∨ w = v + 1) :
    Set.ncard (φ '' {v | IsSecondBlockVec v}) = 8 := by
  have hI : Set.InjOn φ {v | IsSecondBlockVec v} := by
    intro v hv w hw h
    rcases hinj v w hv.1 hw.1 h with h1 | h1
    · exact h1.symm
    · exfalso
      have h4 : w 0 = 0 := hw.2 0 (by decide)
      have h5 : v 0 = 0 := hv.2 0 (by decide)
      rw [h1] at h4
      simp [h5] at h4
  rw [hI.ncard_image]
  have hset : {v : Fin 8 → ZMod 2 | IsSecondBlockVec v} =
      ↑(Finset.univ.filter fun v : Fin 8 → ZMod 2 => IsSecondBlockVec v) := by
    ext v
    simp
  rw [hset, Set.ncard_coe_finset]
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
