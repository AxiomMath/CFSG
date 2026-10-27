module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutN0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84tw_coset (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q}
    (hxN : x ∈ normalizer (ffPS hQ fr : Set (ProjSim Q))) (hxG : ¬ SimInGStar x)
    (hxx : x * x = 1) :
    (ffX0 fr)⁻¹ * x ∈ ffPS hQ fr ∨
      (ffX0 fr * ffM fr ffRhoPerm ffRhoSet)⁻¹ * x ∈ ffPS hQ fr := by
  have hhN : (ffX0 fr)⁻¹ * x ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
    (normalizer (ffPS hQ fr : Set (ProjSim Q))).mul_mem
      ((normalizer (ffPS hQ fr : Set (ProjSim Q))).inv_mem
        (ffX0_mem_normalizer_ffPS hQ fr)) hxN
  have hhG : SimInGStar ((ffX0 fr)⁻¹ * x) :=
    ffSimInGStar_inv_mul_of_not (ffX0_not_simInGStar fr) hxG
  obtain ⟨σ, K, hhEq, hσ⟩ := ff_N0_monomial hQ hdim hsgn fr hhN hhG
  have hxxPS : x * x ∈ ffPS hQ fr := by rw [hxx]; exact one_mem _
  rcases ff_N0_class hQ fr hσ K with hPS | haPS | hbPS | hrPS
  · left
    rwa [hhEq]
  · exfalso
    set g : ProjSim Q := (ffM fr 1 {0})⁻¹ * ffM fr σ K with hgdef
    have hgPS : g ∈ ffPS hQ fr := by rw [hgdef]; exact haPS
    have hxg : x = ffX0 fr * ((ffM fr 1 {0}) * g) := by
      rw [hgdef, ← hhEq]; group
    have hsq : (ffX0 fr * ((ffM fr 1 {0}) * g)) *
        (ffX0 fr * ((ffM fr 1 {0}) * g)) ∈ ffPS hQ fr := by rw [← hxg]; exact hxxPS
    have hnorm : (ffM fr 1 {0}) ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
      ffM_mem_normalizer_ffPS hQ fr (fun τ hτ => by simpa using hτ) {0}
    have hres := ffOut_sq_aux (H := ProjSim Q) (P := ffPS hQ fr)
      (x := ffX0 fr) (c := ffM fr 1 {0}) (g := g)
      (ffX0_mul_self fr) (ffX0_mem_normalizer_ffPS hQ fr) hnorm hgPS hsq
    have hnotPS : ffM fr ffBeta {2} ∉ ffPS hQ fr := fun hmem =>
      ff_beta_not_mem ((ffM_mem_ffPS_iff hQ fr ffBeta {2}).mp hmem).1
    rw [ffOutClass_conj_a fr, ffOutClass_a_mul fr] at hres
    exact hnotPS hres
  · exfalso
    set g : ProjSim Q := (ffM fr ffBeta ∅)⁻¹ * ffM fr σ K with hgdef
    have hgPS : g ∈ ffPS hQ fr := by rw [hgdef]; exact hbPS
    have hxg : x = ffX0 fr * ((ffM fr ffBeta ∅) * g) := by
      rw [hgdef, ← hhEq]; group
    have hsq : (ffX0 fr * ((ffM fr ffBeta ∅) * g)) *
        (ffX0 fr * ((ffM fr ffBeta ∅) * g)) ∈ ffPS hQ fr := by rw [← hxg]; exact hxxPS
    have hnorm : (ffM fr ffBeta ∅) ∈ normalizer (ffPS hQ fr : Set (ProjSim Q)) :=
      ffM_mem_normalizer_ffPS hQ fr (fun τ hτ => ff_beta_conj_mem hτ) ∅
    have hres := ffOut_sq_aux (H := ProjSim Q) (P := ffPS hQ fr)
      (x := ffX0 fr) (c := ffM fr ffBeta ∅) (g := g)
      (ffX0_mul_self fr) (ffX0_mem_normalizer_ffPS hQ fr) hnorm hgPS hsq
    have hnotPS : ffM fr ffBeta {0} ∉ ffPS hQ fr := fun hmem =>
      ff_beta_not_mem ((ffM_mem_ffPS_iff hQ fr ffBeta {0}).mp hmem).1
    rw [ffOutClass_conj_b fr, ffOutClass_b_mul fr] at hres
    exact hnotPS hres
  · right
    have hρh : (ffM fr ffRhoPerm ffRhoSet)⁻¹ * ((ffX0 fr)⁻¹ * x) ∈ ffPS hQ fr := by
      rw [hhEq]; exact hrPS
    have heq : (ffX0 fr * ffM fr ffRhoPerm ffRhoSet)⁻¹ * x =
        (ffM fr ffRhoPerm ffRhoSet)⁻¹ * ((ffX0 fr)⁻¹ * x) := by group
    rw [heq]
    exact hρh

theorem sec8t84tw_y_inv (fr : NFrame Q (Fin 6) 1) {y : ProjSim Q}
    (hy : y = ffX0 fr ∨ y = ffX0 fr * ffM fr ffRhoPerm ffRhoSet) :
    y * y = 1 ∧ ¬ SimInGStar y := by
  rcases hy with rfl | rfl
  · exact ⟨ffX0_mul_self fr, ffX0_not_simInGStar fr⟩
  · refine ⟨?_, ?_⟩
    · have hξρ : ffX0 fr * ffM fr ffRhoPerm ffRhoSet = ffM fr ffRhoPerm ffRhoSet * ffX0 fr :=
        ffX0_conj_rho fr
      calc (ffX0 fr * ffM fr ffRhoPerm ffRhoSet) * (ffX0 fr * ffM fr ffRhoPerm ffRhoSet)
          = ffX0 fr * (ffM fr ffRhoPerm ffRhoSet * ffX0 fr) * ffM fr ffRhoPerm ffRhoSet := by
            group
        _ = ffX0 fr * (ffX0 fr * ffM fr ffRhoPerm ffRhoSet) * ffM fr ffRhoPerm ffRhoSet := by
            rw [← hξρ]
        _ = (ffX0 fr * ffX0 fr) * (ffM fr ffRhoPerm ffRhoSet * ffM fr ffRhoPerm ffRhoSet) := by
            group
        _ = 1 := by rw [ffX0_mul_self fr, ffRho_mul_self fr, one_mul]
    · intro h
      have hρG : SimInGStar (ffM fr ffRhoPerm ffRhoSet) := ffM_simInGStar fr _ _
      have hξG : SimInGStar (ffX0 fr) := by
        have hh := ffSimInGStar_mul h (ffSimInGStar_inv hρG)
        simpa [mul_assoc] using hh
      exact ffX0_not_simInGStar fr hξG

private def sec8t84tw_Ks (σ : Equiv.Perm (Fin 6)) : Finset (Fin 6) :=
  if σ = Equiv.swap 0 2 * Equiv.swap 1 3 then {2, 3}
  else if σ = Equiv.swap 0 2 * Equiv.swap 4 5 then {2, 5}
  else if σ = Equiv.swap 1 3 * Equiv.swap 4 5 then {3, 5} else ∅

private def sec8t84tw_Kr (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)) : Finset (Fin 6) :=
  symmDiff (ffRhoSet.map ((σ * ffRhoPerm⁻¹)⁻¹).toEmbedding)
    (symmDiff (K.map ffRhoPerm.toEmbedding) (ffRhoSet.map ffRhoPerm.toEmbedding))

private theorem sec8t84tw_x0_conj_K0 (fr : NFrame Q (Fin 6) 1) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ffK0) :
    ffX0 fr * ffM fr σ ∅ = ffM fr 1 (sec8t84tw_Ks σ) * ffX0 fr := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    exact ffX0_conj_of_mat fr (Or.inl (by unfold sec8t84tw_Ks; decide +kernel))

private theorem sec8t84tw_x0_conj (fr : NFrame Q (Fin 6) 1) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ffK0) (K : Finset (Fin 6)) :
    ffX0 fr * ffM fr σ K * ffX0 fr =
      ffM fr (ffConjPerm K) (symmDiff ((sec8t84tw_Ks σ).map (ffConjPerm K)⁻¹.toEmbedding)
        (ffConjSign K)) := by
  have hz : ffM fr σ K = ffM fr σ ∅ * ffM fr 1 K := by
    rw [ffM_mul, mul_one]
    simp only [Finset.map_empty]
    exact (ffM_eq_iff fr).mpr ⟨rfl, Or.inl (by ext i; simp [Finset.mem_symmDiff])⟩
  calc ffX0 fr * ffM fr σ K * ffX0 fr
      = (ffX0 fr * ffM fr σ ∅) * ffM fr 1 K * ffX0 fr := by rw [hz]; group
    _ = ffM fr 1 (sec8t84tw_Ks σ) * (ffX0 fr * ffM fr 1 K) * ffX0 fr := by
        rw [sec8t84tw_x0_conj_K0 fr hσ]; group
    _ = ffM fr 1 (sec8t84tw_Ks σ) * ffM fr (ffConjPerm K) (ffConjSign K) *
          (ffX0 fr * ffX0 fr) := by
        rw [ffX0_conj_signChange]; group
    _ = _ := by
        rw [ffX0_mul_self, mul_one, ffM_mul, one_mul]

private theorem sec8t84tw_conj_perm_eq (fr : NFrame Q (Fin 6) 1) (σ τ : Equiv.Perm (Fin 6))
    (K J : Finset (Fin 6)) :
    ffM fr σ K * ffM fr τ J * (ffM fr σ K)⁻¹ = ffM fr (σ * τ * σ⁻¹)
      (symmDiff (K.map ((τ * σ⁻¹)⁻¹).toEmbedding)
        (symmDiff (J.map σ.toEmbedding) (K.map σ.toEmbedding))) := by
  rw [ffM_inv, mul_assoc, ffM_mul, inv_inv, ffM_mul, mul_assoc]

private theorem sec8t84tw_rho_conj (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6))
    (K : Finset (Fin 6)) :
    ffM fr ffRhoPerm ffRhoSet * ffM fr σ K * ffM fr ffRhoPerm ffRhoSet =
      ffM fr (ffRhoPerm * σ * ffRhoPerm⁻¹) (sec8t84tw_Kr σ K) := by
  have hR : (ffM fr ffRhoPerm ffRhoSet)⁻¹ = ffM fr ffRhoPerm ffRhoSet :=
    inv_eq_of_mul_eq_one_right (ffRho_mul_self fr)
  calc ffM fr ffRhoPerm ffRhoSet * ffM fr σ K * ffM fr ffRhoPerm ffRhoSet
      = ffM fr ffRhoPerm ffRhoSet * ffM fr σ K * (ffM fr ffRhoPerm ffRhoSet)⁻¹ := by rw [hR]
    _ = _ := sec8t84tw_conj_perm_eq fr ffRhoPerm σ ffRhoSet K

private theorem sec8t84tw_x0rho_conj (fr : NFrame Q (Fin 6) 1) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ffK0) (K : Finset (Fin 6)) :
    (ffX0 fr * ffM fr ffRhoPerm ffRhoSet) * ffM fr σ K *
        (ffX0 fr * ffM fr ffRhoPerm ffRhoSet)⁻¹ =
      ffM fr (ffConjPerm (sec8t84tw_Kr σ K))
        (symmDiff ((sec8t84tw_Ks (ffRhoPerm * σ * ffRhoPerm⁻¹)).map
          (ffConjPerm (sec8t84tw_Kr σ K))⁻¹.toEmbedding) (ffConjSign (sec8t84tw_Kr σ K))) := by
  have hσ₁ : ffRhoPerm * σ * ffRhoPerm⁻¹ ∈ ffK0 := by
    revert σ; decide +kernel
  have h1 := sec8t84tw_x0_conj fr hσ₁ (sec8t84tw_Kr σ K)
  rw [← sec8t84tw_rho_conj fr σ K] at h1
  have hR : (ffM fr ffRhoPerm ffRhoSet)⁻¹ = ffM fr ffRhoPerm ffRhoSet :=
    inv_eq_of_mul_eq_one_right (ffRho_mul_self fr)
  rw [← h1, mul_inv_rev, hR, ffX0_inv]
  group

private theorem sec8t84tw_key_x0 : ∀ σ ∈ ffK0, ∀ K : Finset (Fin 6),
    (σ = ffConjPerm K ∧
      (K = symmDiff ((sec8t84tw_Ks σ).map (ffConjPerm K)⁻¹.toEmbedding) (ffConjSign K) ∨
        K = (symmDiff ((sec8t84tw_Ks σ).map (ffConjPerm K)⁻¹.toEmbedding)
          (ffConjSign K))ᶜ)) ↔ (σ = 1 ∧ K ∈ ffF0) := by
  decide +kernel

private theorem sec8t84tw_key_x0rho : ∀ σ ∈ ffK0, ∀ K : Finset (Fin 6),
    (σ = ffConjPerm (sec8t84tw_Kr σ K) ∧
      (K = symmDiff ((sec8t84tw_Ks (ffRhoPerm * σ * ffRhoPerm⁻¹)).map
          (ffConjPerm (sec8t84tw_Kr σ K))⁻¹.toEmbedding) (ffConjSign (sec8t84tw_Kr σ K)) ∨
        K = (symmDiff ((sec8t84tw_Ks (ffRhoPerm * σ * ffRhoPerm⁻¹)).map
          (ffConjPerm (sec8t84tw_Kr σ K))⁻¹.toEmbedding)
            (ffConjSign (sec8t84tw_Kr σ K)))ᶜ)) ↔ (σ = 1 ∧ K ∈ ffF0) := by
  decide +kernel

theorem sec8t84tw_cent_iff (fr : NFrame Q (Fin 6) 1) {y : ProjSim Q}
    (hy : y = ffX0 fr ∨ y = ffX0 fr * ffM fr ffRhoPerm ffRhoSet) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ffK0) (K : Finset (Fin 6)) :
    y * ffM fr σ K = ffM fr σ K * y ↔ σ = 1 ∧ K ∈ ffF0 := by
  have e1 : y * ffM fr σ K = ffM fr σ K * y ↔ y * ffM fr σ K * y⁻¹ = ffM fr σ K :=
    mul_inv_eq_iff_eq_mul.symm
  rw [e1]
  rcases hy with rfl | rfl
  · rw [ffX0_inv, sec8t84tw_x0_conj fr hσ K]
    exact (eq_comm.trans (ffM_eq_iff fr)).trans (sec8t84tw_key_x0 σ hσ K)
  · rw [sec8t84tw_x0rho_conj fr hσ K]
    exact (eq_comm.trans (ffM_eq_iff fr)).trans (sec8t84tw_key_x0rho σ hσ K)

theorem sec8t84tw_signChange_comm (fr : NFrame Q (Fin 6) 1) (J K : Finset (Fin 6)) :
    ffM fr 1 J * ffM fr 1 K = ffM fr 1 K * ffM fr 1 J := by
  rw [ffM_mul, ffM_mul, mul_one, inv_one, ffOutClass_map_one, ffOutClass_map_one,
    symmDiff_comm]

theorem sec8t84tw_signChange_sq (fr : NFrame Q (Fin 6) 1) (J : Finset (Fin 6)) :
    ffM fr 1 J * ffM fr 1 J = 1 := by
  rw [ffM_mul, mul_one, inv_one, ffOutClass_map_one, symmDiff_self, Finset.bot_eq_empty,
    ffM_one]

private theorem sec8t84tw_R4_inj :
    ∀ A ∈ ({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))),
      ∀ B ∈ ({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))),
        (A = B ∨ A = Bᶜ) → A = B := by
  decide +kernel

private theorem sec8t84tw_R4_sub :
    ∀ A ∈ ({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))), A ∈ ffF0 := by
  decide +kernel

private theorem sec8t84tw_F0_cover : ∀ J ∈ ffF0,
    J ∈ ({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))) ∨
      Jᶜ ∈ ({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))) := by
  decide +kernel

theorem sec8t84tw_T4_card (fr : NFrame Q (Fin 6) 1) :
    {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J}.ncard = 4 := by
  classical
  have hset : {z : ProjSim Q | ∃ J ∈ ffF0, z = ffM fr 1 J} =
      ↑(({∅, {0, 2}, {1, 3}, {4, 5}} : Finset (Finset (Fin 6))).image
        (fun J => ffM fr 1 J)) := by
    ext z
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨J, hJ, rfl⟩
      rcases sec8t84tw_F0_cover J hJ with h | h
      · exact ⟨J, h, rfl⟩
      · exact ⟨Jᶜ, h, ffM_compl fr 1 J⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, sec8t84tw_R4_sub J hJ, rfl⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  · decide +kernel
  · intro A hA B hB hAB
    exact sec8t84tw_R4_inj A hA B hB ((ffM_eq_iff fr).mp hAB).2

theorem sec8t84tw_F0_even : ∀ J ∈ ffF0, Even J.card := by
  decide +kernel

theorem sec8t84tw_E16_shape (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {U : Subgroup ↥(omegaProj hQ)}
    (hU : U ≤ ffP1 hQ fr) (hE : IsElemAb2 U 4) (hne : U ≠ ffB1 hQ fr) :
    ∀ w ∈ U, ∃ σ ∈ ffK0, ∃ J ∈ ffF0, ffOmegaToSim hQ w = ffM fr σ J := by
  have hl : IsLiftE16 hQ fr (ffLift hQ U) := ffLift_isLiftE16 hQ hdim hsgn fr hU hE
  have hne' : ffLift hQ U ≠ ffB0 fr := by
    intro h
    rw [← ffLift_ffB1 hQ fr] at h
    exact hne (ffLift_injective hQ h)
  intro w hw
  obtain ⟨g, hg⟩ := omegaToProj_surjective hQ w
  have hgmem : (g : OGroup Q) ∈ ffLift hQ U := by
    rw [mem_ffLift_iff]
    exact ⟨g.2, by rw [hg]; exact hw⟩
  obtain ⟨σ, hσ, J, hJ, hgeq⟩ := ff_liftE16_subset hQ fr hl hne' hgmem
  refine ⟨σ, hσ, J, hJ, ?_⟩
  rw [ffOmegaToSim_apply, ← hg, coe_omegaToProj, hgeq]
  rfl

end CFSG.OddStandard.SmallF3.Omega
