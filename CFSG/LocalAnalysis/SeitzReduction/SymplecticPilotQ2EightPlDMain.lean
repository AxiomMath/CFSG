module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDCompat
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmKind
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 3 ≤ 3 + 2) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}

theorem plDFamily_star_iota (hΦ : ∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k))
    (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h0 : (0 : Fin (3 + 2)) ∉ J.1) (h1 : (1 : Fin (3 + 2)) ∉ J.1) (hm : PlDMoves J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam J) {z : StatedSp (3 + 1) K}
    (hz : peRho hn (x : spinGroup (quadPlus (3 + 2) K)) =
      q2OmIota (r := 3 + 1) (by omega) hK (by omega) z) :
    plDFamily hK hn Φ J x = ((e.symm z : L) : G) := by
  obtain ⟨mz, hmz⟩ := plD_place_star hK hn J h0 h1 x
  rw [plDFamily_star hK hn Φ J h0 h1 hm x hmz]
  refine peTrans_value_iota (peNormal_minus hK le_rfl hΦ) ?_
  rw [hmz, hz]

omit [Finite K] [CharP K 2] in
theorem plD_peMPhi_mem_nsGlobal (i : Fin (3 + 1))
    (g : StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) : peMPhi Φ i g ∈ nsGlobal e := by
  rw [nsGlobal_def]
  exact le_iSup (fun k : Fin (3 + 1) => centralizerPerfectCore (modelToG e (nsTorusSp K k))) i
    (Φ i g).2

theorem range_plDFamily_le (J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2}) :
    (plDFamily hK hn Φ J).range ≤ nsGlobal e := by
  have hε : ∀ y : StatedSp (3 + 1) K, ((e.symm y : L) : G) ∈ nsGlobal e := fun y =>
    le_nsGlobal hK le_rfl e (e.symm y).2
  rintro _ ⟨x, rfl⟩
  by_cases h0 : PlDBad0 J.1
  · obtain ⟨h, hh⟩ := plD_place_bad0 hK hn J h0 x
    rw [pcOMExt_plDG'] at hh
    rw [plDFamily_bad0 hK hn Φ J h0 x hh]
    exact mul_mem (mul_mem (plD_peMPhi_mem_nsGlobal _ _) (hε _))
      (inv_mem (plD_peMPhi_mem_nsGlobal _ _))
  by_cases h1 : PlDBad1 J.1
  · obtain ⟨h, hh⟩ := plD_place_bad1 hK hn J h1 x
    rw [pcOMExt_plDG'] at hh
    rw [plDFamily_bad1 hK hn Φ J h0 h1 x hh]
    exact mul_mem (mul_mem (plD_peMPhi_mem_nsGlobal _ _) (hε _))
      (inv_mem (plD_peMPhi_mem_nsGlobal _ _))
  by_cases hm : PlDMoves J.1
  · have h0' := plD_not_zero_of_star h0 hm
    have h1' := plD_not_one_of_star h1 hm
    obtain ⟨mz, hmz⟩ := plD_place_star hK hn J h0' h1' x
    rw [plDFamily_star hK hn Φ J h0' h1' hm x hmz]
    exact mul_mem (mul_mem (hε _) (plD_peMPhi_mem_nsGlobal _ _)) (inv_mem (hε _))
  · obtain ⟨h, hh⟩ := plD_exists_iota_of_lev hK hn J hm x
    rw [plDFamily_lev hK hn Φ J hm x hh]
    exact hε h

end Family

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsOmegaCTData_minus_of_aligned_eight (hK : Nat.card K = 2) (e : L ≃* StatedSp (3 + 1) K)
    (t : G) (Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) (hal : NsOmMinusAligned e Φ) :
    NsOmegaCTData e .omegaMinus := by
  have hr3 : 3 ≤ 3 := le_rfl
  have hn : 3 ≤ 3 + 2 := by omega
  have hJ₀ : ({(Fin.last 3).castSucc, Fin.last (3 + 1)} : Finset (Fin (3 + 2))).card ≤ 2 :=
    Finset.card_le_two
  have hw₀ : peTorusWord K hn (Fin.last 3).castSucc (Fin.last (3 + 1)) ∈
      (plusDatum (3 + 2) K hn).leviAmalgam ⟨_, hJ₀⟩ :=
    peTorusWord_mem_levi hn (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hρw₀ : peRho hn (peTorusWord K hn (Fin.last 3).castSucc (Fin.last (3 + 1))) =
      q2OmIota (r := 3 + 1) (by omega) hK (by omega) (nsElt (Fin.last 3)) := by
    rw [q2OmIota_nsElt_eq (Fin.last 3) hK hr3]
    exact peRho_peTorusWord (by omega) hn
  have h0₀ : (0 : Fin (3 + 2)) ∉
      ({(Fin.last 3).castSucc, Fin.last (3 + 1)} : Finset (Fin (3 + 2))) := by decide
  have h1₀ : (1 : Fin (3 + 2)) ∉
      ({(Fin.last 3).castSucc, Fin.last (3 + 1)} : Finset (Fin (3 + 2))) := by decide
  have hm₀ : PlDMoves ({(Fin.last 3).castSucc, Fin.last (3 + 1)} : Finset (Fin (3 + 2))) :=
    ⟨Fin.last (3 + 1), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by simp⟩
  have hφw₀ : plDFamily hK hn Φ ⟨_, hJ₀⟩ ⟨_, hw₀⟩ = ((e.symm (nsElt (Fin.last 3)) : L) : G) :=
    plDFamily_star_iota hK hn hΦ ⟨_, hJ₀⟩ h0₀ h1₀ hm₀ ⟨_, hw₀⟩ hρw₀
  have hnt : ∃ J, ∃ x, plDFamily hK hn Φ J x ≠ 1 := by
    refine ⟨⟨_, hJ₀⟩, ⟨_, hw₀⟩, ?_⟩
    rw [hφw₀]
    intro h
    apply nsElt_ne_one (K := K) (Fin.last 3)
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hadm : StatedLieAdmissible .POmegaPlus (3 + 2) 2 1 := ⟨Nat.prime_two, le_rfl, by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨ψ, hψinj, hψrange, hψφ⟩ := exists_ct_of_compatible
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinPlus.{0} (F := K) hadm hK1 hn)
    (q2Omega_center_spinGroup_quadPlus_eq_bot hn) (plDFamily hK hn Φ)
    (isCompatible_plDFamily hK hn hΦ hal) hnt
  have hrot : ∀ k : Fin (3 + 1), ψ ((peRhoEquiv hn).symm (pdMRot k (by omega))) =
      ((e.symm (nsElt k) : L) : G) := by
    refine pe_forall_of_last ?_ ?_
    · have h1 : (peRhoEquiv hn).symm (pdMRot (Fin.last 3) (by omega)) =
          peTorusWord K hn (Fin.last 3).castSucc (Fin.last (3 + 1)) := by
        rw [MulEquiv.symm_apply_eq, peRhoEquiv_apply, peRho_peTorusWord (by omega) hn]
      rw [h1, ← hφw₀]
      exact hψφ ⟨_, hJ₀⟩ ⟨_, hw₀⟩
    · intro k hk ih
      have hfix := peRho_weylD_mem_fixed (K := K) hn hk
      set w := kOmegaFixRes K (by omega : 2 ≤ 3 + 1) ⟨_, hfix⟩ with hwdef
      have hιw : q2OmIota (r := 3 + 1) (by omega) hK (by omega) w =
          peRho hn (weylD K hn k.castSucc) := pe_q2OmIota_kOmegaFixRes hK hr3 _ hfix
      have hJ₁ : ({k.castSucc} : Finset (Fin (3 + 2))).card ≤ 2 := by simp
      have hn₁ : weylD K hn k.castSucc ∈ (plusDatum (3 + 2) K hn).leviAmalgam ⟨_, hJ₁⟩ :=
        weylD_mem_levi hn (Finset.mem_singleton_self _)
      have hm₁ : ¬ PlDMoves ({k.castSucc} : Finset (Fin (3 + 2))) := by
        rintro ⟨j, hj, h3⟩
        rw [Finset.mem_singleton] at hj
        subst hj
        simp only [Fin.val_castSucc] at h3
        omega
      have hψn : ψ (weylD K hn k.castSucc) = ((e.symm w : L) : G) := by
        rw [show weylD K hn k.castSucc = ((⟨_, hn₁⟩ : (plusDatum (3 + 2) K hn).leviAmalgam
          ⟨_, hJ₁⟩) : spinGroup (quadPlus (3 + 2) K)) from rfl, hψφ]
        exact plDFamily_lev hK hn Φ _ hm₁ _ hιw
      have hconj := peRho_weylD_mul_pdMRot (K := K) hn hk (by omega)
      have hP : pdMRot k (by omega) = peRho hn (weylD K hn k.castSucc) *
          pdMRot ⟨k.val + 1, hk⟩ (by omega) * (peRho hn (weylD K hn k.castSucc))⁻¹ := by
        rw [hconj, mul_inv_cancel_right]
      have hsymm : (peRhoEquiv hn).symm (pdMRot k (by omega)) = weylD K hn k.castSucc *
          (peRhoEquiv hn).symm (pdMRot ⟨k.val + 1, hk⟩ (by omega)) *
            (weylD K hn k.castSucc)⁻¹ := by
        rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          peRhoEquiv_apply, hP]
      have hw : w * nsElt ⟨k.val + 1, hk⟩ * w⁻¹ = nsElt (K := K) k := by
        apply q2OmIota_injective (r := 3 + 1) (by omega) hK (by omega)
        rw [map_mul, map_mul, map_inv, hιw, q2OmIota_nsElt_eq _ hK hr3,
          q2OmIota_nsElt_eq _ hK hr3, ← hP]
      rw [hsymm, map_mul, map_mul, map_inv, hψn, ih, ← hw]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hE : ∀ k : Fin (3 + 1), centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ ψ.range := by
    intro k
    have hFinj : Function.Injective (peMPhi Φ k) :=
      Subtype.val_injective.comp (Φ k).injective
    have hFrange : (peMPhi Φ k).range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact (Φ k m).2
      · intro hy
        exact ⟨(Φ k).symm ⟨y, hy⟩, by rw [peMPhi_apply, MulEquiv.apply_symm_apply]⟩
    have : Finite (StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) := Finite.of_injective _ hFinj
    have hperfM : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadMinus (3 + 1) K 1 1))),
        (⊤ : Subgroup (StatedOmega (StatedQuadMinus (3 + 1) K 1 1)))⁆ =
          (⊤ : Subgroup (StatedOmega (StatedQuadMinus (3 + 1) K 1 1))) := by
      apply Subgroup.map_injective hFinj
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hFrange,
        F4Pilot.commutator_centralizerPerfectCore]
    set f := (peRhoEquiv hn).symm.toMonoidHom.comp (pcOMExt (K := K) k) with hfdef
    have hfinj : Function.Injective f :=
      (peRhoEquiv hn).symm.injective.comp (pcOMExt_injective k)
    have hA : ⁅f.range, f.range⁆ = f.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperfM]
    have hAz : f.range.map ψ ≤ centralizer ({((e.symm (nsElt k) : L) : G)} : Set G) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hrot k, ← map_mul, ← map_mul]
      congr 1
      apply (peRhoEquiv hn).injective
      have hc := pcOMExt_range_le_centralizer (K := K) k (by omega) ⟨m, rfl⟩
      rw [mem_centralizer_singleton_iff] at hc
      simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
        MulEquiv.apply_symm_apply]
      exact hc
    have hΦz : (peMPhi Φ k).range =
        perfectCore (centralizer ({((e.symm (nsElt k) : L) : G)} : Set G)) := by
      rw [hFrange, F4Pilot.centralizerPerfectCore_def, nsTorusSp, centralizer_modelToG_zpowers]
    have hcard : Nat.card (StatedOmega (StatedQuadMinus (3 + 1) K 1 1)) ≤ Nat.card f.range :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le
    rw [← hFrange]
    exact range_le_range_of_perfect_centralizer hψinj hA hAz hΦz hcard
  refine ⟨hn, plDFamily hK hn Φ, isCompatible_plDFamily hK hn hΦ hal, ?_⟩
  refine le_antisymm (iSup_le fun J => range_plDFamily_le hK hn J) ?_
  rw [← hψrange, nsGlobal_def]
  exact iSup_le hE

theorem spTwoOmegaMinusPlaceEightInput_holds : SpTwoOmegaMinusPlaceEightInput := by
  intro G _ _ L _ K _ _ _ hK e t _ _ _ Φ hΦ hal
  exact nsOmegaCTData_minus_of_aligned_eight hK e t Φ hΦ hal

end Main

end CFSG.SeitzReduction.SymplecticPilot
