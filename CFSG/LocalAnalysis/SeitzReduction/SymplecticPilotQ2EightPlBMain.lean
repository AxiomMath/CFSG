module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlBCompat
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightOmKind
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPEPlus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Family

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}

theorem plBFamily_star_iota (hΦ : ∀ k, IsNsOmPlusParam hK plB_two_le_three le_rfl e t k (Φ k))
    (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0 : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1)
    (h1 : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ J.1) (hs : PEMShort J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    {z : StatedSp (3 + 1) K}
    (hz : peRhoM hn (q2Omega_irreducible_one_one hK)
        (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) =
      q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK z) :
    plBFamily hK hn Φ J x = ((e.symm z : L) : G) := by
  obtain ⟨mz, hmz⟩ := plB_place_star hK hn J h0 h1 x
  rw [plBFamily_star hK hn Φ J h0 h1 hs x hmz]
  refine peTrans_value_iota (peNormal_plus hK plB_two_le_three le_rfl hΦ) ?_
  rw [hmz, hz]

omit [Finite K] [CharP K 2] in
theorem plB_pePPhi_mem_nsGlobal (i : Fin (3 + 1)) (g : StatedOmega (StatedQuadPlus (3 + 1) K)) :
    pePPhi Φ i g ∈ nsGlobal e := by
  rw [nsGlobal_def]
  exact le_iSup (fun k : Fin (3 + 1) => centralizerPerfectCore (modelToG e (nsTorusSp K k))) i
    (Φ i g).2

theorem range_plBFamily_le (J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2}) :
    (plBFamily hK hn Φ J).range ≤ nsGlobal e := by
  have hε : ∀ y : StatedSp (3 + 1) K, ((e.symm y : L) : G) ∈ nsGlobal e := fun y =>
    le_nsGlobal hK le_rfl e (e.symm y).2
  rintro _ ⟨x, rfl⟩
  by_cases h0 : PlBBad0 J.1
  · obtain ⟨h, hh⟩ := plB_place_bad0 hK hn J h0 x
    rw [pcOPExt_plBG2] at hh
    rw [plBFamily_bad0 hK hn Φ J h0 x hh]
    exact mul_mem (mul_mem (plB_pePPhi_mem_nsGlobal _ _) (hε _))
      (inv_mem (plB_pePPhi_mem_nsGlobal _ _))
  by_cases h1 : PlBBad1 J.1
  · obtain ⟨h, hh⟩ := plB_place_bad1 hK hn J h1 x
    rw [pcOPExt_plBG0] at hh
    rw [plBFamily_bad1 hK hn Φ J h0 h1 x hh]
    exact mul_mem (mul_mem (plB_pePPhi_mem_nsGlobal _ _) (hε _))
      (inv_mem (plB_pePPhi_mem_nsGlobal _ _))
  by_cases hs : PEMShort J.1
  · have h0' := plB_not_zero_of_star h0 hs
    have h1' := plB_not_one_of_star h1 hs
    obtain ⟨mz, hmz⟩ := plB_place_star hK hn J h0' h1' x
    rw [plBFamily_star hK hn Φ J h0' h1' hs x hmz]
    exact mul_mem (mul_mem (hε _) (plB_pePPhi_mem_nsGlobal _ _)) (inv_mem (hε _))
  · obtain ⟨h, hh⟩ := plB_exists_iota_of_lev hK hn J hs x
    rw [plBFamily_lev hK hn Φ J hs x hh]
    exact hε h

end Family

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsOmegaCTData_plus_of_aligned_eight (hK : Nat.card K = 2) (e : L ≃* StatedSp (3 + 1) K)
    (t : G) (Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
      centralizerPerfectCore (modelToG e (nsTorusSp K k)))
    (hΦ : ∀ k, IsNsOmPlusParam hK plB_two_le_three le_rfl e t k (Φ k))
    (hal : NsOmPlusAligned e Φ) :
    NsOmegaCTData e .omegaPlus := by
  have hr2 : 2 ≤ 3 := by norm_num
  have hn : 4 ≤ 3 + 1 + 1 := by norm_num
  have hirr := q2Omega_irreducible_one_one hK
  have hJ₀ : ({((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))} :
      Finset (Fin (3 + 1 + 1 - 1))).card ≤ 2 := by simp
  have hw₀ : peShortWord (3 + 1 + 1) hirr ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) ∈
      (minusDatum (3 + 1 + 1) hirr).leviAmalgam ⟨_, hJ₀⟩ :=
    peShortWord_mem_levi hirr (by simp) (Finset.mem_singleton_self _)
  have hρw₀ : peRhoM hn hirr
      (peShortWord (3 + 1 + 1) hirr ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))) =
      q2OmMIota (r := 3 + 1) (by omega) hirr hK (nsElt (Fin.last 3)) := by
    rw [q2OmMIota_nsElt_eq (Fin.last 3) hK hr2]
    exact peRhoM_peShortWord hK hn hr2
  have h0₀ : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉
      ({((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))} : Finset (Fin (3 + 1 + 1 - 1))) := by
    simp [Fin.ext_iff]
  have h1₀ : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉
      ({((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))} : Finset (Fin (3 + 1 + 1 - 1))) := by
    simp [Fin.ext_iff]
  have hs₀ : PEMShort ({((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))} :
      Finset (Fin (3 + 1 + 1 - 1))) := ⟨_, Finset.mem_singleton_self _, by simp⟩
  have hφw₀ : plBFamily hK hn Φ ⟨_, hJ₀⟩ ⟨_, hw₀⟩ = ((e.symm (nsElt (Fin.last 3)) : L) : G) :=
    plBFamily_star_iota hK hn hΦ ⟨_, hJ₀⟩ h0₀ h1₀ hs₀ ⟨_, hw₀⟩ hρw₀
  have hnt : ∃ J, ∃ x, plBFamily hK hn Φ J x ≠ 1 := by
    refine ⟨⟨_, hJ₀⟩, ⟨_, hw₀⟩, ?_⟩
    rw [hφw₀]
    intro h
    apply nsElt_ne_one (K := K) (Fin.last 3)
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hadm : StatedLieAdmissible .POmegaMinus (3 + 1 + 1) 2 1 :=
    ⟨Nat.prime_two, le_rfl, by omega⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  obtain ⟨ψ, hψinj, hψrange, hψφ⟩ := exists_ct_of_compatible
    (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinMinus.{0} (F := K) hirr hadm hK1)
    (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hn hirr)
    (plBFamily hK hn Φ) (isCompatible_plBFamily hK hn hΦ hal) hnt
  have hrot : ∀ k : Fin (3 + 1), ψ ((peRhoMEquiv hn hirr).symm (pdPRot k hK hr2)) =
      ((e.symm (nsElt k) : L) : G) := by
    refine pe_forall_of_last ?_ ?_
    · have h1 : (peRhoMEquiv hn hirr).symm (pdPRot (Fin.last 3) hK hr2) =
          peShortWord (3 + 1 + 1) hirr ((Fin.last 3 : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) := by
        rw [MulEquiv.symm_apply_eq, peRhoMEquiv_apply, peRhoM_peShortWord hK hn hr2]
      rw [h1, ← hφw₀]
      exact hψφ ⟨_, hJ₀⟩ ⟨_, hw₀⟩
    · intro k hk ih
      have hfix := peRhoM_minusWeyl_mem_fixed (K := K) hK hn hk
      set w := kOmMFixRes K (by omega : 3 ≤ 3 + 1) hirr ⟨_, hfix⟩ with hwdef
      have hιw : q2OmMIota (r := 3 + 1) (by omega) hirr hK w =
          peRhoM hn hirr (minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1))) :=
        pe_q2OmMIota_kOmMFixRes hK hr2 _ hfix
      have hJ₁ : ({(k : Fin (3 + 1 + 1 - 1))} : Finset (Fin (3 + 1 + 1 - 1))).card ≤ 2 := by simp
      have hn₁ : minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1)) ∈
          (minusDatum (3 + 1 + 1) hirr).leviAmalgam ⟨_, hJ₁⟩ :=
        minusWeyl_mem_levi hirr (Finset.mem_singleton_self _)
      have hs₁ : ¬ PEMShort ({(k : Fin (3 + 1 + 1 - 1))} : Finset (Fin (3 + 1 + 1 - 1))) := by
        rintro ⟨j, hj, hj3⟩
        rw [Finset.mem_singleton] at hj
        subst hj
        exact hj3 (by simpa using hk)
      have hψn : ψ (minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1))) =
          ((e.symm w : L) : G) := by
        rw [show minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1)) =
          ((⟨_, hn₁⟩ : (minusDatum (3 + 1 + 1) hirr).leviAmalgam ⟨_, hJ₁⟩) :
            spinGroup (quadMinus (3 + 1 + 1) K 1 1)) from rfl, hψφ]
        exact plBFamily_lev hK hn Φ _ hs₁ _ hιw
      have hconj := peRhoM_minusWeyl_mul_pdPRot (K := K) hK hn hk hr2
      have hP : pdPRot k hK hr2 = peRhoM hn hirr (minusWeyl (3 + 1 + 1) hirr
          (k : Fin (3 + 1 + 1 - 1))) * pdPRot ⟨k.val + 1, hk⟩ hK hr2 *
            (peRhoM hn hirr (minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1))))⁻¹ := by
        rw [hconj, mul_inv_cancel_right]
      have hsymm : (peRhoMEquiv hn hirr).symm (pdPRot k hK hr2) =
          minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1)) *
            (peRhoMEquiv hn hirr).symm (pdPRot ⟨k.val + 1, hk⟩ hK hr2) *
              (minusWeyl (3 + 1 + 1) hirr (k : Fin (3 + 1 + 1 - 1)))⁻¹ := by
        rw [MulEquiv.symm_apply_eq, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
          peRhoMEquiv_apply, hP]
      have hw : w * nsElt ⟨k.val + 1, hk⟩ * w⁻¹ = nsElt (K := K) k := by
        apply q2OmMIota_injective (r := 3 + 1) (by omega) hirr hK
        rw [map_mul, map_mul, map_inv, hιw, q2OmMIota_nsElt_eq _ hK hr2,
          q2OmMIota_nsElt_eq _ hK hr2, ← hP]
      rw [hsymm, map_mul, map_mul, map_inv, hψn, ih, ← hw]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hE : ∀ k : Fin (3 + 1), centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ ψ.range := by
    intro k
    have hFinj : Function.Injective (pePPhi Φ k) :=
      Subtype.val_injective.comp (Φ k).injective
    have hFrange : (pePPhi Φ k).range = centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      ext y
      constructor
      · rintro ⟨m, rfl⟩
        exact (Φ k m).2
      · intro hy
        exact ⟨(Φ k).symm ⟨y, hy⟩, by rw [pePPhi_apply, MulEquiv.apply_symm_apply]⟩
    have : Finite (StatedOmega (StatedQuadPlus (3 + 1) K)) := Finite.of_injective _ hFinj
    have hperfM : ⁅(⊤ : Subgroup (StatedOmega (StatedQuadPlus (3 + 1) K))),
        (⊤ : Subgroup (StatedOmega (StatedQuadPlus (3 + 1) K)))⁆ =
          (⊤ : Subgroup (StatedOmega (StatedQuadPlus (3 + 1) K))) := by
      apply Subgroup.map_injective hFinj
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, hFrange,
        F4Pilot.commutator_centralizerPerfectCore]
    set f := (peRhoMEquiv hn hirr).symm.toMonoidHom.comp (pcOPExt (K := K) k) with hfdef
    have hfinj : Function.Injective f :=
      (peRhoMEquiv hn hirr).symm.injective.comp (pcOPExt_injective k)
    have hA : ⁅f.range, f.range⁆ = f.range := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperfM]
    have hAz : f.range.map ψ ≤ centralizer ({((e.symm (nsElt k) : L) : G)} : Set G) := by
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hrot k, ← map_mul, ← map_mul]
      congr 1
      apply (peRhoMEquiv hn hirr).injective
      have hc := pcOPExt_range_le_centralizer (K := K) k hK hr2 ⟨m, rfl⟩
      rw [mem_centralizer_singleton_iff] at hc
      simp only [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
        MulEquiv.apply_symm_apply]
      exact hc
    have hΦz : (pePPhi Φ k).range =
        perfectCore (centralizer ({((e.symm (nsElt k) : L) : G)} : Set G)) := by
      rw [hFrange, F4Pilot.centralizerPerfectCore_def, nsTorusSp, centralizer_modelToG_zpowers]
    have hcard : Nat.card (StatedOmega (StatedQuadPlus (3 + 1) K)) ≤ Nat.card f.range :=
      (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).le
    rw [← hFrange]
    exact range_le_range_of_perfect_centralizer hψinj hA hAz hΦz hcard
  refine ⟨1, 1, hirr, plBFamily hK hn Φ, isCompatible_plBFamily hK hn hΦ hal, ?_⟩
  refine le_antisymm (iSup_le fun J => range_plBFamily_le hK hn J) ?_
  rw [← hψrange, nsGlobal_def]
  exact iSup_le hE

theorem spTwoOmegaPlusPlaceEightInput_holds : SpTwoOmegaPlusPlaceEightInput := by
  intro G _ _ L _ K _ _ _ hK e t _ _ _ Φ hΦ hal
  exact nsOmegaCTData_plus_of_aligned_eight hK e t Φ hΦ hal

end Main

end CFSG.SeitzReduction.SymplecticPilot
