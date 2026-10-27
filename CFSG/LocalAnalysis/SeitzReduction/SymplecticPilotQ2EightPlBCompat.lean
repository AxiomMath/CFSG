module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlBFamily

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Fix

variable {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1)

theorem plBE2_fix_star :
    (((plBE2 hK hn : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl ((⟨0, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) :
          Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩) =
      Pi.single (Sum.inl ((⟨0, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) :
        Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ ∧
    (((plBE2 hK hn : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr (Sum.inl ((⟨0, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))) :
          Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩) =
      Pi.single (Sum.inr (Sum.inl ((⟨0, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))) :
        Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ :=
  ⟨plBSieg_mulVec_inl_add_pdPP hK hn _ _ _ (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)),
    plBSieg_mulVec_inr_add_pdPP hK hn _ _ _ (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num))⟩

theorem plBE0_fix_star2 :
    (((plBE0 hK hn : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl ((⟨2, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) :
          Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩) =
      Pi.single (Sum.inl ((⟨2, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1)) :
        Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ ∧
    (((plBE0 hK hn : StatedOmega (StatedQuadMinus (3 + 1 + 1) K 1 1)) :
      GL (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2)
          (Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr (Sum.inl ((⟨2, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))) :
          Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩) =
      Pi.single (Sum.inr (Sum.inl ((⟨2, by omega⟩ : Fin (3 + 1)) : Fin (3 + 1 + 1 - 1))) :
        Fin (3 + 1 + 1 - 1) ⊕ Fin (3 + 1 + 1 - 1) ⊕ Fin 2) 1 + pdPP ⟨1, by omega⟩ :=
  ⟨plBSieg_mulVec_inl_add_pdPP hK hn _ _ _ (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)),
    plBSieg_mulVec_inr_add_pdPP hK hn _ _ _ (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num))⟩

end Fix

section Compat

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 4 ≤ 3 + 1 + 1) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadPlus (3 + 1) K) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}
  (hΦ : ∀ k, IsNsOmPlusParam hK plB_two_le_three le_rfl e t k (Φ k)) (hal : NsOmPlusAligned e Φ)
include hΦ hal

theorem plB_compat_star_bad0 (I J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0I : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ I.1)
    (h1I : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ I.1) (hsI : PEMShort I.1)
    (hb0J : PlBBad0 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam I)
    (y : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    (hρ : peRhoM hn (q2Omega_irreducible_one_one hK) (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) =
      peRhoM hn (q2Omega_irreducible_one_one hK) (y : spinGroup (quadMinus (3 + 1 + 1) K 1 1))) :
    plBFamily hK hn Φ I x = plBFamily hK hn Φ J y := by
  obtain ⟨mz, hmz⟩ := plB_place_star hK hn I h0I h1I x
  obtain ⟨h', hh'⟩ := plB_place_bad0 hK hn J hb0J y
  rw [pcOPExt_plBG2] at hh'
  rw [plBFamily_star hK hn Φ I h0I h1I hsI x hmz, plBFamily_bad0 hK hn Φ J hb0J y hh']
  obtain ⟨hA, hB⟩ := plBE2_fix_star (K := K) hK hn
  refine (plB_agree_trans hK hn hΦ hal plB_two_ne_last plB_two_ne_one plB_one_ne_last
    (pcOPExt_plBG2 hK hn) ⟨0, by omega⟩ (y := plBT01 hK (by norm_num))
    (q2OmMIota_plBT01_mem_range hK (by norm_num) (k := Fin.last 3) (by decide) (by decide))
    ?_ ?_ hh' (hmz.trans (by rw [hρ]))).symm
  · rw [q2OmMIota_plBT01_mulVec_a]
    exact hA
  · rw [q2OmMIota_plBT01_mulVec_b]
    exact hB

theorem plB_compat_star_bad1 (I J : {J : Finset (Fin (3 + 1 + 1 - 1)) // J.card ≤ 2})
    (h0I : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ I.1)
    (h1I : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∉ I.1) (hsI : PEMShort I.1)
    (hshort : ∀ j ∈ I.1, 3 ≤ j.val) (hb0J : ¬ PlBBad0 J.1) (hb1J : PlBBad1 J.1)
    (x : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam I)
    (y : (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam J)
    (hρ : peRhoM hn (q2Omega_irreducible_one_one hK) (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) =
      peRhoM hn (q2Omega_irreducible_one_one hK) (y : spinGroup (quadMinus (3 + 1 + 1) K 1 1))) :
    plBFamily hK hn Φ I x = plBFamily hK hn Φ J y := by
  obtain ⟨mz, hmz⟩ := plB_place_star hK hn I h0I h1I x
  obtain ⟨mz2, hmz2⟩ := plB_place_star2 hK hn I hshort x
  obtain ⟨h', hh'⟩ := plB_place_bad1 hK hn J hb1J y
  rw [pcOPExt_plBG0] at hh'
  rw [plBFamily_star hK hn Φ I h0I h1I hsI x hmz, plBFamily_bad1 hK hn Φ J hb0J hb1J y hh']
  obtain ⟨hA, hB⟩ := plBE0_fix_star2 (K := K) hK hn
  have h1 := plB_agree_trans hK hn hΦ hal plB_zero_ne_last plB_zero_ne_one plB_one_ne_last
    (pcOPExt_plBG0 hK hn) ⟨2, by omega⟩
    (y := plBT01 hK (by norm_num) * plBT21 hK (by norm_num))
    (q2OmMIota_plBT0121_mem_range hK (by norm_num) (k := Fin.last 3) (by decide) (by decide)
      (by decide))
    (by rw [q2OmMIota_plBT0121_mulVec_a]; exact hA) (by rw [q2OmMIota_plBT0121_mulVec_b]; exact hB)
    hh' (hmz2.trans (by rw [hρ]))
  have h2 := peTrans_value_eq (ext := fun k => pcOPExt (K := K) k) (Φ := pePPhi Φ)
    (iota := q2OmMIota (r := 3 + 1) (by omega) (q2Omega_irreducible_one_one hK) hK)
    (ε := L.subtype.comp e.symm.toMonoidHom) (peAligned_plus hal)
    (peNormal_plus hK plB_two_le_three le_rfl hΦ) (i := ⟨0, by omega⟩) (i' := ⟨2, by omega⟩)
    (y := plBT01 hK (by norm_num)) (y' := plBT01 hK (by norm_num) * plBT21 hK (by norm_num))
    (by
      rw [inv_mul_cancel_left]
      exact q2OmMIota_plBT21_mem_range hK (by norm_num) (k := ⟨0, by omega⟩) (by simp) (by simp))
    hmz hmz2
  exact h2.trans h1.symm

theorem isCompatible_plBFamily :
    CFSG.LieType.CurtisTits.IsCompatible
      (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).leviAmalgam
      (plBFamily hK hn Φ) := by
  intro I J hIJ x y hxy
  have hsub : I.1 ⊆ J.1 := hIJ
  rcases I.1.eq_empty_or_nonempty with hI | hI
  · have hx : (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) = 1 := by
      have h := x.2
      change (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) ∈
        CFSG.LieType.CurtisTits.levi
          (minusDatum (3 + 1 + 1) (q2Omega_irreducible_one_one hK)).rootGroup I.1 at h
      rw [hI, pe_levi_empty_eq_bot, Subgroup.mem_bot] at h
      exact h
    have hx1 : x = 1 := Subtype.ext hx
    have hy1 : y = 1 := Subtype.ext (hxy.symm.trans hx)
    rw [hx1, hy1, map_one, map_one]
  have hρ : peRhoM hn (q2Omega_irreducible_one_one hK)
      (x : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) =
      peRhoM hn (q2Omega_irreducible_one_one hK) (y : spinGroup (quadMinus (3 + 1 + 1) K 1 1)) :=
    congrArg _ hxy
  by_cases hsI : PEMShort I.1
  · have hsJ : PEMShort J.1 := by
      obtain ⟨j, hj, h3⟩ := hsI
      exact ⟨j, hsub hj, h3⟩
    by_cases h0I : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ I.1
    ·
      have hb0I : PlBBad0 I.1 := ⟨hsI, h0I⟩
      have hb0J : PlBBad0 J.1 := ⟨hsJ, hsub h0I⟩
      obtain ⟨h', hh'⟩ := plB_place_bad0 hK hn I hb0I x
      rw [pcOPExt_plBG2] at hh'
      rw [plBFamily_bad0 hK hn Φ I hb0I x hh',
        plBFamily_bad0 hK hn Φ J hb0J y (hh'.trans (by rw [hρ]))]
    by_cases h1I : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ I.1
    ·
      have hb1I : PlBBad1 I.1 := ⟨hsI, h1I⟩
      have hb1J : PlBBad1 J.1 := ⟨hsJ, hsub h1I⟩
      have hb0I : ¬ PlBBad0 I.1 := fun h => h0I h.2
      have hb0J : ¬ PlBBad0 J.1 := fun h => by
        have := plB_val_of_bad0 J.2 h (hsub h1I)
        simp at this
      obtain ⟨h', hh'⟩ := plB_place_bad1 hK hn I hb1I x
      rw [pcOPExt_plBG0] at hh'
      rw [plBFamily_bad1 hK hn Φ I hb0I hb1I x hh',
        plBFamily_bad1 hK hn Φ J hb0J hb1J y (hh'.trans (by rw [hρ]))]
    by_cases h0J : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J.1
    · exact plB_compat_star_bad0 hK hn hΦ hal I J h0I h1I hsI ⟨hsJ, h0J⟩ x y hρ
    by_cases h1J : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J.1
    · have hshort : ∀ j ∈ I.1, 3 ≤ j.val := by
        intro j hj
        rcases plB_val_of_bad1 J.2 ⟨hsJ, h1J⟩ (hsub hj) with h | h
        · exfalso
          have hj1 : j = (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) := Fin.ext h
          exact h1I (hj1 ▸ hj)
        · omega
      exact plB_compat_star_bad1 hK hn hΦ hal I J h0I h1I hsI hshort (fun h => h0J h.2)
        ⟨hsJ, h1J⟩ x y hρ
    ·
      obtain ⟨mz, hmz⟩ := plB_place_star hK hn I h0I h1I x
      rw [plBFamily_star hK hn Φ I h0I h1I hsI x hmz,
        plBFamily_star hK hn Φ J h0J h1J hsJ y (hmz.trans (by rw [hρ]))]
  ·
    obtain ⟨h, hh⟩ := plB_exists_iota_of_lev hK hn I hsI x
    rw [plBFamily_lev hK hn Φ I hsI x hh]
    by_cases hsJ : PEMShort J.1
    · by_cases h0J : (⟨0, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J.1
      · have hb0J : PlBBad0 J.1 := ⟨hsJ, h0J⟩
        have hval : ∀ j ∈ I.1, j.val = 0 := fun j hj => by
          have h1 := plB_val_of_bad0 J.2 hb0J (hsub hj)
          have h2 := plB_val_lt_of_not_short hsI hj
          omega
        obtain ⟨h', hh'⟩ := plB_place_bad0 hK hn J hb0J y
        rw [pcOPExt_plBG2] at hh'
        rw [plBFamily_bad0 hK hn Φ J hb0J y hh']
        refine (plB_agree_comm hK hn hΦ hal plB_two_ne_last plB_two_ne_one plB_one_ne_last
          (pcOPExt_plBG2 hK hn) I x hsI ?_ ?_ hh (hh'.trans (by rw [hρ]; rfl))).symm
        · refine plB_not_mem_peSuppM fun j hj => ?_
          have := hval j hj
          exact ⟨by simp; omega, fun _ => by simp; omega⟩
        · refine plB_not_mem_peSuppM fun j hj => ?_
          have := hval j hj
          exact ⟨by simp; omega, fun _ => by simp; omega⟩
      by_cases h1J : (⟨1, by omega⟩ : Fin (3 + 1 + 1 - 1)) ∈ J.1
      · have hb0J : ¬ PlBBad0 J.1 := fun h => h0J h.2
        have hb1J : PlBBad1 J.1 := ⟨hsJ, h1J⟩
        have hval : ∀ j ∈ I.1, j.val = 1 := fun j hj => by
          have h1 := plB_val_of_bad1 J.2 hb1J (hsub hj)
          have h2 := plB_val_lt_of_not_short hsI hj
          omega
        obtain ⟨h', hh'⟩ := plB_place_bad1 hK hn J hb1J y
        rw [pcOPExt_plBG0] at hh'
        rw [plBFamily_bad1 hK hn Φ J hb0J hb1J y hh']
        refine (plB_agree_comm hK hn hΦ hal plB_zero_ne_last plB_zero_ne_one plB_one_ne_last
          (pcOPExt_plBG0 hK hn) I x hsI ?_ ?_ hh (hh'.trans (by rw [hρ]; rfl))).symm
        · refine plB_not_mem_peSuppM fun j hj => ?_
          have := hval j hj
          exact ⟨by simp; omega, fun _ => by simp⟩
        · refine plB_not_mem_peSuppM fun j hj => ?_
          have := hval j hj
          exact ⟨by simp; omega, fun _ => by simp; omega⟩
      ·
        obtain ⟨mz, hmz⟩ := plB_place_star hK hn J h0J h1J y
        rw [plBFamily_star hK hn Φ J h0J h1J hsJ y hmz]
        refine (peTrans_value_iota (peNormal_plus hK plB_two_le_three le_rfl hΦ) ?_).symm
        rw [hmz, hh, hρ]
    · exact (plBFamily_lev hK hn Φ J hsJ y (hh.trans hρ)).symm

end Compat

end CFSG.SeitzReduction.SymplecticPilot
