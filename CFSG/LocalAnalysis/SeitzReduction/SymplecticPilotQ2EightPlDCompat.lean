module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightPlDFamily

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Compat

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = 2) (hn : 3 ≤ 3 + 2) {e : L ≃* StatedSp (3 + 1) K} {t : G}
  {Φ : ∀ k : Fin (3 + 1), StatedOmega (StatedQuadMinus (3 + 1) K 1 1) ≃*
    centralizerPerfectCore (modelToG e (nsTorusSp K k))}

theorem plD_mem_S2 : ((2 : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∈
      ({(2 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) ∧
    ((Fin.last 3).castSucc : Fin (3 + 2)) ∈
      ({(2 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) ∧
    Fin.last (3 + 1) ∈
      ({(2 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide

theorem plD_mem_S0 : ((0 : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∈
      ({(0 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) ∧
    ((Fin.last 3).castSucc : Fin (3 + 2)) ∈
      ({(0 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) ∧
    Fin.last (3 + 1) ∈
      ({(0 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide

omit [Finite K] in
theorem plDSieg_two_fix_star :
    (((plDSieg (K := K) (r := 3) (by omega) plD_two_ne_last :
      StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩) =
      Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ ∧
    (((plDSieg (K := K) (r := 3) (by omega) plD_two_ne_last :
      StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
          (Pi.single (Sum.inr (⟨0, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩) =
      Pi.single (Sum.inr (⟨0, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  obtain ⟨h2, h3, h4⟩ := plD_mem_S2
  have ha : ((⟨0, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉
      ({(2 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide
  have hb : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉
      ({(2 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide
  exact ⟨plDSieg_mulVec_of_peOff (by omega) plD_two_ne_last (peOff_inl_add_pdMP ha hb) h2 h3 h4,
    plDSieg_mulVec_of_peOff (by omega) plD_two_ne_last (peOff_inr_add_pdMP ha hb) h2 h3 h4⟩

omit [Finite K] in
theorem plDSieg_zero_fix_star2 :
    (((plDSieg (K := K) (r := 3) (by omega) plD_zero_ne_last :
      StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
          (Pi.single (Sum.inl (⟨2, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩) =
      Pi.single (Sum.inl (⟨2, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ ∧
    (((plDSieg (K := K) (r := 3) (by omega) plD_zero_ne_last :
      StatedOmega (StatedQuadPlus (3 + 2) K)) : GL (Fin (3 + 2) ⊕ Fin (3 + 2)) K) :
        Matrix (Fin (3 + 2) ⊕ Fin (3 + 2)) (Fin (3 + 2) ⊕ Fin (3 + 2)) K) *ᵥ
          (Pi.single (Sum.inr (⟨2, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩) =
      Pi.single (Sum.inr (⟨2, by omega⟩ : Fin (3 + 1)).castSucc) 1 + pdMP ⟨1, by omega⟩ := by
  obtain ⟨h0, h3, h4⟩ := plD_mem_S0
  have ha : ((⟨2, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉
      ({(0 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide
  have hb : ((⟨1, by omega⟩ : Fin (3 + 1)).castSucc : Fin (3 + 2)) ∉
      ({(0 : Fin (3 + 1)).castSucc, (Fin.last 3).castSucc, Fin.last (3 + 1)} :
        Finset (Fin (3 + 2))) := by decide
  exact ⟨plDSieg_mulVec_of_peOff (by omega) plD_zero_ne_last (peOff_inl_add_pdMP ha hb) h0 h3 h4,
    plDSieg_mulVec_of_peOff (by omega) plD_zero_ne_last (peOff_inr_add_pdMP ha hb) h0 h3 h4⟩

variable (hΦ : ∀ k, IsNsOmMinusParam hK le_rfl e t k (Φ k)) (hal : NsOmMinusAligned e Φ)
include hΦ hal

theorem plD_compat_star_bad0 (I J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h0I : (0 : Fin (3 + 2)) ∉ I.1) (h1I : (1 : Fin (3 + 2)) ∉ I.1) (hmI : PlDMoves I.1)
    (hb0J : PlDBad0 J.1) (x : (plusDatum (3 + 2) K hn).leviAmalgam I)
    (y : (plusDatum (3 + 2) K hn).leviAmalgam J)
    (hρ : peRho hn (x : spinGroup (quadPlus (3 + 2) K)) =
      peRho hn (y : spinGroup (quadPlus (3 + 2) K))) :
    plDFamily hK hn Φ I x = plDFamily hK hn Φ J y := by
  obtain ⟨mz, hmz⟩ := plD_place_star hK hn I h0I h1I x
  obtain ⟨h', hh'⟩ := plD_place_bad0 hK hn J hb0J y
  rw [pcOMExt_plDG'] at hh'
  rw [plDFamily_star hK hn Φ I h0I h1I hmI x hmz, plDFamily_bad0 hK hn Φ J hb0J y hh']
  obtain ⟨hA, hB⟩ := plDSieg_two_fix_star (K := K)
  refine (plD_agree_trans hK hΦ hal plD_two_ne_last ⟨0, by omega⟩ (y := plDT01 le_rfl)
    (q2OmIota_plDT01_mem_range hK le_rfl (k := Fin.last 3) (by decide) (by decide)) ?_ ?_ hh'
    (hmz.trans (by rw [hρ]))).symm
  · rw [q2OmIota_plDT01_mulVec_a]
    exact hA
  · rw [q2OmIota_plDT01_mulVec_b]
    exact hB

theorem plD_compat_star_bad1 (I J : {J : Finset (Fin (3 + 2)) // J.card ≤ 2})
    (h0I : (0 : Fin (3 + 2)) ∉ I.1) (h1I : (1 : Fin (3 + 2)) ∉ I.1) (hmI : PlDMoves I.1)
    (hfork : ∀ j ∈ I.1, 3 ≤ j.val) (hb0J : ¬ PlDBad0 J.1) (hb1J : PlDBad1 J.1)
    (x : (plusDatum (3 + 2) K hn).leviAmalgam I) (y : (plusDatum (3 + 2) K hn).leviAmalgam J)
    (hρ : peRho hn (x : spinGroup (quadPlus (3 + 2) K)) =
      peRho hn (y : spinGroup (quadPlus (3 + 2) K))) :
    plDFamily hK hn Φ I x = plDFamily hK hn Φ J y := by
  obtain ⟨mz, hmz⟩ := plD_place_star hK hn I h0I h1I x
  obtain ⟨mz2, hmz2⟩ := plD_place_star2 hK hn I hfork x
  obtain ⟨h', hh'⟩ := plD_place_bad1 hK hn J hb1J y
  rw [pcOMExt_plDG'] at hh'
  rw [plDFamily_star hK hn Φ I h0I h1I hmI x hmz, plDFamily_bad1 hK hn Φ J hb0J hb1J y hh']
  obtain ⟨hA, hB⟩ := plDSieg_zero_fix_star2 (K := K)
  have h1 := plD_agree_trans hK hΦ hal plD_zero_ne_last ⟨2, by omega⟩
    (y := plDT01 le_rfl * plDT21 le_rfl)
    (q2OmIota_plDT0121_mem_range hK le_rfl (k := Fin.last 3) (by decide) (by decide) (by decide))
    (by rw [q2OmIota_plDT0121_mulVec_a]; exact hA) (by rw [q2OmIota_plDT0121_mulVec_b]; exact hB)
    hh' (hmz2.trans (by rw [hρ]))
  have h2 := peTrans_value_eq (ext := fun k => pcOMExt (K := K) k) (Φ := peMPhi Φ)
    (iota := q2OmIota (r := 3 + 1) (by omega) hK (by omega))
    (ε := L.subtype.comp e.symm.toMonoidHom) (peAligned_minus hal)
    (peNormal_minus hK le_rfl hΦ) (i := ⟨0, by omega⟩) (i' := ⟨2, by omega⟩)
    (y := plDT01 le_rfl) (y' := plDT01 le_rfl * plDT21 le_rfl)
    (by
      rw [inv_mul_cancel_left]
      exact q2OmIota_plDT21_mem_range hK le_rfl (k := ⟨0, by omega⟩) (by simp) (by simp))
    hmz hmz2
  exact h2.trans h1.symm

theorem isCompatible_plDFamily :
    CFSG.LieType.CurtisTits.IsCompatible (plusDatum (3 + 2) K hn).leviAmalgam
      (plDFamily hK hn Φ) := by
  intro I J hIJ x y hxy
  have hsub : I.1 ⊆ J.1 := hIJ
  rcases I.1.eq_empty_or_nonempty with hI | hI
  · have hx : (x : spinGroup (quadPlus (3 + 2) K)) = 1 := by
      have h := x.2
      change (x : spinGroup (quadPlus (3 + 2) K)) ∈
        CFSG.LieType.CurtisTits.levi (plusDatum (3 + 2) K hn).rootGroup I.1 at h
      rw [hI, pe_levi_empty_eq_bot, Subgroup.mem_bot] at h
      exact h
    have hx1 : x = 1 := Subtype.ext hx
    have hy1 : y = 1 := Subtype.ext (hxy.symm.trans hx)
    rw [hx1, hy1, map_one, map_one]
  have hρ : peRho hn (x : spinGroup (quadPlus (3 + 2) K)) =
      peRho hn (y : spinGroup (quadPlus (3 + 2) K)) := congrArg _ hxy
  by_cases hmI : PlDMoves I.1
  · have hmJ : PlDMoves J.1 := by
      obtain ⟨j, hj, h3⟩ := hmI
      exact ⟨j, hsub hj, h3⟩
    by_cases h0I : (0 : Fin (3 + 2)) ∈ I.1
    ·
      have hb0I : PlDBad0 I.1 := ⟨hmI, h0I⟩
      have hb0J : PlDBad0 J.1 := ⟨hmJ, hsub h0I⟩
      obtain ⟨h', hh'⟩ := plD_place_bad0 hK hn I hb0I x
      rw [pcOMExt_plDG'] at hh'
      rw [plDFamily_bad0 hK hn Φ I hb0I x hh',
        plDFamily_bad0 hK hn Φ J hb0J y (hh'.trans (by rw [hρ]))]
    by_cases h1I : (1 : Fin (3 + 2)) ∈ I.1
    ·
      have hb1I : PlDBad1 I.1 := ⟨hmI, h1I⟩
      have hb1J : PlDBad1 J.1 := ⟨hmJ, hsub h1I⟩
      have hb0I : ¬ PlDBad0 I.1 := fun h => h0I h.2
      have hb0J : ¬ PlDBad0 J.1 := fun h => by
        have := plD_val_of_bad0 J.2 h (hsub h1I)
        simp at this
      obtain ⟨h', hh'⟩ := plD_place_bad1 hK hn I hb1I x
      rw [pcOMExt_plDG'] at hh'
      rw [plDFamily_bad1 hK hn Φ I hb0I hb1I x hh',
        plDFamily_bad1 hK hn Φ J hb0J hb1J y (hh'.trans (by rw [hρ]))]
    by_cases h0J : (0 : Fin (3 + 2)) ∈ J.1
    · exact plD_compat_star_bad0 hK hn hΦ hal I J h0I h1I hmI ⟨hmJ, h0J⟩ x y hρ
    by_cases h1J : (1 : Fin (3 + 2)) ∈ J.1
    · have hfork : ∀ j ∈ I.1, 3 ≤ j.val := by
        intro j hj
        rcases plD_val_of_bad1 J.2 ⟨hmJ, h1J⟩ (hsub hj) with h | h
        · exfalso
          have hj1 : j = (1 : Fin (3 + 2)) := Fin.ext (by rw [h]; rfl)
          exact h1I (hj1 ▸ hj)
        · exact h
      exact plD_compat_star_bad1 hK hn hΦ hal I J h0I h1I hmI hfork (fun h => h0J h.2)
        ⟨hmJ, h1J⟩ x y hρ
    ·
      obtain ⟨mz, hmz⟩ := plD_place_star hK hn I h0I h1I x
      rw [plDFamily_star hK hn Φ I h0I h1I hmI x hmz,
        plDFamily_star hK hn Φ J h0J h1J hmJ y (hmz.trans (by rw [hρ]))]
  ·
    obtain ⟨h, hh⟩ := plD_exists_iota_of_lev hK hn I hmI x
    rw [plDFamily_lev hK hn Φ I hmI x hh]
    by_cases hmJ : PlDMoves J.1
    · by_cases h0J : (0 : Fin (3 + 2)) ∈ J.1
      · have hb0J : PlDBad0 J.1 := ⟨hmJ, h0J⟩
        have hval : ∀ j ∈ I.1, j.val = 0 := fun j hj => by
          have h1 := plD_val_of_bad0 J.2 hb0J (hsub hj)
          have h2 := plD_val_le_of_not_moves hmI hj
          omega
        obtain ⟨h', hh'⟩ := plD_place_bad0 hK hn J hb0J y
        rw [pcOMExt_plDG'] at hh'
        rw [plDFamily_bad0 hK hn Φ J hb0J y hh']
        refine (plD_agree_comm hK hn hΦ hal plD_two_ne_last I x ?_ ?_ ?_ hh
          (hh'.trans (by rw [hρ]))).symm
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : ((2 : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 2 := rfl
          omega
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : ((Fin.last 3).castSucc : Fin (3 + 2)).val = 3 := rfl
          omega
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : (Fin.last (3 + 1)).val = 4 := rfl
          omega
      by_cases h1J : (1 : Fin (3 + 2)) ∈ J.1
      · have hb0J : ¬ PlDBad0 J.1 := fun h => h0J h.2
        have hb1J : PlDBad1 J.1 := ⟨hmJ, h1J⟩
        have hval : ∀ j ∈ I.1, j.val = 1 := fun j hj => by
          have h1 := plD_val_of_bad1 J.2 hb1J (hsub hj)
          have h2 := plD_val_le_of_not_moves hmI hj
          omega
        obtain ⟨h', hh'⟩ := plD_place_bad1 hK hn J hb1J y
        rw [pcOMExt_plDG'] at hh'
        rw [plDFamily_bad1 hK hn Φ J hb0J hb1J y hh']
        refine (plD_agree_comm hK hn hΦ hal plD_zero_ne_last I x ?_ ?_ ?_ hh
          (hh'.trans (by rw [hρ]))).symm
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : ((0 : Fin (3 + 1)).castSucc : Fin (3 + 2)).val = 0 := rfl
          omega
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : ((Fin.last 3).castSucc : Fin (3 + 2)).val = 3 := rfl
          omega
        · refine plD_not_mem_peSupp fun j hj => ?_
          have := hval j hj
          have hv : (Fin.last (3 + 1)).val = 4 := rfl
          omega
      ·
        obtain ⟨mz, hmz⟩ := plD_place_star hK hn J h0J h1J y
        rw [plDFamily_star hK hn Φ J h0J h1J hmJ y hmz]
        refine (peTrans_value_iota (peNormal_minus hK le_rfl hΦ) ?_).symm
        rw [hmz, hh, hρ]
    · exact (plDFamily_lev hK hn Φ J hmJ y (hh.trans hρ)).symm

end Compat

end CFSG.SeitzReduction.SymplecticPilot
