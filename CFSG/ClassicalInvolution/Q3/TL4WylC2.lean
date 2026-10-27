module

public import CFSG.ClassicalInvolution.Q3.TL4WylC
public import CFSG.ClassicalInvolution.Q3.TL4WylB4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

section Cit3


@[expose] def TightW2CaseBR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W →
          dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
              dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) →
            ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)) → False

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.centralizer_le_normalizer_alpha_of_conn (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hA : ∀ J₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ J₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ t₁ t₂ : Y,
        IsUniqueInvolution J₁ t₁ → IsUniqueInvolution J₂ t₂ →
          alphaOf (Subgroup.closure ({t₁, z} : Set Y)) =
            alphaOf (Subgroup.closure ({t₂, z} : Set Y)))
    (hN : sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y))
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {s : Y} (hs' : IsUniqueInvolution M s)
    (hconn : DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))) :
    Subgroup.centralizer ({z * s} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) := hs.mem
  have hnt : ∀ M ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ M' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hM
  obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
  have hμ' := muIsoWylD4_conjSub hs.hyp hμ g
  obtain ⟨F⟩ := Wyl.exists_frameData hstd.toStd8Core hμ'
    (Wyl.not_dbarConnected_of_ne hstd.toStd8Core hne)
  obtain ⟨P, hP, hind⟩ := hstd.wyl_exists_triFrame F
  have hHyp : Hyp51 (Subgroup.closure ({z, s, F.zz 2} : Set Y)) :=
    hH Y Rd Sd z hs.large ![tightCore Rd, M, (F.ρ 2).K] ![z, s, F.zz 2] P hP hind
  have hc01 : z * s = s * z := triFrame_comm_gen hP hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := triFrame_comm_gen hP hΩ 0 2
  have hc12 : s * F.zz 2 = F.zz 2 * s := triFrame_comm_gen hP hΩ 1 2
  have hz2 : z * z = 1 := hP.sq 0
  have hs2 : s * s = 1 := hP.sq 1
  have hw2 : F.zz 2 * F.zz 2 = 1 := hP.sq 2
  have hz1 : z ≠ 1 := hP.ne_one 0
  have hs1 : s ≠ 1 := hP.ne_one 1
  have hw1 : F.zz 2 ≠ 1 := hP.ne_one 2
  have hzs : z ≠ s := hP.x_ne hnt (i := 0) (j := 1) (by decide)
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, s, F.zz 2} : Set Y)) :=
    T8T.isElemAbelian_closure_three hz2 hs2 hw2 hc01 hc02 hc12
  have hB8 : Nat.card ↥(Subgroup.closure ({z, s, F.zz 2} : Set Y)) = 8 :=
    T8T.natCard_closure_three hz2 hs2 hw2 hc01 hc02 hc12 hz1 hs1 hzs hw1 hind
  have hDB : Subgroup.closure ({s, z} : Set Y) ≤ Subgroup.closure ({z, s, F.zz 2} : Set Y) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({s, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair hs2 hz2 hs1 hz1 hzs.symm hc01.symm
  have h3 := (lemma54_odd_and_eq hHyp hDB hD).2
  have hα : alphaOf (Subgroup.closure ({s, z} : Set Y)) =
      alphaOf (Subgroup.closure ({t, z} : Set Y)) := hA M hM J hs.hJ s t hs' hs.ht
  intro c hc
  have hKx : T8.XMem (CoreAssembly.conjClass (tightCore Rd)) (z * s) (tightCore Rd) :=
    hstd.xMem_K
  have hKc : T8.XMem (CoreAssembly.conjClass (tightCore Rd)) (z * s) (conjSub c (tightCore Rd)) :=
    XMem.conj' hΩ.conjInvariant hKx hc
  obtain ⟨ν, hν, hνK⟩ := exists_conj_mem_dComp_of_conn h hKx hconn hKc
  have hνc : (ν : Y) * c ∈ sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    rw [T8.mem_sigmaNorm_iff hΩ.conjInvariant hK, conjSub_mul]
    exact hνK
  have hzsB : z * s ∈ Subgroup.closure ({z, s, F.zz 2} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hν' : (ν : Y) ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({s, z} : Set Y)) : Set Y) :=
    T8T.oddCoreOf_centralizer_le_normalizer hB hB8 hzsB h3
      ((oddCoreOf_layerY_le hΩ.conjInvariant) ⟨ν, hν, rfl⟩)
  rw [hα] at hν'
  have hc' : c = (ν : Y)⁻¹ * ((ν : Y) * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hν') (hN hνc)

theorem TightStd8R.oddCoreOf_centralizer_le_sigmaNorm_of_alpha
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥) :
    oddCoreOf (Subgroup.centralizer ({z * t} : Set Y)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have hzA : z ∈ Subgroup.closure ({t, z} : Set Y) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have htA : t ∈ Subgroup.closure ({t, z} : Set Y) := Subgroup.subset_closure (Set.mem_insert _ _)
  have haA : z * t ∈ Subgroup.closure ({t, z} : Set Y) := Subgroup.mul_mem _ hzA htA
  have ha1 : z * t ≠ 1 := T8.zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht
  intro x hx
  have hxz : x * z = z * x := T8.oddCoreOf_centralizer_commutes hα haA ha1 hzA x hx
  exact hs.centralizer_le_sigmaNorm (Subgroup.mem_centralizer_singleton_iff.mpr hxz)

theorem TightStd8R.false_of_caseA_of_alpha_bot (hT4 : Thm4RBelow r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hconn : DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥) : False := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ := hs.hyp
  have hK := hs.xMem_K
  have hOY : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    (oddCoreOf_layerY_le hΩ.conjInvariant).trans
      (hs.oddCoreOf_centralizer_le_sigmaNorm_of_alpha hα)
  have hY := Wyl.layerY_le_sigmaNorm_of_dConn h hK hconn hOY
  have hC := Wyl.centralizer_le_sigmaNorm_of_layerY_le h hT4 hs.natCard_secQuot_lt hK hY
  obtain ⟨F⟩ :=
    Wyl.exists_frameData hs.toStd8Core hμ (Wyl.not_dbarConnected_of_ne hs.toStd8Core hne)
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1
  have hM := Wyl.mgrp_le_centralizer c F 0 1
  rw [F.hz0, F.hz1] at hM
  exact Wyl.mgrp_not_le_sigmaNorm hs.toStd8Core hne (hM.trans hC)

end Cit3

section Cit3B


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.false_of_caseA_uniform (hB : TightBenderEndR) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))) : False := by
  have hA := hs.alphaConst_of_wylD4 hF hdisc hμ hne
  have hN := hs.sigmaNorm_le_normalizer_alpha hA
  have hH' : T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
      hs.centralizer_le_normalizer_alpha_of_conn hH hμ hne hA hN hM hs' (huni M hM s hs'))
  rw [hs.h274_eq_top_of_wylD4 hB hμ hne, top_le_iff] at hH'
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH'
  have hodd := hs.alphaOf_odd_of_wylD4 hH hμ hne
  have hle : alphaOf (Subgroup.closure ({t, z} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnorm, hodd⟩
  rw [hs.large.cls.2.2, le_bot_iff] at hle
  exact hs.false_of_caseA_of_alpha_bot hT4 hμ hne (huni J hs.hJ t hs.ht) hle

theorem TightStd8R.false_of_wylD4_of_caseB (hB : TightBenderEndR) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n) (hCB : TightW2CaseBR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) : False := by
  by_cases huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))
  · exact hs.false_of_caseA_uniform hB hF hH hT4 hdisc hμ hne huni
  · push Not at huni
    obtain ⟨M, hM, s, hs', hnc⟩ := huni
    obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
    exact hCB Y Rd Sd z M S' R' T' (conjSub g W) s hstd hdisc (muIsoWylD4_conjSub hs.hyp hμ g)
      hne hnc

theorem tightC26_13R_of_caseB (hmin : TightC27_4MR r n) (hB : TightBenderEndR)
    (hT4 : Thm4RBelow r n) (hYs : TightC27_YsmallR r n) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hCB : TightW2CaseBR r n) : TightC26_13R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc hμ
  by_cases hcomp : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
  · exact hs.false_of_wylD4_of_dComp_eq hmin hB hT4 hYs hdisc hμ hcomp
  · exact hs.false_of_wylD4_of_caseB hB hF hH hT4 hCB hdisc hμ hcomp

end Cit3B

end CFSG.ClassicalInvolution.Q3.TL4
