module

public import CFSG.ClassicalInvolution.Q3.TL4WylD2
public import CFSG.ClassicalInvolution.Q3.TL4WylC2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

theorem Wyl.vGrp_le_closure {G : Type} [Group G] {Ω : Set (Subgroup G)} {W K J : Subgroup G}
    {z t : G} (F : FrameData Ω W K J z t) :
    Wyl.vGrp F ≤ Subgroup.closure ({z, t, F.zz 2} : Set G) := by
  unfold Wyl.vGrp
  rw [Subgroup.closure_le]
  rintro y (rfl | rfl)
  · rw [← Wyl.zt_eq F]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · rw [F.hz0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_lemma54 (hH : TightHyp51TriR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) :
    IsElemAbelian 2 (Subgroup.closure ({z, t, F.zz 2} : Set Y)) ∧
      Nat.card ↥(Subgroup.closure ({z, t, F.zz 2} : Set Y)) = 8 ∧
        ∀ A : Subgroup Y, A ≤ Subgroup.closure ({z, t, F.zz 2} : Set Y) → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure ({t, z} : Set Y)) := by
  have hΩ := hs.hyp
  have hnt : ∀ M ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ M' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.trans hs.noTwins hM
  obtain ⟨P, hP, hind⟩ := hs.wyl_exists_triFrame F
  have hHyp : Hyp51 (Subgroup.closure ({z, t, F.zz 2} : Set Y)) :=
    hH Y Rd Sd z hs.large ![tightCore Rd, J, (F.ρ 2).K] ![z, t, F.zz 2] P hP hind
  have hc01 : z * t = t * z := triFrame_comm_gen hP hΩ 0 1
  have hc02 : z * F.zz 2 = F.zz 2 * z := triFrame_comm_gen hP hΩ 0 2
  have hc12 : t * F.zz 2 = F.zz 2 * t := triFrame_comm_gen hP hΩ 1 2
  have hz2 : z * z = 1 := hP.sq 0
  have ht2 : t * t = 1 := hP.sq 1
  have hw2 : F.zz 2 * F.zz 2 = 1 := hP.sq 2
  have hz1 : z ≠ 1 := hP.ne_one 0
  have ht1 : t ≠ 1 := hP.ne_one 1
  have hw1 : F.zz 2 ≠ 1 := hP.ne_one 2
  have hzt : z ≠ t := hP.x_ne hnt (i := 0) (j := 1) (by decide)
  have hDB : Subgroup.closure ({t, z} : Set Y) ≤ Subgroup.closure ({z, t, F.zz 2} : Set Y) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set Y)) 2 :=
    T7A.isElemAbelian2_closure_pair ht2 hz2 ht1 hz1 hzt.symm hc01.symm
  exact ⟨T8T.isElemAbelian_closure_three hz2 ht2 hw2 hc01 hc02 hc12,
    T8T.natCard_closure_three hz2 ht2 hw2 hc01 hc02 hc12 hz1 ht1 hzt hw1 hind,
    (lemma54_odd_and_eq hHyp hDB hD).2⟩

theorem TightStd8R.alphaOf_vGrp_eq (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t) :
    alphaOf (Wyl.vGrp F) = alphaOf (Subgroup.closure ({t, z} : Set Y)) :=
  (hs.wyl_lemma54 hH F).2.2 _ (Wyl.vGrp_le_closure F)
    (Wyl.isElemAbelian2_vGrp (Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1) F)

theorem TightStd8R.centralizer_le_normalizer_alpha_of_frattini (hH : TightHyp51TriR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    (hfr : ∀ c ∈ Subgroup.centralizer ({z * t} : Set Y),
      ∃ o ∈ oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)),
        conjSub (o * c) (Wyl.vGrp F) = Wyl.vGrp F) :
    Subgroup.centralizer ({z * t} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
  obtain ⟨hB, hB8, h3⟩ := hs.wyl_lemma54 hH F
  have hαV := hs.alphaOf_vGrp_eq hH F
  have hztB : z * t ∈ Subgroup.closure ({z, t, F.zz 2} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  intro c hc
  obtain ⟨o, ho, hn⟩ := hfr c hc
  have hoN : o ∈ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) :=
    T8T.oddCoreOf_centralizer_le_normalizer hB hB8 hztB h3
      ((oddCoreOf_layerY_le hs.hyp.conjInvariant) ho)
  have hnN : o * c ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
    rw [mem_normalizer_iff_conjSub_eq, ← hαV, ← alphaOf_conjSub, hn]
  have hc' : c = o⁻¹ * (o * c) := by group
  rw [hc']
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hoN) hnN

theorem TightStd8R.centralizer_le_normalizer_alpha_of_edge (hH : TightHyp51TriR r n)
    (hT4 : Thm4RBelow r n) (hS : TightSecFrameR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
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
    {s : Y} (hs' : IsUniqueInvolution M s) :
    Subgroup.centralizer ({z * s} : Set Y) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) := by
  by_cases hconn : DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))
  · exact hs.centralizer_le_normalizer_alpha_of_conn hH hμ hne hA hN hM hs' hconn
  · obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
    have hμ' := muIsoWylD4_conjSub hs.hyp hμ g
    obtain ⟨F'⟩ := Wyl.exists_frameData hstd.toStd8Core hμ'
      (Wyl.not_dbarConnected_of_ne hstd.toStd8Core hne)
    have hC := hstd.centralizer_le_normalizer_alpha_of_frattini hH F' fun c hc =>
      Wyl.frattini hS hT4 (TightLargeHypR.typeRFam hs.large) hstd.toStd8Core
        hstd.natCard_secQuot_lt hconn F' hc
    rwa [hA M hM J hs.hJ s t hs' hs.ht] at hC

end Cit3

section Cit3B


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.alphaOf_eq_bot_of_wylD4 (hB : TightBenderEndR) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n) (hS : TightSecFrameR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :
    alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥ := by
  have hA := hs.alphaConst_of_wylD4 hF hdisc hμ hne
  have hN := hs.sigmaNorm_le_normalizer_alpha hA
  have hH' : T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set Y)) : Set Y) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' =>
      hs.centralizer_le_normalizer_alpha_of_edge hH hT4 hS hμ hne hA hN hM hs')
  rw [hs.h274_eq_top_of_wylD4 hB hμ hne, top_le_iff] at hH'
  have hnorm : (alphaOf (Subgroup.closure ({t, z} : Set Y))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp hH'
  have hle : alphaOf (Subgroup.closure ({t, z} : Set Y)) ≤ classicalInvolutionOddCore Y :=
    le_sSup ⟨hnorm, hs.alphaOf_odd_of_wylD4 hH hμ hne⟩
  rwa [hs.large.cls.2.2, le_bot_iff] at hle

theorem TightStd8R.false_of_wylD4_of_conn_edge (hB : TightBenderEndR)
    (hF : TightAlphaFrameR r n) (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n)
    (hS : TightSecFrameR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {M : Subgroup Y} (hM : M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {s : Y} (hs' : IsUniqueInvolution M s)
    (hconn : DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))) : False := by
  have hα := hs.alphaOf_eq_bot_of_wylD4 hB hF hH hT4 hS hdisc hμ hne
  have hA := hs.alphaConst_of_wylD4 hF hdisc hμ hne
  obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
  have hα' : alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥ := by
    rw [hA M hM J hs.hJ s t hs' hs.ht]
    exact hα
  exact hstd.false_of_caseA_of_alpha_bot hT4 (muIsoWylD4_conjSub hs.hyp hμ g) hne hconn hα'

end Cit3B

end CFSG.ClassicalInvolution.Q3.TL4
