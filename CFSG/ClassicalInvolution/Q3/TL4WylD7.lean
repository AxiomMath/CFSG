module

public import CFSG.ClassicalInvolution.Q3.TL4WylD6
import CFSG.ClassicalInvolution.Asc77.AscT8YC7Eng

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)

namespace Wyl

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W K J : Subgroup G} {z t : G}

omit [Finite G] in
theorem omegaNbr_ncard_conj (hΩ : ConjInvariant Ω) (L : Subgroup G) (g : G) :
    (omegaNbr Ω (conjSub g L)).ncard = (omegaNbr Ω L).ncard := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.omegaNbr_ncard_conjE hΩ L g

omit [Finite G] in
theorem ncard_others (F : FrameData Ω W K J z t) (i : Fin 4) :
    {L | ∃ j, j ≠ i ∧ L = (F.ρ j).K}.ncard = 3 := by
  exact CFSG.ClassicalInvolution.Asc77.T8YY.FrameData.ncard_othersE F i

end Wyl

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_neighbours_of_frame (hs : TightStd8R r n Rd Sd z J S R T W t)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    (h0 : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∃ j, M = (F.ρ j).K) :
    ∀ i : Fin 4, ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ i).K,
      ∃ j, M = (F.ρ j).K := by
  have hcl := hs.hyp.conjInvariant
  have hK3 : (omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)).ncard = 3 := by
    have e : omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) =
        {L | ∃ j, j ≠ 0 ∧ L = (F.ρ j).K} := by
      ext M
      constructor
      · intro hM
        obtain ⟨j, rfl⟩ := h0 M hM
        refine ⟨j, fun hj => ?_, rfl⟩
        apply hM.2.1
        rw [hj, F.h0]
      · rintro ⟨j, hj, rfl⟩
        exact Wyl.frame_mem_omegaNbr F hj
    rw [e, Wyl.ncard_others]
  intro i M hM
  obtain ⟨g, hg⟩ := hs.trans (F.ρ i).K (F.ρ i).hK
  have hcard : (omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ i).K).ncard = 3 := by
    rw [← hg, Wyl.omegaNbr_ncard_conj hcl, hK3]
  have hsub : {L | ∃ j, j ≠ i ∧ L = (F.ρ j).K} ⊆
      omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ i).K := by
    rintro _ ⟨j, hj, rfl⟩
    exact F.hadj i j (Ne.symm hj)
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Wyl.ncard_others])
    (Set.toFinite _)
  rw [← heq] at hM
  obtain ⟨j, -, rfl⟩ := hM
  exact ⟨j, rfl⟩

end Cit3

section Cit3B


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.wyl_false_of_singleFrame (hB : TightBenderEndR) (hH : TightHyp51TriR r n)
    (hT4 : Thm4RBelow r n) (hS : TightSecFrameR r n) (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set Y)) = ⊥)
    (F : FrameData (CoreAssembly.conjClass (tightCore Rd)) W (tightCore Rd) J z t)
    (hsingle : ∀ i : Fin 4, ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (F.ρ i).K,
      ∃ j, M = (F.ρ j).K) : False := by
  have hΩ := hs.hyp
  have hcl := hΩ.conjInvariant
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) := hs.mem
  have c0 := Q3CL.T8.ctxOf (partIHyp_of_std8 hs.toStd8Core) hs.hW.1
  have hVab := Wyl.isElemAbelian2_vGrp c0 F
  have hαV : alphaOf (Wyl.vGrp F) = ⊥ := (hs.alphaOf_vGrp_eq hH F).trans hα
  have hSig : ∀ L ∈ dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∃ i, L = (F.ρ i).K := by
    intro L hL
    induction hL with
    | refl => exact ⟨0, F.h0.symm⟩
    | @tail b c _ hbc ih =>
      obtain ⟨i, rfl⟩ := ih
      obtain ⟨hcΩ, hadj⟩ := hbc
      rcases hadj with h | h
      · exact hsingle i c h
      · exact hsingle i c (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ (F.ρ i).hK h)
  have hFm : ∀ i, (F.ρ i).K ∈ dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    intro i
    by_cases h0 : i = 0
    · rw [h0, F.h0]
      exact Relation.ReflTransGen.refl
    · exact T8.mem_dComp_of_mem_omegaNbr (Wyl.frame_mem_omegaNbr F h0)
  have hN : sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≤
      Subgroup.normalizer (Wyl.vGrp F : Set Y) := by
    intro g hg
    have hKg := (T8.mem_sigmaNorm_iff hcl hK).mp hg
    have hdeq := T8.dComp_eq_of_mem hK hKg
    have hperm : ∀ i, ∃ j, conjSub g (F.ρ i).K = (F.ρ j).K := by
      intro i
      have h1 := mem_dComp_conjSub hcl (hFm i) g
      rw [hdeq] at h1
      exact hSig _ h1
    choose π hπ using hperm
    have hzπ : ∀ i, g * F.zz i * g⁻¹ = F.zz (π i) := fun i =>
      ((F.hz i).conj g).eq (by rw [hπ i]; exact F.hz (π i))
    refine Thompson.mem_normalizer_of_conjSub_le ?_
    unfold Wyl.vGrp
    rw [T7A.conjSub_closure_pair, Subgroup.closure_le]
    have hconj : ∀ i j, g * (F.zz i * F.zz j) * g⁻¹ = F.zz (π i) * F.zz (π j) := by
      intro i j
      rw [← hzπ i, ← hzπ j]
      group
    rintro y (rfl | rfl)
    · rw [hconj 0 1]
      exact Wyl.mul_mem_vGrp c0 F _ _
    · rw [hconj 0 2]
      exact Wyl.mul_mem_vGrp c0 F _ _
  have hC : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → Subgroup.centralizer ({z * s} : Set Y) ≤
        Subgroup.normalizer (Wyl.vGrp F : Set Y) := by
    intro M hM s hs'
    obtain ⟨g, S', R', T', hstd⟩ := TightLargeHypR.exists_std8_of_wset hs.large hM hs' hs.hW.1
    obtain ⟨F'⟩ := Wyl.exists_frameData hstd.toStd8Core (muIsoWylD4_conjSub hs.hyp hμ g)
      (Wyl.not_dbarConnected_of_ne hstd.toStd8Core hne)
    have c' := Q3CL.T8.ctxOf (partIHyp_of_std8 hstd.toStd8Core) hstd.hW.1
    have hmemF' : ∀ j, ∃ i, (F'.ρ j).K = (F.ρ i).K := by
      intro j
      by_cases h0 : j = 0
      · exact ⟨0, by rw [h0, F'.h0, F.h0]⟩
      · exact hsingle 0 _ (by rw [F.h0]; exact Wyl.frame_mem_omegaNbr F' h0)
    have hVeq : Wyl.vGrp F' = Wyl.vGrp F := Wyl.vGrp_eq_of_members c0 c' F F' hmemF'
    have hzsV : z * s ∈ Wyl.vGrp F := hVeq ▸ Wyl.zt_mem_vGrp F'
    have hzs1 : z * s ≠ 1 := T8.zt_ne_one hstd.noTwins hstd.hJ hstd.hz hstd.ht
    intro x hx
    obtain ⟨o, ho, hconj⟩ := Wyl.frattini hS hT4 (TightLargeHypR.typeRFam hs.large)
      hstd.toStd8Core hstd.natCard_secQuot_lt (huni M hM s hs') F' hx
    have hoC := oddCoreOf_layerY_le hcl ho
    have hocomm : ∀ y ∈ Wyl.vGrp F, o * y = y * o := fun y hy =>
      T8.oddCoreOf_centralizer_commutes hαV hzsV hzs1 hy o hoC
    have hoN : o ∈ Subgroup.normalizer (Wyl.vGrp F : Set Y) := by
      refine Thompson.mem_normalizer_of_conjSub_le ?_
      intro y hy
      rw [mem_conjSub_iff] at hy
      have e : y = o⁻¹ * y * o := by
        calc y = o * (o⁻¹ * y * o) * o⁻¹ := by group
          _ = (o⁻¹ * y * o) * o * o⁻¹ := by rw [hocomm _ hy]
          _ = o⁻¹ * y * o := by group
      rw [e]
      exact hy
    have hoxN : o * x ∈ Subgroup.normalizer (Wyl.vGrp F : Set Y) := by
      rw [mem_normalizer_iff_conjSub_eq, ← hVeq]
      exact hconj
    have hx' : x = o⁻¹ * (o * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hoN) hoxN
  have hH' : T8.H274 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) z ≤
      Subgroup.normalizer (Wyl.vGrp F : Set Y) :=
    sup_le hN (iSup₂_le fun M hM => iSup_le fun s => iSup_le fun hs' => hC M hM s hs')
  rw [hs.h274_eq_top_of_wylD4 hB hμ hne, top_le_iff] at hH'
  have hVn : (Wyl.vGrp F).Normal := Subgroup.normalizer_eq_top_iff.mp hH'
  have hVcomm : ∀ a b : ↥(Wyl.vGrp F), a * b = b * a := by
    intro a b
    apply Subtype.ext
    have ha := hVab.2 _ a.2
    have hb := hVab.2 _ b.2
    have hab := hVab.2 _ ((Wyl.vGrp F).mul_mem a.2 b.2)
    show (a : Y) * b = b * a
    calc (a : Y) * b = ((a : Y) * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
      _ = (b : Y)⁻¹ * (a : Y)⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [inv_eq_of_mul_eq_one_right hb, inv_eq_of_mul_eq_one_right ha]
  have hVnil : Group.IsNilpotent ↥(Wyl.vGrp F) := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥(Wyl.vGrp F) →* Unit) ?_
    intro v _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hVcomm w v
  have hVF : Wyl.vGrp F ≤ genFittingFitting Y := le_sSup ⟨hVn, hVnil⟩
  have hFZ := genFittingFitting_le_center_of_selfGen hs.large.datum hs.large.cls.2.1
    hs.large.cls.2.2 hs.large.notInO2
  have hzt := hFZ (hVF (Wyl.zt_mem_vGrp F))
  rw [hs.large.center, Subgroup.mem_bot] at hzt
  exact T8.zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht hzt

theorem TightStd8R.wyl_false_of_pureB (hB : TightBenderEndR) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n) (hS : TightSecFrameR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)))
    (hμ : MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hne : dComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      dstarComp (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))) : False := by
  have hα := hs.alphaOf_eq_bot_of_wylD4 hB hF hH hT4 hS hdisc hμ hne
  have hA := hs.alphaConst_of_wylD4 hF hdisc hμ hne
  have hαall : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd), ∀ s : Y,
      IsUniqueInvolution M s → alphaOf (Subgroup.closure ({s, z} : Set Y)) = ⊥ :=
    fun M hM s hs' => (hA M hM J hs.hJ s t hs' hs.ht).trans hα
  obtain ⟨F⟩ :=
    Wyl.exists_frameData hs.toStd8Core hμ (Wyl.not_dbarConnected_of_ne hs.toStd8Core hne)
  exact hs.wyl_false_of_singleFrame hB hH hT4 hS hμ hne huni hα F
    (hs.wyl_neighbours_of_frame F (hs.wyl_singleFrame0 hS hH hμ hne huni hαall F))

theorem tightW2CaseBR_of (hB : TightBenderEndR) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hT4 : Thm4RBelow r n) (hS : TightSecFrameR r n) :
    TightW2CaseBR r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc hμ hne _
  by_cases huni : ∀ M ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
      ∀ s : Y, IsUniqueInvolution M s →
        ¬ DConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * s))
  · exact hs.wyl_false_of_pureB hB hF hH hT4 hS hdisc hμ hne huni
  · push Not at huni
    obtain ⟨M, hM, s, hs', hconn⟩ := huni
    exact hs.false_of_wylD4_of_conn_edge hB hF hH hT4 hS hdisc hμ hne hM hs' hconn

theorem tightC26_13R_of_secFrame (hmin : TightC27_4MR r n) (hB : TightBenderEndR)
    (hT4 : Thm4RBelow r n) (hYs : TightC27_YsmallR r n) (hF : TightAlphaFrameR r n)
    (hH : TightHyp51TriR r n) (hS : TightSecFrameR r n) : TightC26_13R r n :=
  tightC26_13R_of_caseB hmin hB hT4 hYs hF hH (tightW2CaseBR_of hB hF hH hT4 hS)

end Cit3B

end CFSG.ClassicalInvolution.Q3.TL4
