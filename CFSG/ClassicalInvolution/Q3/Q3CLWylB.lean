module

public import CFSG.ClassicalInvolution.Q3.Q3CLWylA
public import CFSG.ClassicalInvolution.Asc77.AscT8YB2
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL.Wyl

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core partIHyp_of_std8 stdRepK)
open CFSG.ClassicalInvolution.Asc77.T8YY (FrameData)
open CFSG.StronglyEmbedded.UniqueCoset

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_prod_eq_one (c : Q3CL.Thompson.Ctx Ω W) (hclC : Q3CL.ClassicalClause Ω)
    (hnc : ¬ DbarConnected Ω W) (ρ : Fin 4 → Rep Ω W) (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hadj : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) {zz : Fin 4 → G}
    (hz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) : zz 0 * zz 1 * zz 2 * zz 3 = 1 := by
  obtain ⟨σ, tt, g, ht, -, hg, hrel⟩ := c.exists_relation hclC hnc ρ hne hadj
  have hgW : ∀ i, g i ∈ W := fun i => (hg i).1.2
  have hsq : ∀ i, g i ^ 2 = zz i := by
    intro i
    have h4 : g i ^ 4 = 1 := by rw [← (hg i).2]; exact pow_orderOf_eq_one _
    have hmem : g i * g i ∈ (ρ i).K := (ρ i).K.mul_mem (hg i).1.1 (hg i).1.1
    have hyy : (g i * g i) * (g i * g i) = 1 := by
      have : (g i * g i) * (g i * g i) = g i ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [this, h4]
    rcases (hz i).unique _ hmem hyy with h | h
    · exfalso
      have h2 : g i ^ 2 = 1 := by rw [pow_two]; exact h
      have := orderOf_dvd_of_pow_eq_one h2
      rw [(hg i).2] at this
      omega
    · rw [pow_two]; exact h
  have hcomm : ∀ x y : G, x ∈ W → y ∈ W → Commute x y := fun x y hx hy => c.comm_W x hx y hy
  have hW01 : g 0 * g 1 ∈ W := W.mul_mem (hgW 0) (hgW 1)
  have hW012 : g 0 * g 1 * g 2 ∈ W := W.mul_mem hW01 (hgW 2)
  have hexp : (g 0 * g 1 * g 2 * g 3) ^ 2 = g 0 ^ 2 * g 1 ^ 2 * g 2 ^ 2 * g 3 ^ 2 := by
    rw [(hcomm _ _ hW012 (hgW 3)).mul_pow, (hcomm _ _ hW01 (hgW 2)).mul_pow,
      (hcomm _ _ (hgW 0) (hgW 1)).mul_pow]
  have ht2 : tt ^ 2 = 1 := by rw [pow_two]; exact ht.sq
  calc zz 0 * zz 1 * zz 2 * zz 3 = g 0 ^ 2 * g 1 ^ 2 * g 2 ^ 2 * g 3 ^ 2 := by
        rw [hsq 0, hsq 1, hsq 2, hsq 3]
    _ = (g 0 * g 1 * g 2 * g 3) ^ 2 := hexp.symm
    _ = 1 := by rw [← hrel]; exact ht2

theorem exists_rep_not_mem_dComp (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ∃ σ : Rep Ω W, σ.K ∉ dComp Ω K := by
  by_contra hcon
  push Not at hcon
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨K₁, hK₁d, J₁, hJ₁, hJ₁n⟩ :=
    Q3T8.Asc77.Thompson.exists_boundary_of_dComp_ne hΩ hK hne
  have hK₁ : K₁ ∈ Ω := mem_of_mem_dComp' hK hK₁d
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := c.exists_conj_reps_of_mem_omegaStarNbr hK₁ hJ₁
  have h1 : ρ.K ∈ dComp Ω K := hcon ρ
  have h2 : σ.K ∈ dComp Ω K := hcon σ
  have h3 : σ.K ∈ dComp Ω ρ.K := by
    rw [T8.dComp_eq_of_mem hK h1]
    exact h2
  rw [hρ, hσ] at h3
  have h4 := mem_dComp_conjSub hΩ.conjInvariant h3 g⁻¹
  rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h4
  exact hJ₁n (dComp_trans' hK₁d h4)

theorem mgrp_not_le_sigmaNorm (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ MGrp Ω W ≤ sigmaNorm Ω K := by
  intro hle
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnc : ¬ DbarConnected Ω W := not_dbarConnected_of_ne hs hne
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨σ, hσ⟩ := exists_rep_not_mem_dComp hs hne
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hs.stand.cls hnc (stdRepK hs) σ
  have hK' : conjSub m K ∈ dComp Ω K := (T8.mem_sigmaNorm_iff hΩ.conjInvariant hK).mp (hle hm)
  have hmK' : conjSub m K = σ.K := hmK
  rw [hmK'] at hK'
  exact hσ hK'

theorem exists_frameData (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : Nonempty (FrameData Ω W K J z t) := by
  classical
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨ρ, h0, h1, hne, hadj, hclos⟩ := exists_frame_closed hs hμ hnc
  have hex : ∀ i, ∃ zi : G, IsUniqueInvolution (ρ i).K zi := fun i =>
    Sec6Gen.exists_uniqueInvolution hΩ (ρ i).hK
  choose zz hz using hex
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  refine ⟨⟨ρ, zz, h0, h1, hz, ?_, ?_, hne, hadj, hclos,
    frame_prod_eq_one c hs.stand.cls hnc ρ hne hadj hz, ?_,
    fun i => mem_W_of_uniqueInvolution c (ρ i) (hz i)⟩⟩
  · exact (hz 0).eq (by rw [h0]; exact hs.hz)
  · exact (hz 1).eq (by rw [h1]; exact hs.ht)
  · intro i j hij heq
    have hmem : (ρ j).K ∈ twinSet Ω (ρ i).K := ⟨(ρ j).hK, zz j, heq ▸ hz i, hz j⟩
    exact hne j i (Ne.symm hij) (hnt _ (ρ i).hK _ hmem)

omit [Finite G] in
theorem frame_mul_ne_one (F : FrameData Ω W K J z t) (i j : Fin 4) (hij : i ≠ j) :
    F.zz i * F.zz j ≠ 1 := by
  intro h
  have : F.zz i = F.zz j := by
    have h' := congrArg (· * F.zz j) h
    simpa [mul_assoc, (F.hz j).sq] using h'
  exact F.hinj i j hij this

theorem mgrp_le_centralizer (c : Q3CL.Thompson.Ctx Ω W) (F : FrameData Ω W K J z t)
    (i j : Fin 4) : MGrp Ω W ≤ Subgroup.centralizer ({F.zz i * F.zz j} : Set G) := by
  refine iSup₂_le fun R'' hR'' x hx => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_frame_prod_of_mem_DSet c F.ρ F.hadj F.hclos F.hz hR'' hx i j)


theorem mgrp_le_H274 (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : MGrp Ω W ≤ T8.H274 Ω K z := by
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := Q3CL.T8.ctxOf (partIHyp_of_std8 hs) hs.hW.1
  have h01 := mgrp_le_centralizer c F 0 1
  rw [F.hz0, F.hz1] at h01
  exact h01.trans (T8.centralizer_mul_le_H274 hs.hJ hs.ht)

theorem exists_conj_mem_mgrp (hs : Std8Core Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSH : (S : Subgroup G) ≤ T8.H274 Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {x : G} (hxL : x ∈ L)
    (hxo : orderOf x = 4) (hxH : x ∈ T8.H274 Ω K z) :
    ∃ y ∈ T8.H274 Ω K z, ∃ m ∈ MGrp Ω W, conjSub y L = conjSub m K := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := not_dbarConnected_of_ne hs hne
  have c := Q3CL.T8.ctxOf hP hW
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hxo]; norm_num)
  obtain ⟨y, hyH, hyS⟩ := T8.exists_conj_into_sylow S hSH hxH hx2
  have hL' : conjSub y L ∈ Ω := hΩ.conjInvariant y L hL
  have hord : orderOf (y * x * y⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) x
    rw [MulAut.conj_apply, hxo] at this
    exact this
  have hle : Subgroup.zpowers (y * x * y⁻¹) ≤ conjSub y L ⊓ (S : Subgroup G) :=
    le_inf (Subgroup.zpowers_le.mpr (conj_mem_conjSub hxL)) (Subgroup.zpowers_le.mpr hyS)
  have hcard : 4 ≤ Nat.card ↥(conjSub y L ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hord] at this
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  obtain ⟨η, hη, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    ((hWη ▸ le_iSup₂ (f := fun (U : Subgroup G) (_ : U ∈ η) => U) V hV : V ≤ W)).trans hWS
  obtain ⟨S', hS'η, -⟩ := id hη
  have hUη : conjSub y L ⊓ (⨆ V ∈ η, V) ∈ η :=
    Q3T8.Asc77.l6_11_proved G Ω hΩ S η hη hηS (conjSub y L) hL' (by omega)
  have hUSet : conjSub y L ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hS'η.1 hUη).1
  have hUS : conjSub y L ⊓ (⨆ V ∈ η, V) ≤ (S : Subgroup G) :=
    inf_le_right.trans (hWη ▸ hWS)
  obtain ⟨T₁, hT₁D, hT₁L⟩ :=
    Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW hWS hL' hUSet inf_le_left hUS
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hs.stand.cls hnc (stdRepK hs)
    (Q3CL.T8.mkRep hP hW hL' hT₁D hT₁L)
  exact ⟨y, hyH, m, hm, hmK.symm⟩

theorem mem_H274_of_conj_mem_sylow (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have htrans := hs.stand.trans
  have hz := hs.hz
  have ht := hs.ht
  have hJ := hs.hJ
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hJ.1
  have hJc : J ∈ dComp Ω K := T8.mem_dComp_of_mem_omegaNbr hJ
  have hntJ : ∀ J' ∈ twinSet Ω J, J' = J :=
    T8.noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hJΩ
  have hSH : (S : Subgroup G) ≤ T8.H274 Ω K z :=
    (Q3T8.Asc77.T8.sylow_le_sigmaNorm hΩ hK hRΩ hRK hRS hz).trans (T8.sigmaNorm_le_H274 K z)
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ T8.H274 Ω K z :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hz).trans
      ((T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK).trans (T8.sigmaNorm_le_H274 K z))
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ T8.H274 Ω K z :=
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ hntJ ht).trans
      ((T8.normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hJc).trans
        (T8.sigmaNorm_le_H274 K z))
  have hCzt : Subgroup.centralizer ({z * t} : Set G) ≤ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hJ ht
  obtain ⟨b, hbdef⟩ : ∃ b, b = g⁻¹ * z * g := ⟨_, rfl⟩
  rw [← hbdef] at hg
  obtain ⟨L, hLdef⟩ : ∃ L, L = conjSub g⁻¹ K := ⟨_, rfl⟩
  have hLΩ : L ∈ Ω := hLdef ▸ hΩ.conjInvariant g⁻¹ K hK
  have hb : IsUniqueInvolution L b := by
    have := hz.conj g⁻¹
    rwa [inv_inv, ← hbdef, ← hLdef] at this
  have hntL : ∀ L' ∈ twinSet Ω L, L' = L :=
    T8.noTwins_of_mem hΩ.conjInvariant htrans hs.noTwins hLΩ
  have hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hLΩ hntL hb
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hRΩ; omega)
  have htT : t ∈ T := T3.mem_of_isPGroup ht hTJ hTsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hTΩ; omega)
  have key : ∃ x ∈ L, orderOf x = 4 ∧ x ∈ T8.H274 Ω K z := by
    by_cases hRb : conjSub b R = R
    swap
    · have hKb : conjSub b K ∈ omegaNbr Ω K :=
        Q3T8.Asc77.T8.conjSub_mem_omegaNbr hΩ hK hRΩ hRK hRS hz hg hRb
      obtain ⟨x, hxL, hxo, hxc⟩ := Q3T8.Asc77.T8.exists_orderFour_centralizes_mul_conj hΩ hK
        hRΩ hRK hRS hz hg hRb hLΩ hb hCb
      exact ⟨x, hxL, hxo, T8.centralizer_mul_le_H274 hKb (hz.conj b)
        (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    by_cases hTb : conjSub b T = T
    swap
    · have hJb : conjSub b J ∈ omegaNbr Ω J :=
        Q3T8.Asc77.T8.conjSub_mem_omegaNbr hΩ hJΩ hTΩ hTJ hTS ht hg hTb
      obtain ⟨x, hxL, hxo, hxc⟩ := Q3T8.Asc77.T8.exists_orderFour_centralizes_mul_conj hΩ hJΩ
        hTΩ hTJ hTS ht hg hTb hLΩ hb hCb
      exact ⟨x, hxL, hxo, T8.centralizer_mul_le_H274_of_mem_dComp hΩ.conjInvariant hK htrans
        hJc hz ht hJb (ht.conj b) (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    have hKb : conjSub b K = K := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hRb
    have hJb : conjSub b J = J := Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hTb
    have hbz : b * z * b⁻¹ = z := hz.conj_eq hKb
    have hbt : b * t * b⁻¹ = t := ht.conj_eq hJb
    have hzb : z ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * b = (b * z * b⁻¹) * b := by rw [hbz]
        _ = b * z := by group
    have htb : t ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * b = (b * t * b⁻¹) * b := by rw [hbt]
        _ = b * t := by group
    obtain ⟨x, hxL, hxo, hxc⟩ := Q3T8.Asc77.T8.exists_orderFour_centralizes_one_of_three hΩ hLΩ
      hb S.isPGroup' (hRS hzR) (hTS htT) (mem_normalizer_iff_conjSub_eq.mp (hCb hzb))
      (mem_normalizer_iff_conjSub_eq.mp (hCb htb))
    refine ⟨x, hxL, hxo, ?_⟩
    rcases hxc with h | h | h
    · exact hCz (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCt (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCzt (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨x, hxL, hxo, hxH⟩ := key
  obtain ⟨y, hyH, m, hm, hym⟩ := exists_conj_mem_mgrp hs hne hSH hLΩ hxL hxo hxH
  have hnc : ¬ DbarConnected Ω W := not_dbarConnected_of_ne hs hne
  have hMH := mgrp_le_H274 hs hμ hnc
  have hN : m⁻¹ * (y * g⁻¹) ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, ← hLdef, hym, ← conjSub_mul,
      inv_mul_cancel, conjSub_one]
  have hNH : m⁻¹ * (y * g⁻¹) ∈ T8.H274 Ω K z :=
    T8.sigmaNorm_le_H274 K z (T8.normalizer_le_sigmaNorm hΩ.conjInvariant hK hN)
  have h1 : g⁻¹ ∈ T8.H274 Ω K z := by
    have h2 := (T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).inv_mem hyH)
      (hMH hm)) hNH
    simpa [mul_assoc] using h2
  simpa using (T8.H274 Ω K z).inv_mem h1

theorem mem_H274_of_conj_mem_H274 (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ T8.H274 Ω K z) :
    g ∈ T8.H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ T8.H274 Ω K z :=
    (Q3T8.Asc77.T8.sylow_le_sigmaNorm hΩ hK hRΩ hRK hRS hs.hz).trans (T8.sigmaNorm_le_H274 K z)
  have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have := hs.hz.conj g⁻¹
    rwa [inv_inv] at this
  have hb2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * z * g)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact hb.sq) hb.ne_one)
  obtain ⟨y, hyH, hyS⟩ := T8.exists_conj_into_sylow S hSH hg hb2
  have h1 : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) ∈ (S : Subgroup G) := by
    have : (g * y⁻¹)⁻¹ * z * (g * y⁻¹) = y * (g⁻¹ * z * g) * y⁻¹ := by group
    rwa [this]
  have h2 := mem_H274_of_conj_mem_sylow hs hμ hne h1
  have : g = (g * y⁻¹) * y := by group
  rw [this]
  exact (T8.H274 Ω K z).mul_mem h2 hyH

theorem fixesUniqueCoset_z (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset z (T8.H274 Ω K z) := by
  have hzH : z ∈ T8.H274 Ω K z :=
    T8.sigmaNorm_le_H274 K z (T8.normalizer_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
      (Subgroup.le_normalizer hs.hz.mem))
  show ∃! c : G ⧸ T8.H274 Ω K z, z • c = c
  refine ⟨((1 : G) : G ⧸ T8.H274 Ω K z), ?_, fun c hc => ?_⟩
  · show z • ((1 : G) : G ⧸ T8.H274 Ω K z) = ((1 : G) : G ⧸ T8.H274 Ω K z)
    rw [smul_coe_eq_iff]
    simpa using hzH
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : z • (x : G ⧸ T8.H274 Ω K z) = x := hc
    have hx := (smul_coe_eq_iff _ z x).mp hc'
    have hxH := mem_H274_of_conj_mem_H274 hs hμ hne hx
    rw [QuotientGroup.eq]
    simpa using (T8.H274 Ω K z).inv_mem hxH


theorem mem_H274_of_conj_zt_mem_sylow (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hP := partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := not_dbarConnected_of_ne hs hne
  have c := Q3CL.T8.ctxOf hP hW
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  set d := g⁻¹ * (z * t) * g with hd
  have hdd : d * d = 1 := by
    rw [hd]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [hx]; group
  have hdN : d ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 d hg)
  obtain ⟨R'', hR''D, hdR''⟩ := Q3T8.Asc77.l7_12_proved G Ω hP W hW hnc d hdN hdd
  obtain ⟨K'', hK'', hR''K''⟩ := exists_isSylow2In_of_mem_RSet hR''D.1
  have hKd : conjSub d K'' = K'' :=
    Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK'' hR''D.1 hR''K''.1 hdR''
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hs.stand.cls hnc (stdRepK hs)
    (Q3CL.T8.mkRep hP hW hK'' hR''D hR''K'')
  have hmK' : conjSub m K = K'' := hmK
  have hz'' : IsUniqueInvolution K'' (m * z * m⁻¹) := by
    have := hs.hz.conj m
    rwa [hmK'] at this
  have hdz : d * (m * z * m⁻¹) * d⁻¹ = m * z * m⁻¹ := hz''.conj_eq hKd
  have hb' : g * (m * z * m⁻¹) * g⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (z * t) * (g * (m * z * m⁻¹) * g⁻¹) * (z * t)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by
      have := congrArg (fun w => g * w * g⁻¹) hdz
      simp only [hd] at this
      calc (z * t) * (g * (m * z * m⁻¹) * g⁻¹) * (z * t)⁻¹
          = g * (g⁻¹ * (z * t) * g * (m * z * m⁻¹) * (g⁻¹ * (z * t) * g)⁻¹) * g⁻¹ := by group
        _ = g * (m * z * m⁻¹) * g⁻¹ := this
    calc g * (m * z * m⁻¹) * g⁻¹ * (z * t)
        = ((z * t) * (g * (m * z * m⁻¹) * g⁻¹) * (z * t)⁻¹) * (z * t) := by rw [h1]
      _ = (z * t) * (g * (m * z * m⁻¹) * g⁻¹) := by group
  have hxH := mem_H274_of_conj_mem_H274 hs hμ hne (g := (g * m)⁻¹) (by
    have : ((g * m)⁻¹)⁻¹ * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
    rw [this]
    exact T8.centralizer_mul_le_H274 hs.hJ hs.ht hb')
  have h2 : g * m ∈ T8.H274 Ω K z := by simpa using (T8.H274 Ω K z).inv_mem hxH
  have hmH := mgrp_le_H274 hs hμ hnc hm
  have : g = (g * m) * m⁻¹ := by group
  rw [this]
  exact (T8.H274 Ω K z).mul_mem h2 ((T8.H274 Ω K z).inv_mem hmH)

theorem fixesUniqueCoset_zt (hs : Std8Core Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset (z * t) (T8.H274 Ω K z) := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ T8.H274 Ω K z :=
    (Q3T8.Asc77.T8.sylow_le_sigmaNorm hΩ hK hRΩ hRK hRS hs.hz).trans (T8.sigmaNorm_le_H274 K z)
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  show ∃! c : G ⧸ T8.H274 Ω K z, (z * t) • c = c
  refine ⟨((1 : G) : G ⧸ T8.H274 Ω K z), ?_, fun c hc => ?_⟩
  · show (z * t) • ((1 : G) : G ⧸ T8.H274 Ω K z) = ((1 : G) : G ⧸ T8.H274 Ω K z)
    rw [smul_coe_eq_iff]
    simpa using hzt
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : (z * t) • (g : G ⧸ T8.H274 Ω K z) = g := hc
    have hg := (smul_coe_eq_iff _ (z * t) g).mp hc'
    have hb2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * (z * t) * g)) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two]
          calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by
                group
            _ = 1 := by rw [hx]; group
        · intro h1
          have : z * t = 1 := by
            calc z * t = g * (g⁻¹ * (z * t) * g) * g⁻¹ := by group
              _ = 1 := by rw [h1]; group
          exact T8.zt_ne_one hs.noTwins hs.hJ hs.hz hs.ht this)
    obtain ⟨y, hyH, hyS⟩ := T8.exists_conj_into_sylow S hSH hg hb2
    have h1 : (g * y⁻¹)⁻¹ * (z * t) * (g * y⁻¹) ∈ (S : Subgroup G) := by
      have : (g * y⁻¹)⁻¹ * (z * t) * (g * y⁻¹) = y * (g⁻¹ * (z * t) * g) * y⁻¹ := by group
      rwa [this]
    have h2 := mem_H274_of_conj_zt_mem_sylow hs hμ hne h1
    have hgH : g ∈ T8.H274 Ω K z := by
      have : g = (g * y⁻¹) * y := by group
      rw [this]
      exact (T8.H274 Ω K z).mul_mem h2 hyH
    rw [QuotientGroup.eq]
    simpa using (T8.H274 Ω K z).inv_mem hgH

end CFSG.ClassicalInvolution.Q3.Q3CL.Wyl
