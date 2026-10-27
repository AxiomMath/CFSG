module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB2
import CFSG.StronglyEmbedded.UniqueCosetFixedEng
public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem muIsoWylD4_transfer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W W' : Subgroup G} (hW : W ∈ WSet Ω) (hW' : W' ∈ WSet Ω) (h : MuIsoWylD4 Ω W) :
    MuIsoWylD4 Ω W' := by
  obtain ⟨φ⟩ := h
  obtain ⟨e⟩ := l7_5_2_proved p f hp hq G Ω hΩ W hW W' hW'
  exact ⟨e.symm.trans φ⟩

theorem mgrp_le_H274 (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) : MGrp Ω W ≤ T8.H274 Ω K z := by
  obtain ⟨F⟩ := exists_frameData hs hμ hnc
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have h01 := F.mgrp_le_centralizer c 0 1
  rw [F.hz0, F.hz1] at h01
  exact h01.trans (T8.centralizer_mul_le_H274 hs.hJ hs.ht)

theorem exists_conj_mem_mgrp (hs : Std8 p f Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hSH : (S : Subgroup G) ≤ T8.H274 Ω K z) {L : Subgroup G} (hL : L ∈ Ω) {x : G} (hxL : x ∈ L)
    (hxo : orderOf x = 4) (hxH : x ∈ T8.H274 Ω K z) :
    ∃ y ∈ T8.H274 Ω K z, ∃ m ∈ MGrp Ω W, conjSub y L = conjSub m K := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have c := T8.ctxOf hP hW
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
    l6_11_proved p f hp hq G Ω hΩ S η hη hηS (conjSub y L) hL' (by omega)
  have hUSet : conjSub y L ⊓ (⨆ V ∈ η, V) ∈ USet Ω := (hS'η.1 hUη).1
  have hUS : conjSub y L ⊓ (⨆ V ∈ η, V) ≤ (S : Subgroup G) :=
    inf_le_right.trans (hWη ▸ hWS)
  obtain ⟨T₁, hT₁D, hT₁L⟩ := exists_sylow_mem_DSet hp hq hΩ hW hWS hL' hUSet inf_le_left hUS
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hnc (T8.stdRepK hs)
    (T8.mkRep hP hW hL' hT₁D hT₁L)
  exact ⟨y, hyH, m, hm, hmK.symm⟩


theorem mem_H274_of_conj_mem_sylow (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
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
    (T8.sylow_le_sigmaNorm hp hq hΩ hK hRΩ hRK hRS hz).trans (T8.sigmaNorm_le_H274 K z)
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
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hRsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hRΩ; omega)
  have htT : t ∈ T := T3.mem_of_isPGroup ht hTJ hTsyl.2.1
    (by have := hΩ.eight_le_of_mem_RSet hp hTΩ; omega)
  have key : ∃ x ∈ L, orderOf x = 4 ∧ x ∈ T8.H274 Ω K z := by
    by_cases hRb : conjSub b R = R
    swap
    · have hKb : conjSub b K ∈ omegaNbr Ω K :=
        T8.conjSub_mem_omegaNbr hp hq hΩ hK hRΩ hRK hRS hz hg hRb
      obtain ⟨x, hxL, hxo, hxc⟩ := T8.exists_orderFour_centralizes_mul_conj hp hq hΩ hK hRΩ hRK
        hRS hz hg hRb hLΩ hb hCb
      exact ⟨x, hxL, hxo, T8.centralizer_mul_le_H274 hKb (hz.conj b)
        (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    by_cases hTb : conjSub b T = T
    swap
    · have hJb : conjSub b J ∈ omegaNbr Ω J :=
        T8.conjSub_mem_omegaNbr hp hq hΩ hJΩ hTΩ hTJ hTS ht hg hTb
      obtain ⟨x, hxL, hxo, hxc⟩ := T8.exists_orderFour_centralizes_mul_conj hp hq hΩ hJΩ hTΩ
        hTJ hTS ht hg hTb hLΩ hb hCb
      exact ⟨x, hxL, hxo, T8.centralizer_mul_le_H274_of_mem_dComp hΩ.conjInvariant hK htrans
        hJc hz ht hJb (ht.conj b) (Subgroup.mem_centralizer_singleton_iff.mpr hxc)⟩
    have hKb : conjSub b K = K := T8.conjSub_eq_of_conjSub_eq hp hΩ hK hRΩ hRK hRb
    have hJb : conjSub b J = J := T8.conjSub_eq_of_conjSub_eq hp hΩ hJΩ hTΩ hTJ hTb
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
    obtain ⟨x, hxL, hxo, hxc⟩ := T8.exists_orderFour_centralizes_one_of_three hp hΩ hLΩ hb
      S.isPGroup' (hRS hzR) (hTS htT) (mem_normalizer_iff_conjSub_eq.mp (hCb hzb))
      (mem_normalizer_iff_conjSub_eq.mp (hCb htb))
    refine ⟨x, hxL, hxo, ?_⟩
    rcases hxc with h | h | h
    · exact hCz (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCt (Subgroup.mem_centralizer_singleton_iff.mpr h)
    · exact hCzt (Subgroup.mem_centralizer_singleton_iff.mpr h)
  obtain ⟨x, hxL, hxo, hxH⟩ := key
  obtain ⟨y, hyH, m, hm, hym⟩ := exists_conj_mem_mgrp hs hne hSH hLΩ hxL hxo hxH
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
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

theorem mem_H274_of_conj_mem_H274 (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * z * g ∈ T8.H274 Ω K z) :
    g ∈ T8.H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ T8.H274 Ω K z :=
    (T8.sylow_le_sigmaNorm hp hq hΩ hK hRΩ hRK hRS hs.hz).trans (T8.sigmaNorm_le_H274 K z)
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

theorem fixesUniqueCoset_z (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) :
    FixesUniqueCoset z (T8.H274 Ω K z) := by
  have hzH : z ∈ T8.H274 Ω K z :=
    T8.sigmaNorm_le_H274 K z (T8.normalizer_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem
      (Subgroup.le_normalizer hs.hz.mem))
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzH (fun x hx => ?_)
  exact mem_H274_of_conj_mem_H274 hs hμ hne hx

end T8YY

end CFSG.ClassicalInvolution.Asc77
