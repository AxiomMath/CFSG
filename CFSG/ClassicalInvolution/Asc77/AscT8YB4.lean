module

public import CFSG.ClassicalInvolution.Asc77.AscT8YB3
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTwelve
import CFSG.StronglyEmbedded.UniqueCosetFixedEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.StronglyEmbedded.UniqueCoset

namespace T8YY


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem mem_H274_of_conj_zt_mem_sylow (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {g : G} (hg : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) :
    g ∈ T8.H274 Ω K z := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have c := T8.ctxOf hP hW
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  set d := g⁻¹ * (z * t) * g with hd
  have hdd : d * d = 1 := by
    rw [hd]
    calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
      _ = 1 := by rw [hx]; group
  have hdN : d ∈ Subgroup.normalizer (W : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 d hg)
  obtain ⟨R'', hR''D, hdR''⟩ := l7_12_proved (p := p) (f := f) G Ω hP W hW hnc d hdN hdd
  obtain ⟨K'', hK'', hR''K''⟩ := exists_isSylow2In_of_mem_RSet hR''D.1
  have hKd : conjSub d K'' = K'' :=
    T8.conjSub_eq_of_conjSub_eq hp hΩ hK'' hR''D.1 hR''K''.1 hdR''
  obtain ⟨m, hm, hmK⟩ := c.exists_conj_of_rep hnc (T8.stdRepK hs)
    (T8.mkRep hP hW hK'' hR''D hR''K'')
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
  have hbH : g * (m * z * m⁻¹) * g⁻¹ ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht hb'
  have hxH := mem_H274_of_conj_mem_H274 hs hμ hne (g := (g * m)⁻¹) (by
    have : ((g * m)⁻¹)⁻¹ * z * (g * m)⁻¹ = g * (m * z * m⁻¹) * g⁻¹ := by group
    rwa [this])
  have h2 : g * m ∈ T8.H274 Ω K z := by simpa using (T8.H274 Ω K z).inv_mem hxH
  have hmH := mgrp_le_H274 hs hμ hnc hm
  have : g = (g * m) * m⁻¹ := by group
  rw [this]
  exact (T8.H274 Ω K z).mul_mem h2 ((T8.H274 Ω K z).inv_mem hmH)

theorem fixesUniqueCoset_zt (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : FixesUniqueCoset (z * t) (T8.H274 Ω K z) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  have hSH : (S : Subgroup G) ≤ T8.H274 Ω K z :=
    (T8.sylow_le_sigmaNorm hp hq hΩ hK hRΩ hRK hRS hs.hz).trans (T8.sigmaNorm_le_H274 K z)
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  have hb2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * (z * t) * g)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc g⁻¹ * (z * t) * g * (g⁻¹ * (z * t) * g) = g⁻¹ * (z * t * (z * t)) * g := by group
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
  exact hgH

theorem h274_eq_top [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K) : T8.H274 Ω K z = ⊤ := by
  by_contra hH
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := fixesUniqueCoset_z hs hμ hne
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact fixesUniqueCoset_zt hstd
        (muIsoWylD4_transfer hs.stand.odd hs.stand.five hs.stand.hyp hs.hW.1 hstd.hW.1 hμ) hne
  have hKs := not_isSolvable_of_mem hs.stand.hyp hs.stand.mem hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
    exact hKs inferInstance
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact false_of_uniqueCoset_of_not_isSolvable hH hz2 h1 h2'
    hTs hTnab hTc (le_centralizer_of_isUniqueInvolution hz) hKs

end T8YY

end CFSG.ClassicalInvolution.Asc77
