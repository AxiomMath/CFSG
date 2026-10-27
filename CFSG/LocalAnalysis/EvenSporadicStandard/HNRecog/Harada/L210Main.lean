module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QInvol
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QOuter
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QIrr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210OddC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210OddD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210Abs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)
  {φ : ↥(normalizer (Rgrp h : Set G)) →* A5WrTwo}

theorem odd_Xq (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ) :
    ∀ P : Subgroup (Xq z), P.Normal → Odd (Nat.card P) → P = ⊥ :=
  eq_bot_of_odd_normal_Xq (by simpa [pow_two] using h.z_sq) h.z_ne_one
    (fun _ hU hn hodd => eq_bot_of_odd_normal_Mgrp h hzt htz
      (fun _ hBR hzB hB => Rgrp_irreducible h hzt htz hs hBR hzB hB) hU hn hodd)

theorem abs210_Aq (hzt : ¬ IsConj t z) (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ)
    (hF : Facts210 G t z) : Abs210 (Aq h) (wq h) (psiq h hs) where
  toL28Hyp := l28Hyp_Aq h hzt htz hs
  outer := outer_Aq h hs
  invol := invol_Aq h hs
  odd := odd_Xq h hzt htz hs
  noA5 := noA5_Aq h hF

theorem Rgrp_conj_Mgrp (hGold : GoldschmidtTheoremA) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ) (hF : Facts210 G t z) {m : G}
    (hm : m ∈ Mgrp z) {r : G} (hr : r ∈ Rgrp h) : m * r * m⁻¹ ∈ Rgrp h := by
  have hN : (Aq h).Normal := Abs210.normal hGold (abs210_Aq h hzt htz hs hF)
  have hrM : r ∈ Mgrp z := Rgrp_le_Mgrp h hr
  have hA : piq z ⟨r, hrM⟩ ∈ Aq h := (mem_Aq_iff h ⟨r, hrM⟩).mpr hr
  have hconj : piq z ⟨m, hm⟩ * piq z ⟨r, hrM⟩ * (piq z ⟨m, hm⟩)⁻¹ ∈ Aq h :=
    hN.conj_mem _ hA _
  have hconj' : piq z (⟨m, hm⟩ * ⟨r, hrM⟩ * ⟨m, hm⟩⁻¹) ∈ Aq h := by
    simpa only [map_mul, map_inv] using hconj
  have hR := (mem_Aq_iff h (⟨m, hm⟩ * ⟨r, hrM⟩ * ⟨m, hm⟩⁻¹)).mp hconj'
  simpa [Subgroup.coe_mul] using hR

theorem normalizer_Rgrp_eq_Mgrp (hGold : GoldschmidtTheoremA) (hzt : ¬ IsConj t z)
    (htz : IsConj t (t * z)) (hs : Lemma27Spec h φ) (hF : Facts210 G t z) :
    normalizer (Rgrp h : Set G) = Mgrp z := by
  refine le_antisymm (normalizer_Rgrp_le_Mgrp h) ?_
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Rgrp_conj_Mgrp h hGold hzt htz hs hF hm hx
  · intro hx
    have hx' := Rgrp_conj_Mgrp h hGold hzt htz hs hF (inv_mem hm) hx
    have heq : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
    rwa [heq] at hx'

end CFSG.EvenSporadicStandard.HNRecog.Harada
