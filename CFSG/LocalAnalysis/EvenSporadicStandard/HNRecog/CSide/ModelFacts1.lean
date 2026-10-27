module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelIota
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheckDefs
public import Mathlib.Tactic.Basify

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

private noncomputable def dsMf1_iotaProd (g : A5 × A5) : SL2 × SL2 := (iota g.1, iota g.2)

private lemma dsMf1_iotaProd_eq_prodCongr (g : A5 × A5) :
    dsMf1_iotaProd g = MulEquiv.prodCongr iota iota g := rfl

private lemma dsMf1_iotaProd_pow_eq_one_iff (g : A5 × A5) (n : ℕ) :
    dsMf1_iotaProd g ^ n = 1 ↔ g ^ n = 1 := by
  rw [dsMf1_iotaProd_eq_prodCongr, ← map_pow, MulEquiv.map_eq_one_iff]

private lemma dsMf1_iotaProd_eq_one_iff (g : A5 × A5) : dsMf1_iotaProd g = 1 ↔ g = 1 := by
  rw [dsMf1_iotaProd_eq_prodCongr, MulEquiv.map_eq_one_iff]

private lemma dsMf1_iotaProd_ne_one_iff (g : A5 × A5) : dsMf1_iotaProd g ≠ 1 ↔ g ≠ 1 :=
  dsMf1_iotaProd_eq_one_iff g |>.not

private lemma dsMf1_iotaProd_fst_eq_one_iff (g : A5 × A5) :
    (dsMf1_iotaProd g).1 = 1 ↔ g.1 = 1 := by
  rw [show (dsMf1_iotaProd g).1 = iota g.1 from rfl, MulEquiv.map_eq_one_iff]

private lemma dsMf1_iotaProd_snd_eq_one_iff (g : A5 × A5) :
    (dsMf1_iotaProd g).2 = 1 ↔ g.2 = 1 := by
  rw [show (dsMf1_iotaProd g).2 = iota g.2 from rfl, MulEquiv.map_eq_one_iff]

private lemma dsMf1_iotaProd_fst_ne_one_iff (g : A5 × A5) :
    (dsMf1_iotaProd g).1 ≠ 1 ↔ g.1 ≠ 1 := (dsMf1_iotaProd_fst_eq_one_iff g).not

private lemma dsMf1_iotaProd_snd_ne_one_iff (g : A5 × A5) :
    (dsMf1_iotaProd g).2 ≠ 1 ↔ g.2 ≠ 1 := (dsMf1_iotaProd_snd_eq_one_iff g).not

private lemma dsMf1_actFun_eq (g : A5 × A5) (v : V0) :
    actFun (dsMf1_iotaProd g) v = sigma0 g v := (sigma0_apply g v).symm

private lemma dsMf1_filter_sigma0 (g : A5 × A5) :
    (Finset.univ.filter fun v : V0 => sigma0 g v = v) = cSideFix (dsMf1_iotaProd g) := by
  ext v
  simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and, dsMf1_actFun_eq]

private lemma dsMf1_card_sigma0 (g : A5 × A5)
    (hcard : (cSideFix (dsMf1_iotaProd g)).card = 16) :
    Nat.card {v : V0 // sigma0 g v = v} = 16 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, dsMf1_filter_sigma0, hcard]

theorem cSideFixedZero_sigma0 (h : cSideModelProp) : CSideFixedZero sigma0 := by
  unfold CSideFixedZero
  intro g hord htriv v hv
  have hpow : dsMf1_iotaProd g ^ 3 = 1 ∨ dsMf1_iotaProd g ^ 5 = 1 := by
    rcases hord with h3 | h5
    · left
      rw [dsMf1_iotaProd_pow_eq_one_iff]
      simpa [h3] using pow_orderOf_eq_one g
    · right
      rw [dsMf1_iotaProd_pow_eq_one_iff]
      simpa [h5] using pow_orderOf_eq_one g
  have hne : dsMf1_iotaProd g ≠ 1 := by
    rw [dsMf1_iotaProd_ne_one_iff]
    rintro rfl
    simp only [orderOf_one] at hord
    exact absurd hord (by decide)
  have htriv' : (dsMf1_iotaProd g).1 = 1 ∨ (dsMf1_iotaProd g).2 = 1 := by
    rcases htriv with h1 | h2
    · left; rwa [dsMf1_iotaProd_fst_eq_one_iff]
    · right; rwa [dsMf1_iotaProd_snd_eq_one_iff]
  have hmem : v ∈ cSideFix (dsMf1_iotaProd g) := by
    simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and, dsMf1_actFun_eq]
    exact hv
  exact h.1 (dsMf1_iotaProd g) hpow hne htriv' v hmem

theorem cSideThreeBoth_sigma0 (h : cSideModelProp) : CSideThreeBoth q0 sigma0 := by
  unfold CSideThreeBoth
  intro g hord h1 h2
  have hpow : dsMf1_iotaProd g ^ 3 = 1 := by
    rw [dsMf1_iotaProd_pow_eq_one_iff]
    simpa [hord] using pow_orderOf_eq_one g
  have hg1 : (dsMf1_iotaProd g).1 ≠ 1 := by rwa [dsMf1_iotaProd_fst_ne_one_iff]
  have hg2 : (dsMf1_iotaProd g).2 ≠ 1 := by rwa [dsMf1_iotaProd_snd_ne_one_iff]
  obtain ⟨hcard, hnd, hpl⟩ := h.2.1 (dsMf1_iotaProd g) hpow hg1 hg2
  refine ⟨dsMf1_card_sigma0 g hcard, ?_, ?_⟩
  · intro v hv hv0
    have hvmem : v ∈ cSideFix (dsMf1_iotaProd g) := by
      simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and, dsMf1_actFun_eq]
      exact hv
    obtain ⟨w, hwmem, hw⟩ := hnd v hvmem hv0
    refine ⟨w, ?_, ?_⟩
    · simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and] at hwmem
      rw [← dsMf1_actFun_eq]
      exact hwmem
    · rwa [q0_polar]
  · obtain ⟨v, hvmem, w, hwmem, hv0, hw0, hvw, hqv, hqw, hpvw⟩ := hpl
    simp only [cSideFix, Finset.mem_filter, Finset.mem_univ, true_and] at hvmem hwmem
    refine ⟨v, w, ?_, ?_, hv0, hw0, hvw, ?_, ?_, ?_⟩
    · rw [← dsMf1_actFun_eq]; exact hvmem
    · rw [← dsMf1_actFun_eq]; exact hwmem
    · rwa [q0_apply]
    · rwa [q0_apply]
    · rwa [q0_polar]

theorem cSideInvol_sigma0 (h : cSideModelProp) : CSideInvol sigma0 := by
  unfold CSideInvol
  intro g hg1 hg2
  have hpow : dsMf1_iotaProd g ^ 2 = 1 := by
    rw [dsMf1_iotaProd_pow_eq_one_iff]
    exact hg2
  have hne : dsMf1_iotaProd g ≠ 1 := by rwa [dsMf1_iotaProd_ne_one_iff]
  exact dsMf1_card_sigma0 g (h.2.2.1 (dsMf1_iotaProd g) hpow hne)

end CFSG.EvenSporadicStandard.HNRecog.CSide
