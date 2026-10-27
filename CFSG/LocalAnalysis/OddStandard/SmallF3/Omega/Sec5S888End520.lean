module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End11c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

theorem asc82End520_of (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c)
    (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a) (hSy : Asc82SylowContain) :
    Asc82End520 := by
  classical
  intro h517 _h518b h519 G _ _ t L S z r B A K₁ K₂ h c
  have hq := sec5b517_quad h514 c
  have hQ : Qsub K₁ K₂ h = Sec5B517Q8 hq := by
    rw [sec5b517_Qsub_eq, hq.core_eq]
  have hNz := sec5b517_normalizer_le h514 c
  have hNz8 : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G) := by
    simpa only [hQ] using hNz
  obtain ⟨T, hQT, hTN⟩ := exists_sylow_normalizer_Q8 hq
  have hQT' : Qsub K₁ K₂ h ≤ T := by simpa only [hQ] using hQT
  have hTN' : IsSylow2Of T (normalizer (Qsub K₁ K₂ h : Set G)) := by
    simpa only [hQ] using hTN
  have hTH : IsSylow2Of T (centralizer ({z} : Set G)) :=
    hSy G t L S z r B A K₁ K₂ h c T hQT' hTN'
  have hperm517 := (h517 G t L S z r B A K₁ K₂ h c).1
  have htrans517 := (h517 G t L S z r B A K₁ K₂ h c).2
  have hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (Kfam5 K₁ K₂ h i) n = Kfam5 K₁ K₂ h j := by
    intro n hn i
    have hn' : n ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hn
    have hmem : CFSG.conjugate (Kfam5 K₁ K₂ h i) n ∈ Gamma5 K₁ K₂ h :=
      hperm517 n hn' (Kfam5 K₁ K₂ h i) (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩)
    rw [sec5b517_gamma_eq] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  have htrans : ∀ i j : Fin 4, ∃ n ∈ normalizer (Sec5B517Q8 hq : Set G),
      CFSG.conjugate (Kfam5 K₁ K₂ h i) n = Kfam5 K₁ K₂ h j := by
    intro i j
    obtain ⟨n, hn, hjn⟩ := htrans517 (Kfam5 K₁ K₂ h i)
      (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩) (Kfam5 K₁ K₂ h j)
      (by rw [sec5b517_gamma_eq]; exact ⟨j, rfl⟩)
    exact ⟨n, by simpa only [hQ] using hn, hjn⟩
  have hclosed519 := h519 G t L S z r B A K₁ K₂ h c
  have hclosed : ∀ q ∈ Sec5B517Q8 hq, ∀ x ∈ centralizer ({z} : Set G),
      x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hq : Set G) →
        x⁻¹ * q * x ∈ Sec5B517Q8 hq := by
    intro q hq8 x hx hxq
    have hqsub : q ∈ Qsub K₁ K₂ h := by simpa only [hQ] using hq8
    have hxq' : x⁻¹ * q * x ∈ normalizer (Qsub K₁ K₂ h : Set G) := by
      simpa only [hQ] using hxq
    simpa only [hQ] using hclosed519 q hqsub x hx hxq'
  have hcentS_raw := centS_of_516a h516a c hTN' hNz
  have hcentS : ∀ s ∈ T, (∀ q ∈ Sec5B517Q8 hq, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) →
      s ∈ Sec5B517Q8 hq := by
    intro s hsT hcomm
    have hcomm' : ∀ q ∈ Qsub K₁ K₂ h, s * q * s⁻¹ * q⁻¹ ∈ zpowers z := by
      intro q hqsub
      exact hcomm q (by simpa only [hQ] using hqsub)
    simpa only [hQ] using hcentS_raw s hsT hcomm'
  have hH := pocketHyp_of_G hq hNz8 hTN hTH hQT hperm htrans hclosed hcentS
  obtain ⟨P, p, n, hp, hzP, hsub, hn, h8, hmod⟩ :=
    pocket_of_hyp hGold hN11a hN11b hN11c hH (zCent_mem_center z)
  haveI : Fact p.Prime := hp
  exact ⟨p, n, hp, P.map (centralizer ({z} : Set G)).subtype, hn, h8,
    pocket_to_G z hzP hsub hmod⟩

end CFSG.OddStandard.SmallF3.Omega
