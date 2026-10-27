module

public import CFSG.ClassicalInvolution.Asc77.AscT8V7
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8Y4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

section Reps40

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem sylow_le_layerJoin (hs : Std8 p f Ω K J S R T W z t) {M P : Subgroup G}
    (hM : T8.XMem Ω (z * t) M) (hP : IsSylow2In P M) (hPa : P ≤ T8.cenZ (z * t)) :
    P ≤ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  intro u hu
  exact T8.le_layerJoin ⟨M, hM, rfl⟩ ((hM.isSylow2In_layerRes_of_le hp hq hΩ hx hP hPa).1 hu)

theorem R_le_layerJoin (hs : Std8 p f Ω K J S R T W z t) : R ≤ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hRa : R ≤ T8.cenZ (z * t) := by
    rw [T8.cenZ_eq_centralizer]
    exact T8.le_centralizer_mul hs
  exact sylow_le_layerJoin hs (T8.xMem_zt hs)
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hs.hR.1 hs.hR.2.1) hRa

theorem T_le_layerJoin (hs : Std8 p f Ω K J S R T W z t) : T ≤ T8.layerJoin Ω (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  exact sylow_le_layerJoin hs (xMem_J hs)
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1) (T_le_cenZ hs)

theorem xMem_rep (hs : Std8 p f Ω K J S R T W z t) (ρ : Rep Ω W) (hK : ρ.K ≠ K) (hJ : ρ.K ≠ J)
    (hnK : ρ.K ∉ omegaNbr Ω K) (hnJ : ρ.K ∉ omegaNbr Ω J) {v : G}
    (hv : IsUniqueInvolution ρ.K v) :
    T8.XMem Ω (z * t) ρ.K ∧ ρ.R ≤ T8.cenZ (z * t) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hnK' : K ∉ omegaNbr Ω ρ.K := fun h =>
    hnK (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ ρ.hK hs.stand.mem h)
  have hnJ' : J ∉ omegaNbr Ω ρ.K := fun h =>
    hnJ (T3.omegaNbr_symm (l6_2 p f) hp hq hΩ ρ.hK hs.hJ.1 h)
  have h1 : ρ.r * z * ρ.r⁻¹ = v * z := c.conj_involution ρ (T8.stdRepK hs) hK hnK' hv hs.hz
  have h2 : ρ.r * t * ρ.r⁻¹ = v * t := c.conj_involution ρ (T8.stdRepJ hs) hJ hnJ' hv hs.ht
  have hvW : v ∈ W :=
    (uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW ρ.hK ρ.hR ρ.hRK hv).2
  have hzW := z_mem_W hs
  have htW := t_mem_W hs
  have hvz : v * z = z * v := c.comm_W v hvW z hzW
  have hconj : ρ.r * (z * t) * ρ.r⁻¹ = z * t := by
    calc ρ.r * (z * t) * ρ.r⁻¹ = (ρ.r * z * ρ.r⁻¹) * (ρ.r * t * ρ.r⁻¹) := by group
      _ = (v * z) * (v * t) := by rw [h1, h2]
      _ = v * (z * v) * t := by group
      _ = v * (v * z) * t := by rw [hvz]
      _ = (v * v) * (z * t) := by group
      _ = z * t := by rw [hv.sq, one_mul]
  have hra : ρ.r * (z * t) = (z * t) * ρ.r := by
    calc ρ.r * (z * t) = (ρ.r * (z * t) * ρ.r⁻¹) * ρ.r := by group
      _ = (z * t) * ρ.r := by rw [hconj]
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcR : ∀ x ∈ ρ.R, x * (z * t) = (z * t) * x := centralizes_of_comm_r c ρ haW hra
  have hav : (z * t) * v = v * (z * t) := c.comm_W _ haW v hvW
  refine ⟨⟨ρ.hK, ?_, ρ.R, ρ.hRK, fun r hr => hcR r hr⟩, fun r hr => T8.mem_cenZ_iff.mpr (hcR r hr)⟩
  exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant ρ.hK (hnt _ ρ.hK) hv
    (Subgroup.mem_centralizer_singleton_iff.mpr hav)

end Reps40

section RepsBig

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem rep_K_eq [IsSimpleGroup G] (hD4 : Ih8D4Star p f) (hE : E4SecNoRoot p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t)))
    (ρ : Rep Ω W) : ρ.K = K ∨ ρ.K = J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hρK, hρJ⟩ := hcon
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  obtain ⟨v, hv⟩ := hΩ.exists_uniqueInvolution hp hq ρ.hK
  have hKJ : K ∈ omegaNbr Ω J :=
    T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ
  by_cases h1 : ρ.K ∈ omegaNbr Ω K <;> by_cases h2 : ρ.K ∈ omegaNbr Ω J
  ·
    have hn : CITBelowU p f (Nat.card G) := hs.stand.below f hq
    have hρ1 : K ∈ omegaNbr Ω ρ.K := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem ρ.hK h1
    have hρ2 : J ∈ omegaNbr Ω ρ.K := T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.hJ.1 ρ.hK h2
    have hKJne : K ≠ J := hs.hJ.2.1.symm
    refine hdisc (T8.dstarConnected_layerFamQ_of_reps hD4 (T8.partIHyp_of_std8 hs) hs.hW.1 hn hnt
      ![T8.stdRepK hs, T8.stdRepJ hs, ρ] ![z, t, v] ?_ ?_ ?_ (T8.zt_not_central hs))
    · intro i
      fin_cases i
      · exact hs.hz
      · exact hs.ht
      · exact hv
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hKJne
      · exact hρK.symm
      · exact hKJne.symm
      · exact absurd rfl hij
      · exact hρJ.symm
      · exact hρK
      · exact hρJ
      · exact absurd rfl hij
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hs.hJ
      · exact h1
      · exact hKJ
      · exact absurd rfl hij
      · exact h2
      · exact hρ1
      · exact hρ2
      · exact absurd rfl hij
  ·
    obtain ⟨g, hg, -, hgg⟩ := exists_sq_root c (T8.stdRepJ hs) hs.ht
    obtain ⟨y, hyW, hyy, hyJ, hyK⟩ := exists_y_left c (T8.stdRepJ hs) (T8.stdRepK hs) ρ
      hs.hJ hρJ.symm h2 h1 hs.ht hv hg hgg
    exact no_root_t hE hs hdisc hyW hyy hyK hyJ
  ·
    obtain ⟨g, hg, -, hgg⟩ := exists_sq_root c (T8.stdRepK hs) hs.hz
    obtain ⟨y, hyW, hyy, hyK, hyJ⟩ := exists_y_left c (T8.stdRepK hs) (T8.stdRepJ hs) ρ
      hKJ hρK.symm h1 h2 hs.hz hv hg hgg
    exact no_root_z hE hs hdisc hyW hyy hyK hyJ
  ·
    obtain ⟨hX, hRa⟩ := xMem_rep hs ρ hρK hρJ h1 h2 hv
    obtain ⟨g, hg, hgR, hgg⟩ := exists_sq_root c (T8.stdRepK hs) hs.hz
    obtain ⟨h, hh, hhR, hhh⟩ := exists_sq_root c (T8.stdRepJ hs) hs.ht
    obtain ⟨y, hyW, hy, hyy, hyK, hyJ⟩ := exists_y_both c (T8.stdRepK hs) (T8.stdRepJ hs) ρ
      hs.hJ hKJ hρK.symm hρJ.symm h1 h2 hs.hz hs.ht hv hg hgg hh hhh
    have h8 := hΩ.eight_le_of_mem_RSet hp ρ.hR.1
    have hvR : v ∈ ρ.R := T3.mem_of_isPGroup hv ρ.hRK.1 ρ.hRK.2.1 (by omega)
    have hyY : y ∈ T8.layerJoin Ω (z * t) := by
      rw [hy]
      exact (T8.layerJoin Ω (z * t)).mul_mem ((T8.layerJoin Ω (z * t)).mul_mem
        (sylow_le_layerJoin hs hX ρ.hRK hRa hvR)
        ((T8.layerJoin Ω (z * t)).inv_mem (R_le_layerJoin hs hgR)))
        ((T8.layerJoin Ω (z * t)).inv_mem (T_le_layerJoin hs hhR))
    exact no_root_zt hE hs hdisc hyW hyY hyy hyK hyJ

theorem c27_Ysmall_of_e4sec (hD4 : Ih8D4Star p f) (hE : E4SecNoRoot p f) : C27_Ysmall p f := by
  intro G _ _ _ Ω K J S R T W z t hs _hD _hE4 hnab hdisc
  exfalso
  obtain ⟨d, hd, e, he, hde⟩ := T8.exists_noncomm_of_not_abelian hnab
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKJ : K ∈ omegaNbr Ω J :=
    T3.omegaNbr_symm (l6_2 p f) hp hq hΩ hs.stand.mem hs.hJ.1 hs.hJ
  have key : ∀ ρ σ : Rep Ω W, (ρ.K = K ∨ ρ.K = J) → (σ.K = K ∨ σ.K = J) →
      T8.repElt ρ * T8.repElt σ = T8.repElt σ * T8.repElt ρ := by
    intro ρ σ hρ hσ
    by_cases h : ρ.K = σ.K
    · rw [(T8.repElt_eq_iff c ρ σ).mpr h]
    · refine (T8.repElt_commute_iff c ρ σ h).mpr ?_
      rcases hρ with h1 | h1 <;> rcases hσ with h2 | h2
      · exact absurd (h1.trans h2.symm) h
      · rw [h1, h2]
        exact hs.hJ
      · rw [h1, h2]
        exact hKJ
      · exact absurd (h1.trans h2.symm) h
  obtain ⟨ρ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := T8.exists_rep_of_mem_muDelta he
  exact hde (key ρ σ (rep_K_eq hD4 hE hs hdisc ρ) (rep_K_eq hD4 hE hs hdisc σ))

end RepsBig

end T8V

end CFSG.ClassicalInvolution.Asc77
