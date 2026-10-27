module

public import CFSG.ClassicalInvolution.Asc77.AscT8RC261
public import CFSG.ClassicalInvolution.Asc77.AscT8ROutFEng
import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

namespace T8R

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem eq_of_mem_conj_sylow (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hs' := Std8.conj hs n
  have hX' := eq_sup_oddCoreOf_conj hΩ hX n
  have hV := extraTrans hs' hX'
  exact eq_of_mem_conj_sylow_gen (AschTight.hypOmegaGen_of_mod hp hq hΩ) hs.hz hs.ht hs.hJ
    hs.noTwins (T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht) hs'.stand.mem hs'.hJ.1 hs'.hz
    hs'.ht hs'.hR hs'.hT
    (l6_7_proved p f hp hq G Ω hΩ (conjSylow n S) (conjSub n R) hs'.hR.1 (conjSub n T) hs'.hT.1
      hs'.hR.2.2 hs'.hT.2.2 (R_ne_T hs'))
    (fix_or_swap hs' hX') (eq_of_swap hs' hX' hV) (eq_of_centralizes hs' hX' hV)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _, conj_zt_mul_inv_mem_oddCoreOf hs hX hy⟩)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _,
      conj_zt_mul_inv_mem_oddCoreOf (Std8.symm' hs) (eq_sup_oddCoreOf_swap hs hX) hy⟩)
    (l9_3 (p := p) (f := f) G Ω (partIHyp_of_std8 hs')) hzP htP

theorem outerFusion (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) : OuterFusion K J S R T z t := by
  intro g hbS hbR hbT _ _
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := T3.mem_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have hzRu : IsUniqueInvolution R z := uniqueInvolution_restrict hs.hz hRK hzR
  have htTu : IsUniqueInvolution T t := uniqueInvolution_restrict hs.ht hTJ htT
  have hz2 : z * z = 1 := hs.hz.sq
  have ht2 : t * t = 1 := hs.ht.sq
  have hz1 : z ≠ 1 := hs.hz.ne_one
  have ht1 : t ≠ 1 := hs.ht.ne_one
  have hzt : z ≠ t := by
    intro h'
    exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
  have hztc : z * t = t * z := T8.mul_comm_of_mem_omegaNbr hp hΩ hs.hz hs.hJ hs.ht
  have hbz : (g⁻¹ * (z * t) * g) * z = z * (g⁻¹ * (z * t) * g) := by
    have h : IsUniqueInvolution R ((g⁻¹ * (z * t) * g) * z * (g⁻¹ * (z * t) * g)⁻¹) := by
      have := hzRu.conj (g⁻¹ * (z * t) * g)
      rwa [hbR] at this
    have h' := hzRu.eq h
    calc (g⁻¹ * (z * t) * g) * z
        = ((g⁻¹ * (z * t) * g) * z * (g⁻¹ * (z * t) * g)⁻¹) * (g⁻¹ * (z * t) * g) := by group
      _ = z * (g⁻¹ * (z * t) * g) := by rw [← h']
  have hbt : (g⁻¹ * (z * t) * g) * t = t * (g⁻¹ * (z * t) * g) := by
    have h : IsUniqueInvolution T ((g⁻¹ * (z * t) * g) * t * (g⁻¹ * (z * t) * g)⁻¹) := by
      have := htTu.conj (g⁻¹ * (z * t) * g)
      rwa [hbT] at this
    have h' := htTu.eq h
    calc (g⁻¹ * (z * t) * g) * t
        = ((g⁻¹ * (z * t) * g) * t * (g⁻¹ * (z * t) * g)⁻¹) * (g⁻¹ * (z * t) * g) := by group
      _ = t * (g⁻¹ * (z * t) * g) := by rw [← h']
  obtain ⟨U, hUel, hzU, htU, hUenum⟩ := exists_fourGroup hz2 ht2 hz1 ht1 hzt hztc
  have hU2 : IsPGroup 2 ↥U := IsPGroup.of_card (n := 2) hUel.1
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  have hQC : ∀ y ∈ U, y * (g⁻¹ * (z * t) * (g⁻¹)⁻¹) = (g⁻¹ * (z * t) * (g⁻¹)⁻¹) * y := by
    intro y hy
    rw [inv_inv]
    rcases hUenum y hy with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      exact hbz.symm
    · rw [h]
      exact hbt.symm
    · rw [h]
      exact Commute.mul_left (a := z) (b := t) (c := g⁻¹ * (z * t) * g) hbz.symm hbt.symm
  obtain ⟨n', hn', hUn'⟩ := exists_conj_sylow_of_le_centralizer S haS hU2 hQC
  have key := eq_of_mem_conj_sylow hs hX (hUn' hzU) (hUn' htU)
  rw [inv_inv] at hn'
  rw [← hn']
  exact key

end Cert

variable (p f : ℕ) [Fact p.Prime]


theorem outerFusionAll : OuterFusionAll p f := by
  intro G _ _ _ Ω K J S R T W z t hs _ hX
  exact outerFusion hs hX

theorem c26_1 : C26_1 p f := c26_1_of_outer (outerFusionAll p f)

end T8R

end CFSG.ClassicalInvolution.Asc77
