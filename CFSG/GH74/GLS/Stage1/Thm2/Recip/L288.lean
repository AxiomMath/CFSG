module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.UFacts

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {L J Py P : Subgroup G} {a w : G}

theorem lemma_28_8_L (hBal : IG_balance_fAut) (h44 : II4_44) (hAut : II4_Aut) (h327 : IG_3_27)
    (hs : Setup G x y L J a Py P w) : InducesInner y L ∧ y ∉ cSec L := by
  have hFB := hs.hFB
  have hcfg := hFB.cfg
  have hy1 := mul_self_eq_one_of_orderOf_eq_two hcfg.hy
  have hnotcs : y ∉ cSec L := fun h =>
    hs.hnfy (inducesFAut_of_mem_cSec hcfg.simple hcfg.hx hcfg.hL.1 hcfg.hL.2.1 h)
  refine ⟨?_, hnotcs⟩
  by_contra hni
  have hQ := h44 G hcfg.simple x hcfg.hx L hcfg.hL.1 hcfg.hL.2.1
  have hφ2 := phi_mul_self L hs.hyN hy1
  have hninn : phi L y hs.hyN ∉ innOf (Hat L) := fun h => hni ((phi_mem_inn_iff L hs.hyN).mp h)
  have hnotF : ¬ IsFAutomorphism (Hat L) (phi L y hs.hyN) := fun hF => hs.hnfy ⟨hs.hyN, hF⟩
  have hnosq := ((hAut (Hat L) hQ).2.2 (phi L y hs.hyN) hφ2).2 hninn hnotF
  obtain ⟨m, hm2, hm, hyp⟩ := hFB.exists_pow
  have hya2 : y = a * a := by
    by_cases hm2' : m = 2
    · subst hm2'
      calc y = a ^ (2 ^ (2 - 1)) := hyp
        _ = a * a := by norm_num [pow_two]
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have hcN : (a * a) ^ (2 ^ k) ∈ normalizer (L : Set G) := pow_mem hs.a2N _
      have hcc : (a * a) ^ (2 ^ k) * (a * a) ^ (2 ^ k) = y := by
        rw [hyp, ← pow_add, ← pow_two, ← pow_mul]
        congr 1
        rw [show k + 3 - 1 = k + 2 by omega]
        ring
      refine hnosq (phi L ((a * a) ^ (2 ^ k)) hcN) ?_
      rw [← phi_mul L hcN hcN]
      exact phi_congr L hcc _ hs.hyN
  obtain ⟨u, hu⟩ : ∃ u : G, u = w * (a⁻¹ * w * a) := ⟨_, rfl⟩
  have hbx : u⁻¹ * a⁻¹ * u * a = x := by
    rw [hu, hs.hb_formula]
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
    have e1 : a⁻¹ * a⁻¹ * w * a * a = y⁻¹ * w * y := by
      rw [hya2]
      simp only [mul_inv_rev, mul_assoc]
    have e2 : y⁻¹ * w * y = w⁻¹ := by
      have h1 : y * w * y⁻¹ = w⁻¹ := hs.hwinv
      rw [hyinv] at h1 ⊢
      exact h1
    rw [e1, e2]
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by group
      _ = x⁻¹ := by rw [hs.hww]
      _ = x := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two hcfg.hx)
  have huy : u * y = y * u := by rw [hu]; exact mem_centralizer_singleton_iff.mp hs.hu_cy
  have hJu : IsIntrinsic y (conjugate J u) := isIntrinsic_conjugate huy.symm hcfg.hJ
  have hxJt : x ∈ Jt y := by
    have hmem : u⁻¹ * a⁻¹ * u ∈ conjugate J u := by
      rw [mem_conjugate_iff', show u * (u⁻¹ * a⁻¹ * u) * u⁻¹ = a⁻¹ by group]
      exact inv_mem hFB.ha
    rw [← hbx]
    exact mul_mem (le_Jt hJu hmem) (le_Jt hcfg.hJ hFB.ha)
  obtain ⟨g, hg1, hg2⟩ := hFB.swap hBal h44 hAut h327
  have hyLayer : y ∈ pLayerOf 2 (centralizer ({x} : Set G)) := by
    have h1 : (MulAut.conj g⁻¹).toMonoidHom x ∈ (Jt y).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hxJt
    have h2 := Jt_map_conj_le y g⁻¹ h1
    have e1 : (MulAut.conj g⁻¹).toMonoidHom x = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hg1
    have e2 : g⁻¹ * y * g⁻¹⁻¹ = x := by
      rw [inv_inv]
      exact hg2
    rw [e1, e2] at h2
    exact Jt_le_pLayerOf x h2
  exact hni (mem_innSub_iff.mp (pLayerOf_le_innSub hcfg.hL.1 hyLayer))

end CFSG.GH74.GLS.Stage1.Thm2.Recip
