module

import CFSG.ClassicalInvolution.Asc77.AscT8Layer
public import CFSG.ClassicalInvolution.Asc77.AscMuTabBasic
public import CFSG.ClassicalInvolution.Asc77.AscT7FI

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T7N

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.not_mem_twinSet_J (h : Hyp21 p f Ω K K' z u J t W) : J ∉ twinSet Ω K :=
  fun hJV => (h.hJ.2 J hJV).2.1 rfl

theorem Hyp21.twinSet_eq_pair (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : twinSet Ω K = {K, K'} := by
  classical
  have hst := h.std.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  ext L
  constructor
  · intro hL
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    obtain ⟨hLK, hLK'⟩ := hcon
    have hLΩ : L ∈ Ω := hL.1
    have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
    have c : Ctx p f Ω W := MuTab.muTabCtx hP h.hW
    have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
    obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hK hz h.hzW
    obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hK'Ω hzK' h.hzW
    obtain ⟨ρ₃, hρ₃⟩ := c.exists_rep_of_involution_mem hLΩ hzL h.hzW
    obtain ⟨ρ₄, hρ₄⟩ := c.exists_rep_of_involution_mem h.hJ.1 h.ht h.htW
    have h12 : ρ₂.K ∈ omegaNbr Ω ρ₁.K := by
      rw [hρ₁, hρ₂]
      exact T3.twin_mem_omegaNbr hΩ hK hK'Ω h.std.hne hz hzK'
    have h13 : ρ₃.K ∈ omegaNbr Ω ρ₁.K := by
      rw [hρ₁, hρ₃]
      exact T3.twin_mem_omegaNbr hΩ hK hLΩ hLK hz hzL
    have h23 : ρ₃.K ∈ omegaNbr Ω ρ₂.K := by
      rw [hρ₂, hρ₃]
      exact T3.twin_mem_omegaNbr hΩ hK'Ω hLΩ hLK' hzK' hzL
    have h14 : ρ₄.K ∈ omegaNbr Ω ρ₁.K := by
      rw [hρ₁, hρ₄]
      exact h.hJ.2 K (mem_twinSet_self hK hz)
    have hJ2 : J ≠ K' := fun e => Hyp21.not_mem_twinSet_J h (e ▸ h.std.hK')
    have hJ3 : J ≠ L := fun e => Hyp21.not_mem_twinSet_J h (e ▸ hL)
    have h4 := c.mul_four_eq_one hnc ρ₁ ρ₂ ρ₃ ρ₄ h12 h13 h23 h14 (by rw [hρ₄, hρ₂]; exact hJ2)
      (by rw [hρ₄, hρ₃]; exact hJ3) (hρ₁ ▸ hz) (hρ₂ ▸ hzK') (hρ₃ ▸ hzL) (hρ₄ ▸ h.ht)
    have hzz : z * z = 1 := hz.sq
    have h5 : z * t = 1 := by
      have := h4
      rwa [hzz, one_mul] at this
    have htz : t = z := by
      have h6 : t = z⁻¹ := eq_inv_of_mul_eq_one_right h5
      rw [h6]
      exact inv_eq_of_mul_eq_one_left hzz
    exact Hyp21.not_mem_twinSet_J h ⟨h.hJ.1, z, hz, htz ▸ h.ht⟩
  · rintro (rfl | rfl)
    · exact mem_twinSet_self hK hz
    · exact h.std.hK'

theorem Hyp21.conjSub_twin_eq (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) {n : G} (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    conjSub n K' = K' := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hmem : conjSub n K' ∈ twinSet Ω K := by
    have := twinSet_conj hΩ.conjInvariant h.std.hK' n
    rwa [hnK] at this
  rw [Hyp21.twinSet_eq_pair h hne] at hmem
  rcases hmem with e | e
  · exact absurd (conjSub_injective n (e.trans hnK.symm)) h.std.hne
  · exact e

theorem Hyp21.twin_le_centralizer_t (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : L ≤ Subgroup.centralizer ({t} : Set G) := by
  have hst := h.std.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hfr := h.twinFrameData
  have hzt : z * t = t * z := hfr.comm_zt hp hΩ
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
  have htz : t ≠ z := hfr.t_ne_z
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz.sq h.ht.sq hz.ne_one h.ht.ne_one htz.symm hzt
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hαzt : alphaOf (Subgroup.closure ({z, t} : Set G)) = ⊥ := by
    rw [(hC3 G Ω K K' z u J t W h).2 _ hle hA]
    exact hα
  have hO : ∀ x ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)), x * t = t * x :=
    T8.oddCoreOf_centralizer_commutes hαzt (Subgroup.subset_closure (by simp)) hz.ne_one
      (Subgroup.subset_closure (by simp))
  intro ℓ hℓ
  have hc := T7A.commutator_twin_mem_oddCoreOf hp hq hΩ hfr hL ℓ hℓ
  rw [commutatorElement_def] at hc
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (oddCoreOf_odd_natCard (Subgroup.centralizer ({z} : Set G))) h.ht.sq
    (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer htC))
    (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hℓC)) hc
  have h1 : t * (ℓ * o) = (ℓ * o) * t := mul_inv_eq_iff_eq_mul.mp hfix
  have h2 : o * t = t * o := (hO o hoO)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h3 : (t * ℓ) * o = (ℓ * t) * o := by
    calc (t * ℓ) * o = t * (ℓ * o) := by rw [mul_assoc]
      _ = (ℓ * o) * t := h1
      _ = ℓ * (o * t) := by rw [mul_assoc]
      _ = ℓ * (t * o) := by rw [h2]
      _ = (ℓ * t) * o := by rw [mul_assoc]
  exact (mul_right_cancel h3).symm

end Frame

end T7N

end CFSG.ClassicalInvolution.Asc77
