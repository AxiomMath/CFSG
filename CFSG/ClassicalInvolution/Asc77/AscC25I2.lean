module

public import CFSG.ClassicalInvolution.Asc77.AscC25I1
public import CFSG.ClassicalInvolution.Asc77.AscC25H5
public import CFSG.ClassicalInvolution.Asc77.AscC25H6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25I

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' t₀ : G}


theorem exists_k_nuG' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') {t₀ : G} (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a n : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hδa : diagGamma (nuG hp hq e a) = 1)
    (hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t₀ * n * t₀)))
    (hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t₀ * n * t₀)) *
        SemidirectProduct.rightHom (nuG hp hq e a)) :
    ∃ k ∈ K, nuG hp hq e k = nuG hp hq e ((t₀ * n * t₀) * (a * z) * n⁻¹) := by
  classical
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hazN : a * z ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ haK hzK
  have hmN : (t₀ * n * t₀) * (a * z) * n⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK)
  have hνm : nuG hp hq e ((t₀ * n * t₀) * (a * z) * n⁻¹) =
      nuG hp hq e (t₀ * n * t₀) * nuG hp hq e a * (nuG hp hq e n)⁻¹ := by
    rw [nuG_mul hp hq e (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK),
      nuG_mul hp hq e hn'K hazN, nuG_mul hp hq e haK hzK, nuG_inv hp hq e hnK,
      nuG_z_eq_one h hp hq e, mul_one]
  have hδm : diagChar hp hq e ⟨_, hmN⟩ = 1 := by
    rw [diagChar_eq_diagGamma_nuG hp hq e hmN, hνm, map_mul, map_mul, map_inv, hδa, mul_one, ← hδ,
      mul_inv_cancel]
  have hχm : fieldChar hp hq e ⟨_, hmN⟩ = 1 := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hmN, hνm, map_mul, map_mul, map_inv, hχ]
    exact mul_inv_cancel _
  obtain ⟨k, hkK, hk⟩ := exists_mem_K_nuG_eq_inr hp hq e hmN hδm
  rw [hχm, map_one] at hk
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have h1 : nuG hp hq e (k⁻¹ * ((t₀ * n * t₀) * (a * z) * n⁻¹)) =
      (nuG hp hq e k)⁻¹ * nuG hp hq e ((t₀ * n * t₀) * (a * z) * n⁻¹) := by
    rw [nuG_mul hp hq e (Subgroup.inv_mem _ hkN) hmN, nuG_inv hp hq e hkN]
  rw [h1] at hk
  exact ⟨k, hkK, inv_mul_eq_one.mp hk⟩


theorem exists_triv_conj' (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')
    (hsw : IsSwap K K' z t₀) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a n : G}
    (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t₀ = t₀ * a)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hnz : n * z = z * n) (hn'K : t₀ * n * t₀ ∈ Subgroup.normalizer (K : Set G))
    (hδa : diagGamma (nuG hp hq e a) = 1)
    (hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t₀ * n * t₀)))
    (hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t₀ * n * t₀)) *
        SemidirectProduct.rightHom (nuG hp hq e a)) :
    ∃ c m₁ : G, c * z = z * c ∧ m₁ ∈ Triv hp hq e z t₀ hsw.sq ∧ t₀ * m₁ * t₀ = m₁⁻¹ ∧
      t₀ * m₁ = c * (a * z * t₀) * c⁻¹ := by
  classical
  have hsq : z * z = 1 := h.hz.sq
  have htz : t₀ * z = z * t₀ := hsw.comm
  have ht2 : t₀ * t₀ = 1 := hsw.sq
  have hti : t₀⁻¹ = t₀ := hsw.inv
  obtain ⟨k, hkK, hkν⟩ := exists_k_nuG' h hp hq e haK hnK hn'K hδa hδ hχ
  obtain ⟨n', hn'⟩ : ∃ n' : G, n' = t₀ * n * t₀ := ⟨_, rfl⟩
  rw [← hn'] at hn'K hkν
  obtain ⟨m, hm⟩ : ∃ m : G, m = n' * (a * z) * n⁻¹ := ⟨_, rfl⟩
  rw [← hm] at hkν
  obtain ⟨hmt, hmx⟩ := swap_m_facts ht2 hti haz ha2 hsq hat htz hn'
  rw [← hm] at hmt hmx
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hazN : a * z ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ haK hzK
  have hmN : m ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK)
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have hk'K' : t₀ * k * t₀ ∈ K' := by
    have h1 := conj_mem_conjSub (n := t₀) hkK
    rw [hti, hsw.swapK] at h1
    exact h1
  have hk'N : t₀ * k * t₀ ∈ Subgroup.normalizer (K : Set G) :=
    h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz hk'K'
  have hνk' : nuG hp hq e (t₀ * k * t₀) = 1 := by
    refine (nuG_eq_one_iff hp hq e hk'N).mpr (fun l hl => ?_)
    have hc := h.hΩ.comm_le_oddCore_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz
    exact (hc (Subgroup.commutator_mem_commutator hk'K' hl)).2
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : G, m₁ = (t₀ * k * t₀) * m * k⁻¹ := ⟨_, rfl⟩
  have hC1 : Commute t₀ z := htz
  have hkz : Commute k z := (h.hz.commute_of_mem hkK).symm
  have hk'z : Commute (t₀ * k * t₀) z := (hC1.mul_left hkz).mul_left hC1
  have hnz' : Commute n z := hnz
  have hn'z : Commute n' z := by rw [hn']; exact (hC1.mul_left hnz').mul_left hC1
  have hmz : Commute m z := by
    rw [hm]
    exact (hn'z.mul_left ((show Commute a z from haz).mul_left (Commute.refl z))).mul_left
      hnz'.inv_left
  have hm₁N : m₁ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm₁]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk'N hmN) (Subgroup.inv_mem _ hkN)
  have hm₁z : m₁ * z = z * m₁ := by
    rw [hm₁]
    exact (hk'z.mul_left hmz).mul_left hkz.inv_left
  have e0 : t₀ * (t₀ * k * t₀) * t₀ = k := by
    calc t₀ * (t₀ * k * t₀) * t₀ = (t₀ * t₀) * k * (t₀ * t₀) := by group
      _ = k := by rw [ht2]; group
  have e1 : t₀ * k⁻¹ * t₀ = (t₀ * k * t₀)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  have hm₁t : t₀ * m₁ * t₀ = k * m⁻¹ * (t₀ * k * t₀)⁻¹ := by
    calc t₀ * m₁ * t₀ = (t₀ * (t₀ * k * t₀) * t₀) * (t₀ * m * t₀) * (t₀ * k⁻¹ * t₀) := by
          rw [hm₁]
          calc t₀ * ((t₀ * k * t₀) * m * k⁻¹) * t₀ =
              t₀ * (t₀ * k * t₀) * (t₀ * t₀) * m * (t₀ * t₀) * k⁻¹ * t₀ := by rw [ht2]; group
            _ = _ := by group
      _ = k * m⁻¹ * (t₀ * k * t₀)⁻¹ := by rw [e0, hmt, e1]
  have hm₁t₀N : t₀ * m₁ * t₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm₁t]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N)
  have hνm₁ : nuG hp hq e m₁ = 1 := by
    rw [hm₁, nuG_mul hp hq e (Subgroup.mul_mem _ hk'N hmN) (Subgroup.inv_mem _ hkN),
      nuG_mul hp hq e hk'N hmN, hνk', one_mul, nuG_inv hp hq e hkN, hkν, mul_inv_cancel]
  have hνm₁t : nuG hp hq e (t₀ * m₁ * t₀) = 1 := by
    rw [hm₁t, nuG_mul hp hq e (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N), nuG_mul hp hq e hkN (Subgroup.inv_mem _ hmN),
      nuG_inv hp hq e hmN, nuG_inv hp hq e hk'N, hνk', inv_one, mul_one, hkν, mul_inv_cancel]
  refine ⟨k * n, m₁, (hkz.mul_left hnz'), ⟨hm₁N, hm₁z, hm₁t₀N, hνm₁, hνm₁t⟩, ?_, ?_⟩
  · rw [hm₁t, hm₁]
    group
  · calc t₀ * m₁ = k * (t₀ * m) * k⁻¹ := by
          rw [hm₁]
          calc t₀ * ((t₀ * k * t₀) * m * k⁻¹) = (t₀ * t₀) * k * t₀ * m * k⁻¹ := by group
            _ = k * (t₀ * m) * k⁻¹ := by rw [ht2, one_mul]; group
      _ = k * (n * (a * z * t₀) * n⁻¹) * k⁻¹ := by rw [hmx]
      _ = (k * n) * (a * z * t₀) * (k * n)⁻¹ := by group

end Main

end CFSG.ClassicalInvolution.Asc77.C25I
