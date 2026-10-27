module

public import CFSG.ClassicalInvolution.Asc77.AscC25H5
public import CFSG.ClassicalInvolution.Asc77.AscC25H6
public import CFSG.ClassicalInvolution.Asc77.AscC25H2
public import CFSG.ClassicalInvolution.Asc77.AscC25V10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem exists_triv_conj (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a n : G}
    (ha2 : a * a = 1) (haz : a * z = z * a) (hat : a * t' = t' * a)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hnz : n * z = z * n) (hn'K : t' * n * t' ∈ Subgroup.normalizer (K : Set G))
    (hδa : diagGamma (nuG hp hq e a) = 1)
    (hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t' * n * t')))
    (hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t' * n * t')) *
        SemidirectProduct.rightHom (nuG hp hq e a)) :
    ∃ c m₁ : G, c * z = z * c ∧ m₁ ∈ Triv hp hq e z t' h.ht'2 ∧ t' * m₁ * t' = m₁⁻¹ ∧
      t' * m₁ = c * (a * z * t') * c⁻¹ := by
  classical
  have hsq : z * z = 1 := h.hz.sq
  have htz : t' * z = z * t' := t'_comm_z h
  have ht2 : t' * t' = 1 := h.ht'2
  have hti : t'⁻¹ = t' := h.ht'inv
  obtain ⟨k, hkK, hkν⟩ := exists_k_nuG h hp hq e haK hnK hn'K hδa hδ hχ
  obtain ⟨n', hn'⟩ : ∃ n' : G, n' = t' * n * t' := ⟨_, rfl⟩
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
  have hk'K' : t' * k * t' ∈ K' := by
    have h1 := conj_mem_conjSub (n := t') hkK
    rw [hti, conjSub_t'_K h] at h1
    exact h1
  have hk'N : t' * k * t' ∈ Subgroup.normalizer (K : Set G) :=
    h.hΩ.le_normalizer_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz hk'K'
  have hνk' : nuG hp hq e (t' * k * t') = 1 := by
    refine (nuG_eq_one_iff hp hq e hk'N).mpr (fun l hl => ?_)
    have hc := h.hΩ.comm_le_oddCore_of_twin h.hK' h.hK h.hs.hne h.hz' h.hz
    exact (hc (Subgroup.commutator_mem_commutator hk'K' hl)).2
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : G, m₁ = (t' * k * t') * m * k⁻¹ := ⟨_, rfl⟩
  have hC1 : Commute t' z := htz
  have hkz : Commute k z := (h.hz.commute_of_mem hkK).symm
  have hk'z : Commute (t' * k * t') z := (hC1.mul_left hkz).mul_left hC1
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
  have e0 : t' * (t' * k * t') * t' = k := by
    calc t' * (t' * k * t') * t' = (t' * t') * k * (t' * t') := by group
      _ = k := by rw [ht2]; group
  have e1 : t' * k⁻¹ * t' = (t' * k * t')⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, hti]
    group
  have hm₁t : t' * m₁ * t' = k * m⁻¹ * (t' * k * t')⁻¹ := by
    calc t' * m₁ * t' = (t' * (t' * k * t') * t') * (t' * m * t') * (t' * k⁻¹ * t') := by
          rw [hm₁]
          calc t' * ((t' * k * t') * m * k⁻¹) * t' =
              t' * (t' * k * t') * (t' * t') * m * (t' * t') * k⁻¹ * t' := by rw [ht2]; group
            _ = _ := by group
      _ = k * m⁻¹ * (t' * k * t')⁻¹ := by rw [e0, hmt, e1]
  have hm₁t'N : t' * m₁ * t' ∈ Subgroup.normalizer (K : Set G) := by
    rw [hm₁t]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N)
  have hνm₁ : nuG hp hq e m₁ = 1 := by
    rw [hm₁, nuG_mul hp hq e (Subgroup.mul_mem _ hk'N hmN) (Subgroup.inv_mem _ hkN),
      nuG_mul hp hq e hk'N hmN, hνk', one_mul, nuG_inv hp hq e hkN, hkν, mul_inv_cancel]
  have hνm₁t : nuG hp hq e (t' * m₁ * t') = 1 := by
    rw [hm₁t, nuG_mul hp hq e (Subgroup.mul_mem _ hkN (Subgroup.inv_mem _ hmN))
      (Subgroup.inv_mem _ hk'N), nuG_mul hp hq e hkN (Subgroup.inv_mem _ hmN),
      nuG_inv hp hq e hmN, nuG_inv hp hq e hk'N, hνk', inv_one, mul_one, hkν, mul_inv_cancel]
  refine ⟨k * n, m₁, (hkz.mul_left hnz'), ⟨hm₁N, hm₁z, hm₁t'N, hνm₁, hνm₁t⟩, ?_, ?_⟩
  · rw [hm₁t, hm₁]
    group
  · calc t' * m₁ = k * (t' * m) * k⁻¹ := by
          rw [hm₁]
          calc t' * ((t' * k * t') * m * k⁻¹) = (t' * t') * k * t' * m * k⁻¹ := by group
            _ = k * (t' * m) * k⁻¹ := by rw [ht2, one_mul]; group
      _ = k * (n * (a * z * t') * n⁻¹) * k⁻¹ := by rw [hmx]
      _ = (k * n) * (a * z * t') * (k * n)⁻¹ := by group

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
