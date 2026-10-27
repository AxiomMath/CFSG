module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj

open scoped Pointwise

theorem exists_conj_eq_of_card_three {K : Type*} [Group K] [Finite K]
    (hcyc : ∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) [Fact (Nat.Prime 3)]
    {A B : Subgroup K} (hA : Nat.card A = 3) (hB : Nat.card B = 3) :
    ∃ g : K, B.map (MulAut.conj g).toMonoidHom = A := by
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by rw [hB, pow_one])
  obtain ⟨P, hAP⟩ := hA3.exists_le_sylow
  obtain ⟨Q, hBQ⟩ := hB3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q P
  refine ⟨g, ?_⟩
  have hgQ : (MulAut.conj g • (Q : Subgroup K)) = P := by
    have := congrArg (fun S : Sylow 3 K => (S : Subgroup K)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  have hBgP : B.map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [← hgQ]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨b, hBQ hb, rfl⟩
  have hBcard : Nat.card (B.map (MulAut.conj g).toMonoidHom : Subgroup K) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB]
  have hPcyc : IsCyclic P := hcyc P P.isPGroup'
  have heq := (IsCyclic.subgroup_eq_iff_card_eq
    (H := (B.map (MulAut.conj g).toMonoidHom).subgroupOf P) (K := A.subgroupOf P)).2 (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBgP).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, hBcard, hA])
  have h := Subgroup.subgroupOf_inj.mp heq
  rwa [inf_eq_left.mpr hBgP, inf_eq_left.mpr hAP] at h

theorem exists_conj_mem_centralizer {K : Type*} [Group K] [Finite K]
    (hcyc : ∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) [Fact (Nat.Prime 3)]
    {A : Subgroup K} (hA : Nat.card A = 3) {t : K} (ht : 3 ∣ orderOf t) :
    ∃ x : K, orderOf x = orderOf t ∧ x ∈ Subgroup.centralizer (A : Set K) := by
  have hn : orderOf t ≠ 0 := (orderOf_pos t).ne'
  set s : K := t ^ (orderOf t / 3) with hs
  have hs3 : orderOf s = 3 := orderOf_pow_orderOf_div hn ht
  set B : Subgroup K := Subgroup.zpowers s
  have hB : Nat.card B = 3 := by rw [Nat.card_zpowers, hs3]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_three hcyc hA hB
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective t
    simpa using this
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hg] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hcomm : t * s ^ k = s ^ k * t := by
      exact (((Commute.refl t).pow_right (orderOf t / 3)).zpow_right k).eq
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc g * s ^ k * g⁻¹ * (g * t * g⁻¹) = g * (s ^ k * t) * g⁻¹ := by group
      _ = g * (t * s ^ k) * g⁻¹ := by rw [hcomm]
      _ = g * t * g⁻¹ * (g * s ^ k * g⁻¹) := by group

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupConj
