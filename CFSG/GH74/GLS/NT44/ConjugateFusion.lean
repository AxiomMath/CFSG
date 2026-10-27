module

public import CFSG.GroupTheory.ABGLocalTools.Basic

import CFSG.LargeExtraspecial.S3Fusion

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

theorem exists_normalizer_conj_eq_on_of_conjugate_closure
    {G : Type} [Group G] [Finite G]
    {T : Subgroup G} {x : G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    {D : Set G} {g : G}
    (hD : D ⊆
      (Subgroup.centralizer
        (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G))
    (hDg : (fun d : G => g * d * g⁻¹) '' D ⊆
      (Subgroup.centralizer
        (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G)) :
    ∃ n ∈ Subgroup.normalizer
        (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G),
      ∀ d ∈ D, n * d * n⁻¹ = g * d * g⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup G := Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} with hB
  set N : Subgroup G := Subgroup.normalizer (B : Set G) with hN
  have hBT : B ≤ T := by
    rw [hB, Subgroup.closure_le]
    rintro _ ha
    exact ha.1
  have hB2 : IsPGroup 2 B := hT.isPGroup.to_le hBT
  have hweak : ∀ a : G, B.map (MulAut.conj a).toMonoidHom ≤ T →
      B.map (MulAut.conj a).toMonoidHom = B := by
    intro a haT
    have hle : B.map (MulAut.conj a).toMonoidHom ≤ B := by
      rw [hB, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.subset_closure ⟨haT ⟨b, Subgroup.subset_closure hb, rfl⟩, ?_⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
        hb.2.trans (isConj_iff.mpr ⟨a, rfl⟩)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]
  have hTN : T ≤ N := by
    intro t ht
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq]
    refine hweak t ?_
    rintro _ ⟨b, hb, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      T.mul_mem (T.mul_mem ht (hBT hb)) (T.inv_mem ht)
  have hTsylowN : CFSG.ABGLocalTools.IsSylowOf 2 T N :=
    hT.of_le hTN le_top
  obtain ⟨Q, hQ⟩ := hTsylowN.exists_sylow_eq_subgroupOf
  have hwc : CFSG.LargeExtraspecial.IsWeaklyClosedInNormalizer B := by
    intro a ha
    set A : Subgroup G := B.map (MulAut.conj a).toMonoidHom with hA
    have haA : A ≤ N := by
      simpa [hA] using ha
    have hA2G : IsPGroup 2 A := by
      rw [hA]
      exact hB2.map (MulAut.conj a).toMonoidHom
    have hA2 : IsPGroup 2 (A.subgroupOf N) :=
      hA2G.of_equiv (Subgroup.subgroupOfEquivOfLe haA).symm
    obtain ⟨R, hR⟩ := hA2.exists_le_sylow
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N R Q
    have hAn : B.map (MulAut.conj ((n : G) * a)).toMonoidHom ≤ T := by
      rintro _ ⟨b, hb, rfl⟩
      have hbA : (MulAut.conj a) b ∈ A := by
        rw [hA]
        exact ⟨b, hb, rfl⟩
      have hbN : (⟨(MulAut.conj a) b, haA hbA⟩ : N) ∈ A.subgroupOf N :=
        Subgroup.mem_subgroupOf.mpr hbA
      have hbR : (⟨(MulAut.conj a) b, haA hbA⟩ : N) ∈ (R : Subgroup N) := hR hbN
      have h1 : MulAut.conj n • (⟨(MulAut.conj a) b, haA hbA⟩ : N) ∈
          ((n • R : Sylow 2 N) : Subgroup N) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hbR
      rw [hn, MulAut.smul_def, MulAut.conj_apply] at h1
      rw [hQ, Subgroup.mem_subgroupOf] at h1
      have h1' : (n : G) * (MulAut.conj a) b * (n : G)⁻¹ ∈ T := by
        simpa using h1
      have hEq : (n : G) * (MulAut.conj a) b * (n : G)⁻¹ =
          (MulAut.conj ((n : G) * a)) b := by
        simp only [MulAut.conj_apply]
        group
      rw [hEq] at h1'
      exact h1'
    have hBna : B.map (MulAut.conj ((n : G) * a)).toMonoidHom = B :=
      hweak ((n : G) * a) hAn
    have hmap : B.map (MulAut.conj ((n : G) * a)).toMonoidHom =
        A.map (MulAut.conj (n : G)).toMonoidHom := by
      rw [hA, Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    have hA_n : A.map (MulAut.conj (n : G)).toMonoidHom = B := by
      rw [hBna] at hmap
      exact hmap.symm
    have hNn : B.map (MulAut.conj (n : G)).toMonoidHom = B := by
      have hnN : (n : G) ∈ Subgroup.normalizer (B : Set G) := by
        simp
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
    have hAeq : A = B := by
      refine Subgroup.map_injective (f := (MulAut.conj (n : G)).toMonoidHom)
        (MulAut.conj (n : G)).injective ?_
      rw [hA_n, hNn]
    simpa [hA] using hAeq
  have hD' : D ⊆ (Subgroup.centralizer (B : Set G) : Set G) := by
    rw [hB]
    exact hD
  have hDg' : (fun d : G => g * d * g⁻¹) '' D ⊆
      (Subgroup.centralizer (B : Set G) : Set G) := by
    rw [hB]
    exact hDg
  obtain ⟨n, hnN, hnd⟩ :=
    CFSG.LargeExtraspecial.lemma_3_12 (p := 2) (A := B) hB2 hwc hD' hDg'
  refine ⟨n, ?_, hnd⟩
  exact hnN

end CFSG.GH74.GLS.NT44

end