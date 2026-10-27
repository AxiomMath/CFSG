module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog

private theorem natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private theorem grpS5_normal_two_subgroup_eq_bot (M : Subgroup (Equiv.Perm (Fin 5)))
    (hMnormal : M.Normal) (hM : IsPGroup 2 M) : M = ⊥ := by
  have hcard8 : Nat.card M ∣ 8 := by
    obtain ⟨n, hn⟩ := hM.exists_card_eq
    rw [hn]
    have hdvd : 2 ^ n ∣ 120 := by
      have h := Subgroup.card_subgroup_dvd_card M
      rw [hn, Nat.card_perm, Nat.card_fin] at h
      norm_num at h
      exact h
    have hn3 : n ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ n := by omega
      have h16 : (2 : ℕ) ^ 4 ∣ 120 := (pow_dvd_pow 2 h4).trans hdvd
      norm_num at h16
    simpa using Nat.pow_dvd_pow 2 hn3
  have hpow : ∀ x ∈ M, x ^ 8 = 1 := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard M hx).trans hcard8)
  have hcheck : ∀ g : Equiv.Perm (Fin 5), g ≠ 1 → g ^ 8 = 1 →
      ∃ h : Equiv.Perm (Fin 5), (h * g * h⁻¹ * g⁻¹) ^ 8 ≠ 1 := by
    decide +kernel
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  by_contra hg1
  obtain ⟨h, hh⟩ := hcheck g hg1 (hpow g hg)
  exact hh (hpow _ (by
    have hconj : h * g * h⁻¹ ∈ M := hMnormal.conj_mem g hg h
    exact mul_mem hconj (inv_mem hg)))

theorem cSide_isShapeTwoTwoSixS5_exists {X : Type*} [Group X] (h : IsShapeTwoTwoSixS5 X) :
    ∃ (N : Subgroup X) (_ : N.Normal), IsPGroup 2 N ∧
      Nonempty (X ⧸ N ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨V, N, hVnorm, hNnorm, hVN, ⟨eV⟩, ⟨eN⟩, ⟨eX⟩⟩ := h
  haveI : V.Normal := hVnorm
  haveI : N.Normal := hNnorm
  refine ⟨N, hNnorm, ?_, ⟨eX⟩⟩
  apply IsPGroup.of_card (n := 8)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf N)]
  have hNq : Nat.card (N ⧸ V.subgroupOf N) = 2 ^ 6 := by
    rw [Nat.card_congr eN.toEquiv, natCard_elem2]
  have hVq : Nat.card (V.subgroupOf N) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv,
      Nat.card_congr eV.toEquiv, natCard_elem2]
  rw [hNq, hVq]
  norm_num

theorem cSide_isPGroup_ker_comp {X D A : Type*} [Group X] [Group D] [Group A] (ψ : X →* D)
    (φ : D →* A) (hψ : IsPGroup 2 ψ.ker) (hφ : IsPGroup 2 φ.ker) :
    IsPGroup 2 (φ.comp ψ).ker := by
  rw [← MonoidHom.comap_ker φ ψ]
  exact hφ.comap_of_ker_isPGroup ψ hψ

theorem cSide_noS5 {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : IsPGroup 2 N) (e : X ⧸ N ≃* Equiv.Perm (Fin 5)) (φ : X →* alternatingGroup (Fin 5))
    (hφ : IsPGroup 2 φ.ker) : False := by
  let π : X →* X ⧸ N := QuotientGroup.mk' N
  let M : Subgroup (X ⧸ N) := φ.ker.map π
  have hMnormal : M.Normal :=
    (MonoidHom.normal_ker φ).map π (QuotientGroup.mk'_surjective N)
  have hMpg : IsPGroup 2 M := hφ.map π
  let M' : Subgroup (Equiv.Perm (Fin 5)) := M.map e.toMonoidHom
  have hM'normal : M'.Normal := hMnormal.map e.toMonoidHom e.surjective
  have hM'pg : IsPGroup 2 M' := hMpg.map e.toMonoidHom
  have hM'bot : M' = ⊥ := grpS5_normal_two_subgroup_eq_bot M' hM'normal hM'pg
  have hMbot : M = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    have hmem : e m ∈ M' := Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    rw [hM'bot] at hmem
    exact e.injective (by simpa using hmem)
  have hKN : φ.ker ≤ N := by
    intro k hk
    have hkM : π k ∈ M := Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
    rw [hMbot] at hkM
    have hkq : π k = 1 := by simpa using hkM
    have hker : k ∈ π.ker := MonoidHom.mem_ker.mpr hkq
    rwa [QuotientGroup.ker_mk' N] at hker
  have hX : Nat.card X = 120 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
    have hq : Nat.card (X ⧸ N) = 120 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    rw [hq]
  have hle : Nat.card X ≤ 60 * Nat.card N := by
    have h1 : Nat.card φ.ker ≤ Nat.card N := Subgroup.card_le_of_le hKN
    have h2 : Nat.card φ.range ≤ 60 := by
      have h := Subgroup.card_le_card_group φ.range
      rw [nat_card_alternatingGroup, Nat.card_fin] at h
      norm_num at h
      exact h
    calc Nat.card X = Nat.card φ.ker * Nat.card φ.range :=
          (Subgroup.card_ker_mul_card_range φ).symm
      _ ≤ Nat.card N * 60 := Nat.mul_le_mul h1 h2
      _ = 60 * Nat.card N := by ring
  rw [hX] at hle
  have hpos : 0 < Nat.card N := Nat.card_pos_iff.mpr ⟨⟨1, N.one_mem⟩, inferInstance⟩
  omega

end CFSG.EvenSporadicStandard.HNRecog.CSide
