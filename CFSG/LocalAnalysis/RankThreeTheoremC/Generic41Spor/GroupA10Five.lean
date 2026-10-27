module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Swap
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Cent
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

@[expose] def A10FiveCycleLines (K : Type) [Group K] [Finite K] : Prop :=
  ∀ S : Sylow 5 K, ∃ c₁ c₂ : K, c₁ ∈ (S : Subgroup K) ∧ c₂ ∈ (S : Subgroup K) ∧ c₁ ≠ 1 ∧
    c₂ ∉ Subgroup.zpowers c₁ ∧
    Nat.card (Subgroup.centralizer ({c₁} : Set K)) = 300 ∧
    Nat.card (Subgroup.centralizer ({c₂} : Set K)) = 300 ∧
    (∃ n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), n * c₁ * n⁻¹ ∈ Subgroup.zpowers c₂) ∧
    (∀ s ∈ (S : Subgroup K), s ∉ Subgroup.zpowers c₁ → s ∉ Subgroup.zpowers c₂ →
      ∀ s' ∈ (S : Subgroup K), s' ∉ Subgroup.zpowers c₁ → s' ∉ Subgroup.zpowers c₂ →
        ∃ n ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), n * s * n⁻¹ ∈ Subgroup.zpowers s')

theorem a10_fiveCycleLines :
    ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10FiveCycleLines K := by
  intro K _ _ hK S
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  have hne1 : ∀ a : K, a ≠ 1 → ψ a ≠ 1 := fun a ha h => ha (ψ.injective (by rw [h, map_one]))
  have hzp : ∀ a b : K, ψ b ∈ Subgroup.zpowers (ψ a) ↔ b ∈ Subgroup.zpowers a := by
    intro a b
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ψ.injective ?_⟩
      rw [map_zpow, hk]
    · intro h
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
      rw [map_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hnorm : ∀ n : A10Perm.A10, n ∈ normalizer (A10Perm.S₀ : Set A10Perm.A10) →
      ψ.symm n ∈ normalizer ((S : Subgroup K) : Set K) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hψ, hψ]
    have := (Subgroup.mem_normalizer_iff.1 hn) (ψ y)
    simpa [map_mul, map_inv] using this
  have hS₀pow : ∀ y ∈ A10Perm.S₀, y ^ 5 = 1 := by
    intro y hy
    obtain ⟨i, j, rfl⟩ := A10Perm.mem_S₀.1 hy
    rw [(Commute.pow_pow A10Perm.a₁₂_commute i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 5,
      mul_comm j 5, pow_mul, pow_mul, A10Perm.a₁_pow, A10Perm.a₂_pow, one_pow, one_pow, mul_one]
  have e1 : A10Perm.line₁ = Subgroup.zpowers A10Perm.a₁ := by
    simpa using (A10Perm.zpowers_a₁_pow (i := 1) (by simpa using A10Perm.a₁_ne)).symm
  have e2 : A10Perm.line₂ = Subgroup.zpowers A10Perm.a₂ := by
    simpa using (A10Perm.zpowers_a₂_pow (j := 1) (by simpa using A10Perm.a₂_ne)).symm
  have hψc₁ : ψ (ψ.symm A10Perm.a₁) = A10Perm.a₁ := ψ.apply_symm_apply _
  have hψc₂ : ψ (ψ.symm A10Perm.a₂) = A10Perm.a₂ := ψ.apply_symm_apply _
  refine ⟨ψ.symm A10Perm.a₁, ψ.symm A10Perm.a₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hψ _).2 (by rw [hψc₁]; exact A10Perm.a₁_mem)
  · exact (hψ _).2 (by rw [hψc₂]; exact A10Perm.a₂_mem)
  · intro h
    apply A10Perm.a₁_ne
    rw [← hψc₁, h, map_one]
  · intro h
    have h' := (hzp _ _).2 h
    rw [hψc₁, hψc₂] at h'
    apply A10Perm.line₁_ne_line₂
    rw [e1, e2]
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h') ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, A10Perm.orderOf_eq_five A10Perm.a₁_pow A10Perm.a₁_ne,
      A10Perm.orderOf_eq_five A10Perm.a₂_pow A10Perm.a₂_ne]
  · rw [a10c_card_centralizer_equiv ψ, hψc₁]
    exact a10c_card_line₁ (by rw [e1]; exact Subgroup.mem_zpowers _) A10Perm.a₁_ne
  · rw [a10c_card_centralizer_equiv ψ, hψc₂]
    exact a10c_card_line₂ (by rw [e2]; exact Subgroup.mem_zpowers _) A10Perm.a₂_ne
  ·
    refine ⟨ψ.symm A10Perm.ν₂, hnorm _ A10Perm.spt_ν₂_mem, ?_⟩
    apply (hzp (ψ.symm A10Perm.a₂) _).1
    rw [map_mul, map_mul, map_inv, hψc₁, hψc₂, ψ.apply_symm_apply, A10Perm.ν₂_a₁, pow_zero,
      one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2
  ·
    intro s hs hs1 hs2 s' hs' hs1' hs2'
    have hψs : ψ s ∈ A10Perm.S₀ := (hψ s).1 hs
    have hψs' : ψ s' ∈ A10Perm.S₀ := (hψ s').1 hs'
    have hn1 : ∀ r : K, r ∉ Subgroup.zpowers (ψ.symm A10Perm.a₁) → ψ r ∉ A10Perm.line₁ := by
      intro r hr h
      apply hr
      apply (hzp (ψ.symm A10Perm.a₁) r).1
      rw [hψc₁, ← e1]
      exact h
    have hn2 : ∀ r : K, r ∉ Subgroup.zpowers (ψ.symm A10Perm.a₂) → ψ r ∉ A10Perm.line₂ := by
      intro r hr h
      apply hr
      apply (hzp (ψ.symm A10Perm.a₂) r).1
      rw [hψc₂, ← e2]
      exact h
    have hs0 : s ≠ 1 := fun h => hs1 (h ▸ Subgroup.one_mem _)
    have hs0' : s' ≠ 1 := fun h => hs1' (h ▸ Subgroup.one_mem _)
    have hLcard : Nat.card (Subgroup.zpowers (ψ s)) = 5 :=
      A10Perm.card_zpowers_of_pow_eq (hS₀pow _ hψs) (hne1 s hs0)
    have hLcard' : Nat.card (Subgroup.zpowers (ψ s')) = 5 :=
      A10Perm.card_zpowers_of_pow_eq (hS₀pow _ hψs') (hne1 s' hs0')
    have hmemL : ψ s ∈ Subgroup.zpowers (ψ s) := Subgroup.mem_zpowers _
    have hmemL' : ψ s' ∈ Subgroup.zpowers (ψ s') := Subgroup.mem_zpowers _
    obtain ⟨n, hnN, hnL⟩ := A10Perm.orbit_diag (Subgroup.zpowers_le.mpr hψs)
      (Subgroup.zpowers_le.mpr hψs') hLcard hLcard'
      (fun h => hn1 s hs1 (h ▸ hmemL)) (fun h => hn2 s hs2 (h ▸ hmemL))
      (fun h => hn1 s' hs1' (h ▸ hmemL')) (fun h => hn2 s' hs2' (h ▸ hmemL'))
    refine ⟨ψ.symm n, hnorm n hnN, ?_⟩
    apply (hzp s' _).1
    rw [map_mul, map_mul, map_inv, ψ.apply_symm_apply]
    rw [← hnL]
    exact ⟨ψ s, hmemL, rfl⟩


theorem a10_scalars : ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → A10Scalars K := by
  intro K _ _ hK S
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨ψ, hψ⟩ := A10Perm.exists_iso_sylow e S
  refine ⟨ψ.symm A10Perm.ν₀, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hψ, hψ]
    have := (Subgroup.mem_normalizer_iff.1 A10Perm.ν₀_mem) (ψ y)
    simpa [map_mul, map_inv] using this
  · intro s hs
    apply ψ.injective
    rw [map_mul, map_mul, map_mul, map_inv, ψ.apply_symm_apply]
    exact A10Perm.ν₀_conj ((hψ s).1 hs)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
