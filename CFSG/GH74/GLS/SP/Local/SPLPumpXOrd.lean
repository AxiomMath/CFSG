module

public import CFSG.GH74.GLS.SP.Local.SPLK3B

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise

section Ord

variable {G : Type} [Group G] [Finite G] {D : SPLNot1 G}

theorem sp_card_S (hs : SPLSetup D.toSPLNot0) : Nat.card ↥(D.S : Subgroup G) = 2 ^ (2 * D.n) := by
  have h1 : Nat.card ↥(D.S : Subgroup G) = 2 * Nat.card ↥D.S₁ := hs.syl.index
  rw [h1, K3B_card_S₁ hs, ← pow_succ']
  congr 1

theorem sp_card_two_subgroup_le (hs : SPLSetup D.toSPLNot0) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPt : P ≤ D.Ct) : Nat.card ↥P ≤ 2 ^ (2 * D.n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSc := sp_card_S hs
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  have hQS : Nat.card ↥(Q : Subgroup G) = Nat.card ↥(D.S : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hm2 : 2 * D.n ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : m ≤ 2 * D.n - 1 := by omega
    have h2 : 2 ^ m ≤ 2 ^ (2 * D.n - 1) := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hPQeq : P = (Q : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge hPQ ?_
    rw [hQS, hSc, hm]
    exact Nat.pow_le_pow_right (by norm_num) hm2
  have hQC : (Q : Subgroup G) ≤ D.Ct := hPQeq ▸ hPt
  have htc : ∀ q ∈ (Q : Subgroup G), q * D.t = D.t * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (hQC hq)
  have ht2 : orderOf D.t = 2 := hs.syl.t_ord
  have htP : IsPGroup 2 (zpowers D.t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht2]; norm_num
  have htCen : D.t ∈ centralizer ((Q : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun q hq => htc q hq
  have htN : D.t ∈ normalizer (Q : Set G) :=
    Subgroup.centralizer_le_normalizer _ htCen
  have htQ : D.t ∈ (Q : Subgroup G) := by
    have h := htP.inf_normalizer_sylow Q
    have : D.t ∈ zpowers D.t ⊓ normalizer (Q : Set G) := ⟨mem_zpowers _, htN⟩
    rw [h] at this
    exact this.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q D.S
  have hSQ : (D.S : Subgroup G) = MulAut.conj g • (Q : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  have hu : g * D.t * g⁻¹ ∈ (D.S : Subgroup G) := by
    rw [hSQ]
    have := Subgroup.smul_mem_pointwise_smul D.t (MulAut.conj g) (Q : Subgroup G) htQ
    simpa [MulAut.conj_apply] using this
  have hucen : ∀ s ∈ (D.S : Subgroup G), s * (g * D.t * g⁻¹) = (g * D.t * g⁻¹) * s := by
    intro s hsS
    rw [hSQ, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsS
    have hq : g⁻¹ * s * g ∈ (Q : Subgroup G) := by simpa [MulAut.conj_apply] using hsS
    have := htc _ hq
    calc s * (g * D.t * g⁻¹) = g * ((g⁻¹ * s * g) * D.t) * g⁻¹ := by group
      _ = g * (D.t * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = (g * D.t * g⁻¹) * s := by group
  have hcz : g * D.t * g⁻¹ ∈ zpowers D.z := by
    rw [← hs.syl.z_cen]
    refine ⟨⟨g * D.t * g⁻¹, hu⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hucen s s.2)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  have hz2 : orderOf D.z = 2 := hs.syl.z_inv
  have hmod : D.z ^ (k % 2) = D.z ^ k := by
    have := zpow_mod_orderOf D.z k
    rw [hz2] at this
    simpa using this
  have ht1 : g * D.t * g⁻¹ ≠ 1 := by
    intro h
    have : D.t = 1 := by
      calc D.t = g⁻¹ * (g * D.t * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h]
        _ = 1 := by group
    rw [this, orderOf_one] at ht2
    omega
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0] at hmod
    simp at hmod
    exact ht1 (hk.symm.trans hmod.symm)
  · rw [h1] at hmod
    simp at hmod
    have hzg : g * D.t * g⁻¹ = D.z := hk.symm.trans hmod.symm
    exact hs.syl.t_nconj (isConj_iff.mpr ⟨g⁻¹, by rw [← hzg]; group⟩)

end Ord

end CFSG.GH74.GLS.SP.Local
