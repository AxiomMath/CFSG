module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped Pointwise

section SelfNorm

variable {Y : Type} [Group Y] [Finite Y]

theorem subgroupOf_index_eq_of_card_eq {L T K : Subgroup Y} (hKL : K ≤ L) (hTL : T ≤ L)
    (hc : Nat.card K = Nat.card T) : (K.subgroupOf L).index = (T.subgroupOf L).index := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf L)
  have h2 := Subgroup.card_mul_index (T.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv] at h2
  rw [hc] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

omit [Finite Y] in
theorem not_two_dvd_index_of_le {L J T : Subgroup Y} (hT : IsSylowTwoOf T L) (hTJ : T ≤ J)
    (hJL : J ≤ L) : ¬ 2 ∣ (T.subgroupOf J).index := by
  intro h2
  apply hT.2.2
  have h := Subgroup.relIndex_mul_relIndex T J L hTJ hJL
  have hd : (T.subgroupOf J).index ∣ (T.subgroupOf L).index :=
    ⟨J.relIndex L, h.symm⟩
  exact h2.trans hd

theorem mem_of_mem_normalizer_of_isParabolicTwo {L J : Subgroup Y} (hP : IsParabolicTwo L J)
    {g : Y} (hgL : g ∈ L) (hgJ : g ∈ Subgroup.normalizer (J : Set Y)) : g ∈ J := by
  obtain ⟨hJL, T, hT, hTN⟩ := hP
  have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : Y →* Y := (MulAut.conj g).toMonoidHom with hσ
  set T' : Subgroup Y := T.map σ with hT'
  have hT'J : T' ≤ J := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hgJ x).1 (hTJ hx)
  have hcard : Nat.card T' = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hT'2 : IsPGroup 2 T' := hT.2.1.map σ
  have hidx1 : ¬ 2 ∣ (T.subgroupOf J).index := not_two_dvd_index_of_le hT hTJ hJL
  have hidx2 : ¬ 2 ∣ (T'.subgroupOf J).index := by
    rw [subgroupOf_index_eq_of_card_eq hT'J hTJ hcard]; exact hidx1
  let P₁ : Sylow 2 ↥J := IsPGroup.toSylow (P := T.subgroupOf J) hT.2.1.comap_subtype hidx1
  let P₂ : Sylow 2 ↥J := IsPGroup.toSylow (P := T'.subgroupOf J) hT'2.comap_subtype hidx2
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥J P₂ P₁
  have hfwd : ∀ y ∈ T, (h : Y) * g * y * ((h : Y) * g)⁻¹ ∈ T := by
    intro y hy
    have hy' : g * y * g⁻¹ ∈ T' := ⟨y, hy, rfl⟩
    have hmem : (⟨g * y * g⁻¹, hT'J hy'⟩ : ↥J) ∈ P₂ := hy'
    have hP12 : MulAut.conj h • (P₂ : Subgroup ↥J) = (P₁ : Subgroup ↥J) := by
      have := congrArg (fun P : Sylow 2 ↥J => (P : Subgroup ↥J)) hh
      simpa [Sylow.coe_subgroup_smul] using this
    have h1 := Subgroup.smul_mem_pointwise_smul (⟨g * y * g⁻¹, hT'J hy'⟩ : ↥J)
      (MulAut.conj h) (P₂ : Subgroup ↥J) hmem
    rw [hP12] at h1
    have h2 : (h : Y) * (g * y * g⁻¹) * (h : Y)⁻¹ ∈ T := h1
    have h3 : (h : Y) * g * y * ((h : Y) * g)⁻¹ = (h : Y) * (g * y * g⁻¹) * (h : Y)⁻¹ := by group
    rw [h3]
    exact h2
  set ρ : Y →* Y := (MulAut.conj ((h : Y) * g)).toMonoidHom with hρ
  have hle : T.map ρ ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfwd y hy
  have heq : T.map ρ = T :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj ((h : Y) * g)).injective])
  have hnorm : (h : Y) * g ∈ Subgroup.normalizer (T : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfwd y hy, fun hy => ?_⟩
    have hy' : ρ y ∈ T.map ρ := by
      rw [heq]; exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    have : z = y := (MulAut.conj ((h : Y) * g)).injective hzy
    rw [← this]; exact hz
  have hhg : (h : Y) * g ∈ J :=
    hTN ⟨L.mul_mem (hJL h.2) hgL, hnorm⟩
  have : g = (h : Y)⁻¹ * ((h : Y) * g) := by group
  rw [this]
  exact J.mul_mem (J.inv_mem h.2) hhg

end SelfNorm

end CFSG.HardMathSupport.Curtis.UnitaryLevi
