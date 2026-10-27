module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise

namespace T3Sect13Aux

theorem exists_conj_le_sylow {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsPGroup 2 E) (P : Sylow 2 X) :
    ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q P
  refine ⟨g, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h1 : MulAut.conj g • y ∈ MulAut.conj g • (Q : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (Q : Subgroup X) (hQ hy)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

theorem exists_conj_commute {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : Odd (Nat.card N)) {y : Y} (hy : IsPGroup 2 ↥(zpowers y)) {B : Subgroup Y}
    (hB : IsPGroup 2 ↥B)
    (hc : ∀ b ∈ B, QuotientGroup.mk' N y * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N y) :
    ∃ n ∈ N, ∀ b ∈ B, y * (n * b * n⁻¹) = (n * b * n⁻¹) * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set V : Subgroup Y := (B.map π).comap π with hV
  have hBV : B ≤ V := fun b hb => Subgroup.mem_map_of_mem π hb
  have hVc : ∀ v ∈ V, π y * π v = π v * π y := by
    intro v hv
    obtain ⟨b, hb, hbv⟩ := hv
    rw [← hbv]
    exact hc b hb
  have hyV : y ∈ normalizer (V : Set Y) := by
    rw [mem_normalizer_iff]
    intro v
    have e : π (y * v * y⁻¹) = π y * π v * (π y)⁻¹ := by simp
    constructor
    · intro hv
      have : π (y * v * y⁻¹) = π v := by rw [e, hVc v hv]; group
      show π (y * v * y⁻¹) ∈ B.map π
      rw [this]; exact hv
    · intro hw
      have h1 := hVc _ hw
      have h2 : π (y * v * y⁻¹) = π v := by
        have e2 : π v = (π y)⁻¹ * π (y * v * y⁻¹) * π y := by rw [e]; group
        calc π (y * v * y⁻¹) = (π y)⁻¹ * (π y * π (y * v * y⁻¹)) := by group
          _ = (π y)⁻¹ * (π (y * v * y⁻¹) * π y) := by rw [h1]
          _ = π v := by rw [e2]; group
      show π v ∈ B.map π
      rw [← h2]; exact hw
  set W : Subgroup Y := normalizer (V : Set Y) with hW
  have hVW : V ≤ W := Subgroup.le_normalizer
  obtain ⟨T, hT, hyT⟩ : ∃ T : Subgroup Y, IsSylowOf 2 T W ∧ y ∈ T := by
    have hp : IsPGroup 2 ↥((zpowers y).subgroupOf W) := hy.comap_subtype
    obtain ⟨P', hP'⟩ := hp.exists_le_sylow
    refine ⟨(P' : Subgroup ↥W).map W.subtype, ⟨P', rfl⟩, ?_⟩
    have : (⟨y, hyV⟩ : ↥W) ∈ (P' : Subgroup ↥W) := hP' (mem_subgroupOf.2 (mem_zpowers y))
    exact ⟨⟨y, hyV⟩, this, rfl⟩
  have hS : IsSylowOf 2 (T ⊓ V) V := hT.inf_of_le_normalizer hVW le_rfl
  obtain ⟨Sv, hSv⟩ := hS.exists_sylow_eq_subgroupOf
  have hB' : IsPGroup 2 ↥(B.subgroupOf V) := hB.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_le_sylow hB' Sv
  have hconj : ∀ b ∈ B, (g : Y) * b * (g : Y)⁻¹ ∈ T ⊓ V := by
    intro b hb
    have h1 : (MulAut.conj g).toMonoidHom ⟨b, hBV hb⟩ ∈ (Sv : Subgroup ↥V) :=
      hg (Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 hb))
    rw [hSv] at h1
    exact mem_subgroupOf.1 h1
  obtain ⟨b₀, hb₀, hb₀g⟩ := g.2
  have hn : (g : Y) * b₀⁻¹ ∈ N := by
    have h1 : π ((g : Y) * b₀⁻¹) = 1 := by rw [map_mul, map_inv, ← hb₀g]; group
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hdisj : Disjoint (T ⊓ V) N := by
    have h2grp : IsPGroup 2 ↥(T ⊓ V) := hT.isPGroup.to_inf_left
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2grp
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hN)
  have hycent : ∀ s ∈ T ⊓ V, y * s = s * y := by
    intro s hs
    have h1 : y * s * y⁻¹ ∈ T ⊓ V :=
      ⟨T.mul_mem (T.mul_mem hyT hs.1) (T.inv_mem hyT), (mem_normalizer_iff.1 hyV s).1 hs.2⟩
    have hc' : y * s * y⁻¹ * s⁻¹ ∈ T ⊓ V := (T ⊓ V).mul_mem h1 ((T ⊓ V).inv_mem hs)
    have hcN : y * s * y⁻¹ * s⁻¹ ∈ N := by
      have := hVc s hs.2
      have h1 : π (y * s * y⁻¹ * s⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        calc π y * π s * (π y)⁻¹ * (π s)⁻¹ = (π s * π y) * (π y)⁻¹ * (π s)⁻¹ := by rw [this]
          _ = 1 := by group
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h1' : y * s * y⁻¹ * s⁻¹ = 1 := by
      have := hdisj.le_bot ⟨hc', hcN⟩
      simpa using this
    calc y * s = (y * s * y⁻¹ * s⁻¹) * (s * y) := by group
      _ = s * y := by rw [h1', one_mul]
  refine ⟨(g : Y) * b₀⁻¹, hn, fun b hb => hycent _ ?_⟩
  have := hconj (b₀⁻¹ * b * b₀) (B.mul_mem (B.mul_mem (B.inv_mem hb₀) hb) hb₀)
  have e : (g : Y) * b₀⁻¹ * b * ((g : Y) * b₀⁻¹)⁻¹ = (g : Y) * (b₀⁻¹ * b * b₀) * (g : Y)⁻¹ := by
    group
  rw [e]
  exact this

end T3Sect13Aux

end CFSG.GH74.Generic.BProg.B2
