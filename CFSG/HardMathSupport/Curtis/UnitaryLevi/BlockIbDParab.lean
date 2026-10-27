module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open scoped Pointwise

variable {Y : Type*} [Group Y] [Finite Y]

theorem mem_of_mem_normalizer_of_isParabolicTwo_d {L J : Subgroup Y} (hP : IsParabolicTwo L J)
    {n : Y} (hn : n ∈ L) (hnJ : n ∈ Subgroup.normalizer (J : Set Y)) : n ∈ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJL, T, ⟨hTL, hT2, hTidx⟩, hNJ⟩ := hP
  have hTJ : T ≤ J := fun t ht => hNJ ⟨hTL ht, Subgroup.le_normalizer ht⟩
  have hidx : ¬ 2 ∣ (T.subgroupOf J).index := by
    intro hd
    apply hTidx
    have h := Subgroup.relIndex_mul_relIndex T J L hTJ hJL
    exact hd.trans ⟨J.relIndex L, h.symm⟩
  have hT2J : IsPGroup 2 (T.subgroupOf J) := hT2.comap_subtype (K := J)
  let S1 : Sylow 2 J := hT2J.toSylow hidx
  set a : MulAut J := J.normalizerMonoidHom ⟨n, hnJ⟩ with ha
  let S2 : Sylow 2 J := S1.mapSurjective (f := a.toMonoidHom) a.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J S1 S2
  have hS2 : (S2 : Subgroup J) = (T.subgroupOf J).map a.toMonoidHom :=
    Sylow.coe_mapSurjective (f := a.toMonoidHom) a.surjective S1
  have hgS : (g • S1 : Sylow 2 J) = S2 := hg
  have hcoe : ((g • S1 : Sylow 2 J) : Subgroup J) = ConjAct.toConjAct g • (T.subgroupOf J) :=
    Sylow.coe_subgroup_smul
  rw [hgS, hS2] at hcoe
  have key : ∀ t ∈ T, (g : Y)⁻¹ * (n * t * n⁻¹) * g ∈ T := by
    intro t ht
    have h1 : a.toMonoidHom ⟨t, hTJ ht⟩ ∈ (T.subgroupOf J).map a.toMonoidHom :=
      ⟨⟨t, hTJ ht⟩, ht, rfl⟩
    rw [hcoe] at h1
    rw [Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hse⟩ := h1
    have hse' : ConjAct.toConjAct g • s = a.toMonoidHom ⟨t, hTJ ht⟩ := hse
    have e1 : (g : Y) * (s : Y) * (g : Y)⁻¹ = n * t * n⁻¹ := by
      have := congrArg Subtype.val hse'
      simpa [ha, ConjAct.smul_def, mul_assoc] using this
    have hsT : (s : Y) ∈ T := hs
    have : (g : Y)⁻¹ * (n * t * n⁻¹) * g = s := by
      rw [← e1]; group
    rw [this]
    exact hsT
  have hnorm : (g : Y)⁻¹ * n ∈ Subgroup.normalizer (T : Set Y) := by
    apply Subgroup.mem_normalizer_fintype
    intro t ht
    have := key t ht
    have e : (g : Y)⁻¹ * n * t * ((g : Y)⁻¹ * n)⁻¹ = (g : Y)⁻¹ * (n * t * n⁻¹) * g := by group
    rw [e]
    exact this
  have hmem : (g : Y)⁻¹ * n ∈ J := hNJ ⟨L.mul_mem (L.inv_mem (hJL g.2)) hn, hnorm⟩
  have : n = (g : Y) * ((g : Y)⁻¹ * n) := by group
  rw [this]
  exact J.mul_mem g.2 hmem

end CFSG.HardMathSupport.Curtis.UnitaryLevi
