module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.LU.Lift
public import CFSG.GH74.Generic.S3.Defs
public import CFSG.GH74.Generic.S45.GL42
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_centralizer_singleton (x g : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨c, hc, rfl⟩
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by group⟩
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [hz]
      _ = x * (g⁻¹ * z * g) := by group

theorem isSylowOf_map_conj {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine isSylowOf_of_card (Subgroup.map_mono h.le) ?_
  rw [Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj]
  exact h.card_eq

theorem exists_normalizer_conj {x : G} {T : Subgroup G} (hT : IsSylowOf 2 T (centralizer ({x} : Set G)))
    (g : G) (hTz : ∀ a ∈ T, a * (g * x * g⁻¹) = (g * x * g⁻¹) * a) :
    ∃ n ∈ normalizer (T : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTy : T ≤ centralizer ({g * x * g⁻¹} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hTz t ht)
  have hC := map_conj_centralizer_singleton x g
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hT1 : IsSylowOf 2 (T.map (MulAut.conj g).toMonoidHom)
      (centralizer ({g * x * g⁻¹} : Set G)) := by
    rw [← hC]
    exact isSylowOf_map_conj hT g
  have hT2 : IsSylowOf 2 T (centralizer ({g * x * g⁻¹} : Set G)) := by
    refine isSylowOf_of_card hTy ?_
    rw [hT.card_eq, ← hC, Subgroup.card_map_of_injective hinj]
  obtain ⟨k, hk, hkT⟩ := hT1.exists_mem_conj hT2
  refine ⟨k * g, ?_, ?_⟩
  · rw [mem_set_normalizer_iff'']
    intro z
    have h1 := hkT z
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at h1
    have e : (k * g)⁻¹ * z * (k * g) = g⁻¹ * (k⁻¹ * z * k) * g := by group
    rw [SetLike.mem_coe, SetLike.mem_coe, e]
    exact h1
  · have hky : k * (g * x * g⁻¹) = g * x * g⁻¹ * k := mem_centralizer_singleton_iff.mp hk
    calc k * g * x * (k * g)⁻¹ = k * (g * x * g⁻¹) * k⁻¹ := by group
      _ = g * x * g⁻¹ * k * k⁻¹ := by rw [hky]
      _ = g * x * g⁻¹ := by group

end S3Fusion
end CFSG.GH74.Generic.BProg.B3
