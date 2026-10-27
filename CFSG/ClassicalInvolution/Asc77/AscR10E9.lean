module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Generation
public import CFSG.ClassicalInvolution.RouteD.TypeURecognition

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq genSq_top_sl2 eq_of_map_eq_of_genSq
  ne_two_of_pow_eq_three)
open scoped commutatorElement MatrixGroups



section Lift

variable {p e : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]
  {KY X : Type} [Group KY] [Finite KY] [Group X]

theorem genSq_su_two (h3 : p ^ e = 3) (hK : Nat.card K = (p ^ e) ^ 2) :
    GenSq (⊤ : Subgroup (Su K p e 2)) := by
  obtain ⟨φ⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two (K := K) (p := p)
    (f := e) hK
  obtain ⟨rfl, rfl⟩ := CFSG.ClassicalInvolution.Asc77.T3CII.eq_three_of_pow_eq_three h3
  have := (genSq_top_sl2 (F := CFSG.LieType.Steinberg.fixedSubfield K 3 1)).map φ.toMonoidHom
  rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective] at this

theorem genSq_B12 (h3 : p ^ e = 3) (hK : Nat.card K = (p ^ e) ^ 2) : GenSq (B12 K p e) := by
  have h : B12 K p e = (CFSG.ClassicalInvolution.Phan.blockEmb K p e 3 2 0 (by omega)).range := by
    rw [B12, CFSG.ClassicalInvolution.Phan.embSUid_two_eq_blockEmb]
  rw [h, MonoidHom.range_eq_map]
  exact (genSq_su_two h3 hK).map _

theorem genSq_B23 (h3 : p ^ e = 3) (hK : Nat.card K = (p ^ e) ^ 2) : GenSq (B23 K p e) := by
  have h : B23 K p e = (CFSG.ClassicalInvolution.Phan.blockEmb K p e 3 2 1 (by omega)).range := by
    rw [B23, CFSG.ClassicalInvolution.Phan.embSUid_zero_eq_blockEmb]
  rw [h, MonoidHom.range_eq_map]
  exact (genSq_su_two h3 hK).map _

theorem exists_uni_of_map_three (h3 : p ^ e = 3) (hK : Nat.card K = (p ^ e) ^ 2)
    (ψ : KY →* X) (hker : ψ.ker ≤ Subgroup.center KY) (hker2 : ∀ x ∈ ψ.ker, x * x = 1)
    {R₁ R₂ : Subgroup KY} (hR₁ : GenSq R₁) (hR₂ : GenSq R₂)
    (h : ∃ W, UnitaryBlockStandardPair K p e W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, UnitaryBlockStandardPair K p e W R₁ R₂ := by
  have hp2 := ne_two_of_pow_eq_three h3
  obtain ⟨W, hW⟩ := h
  have hq2 : p ^ e ≠ 2 := by rw [h3]; norm_num
  have hWsup := CFSG.ClassicalInvolution.RouteD.typeU_standardPair_eq_sup hK hq2 hW
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : Su K p e 3 →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπ2 : IsPGroup 2 ψ.rangeRestrict.ker := by
    intro g
    refine ⟨1, ?_⟩
    have := hker2 g (by rw [← MonoidHom.ker_rangeRestrict]; exact g.2)
    simpa [pow_two] using Subtype.ext this
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := p) (f := e) hK 3
  let ε := CFSG.LieType.Universal.Unitary.conjEquiv P hP
  obtain ⟨β, hβ⟩ := CFSG.LieType.Steinberg.exists_lift_SU_three hK hp2 hπ hπker hπ2
    (θ'.comp ε.toMonoidHom)
  let β' : Su K p e 3 →* KY := β.comp ε.symm.toMonoidHom
  have hψβ : ∀ s, ψ (β' s) = θ s := by
    intro s
    have h1 := DFunLike.congr_fun hβ (ε.symm s)
    have := congrArg Subtype.val h1
    simpa [β', θ'] using this
  have hψ : ψ.comp β' = θ := MonoidHom.ext hψβ
  have hB12 : (B12 K p e).map β' = R₁ :=
    eq_of_map_eq_of_genSq ψ hker hker2 ((genSq_B12 h3 hK).map β') hR₁
      (by rw [Subgroup.map_map, hψ, hU])
  have hB23 : (B23 K p e).map β' = R₂ :=
    eq_of_map_eq_of_genSq ψ hker hker2 ((genSq_B23 h3 hK).map β') hR₂
      (by rw [Subgroup.map_map, hψ, hV])
  have hid : (MulAut.conj (1 : Su K p e 3)⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp
  refine ⟨β'.range, β', 1, rfl, fun s hs => hθ ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.mem_ker, ← hψβ, MonoidHom.mem_ker.mp hs, map_one]
  · rw [hid, Subgroup.map_id, hB12]
  · rw [hid, Subgroup.map_id, hB23]

end Lift

end CFSG.ClassicalInvolution.ModelFacts
