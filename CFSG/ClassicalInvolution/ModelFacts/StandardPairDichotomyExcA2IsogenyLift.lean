module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.RouteD.TypeULift
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open scoped commutatorElement MatrixGroups

section Lift

variable {p e : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]
  {KY X : Type} [Group KY] [Finite KY] [Group X]

theorem exists_uni_of_map_odd (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ e) ^ 2) (hq : 5 ≤ p ^ e)
    (ψ : KY →* X) (hker : ψ.ker ≤ Subgroup.center KY) (hkerodd : Odd (Nat.card ψ.ker))
    {R₁ R₂ : Subgroup KY} (hR₁ : ⁅R₁, R₁⁆ = R₁) (hR₂ : ⁅R₂, R₂⁆ = R₂)
    (h : ∃ W, UnitaryBlockStandardPair K p e W (R₁.map ψ) (R₂.map ψ)) :
    ∃ W, UnitaryBlockStandardPair K p e W R₁ R₂ := by
  obtain ⟨W, hW⟩ := h
  have hq2 : p ^ e ≠ 2 := by omega
  have hWsup := CFSG.ClassicalInvolution.RouteD.typeU_standardPair_eq_sup hK hq2 hW
  obtain ⟨θ, hrange, hθ, hU, hV⟩ := CFSG.ClassicalInvolution.Phan.pair_normalize hW
  have hle : θ.range ≤ ψ.range := by
    rw [hrange, hWsup]
    exact sup_le (Subgroup.map_le_range ψ R₁) (Subgroup.map_le_range ψ R₂)
  let θ' : Su K p e 3 →* ψ.range := θ.codRestrict ψ.range fun s => hle ⟨s, rfl⟩
  have hπ : Function.Surjective ψ.rangeRestrict := ψ.rangeRestrict_surjective
  have hπker : ψ.rangeRestrict.ker ≤ Subgroup.center KY := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hπodd : Odd (Nat.card ψ.rangeRestrict.ker) := by
    rwa [MonoidHom.ker_rangeRestrict]
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := p) (f := e) hK 3
  let ε := CFSG.LieType.Universal.Unitary.conjEquiv P hP
  have : Group.IsPerfect (SU (unitaryInvolution K p e) 3) :=
    CFSG.LieType.Steinberg.isPerfect_SU_three hK hp2
  obtain ⟨β, hβ⟩ := OddCover.exists_lift_of_noCover (Q := Odd)
    (fun _ _ hmn hn => hn.of_dvd_nat hmn) (OddCover.noCover_odd_su3 hp2 hK hq)
    ψ.rangeRestrict hπ hπker hπodd (θ'.comp ε.toMonoidHom)
  let β' : Su K p e 3 →* KY := β.comp ε.symm.toMonoidHom
  have hψβ : ∀ s, ψ (β' s) = θ s := by
    intro s
    have h1 := DFunLike.congr_fun hβ (ε.symm s)
    have := congrArg Subtype.val h1
    simpa [β', θ'] using this
  have hψ : ψ.comp β' = θ := MonoidHom.ext hψβ
  have hperf : ∀ B : Subgroup (Su K p e 3), B ≤ ⁅B, B⁆ → ⁅B.map β', B.map β'⁆ = B.map β' :=
    fun B hB => by
      rw [← Subgroup.map_commutator]
      exact congrArg (Subgroup.map β') (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb =>
        B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha)) (B.inv_mem hb)) hB)
  have hB12 : (B12 K p e).map β' = R₁ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker
      (hperf _ (CFSG.ClassicalInvolution.RouteD.B12_perfect_su hK hq)) hR₁
      (by rw [Subgroup.map_map, hψ, hU])
  have hB23 : (B23 K p e).map β' = R₂ :=
    ModelFacts.eq_of_map_eq_of_isPerfect ψ hker
      (hperf _ (CFSG.ClassicalInvolution.RouteD.B23_perfect_su hK hq)) hR₂
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
