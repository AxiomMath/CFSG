module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement

theorem g2_rel_ru_full {R : Type*} [CommRing R] :
    ∃ e₁ e₂ e₃ : R, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ (e₃ = 1 ∨ e₃ = -1) ∧
      ∀ x y : R, ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 1] y⁆ =
        pinnedX .G2 R ![1, 2] (e₁ * (-2 * (x * y))) *
          pinnedX .G2 R ![2, 3] (e₂ * (-3 * (x * y ^ 2))) *
          pinnedX .G2 R ![1, 3] (e₃ * (-3 * (x ^ 2 * y))) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e8, ← e9, ← e10, ← e11]
  have r7 : ((6, 8, 12, [(1, 1, 9, -2), (1, 2, 11, -3), (2, 1, 10, -3)]) : PairRow) ∈
      pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r7 1 (one 6) (one 8)
  refine ⟨σ (1, 1, 9, -2), σ (1, 2, 11, -3), σ (2, 1, 10, -3), hσ _, hσ _, hσ _, fun x y => ?_⟩
  rw [h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, mul_one,
    Int.cast_neg, Int.cast_ofNat, pow_one, mul_assoc]

theorem g2_rel_rv_full {R : Type*} [CommRing R] :
    ∃ e : R, (e = 1 ∨ e = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![0, 1] x, pinnedX .G2 R ![1, 2] y⁆ =
        pinnedX .G2 R ![1, 3] (e * (3 * (x * y))) := by
  have e6 : orbitCertRoot .G2 6 = ![0, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e10 : orbitCertRoot .G2 10 = ![1, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e6, ← e9, ← e10]
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  have one : ∀ k, (1 : WeylGroup .G2) • orbitCertRoot .G2 k = orbitCertRoot .G2 k :=
    fun _ => one_smul _ _
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r9 1 (one 6) (one 9)
  refine ⟨σ (1, 1, 10, 3), hσ _, fun x y => ?_⟩
  rw [h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one, mul_one,
    Int.cast_ofNat, pow_one, mul_assoc]

theorem g2_rel_uv_full {R : Type*} [CommRing R] :
    ∃ e : R, (e = 1 ∨ e = -1) ∧ ∀ x y : R,
      ⁅pinnedX .G2 R ![1, 1] x, pinnedX .G2 R ![1, 2] y⁆ =
        pinnedX .G2 R ![2, 3] (e * (3 * (x * y))) := by
  have e8 : orbitCertRoot .G2 8 = ![1, 1] := List.ofFn_injective (by decide +kernel)
  have e9 : orbitCertRoot .G2 9 = ![1, 2] := List.ofFn_injective (by decide +kernel)
  have e11 : orbitCertRoot .G2 11 = ![2, 3] := List.ofFn_injective (by decide +kernel)
  rw [← e8, ← e9, ← e11]
  set s₁ : WeylGroup .G2 := simple .G2 ⟨0, by decide⟩
  have f6 : s₁ • orbitCertRoot .G2 6 = orbitCertRoot .G2 8 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f9 : s₁ • orbitCertRoot .G2 9 = orbitCertRoot .G2 9 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have f10 : s₁ • orbitCertRoot .G2 10 = orbitCertRoot .G2 11 := by
    rw [simple_smul]; exact List.ofFn_injective (by decide +kernel)
  have r9 : ((6, 9, 12, [(1, 1, 10, 3)]) : PairRow) ∈ pairTable .G2 := by decide +kernel
  obtain ⟨σ, hσ, h⟩ := commutatorElement_pinnedX_signs (R := R) r9 s₁ f6 f9
  refine ⟨σ (1, 1, 10, 3), hσ _, fun x y => ?_⟩
  rw [h x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, f10, mul_one,
    Int.cast_ofNat, pow_one, mul_assoc]

theorem rel_ru_full {K : Type} [Field K] :
    ∃ e₁ e₂ e₃ : K, (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ (e₃ = 1 ∨ e₃ = -1) ∧
      ∀ x y : K, ⁅Xr x, Xu y⁆ =
        Xv (e₁ * (-2 * (x * y))) * Xc (e₂ * (-3 * (x * y ^ 2))) * Xb (e₃ * (-3 * (x ^ 2 * y))) :=
  g2_rel_ru_full

theorem rel_rv_full {K : Type} [Field K] :
    ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K, ⁅Xr x, Xv y⁆ = Xb (e * (3 * (x * y))) :=
  g2_rel_rv_full

theorem rel_uv_full {K : Type} [Field K] :
    ∃ e : K, (e = 1 ∨ e = -1) ∧ ∀ x y : K, ⁅Xu x, Xv y⁆ = Xc (e * (3 * (x * y))) :=
  g2_rel_uv_full

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank
