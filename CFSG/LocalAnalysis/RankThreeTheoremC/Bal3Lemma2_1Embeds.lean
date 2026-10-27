module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_inv_mul_mul_comm_of_zpowers_eq {z d x c : G}
    (hx : zpowers d = (zpowers z).map (MulAut.conj x).toMonoidHom) (hc : c * d = d * c) :
    x⁻¹ * c * x * z = z * (x⁻¹ * c * x) := by
  have hmem : x * z * x⁻¹ ∈ zpowers d := by
    rw [hx]
    exact ⟨z, mem_zpowers z, by simp⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hck : c * (x * z * x⁻¹) = x * z * x⁻¹ * c := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute c d from hc) k).eq
  calc x⁻¹ * c * x * z = x⁻¹ * (c * (x * z * x⁻¹)) * x := by group
    _ = x⁻¹ * (x * z * x⁻¹ * c) * x := by rw [hck]
    _ = z * (x⁻¹ * c * x) := by group

theorem CentralizerEmbeds.of_extremal (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) (hCM : centralizer (D : Set G) ≤ M) {z : G} (hzD : z ∈ D)
    (hz1 : z ≠ 1) (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) (hzM : z ∈ M) :
    CentralizerEmbeds (D.subgroupOf M) ⟨z, hzM⟩ := by
  intro d hdD hdz
  have hdD' : (d : G) ∈ D := hdD
  have hd1 : (d : G) ≠ 1 := by
    intro h
    apply hdz
    have hd : d = 1 := Subtype.ext h
    rw [hd]
    exact one_mem _
  obtain ⟨x, -, hx⟩ := hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCM hzD hz1 hzc
    hN₀M hdD' hd1
  have hcz : ∀ c : centralizer ({d} : Set M),
      x⁻¹ * ((c : M) : G) * x * z = z * (x⁻¹ * ((c : M) : G) * x) := fun c =>
    conj_inv_mul_mul_comm_of_zpowers_eq hx
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.2))
  have hM : ∀ c : centralizer ({d} : Set M), x⁻¹ * ((c : M) : G) * x ∈ M := fun c =>
    hN₀M (centralizer_singleton_le_normalizer_zpowers z
      (mem_centralizer_singleton_iff.mpr (hcz c)))
  have hC : ∀ c : centralizer ({d} : Set M),
      (⟨x⁻¹ * ((c : M) : G) * x, hM c⟩ : M) ∈ centralizer ({⟨z, hzM⟩} : Set M) := fun c =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (hcz c))
  refine ⟨MonoidHom.mk' (fun c => ⟨⟨x⁻¹ * ((c : M) : G) * x, hM c⟩, hC c⟩) ?_, ?_⟩
  · intro a b
    refine Subtype.ext (Subtype.ext ?_)
    change x⁻¹ * (((a : M) : G) * ((b : M) : G)) * x =
      x⁻¹ * ((a : M) : G) * x * (x⁻¹ * ((b : M) : G) * x)
    group
  · intro a b hab
    have h : x⁻¹ * ((a : M) : G) * x = x⁻¹ * ((b : M) : G) * x :=
      congrArg (fun y : centralizer ({⟨z, hzM⟩} : Set M) => ((y : M) : G)) hab
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h)))

end CFSG.LocalAnalysis.RankThreeTheoremC
