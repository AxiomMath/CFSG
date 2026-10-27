module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsY

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def l227InnerHom (p : ℕ) (K J : Subgroup G) (hJK : J ≤ K) :
    ↥J →* MulAut (PSimple p K) :=
  ((MulAut.conj : PSimple p K →* MulAut (PSimple p K)).comp (chevQuotHom p K)).comp
    (Subgroup.inclusion hJK)

theorem l227InnerHom_apply (p : ℕ) (K J : Subgroup G) (hJK : J ≤ K) (j : ↥J) :
    l227InnerHom p K J hJK j = MulAut.conj (chevQuotHom p K ⟨(j : G), hJK j.2⟩) := rfl

theorem range_l227InnerHom (p : ℕ) (K J : Subgroup G) (hJK : J ≤ K) :
    (l227InnerHom p K J hJK).range =
      (chevTransfer p K J).map (MulAut.conj : PSimple p K →* MulAut (PSimple p K)) := by
  unfold chevTransfer l227InnerHom
  rw [Subgroup.map_map, ← MonoidHom.map_range, Subgroup.inclusion_range]

theorem l227InnerHom_conj (p : ℕ) {K J : Subgroup G} (hJK : J ≤ K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G))
    (j : ↥J) :
    chevAut p K ⟨g, hg⟩ * l227InnerHom p K J hJK j * (chevAut p K ⟨g, hg⟩)⁻¹ =
      l227InnerHom p K J hJK ⟨g * j * g⁻¹, (Subgroup.mem_normalizer_iff.1 hgJ j).1 j.2⟩ := by
  rw [l227InnerHom_apply, chevToolsY_mulAut_conj_conj, l227InnerHom_apply, chevAut_chevQuotHom]
  rfl

theorem l227_mem_normalizer_range (p : ℕ) {K J : Subgroup G} (hJK : J ≤ K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hgJ : g ∈ Subgroup.normalizer (J : Set G)) :
    chevAut p K ⟨g, hg⟩ ∈
      Subgroup.normalizer ((l227InnerHom p K J hJK).range : Set (MulAut (PSimple p K))) := by
  have fwd : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (K : Set G))
      (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (y : MulAut (PSimple p K)),
      y ∈ (l227InnerHom p K J hJK).range →
      chevAut p K ⟨g, hg⟩ * y * (chevAut p K ⟨g, hg⟩)⁻¹ ∈ (l227InnerHom p K J hJK).range := by
    intro g hg hgJ y hy
    obtain ⟨j, rfl⟩ := hy
    rw [l227InnerHom_conj p hJK hg hgJ j]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fwd g hg hgJ y, fun hy => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  have hgJ' : g⁻¹ ∈ Subgroup.normalizer (J : Set G) := Subgroup.inv_mem _ hgJ
  have h2 := fwd g⁻¹ hg' hgJ' _ hy
  have e : chevAut p K ⟨g⁻¹, hg'⟩ = (chevAut p K ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at h2
  simpa [mul_assoc] using h2

end CFSG.LocalAnalysis.GLTheoremA
