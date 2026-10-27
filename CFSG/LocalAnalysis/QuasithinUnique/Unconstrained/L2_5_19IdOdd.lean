module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem oddLayer_conj_mem (H : Subgroup G) {d g : G} (hd : d ∈ H) (hg : g ∈ oddLayer H) :
    d * g * d⁻¹ ∈ oddLayer H := by
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨(⟨d, hd⟩ : ↥H) * y * (⟨d, hd⟩ : ↥H)⁻¹, ?_, rfl⟩
  have hy' : QuotientGroup.mk' (CFSG.oddCore ↥H) y ∈ CFSG.layer (↥H ⧸ CFSG.oddCore ↥H) := hy
  have hch : (CFSG.layer (↥H ⧸ CFSG.oddCore ↥H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  have hn : (CFSG.layer (↥H ⧸ CFSG.oddCore ↥H)).Normal := inferInstance
  show QuotientGroup.mk' (CFSG.oddCore ↥H) ((⟨d, hd⟩ : ↥H) * y * (⟨d, hd⟩ : ↥H)⁻¹) ∈
    CFSG.layer (↥H ⧸ CFSG.oddCore ↥H)
  rw [map_mul, map_mul, map_inv]
  exact hn.conj_mem _ hy' _

theorem mem_normalizer_iSup_oddLayer {H K : Subgroup G} {c : G} (hcH : c ∈ H)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    c ∈ Subgroup.normalizer ((⨆ g ∈ oddLayer H, CFSG.conjugate K g : Subgroup G) : Set G) := by
  have key : ∀ d ∈ H, d ∈ Subgroup.normalizer (K : Set G) →
      ∀ x ∈ (⨆ g ∈ oddLayer H, CFSG.conjugate K g : Subgroup G),
        d * x * d⁻¹ ∈ (⨆ g ∈ oddLayer H, CFSG.conjugate K g : Subgroup G) := by
    intro d hdH hdK x hx
    have hle : (⨆ g ∈ oddLayer H, CFSG.conjugate K g : Subgroup G) ≤
        (⨆ g ∈ oddLayer H, CFSG.conjugate K g : Subgroup G).comap
          (MulAut.conj d).toMonoidHom := by
      refine iSup₂_le fun g hg => ?_
      intro y hy
      rw [Subgroup.mem_comap]
      have hy' : g * y * g⁻¹ ∈ K := BenderBranch.mem_conjugate_iff.mp hy
      have hdg : d * g * d⁻¹ ∈ oddLayer H := oddLayer_conj_mem H hdH hg
      refine Subgroup.mem_iSup_of_mem (d * g * d⁻¹) (Subgroup.mem_iSup_of_mem hdg ?_)
      rw [BenderBranch.mem_conjugate_iff]
      have h1 : d * (g * y * g⁻¹) * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK _).mp hy'
      have h2 : (d * g * d⁻¹) * ((MulAut.conj d).toMonoidHom y) * (d * g * d⁻¹)⁻¹ =
          d * (g * y * g⁻¹) * d⁻¹ := by
        show (d * g * d⁻¹) * (d * y * d⁻¹) * (d * g * d⁻¹)⁻¹ = d * (g * y * g⁻¹) * d⁻¹
        group
      rw [h2]
      exact h1
    simpa using hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    simpa using key c hcH hcK x hx
  · intro hx
    have := key c⁻¹ (H.inv_mem hcH) ((Subgroup.normalizer (K : Set G)).inv_mem hcK) _ hx
    simpa [mul_assoc] using this

end CFSG.QuasithinUnique.Id2519
