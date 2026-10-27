module

public import CFSG.LocalAnalysis.OddStandard.ONanSylowTransfer
public import CFSG.LocalAnalysis.OddStandard.ONanSylowQuot

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup CFSG.CosetTable F2 F2.AlpE Model CFSG.GH74.GLS.Bg.TwoGroups.L23

namespace AlpEmb

variable {G : Type*} [Group G] {v1 v2 v3 s t : G} (E : AlpEmb G v1 v2 v3 s t)

include E

theorem φ_stE : E.φ stE = s * t := by
  rw [stE, map_mul, E.φ_s, E.φ_t]

theorem zpowers_x_eq : zpowers (xel v1 v2 v3) = (subE genNE).map E.φ := by
  rw [Subgroup.zpowers_eq_closure, ← E.φ_xE]
  change _ = (closure {g | g ∈ genNE}).map E.φ
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp [genNE]

theorem inf_centralizer_x_eq (hF : f2Check = true) :
    alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G) =
      (subE (genMaxE 1)).map E.φ := by
  rw [(centralizer_special_alpP E hF).2.2, E.closure_genMax]

theorem exists_hom_P0 (hF : f2Check = true) (hQ : f2QuotCheck = true) :
    ∃ ψ : ↥(alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G)) →* TcM,
      Function.Surjective ψ ∧
        ∀ g : ↥(alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G)),
          ψ g = 1 ↔ (g : G) ∈ zpowers (xel v1 v2 v3) := by
  let θ : ↥(subE (genMaxE 1)) ≃*
      ↥(alpP v1 v2 v3 s t ⊓ centralizer ({xel v1 v2 v3} : Set G)) :=
    (Subgroup.equivMapOfInjective _ E.φ E.inj).trans
      (MulEquiv.subgroupCongr (inf_centralizer_x_eq E hF).symm)
  refine ⟨(psi hQ).comp θ.symm.toMonoidHom, (psi_surjective hQ).comp θ.symm.surjective, fun g => ?_⟩
  have hker := ker_psi hQ
  have hg : (psi hQ) (θ.symm g) = 1 ↔ θ.symm g ∈ (subE genNE).subgroupOf (subE (genMaxE 1)) := by
    rw [← hker]
    exact MonoidHom.mem_ker.symm
  show (psi hQ) (θ.symm g) = 1 ↔ _
  rw [hg, Subgroup.mem_subgroupOf, zpowers_x_eq E]
  obtain ⟨a, ha⟩ := θ.surjective g
  rw [← ha]
  simp only [MulEquiv.symm_apply_apply]
  constructor
  · intro hmem
    exact Subgroup.mem_map.2 ⟨a.1, hmem, rfl⟩
  · intro hmem
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 hmem
    have : b = a.1 := E.inj hbe
    rw [← this]
    exact hb

end AlpEmb

end CFSG.OddStandard.ONanRec
