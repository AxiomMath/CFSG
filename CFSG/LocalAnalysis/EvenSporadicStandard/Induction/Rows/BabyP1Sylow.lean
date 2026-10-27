module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverProved
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.B.GSide
  CFSG.Monster.B.TwoA.Amalgam CFSG.Open CFSG.EvenSporadicStandard.Solomon78


theorem vStabEam_mem_commutator_of_mem_center_sylow (T : Sylow 2 (vStab cv0)) {z : vStab cv0}
    (hz : z ∈ ((Subgroup.center (T : Subgroup (vStab cv0))).map
      (T : Subgroup (vStab cv0)).subtype : Set (vStab cv0))) :
    vStabEam z ∈ commutator Eam := by
  have hcomm : ∀ y ∈ commutator (vStab cv0), vStabEam y ∈ commutator Eam := fun y hy => by
    rw [← CFSG.EvenSmallLie.TwoE6.map_commutator_vStabEam]
    exact Subgroup.mem_map_of_mem _ hy
  obtain ⟨r, hr, hset⟩ := (native_H_sylow_two_center T).2
  have hrc : r ∈ commutator (vStab cv0) := by
    obtain ⟨g, hg⟩ := isConj_iff.1 ((mem_RA_iff_isConj r).1 hr)
    rw [← hg]
    exact (inferInstance : (commutator (vStab cv0)).Normal).conj_mem _
      CFSG.EvenSmallLie.TwoE6.lamW0H_mem_commutator g
  have hcE : vStabEam cV0 ∈ commutator Eam := by
    rw [vStabEam_cV0]
    exact CFSG.Monster.B.TwoA.Amalgam.cE'_mem_commutator
  rw [hset] at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · rw [map_one]
    exact Subgroup.one_mem _
  · exact hcE
  · exact hcomm _ hrc
  · rw [map_mul]
    exact Subgroup.mul_mem _ hcE (hcomm _ hrc)

theorem babySylow_proved : BabySylow := by
  intro G _ _ L K u hL hP S hSC hSp hSmax z hzS hzc
  obtain ⟨Ψ, hΨ⟩ := babyCover_pairEquiv hL hP
  let Φ : ↥(L ⊓ centralizer ({u} : Set G)) ≃* vStab cv0 := Ψ.trans vStabEam.symm
  let S₀ : Subgroup ↥(L ⊓ centralizer ({u} : Set G)) :=
    S.subgroupOf (L ⊓ centralizer ({u} : Set G))
  have hS₀p : IsPGroup 2 S₀ := hSp.comap_subtype
  have hT'p : IsPGroup 2 (S₀.map Φ.toMonoidHom) := hS₀p.map _
  have hT'max : ∀ {Q : Subgroup (vStab cv0)}, IsPGroup 2 Q → S₀.map Φ.toMonoidHom ≤ Q →
      Q = S₀.map Φ.toMonoidHom := by
    intro Q hQp hle
    have hQ₀p : IsPGroup 2 (Q.comap Φ.toMonoidHom) := hQp.comap_of_injective _ Φ.injective
    have hS₀Q₀ : S₀ ≤ Q.comap Φ.toMonoidHom := fun x hx => hle ⟨x, hx, rfl⟩
    have hQ₁ := hSmax ((Q.comap Φ.toMonoidHom).map (L ⊓ centralizer ({u} : Set G)).subtype)
      (by rintro _ ⟨x, -, rfl⟩; exact x.2) (hQ₀p.map _)
      (fun s hs => ⟨⟨s, hSC hs⟩, hS₀Q₀ hs, rfl⟩)
    have hQ₀ : Q.comap Φ.toMonoidHom = S₀ := by
      refine le_antisymm (fun x hx => ?_) hS₀Q₀
      have : (x : G) ∈ (Q.comap Φ.toMonoidHom).map
          (L ⊓ centralizer ({u} : Set G)).subtype := ⟨x, hx, rfl⟩
      rw [hQ₁] at this
      exact this
    rw [← hQ₀, Subgroup.map_comap_eq_self_of_surjective Φ.surjective]
  obtain ⟨T, hTdef⟩ : ∃ T : Sylow 2 (vStab cv0),
      (T : Subgroup (vStab cv0)) = S₀.map Φ.toMonoidHom :=
    ⟨{ toSubgroup := S₀.map Φ.toMonoidHom
       isPGroup' := hT'p
       is_maximal' := hT'max }, rfl⟩
  have hzC : z ∈ L ⊓ centralizer ({u} : Set G) := hSC hzS
  let z₀ : ↥(L ⊓ centralizer ({u} : Set G)) := ⟨z, hzC⟩
  have hz₀ : z₀ ∈ S₀ := Subgroup.mem_subgroupOf.2 hzS
  have hy : Φ z₀ ∈ (T : Subgroup (vStab cv0)) := by
    rw [hTdef]
    exact Subgroup.mem_map_of_mem _ hz₀
  have hcen : Φ z₀ ∈ (Subgroup.center (T : Subgroup (vStab cv0))).map
      (T : Subgroup (vStab cv0)).subtype := by
    refine CFSG.Monster.mem_map_center_iff.2 ⟨hy, fun e he => ?_⟩
    have he' : e ∈ S₀.map Φ.toMonoidHom := by rwa [hTdef] at he
    obtain ⟨s₀, hs₀, hts⟩ := Subgroup.mem_map.1 he'
    have hcomm : s₀ * z₀ = z₀ * s₀ := Subtype.ext (hzc _ (Subgroup.mem_subgroupOf.1 hs₀)).symm
    rw [← hts]
    have := congrArg Φ.toMonoidHom hcomm
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using this
  have hmem := vStabEam_mem_commutator_of_mem_center_sylow T (SetLike.mem_coe.2 hcen)
  have hΨz : Ψ z₀ ∈ commutator Eam := by
    have : vStabEam (Φ z₀) = Ψ z₀ := by
      show vStabEam (vStabEam.symm (Ψ z₀)) = Ψ z₀
      exact vStabEam.apply_symm_apply _
    rw [← this]
    exact hmem
  exact (hΨ z₀).2 hΨz

end CFSG.EvenSporadicStandard.Induction.Hyp
