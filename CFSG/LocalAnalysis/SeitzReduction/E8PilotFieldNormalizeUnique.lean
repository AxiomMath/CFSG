module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)

local instance e8PilotFieldNormalizeUniqueNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Unit33

variable {k K : Type} [Field k] [Field K] [Finite K] [CharP K 2]

theorem eq_one_or_eq_entrywise_of_forall_E7 (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {β : MulAut (adjointGroup .E7 K)}
    (hβ : ∀ g, β (adjointBaseChangeE7 ι g) = adjointBaseChangeE7 ι g) :
    β = 1 ∨ β = entrywiseAdjointAut .E7 σ := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hNF, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
  obtain ⟨⟨g, ρ⟩, hgρ, -⟩ := hNF β
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element .E7
  have hρx : ∀ i, Units.map (entrywiseHom ρ.toRingHom) (xUnit .E7 K i 1) = xUnit .E7 K i 1 :=
    fun i => by
      rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_xUnit,
        map_one]
  have hρn : Units.map (entrywiseHom ρ.toRingHom) (canonicalRep (coxeterSystem .E7) K w₀) =
      canonicalRep (coxeterSystem .E7) K w₀ := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_canonicalRep]
  have hιx : ∀ i, (adjointBaseChangeE7 ι ⟨xUnit .E7 k i 1, xUnit_mem_adjointGroup i 1⟩ :
      ModGL .E7 K) = xUnit .E7 K i 1 := fun i => by
    rw [coe_adjointBaseChangeE7, baseChangeGL_xUnit, map_one]
  have hιn : (adjointBaseChangeE7 ι ⟨canonicalRep (coxeterSystem .E7) k w₀,
      canonicalRep_mem_adjointGroup _ k w₀⟩ : ModGL .E7 K) =
        canonicalRep (coxeterSystem .E7) K w₀ := by
    rw [coe_adjointBaseChangeE7, baseChangeGL_canonicalRep]
  have hcomm : ∀ (x : adjointGroup .E7 k),
      Units.map (entrywiseHom ρ.toRingHom) (adjointBaseChangeE7 ι x : ModGL .E7 K) =
        (adjointBaseChangeE7 ι x : ModGL .E7 K) →
      (g : ModGL .E7 K) * (adjointBaseChangeE7 ι x : ModGL .E7 K) =
        (adjointBaseChangeE7 ι x : ModGL .E7 K) * g := by
    intro x hx
    have h1 := congrArg Subtype.val (hβ x)
    rw [hgρ, hx] at h1
    calc (g : ModGL .E7 K) * (adjointBaseChangeE7 ι x : ModGL .E7 K) =
        (g : ModGL .E7 K) * (adjointBaseChangeE7 ι x : ModGL .E7 K) * (g : ModGL .E7 K)⁻¹ *
          g := by group
      _ = _ := by rw [h1]
  have hg1 : g = 1 := by
    refine Subtype.ext (CFSG.SignalizerFunctorTheorem.NonLocalExc.eq_one_of_commute_simple_longest
      g.2 hw₀ (fun i => ?_) ?_)
    · have h := hcomm ⟨xUnit .E7 k i 1, xUnit_mem_adjointGroup i 1⟩ (by rw [hιx, hρx])
      rwa [hιx] at h
    · have h := hcomm ⟨canonicalRep (coxeterSystem .E7) k w₀,
        canonicalRep_mem_adjointGroup _ k w₀⟩ (by rw [hιn, hρn])
      rwa [hιn] at h
  have hβρ : ∀ h, (β h : ModGL .E7 K) = Units.map (entrywiseHom ρ.toRingHom) h := fun h => by
    rw [hgρ, hg1]
    simp
  have hρfix : ∀ c : fixSubfield σ, ρ c = c := by
    intro c
    obtain ⟨a, ha⟩ := (hfix c).1 c.2
    have h1 := congrArg Subtype.val (hβ ⟨pinnedX .E7 k (Pi.single 0 1) a,
      pinnedX_mem_adjointGroup _ a⟩)
    rw [hβρ, coe_adjointBaseChangeE7, baseChangeGL_pinnedX,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_pinnedX] at h1
    have h2 := pinnedX_injective (τ := .E7) (R := K) _ h1
    rw [ha] at h2
    exact h2
  rcases F4Pilot.eq_one_or_eq_of_forall_fixSubfield hσ hρfix with rfl | rfl
  · left
    exact MulEquiv.ext fun h => Subtype.ext (by
      rw [hβρ, CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]
      exact baseChangeGL_id K _)
  · right
    exact MulEquiv.ext fun h => Subtype.ext (by rw [hβρ, coe_entrywiseAdjointAut])

theorem eq_one_or_eq_e7LeviBaseChange_of_forall [Finite k] [CharP k 2] (ι : k →+* K)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι)
    {θ : MulAut (e7Levi K)} (hθ : ∀ g, θ (e7LeviBaseChange ι g) = e7LeviBaseChange ι g) :
    θ = 1 ∨ ∀ x, θ x = e7LeviBaseChange (σ : K →+* K) x := by
  set Λ := e7LeviEquiv K with hΛ
  set β := MulAut.congr Λ θ with hβdef
  have hβapp : ∀ y, β y = Λ (θ (Λ.symm y)) := fun _ => rfl
  have hβ : ∀ g, β (adjointBaseChangeE7 ι g) = adjointBaseChangeE7 ι g := by
    intro g
    obtain ⟨g', rfl⟩ := (e7LeviEquiv k).surjective g
    rw [← e7LeviEquiv_baseChange, hβapp, MulEquiv.symm_apply_apply, hθ]
  rcases eq_one_or_eq_entrywise_of_forall_E7 ι hσ hfix hβ with h1 | h1
  · left
    refine MulEquiv.ext fun x => ?_
    have h2 := DFunLike.congr_fun h1 (Λ x)
    rw [hβapp, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    exact Λ.injective h2
  · right
    intro x
    have h2 := DFunLike.congr_fun h1 (Λ x)
    rw [hβapp, MulEquiv.symm_apply_apply] at h2
    apply Λ.injective
    rw [h2, hΛ, e7LeviEquiv_baseChange]
    exact Subtype.ext (by rw [coe_entrywiseAdjointAut, coe_adjointBaseChangeE7,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]; rfl)

end Unit33

end CFSG.SeitzReduction.E8Pilot
