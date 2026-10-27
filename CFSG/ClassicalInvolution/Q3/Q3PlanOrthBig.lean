module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthCartan
public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthBig
public import CFSG.ClassicalInvolution.SmallOrth.Orth3OddCoreAll

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ComponentClassification.CatalogueBOddQuadratic
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {i : V ≃ₗ[F] V}

@[expose] noncomputable def restrictMinusHom (φ : SL(2, ZMod 3) →* (V ≃ₗ[F] V))
    (hφc : ∀ g, φ g * i = i * φ g) : SL(2, ZMod 3) →* (minusSp i ≃ₗ[F] minusSp i) where
  toFun g := restrictMinus (φ g) (hφc g)
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by simp [restrictMinus_apply])
  map_mul' g h := LinearEquiv.ext fun x => Subtype.ext (by simp [restrictMinus_apply])

theorem restrictMinusHom_apply (φ : SL(2, ZMod 3) →* (V ≃ₗ[F] V)) (hφc : ∀ g, φ g * i = i * φ g)
    (g : SL(2, ZMod 3)) (x : minusSp i) :
    ((restrictMinusHom φ hφc g x : minusSp i) : V) = φ g x := rfl

theorem false_of_finrank_minus_ge_eight3 [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hii : i * i = 1) (hdim : 8 ≤ Module.finrank F (minusSp i))
    (φ : SL(2, ZMod 3) →* (V ≃ₗ[F] V)) (hφinj : Function.Injective φ)
    (hφn : ∀ g, φ g ∈ nM Q i) {T : Subgroup (V ≃ₗ[F] V)} (hsub : IsSubnormal φ.range T)
    (hT3 : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * i = i * g → g ^ 3 = 1 → g ∈ T) :
    False := by
  obtain ⟨h3, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  have : NeZero (2 : F) := ⟨h2⟩
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hodd : Odd (Nat.card F) := by rw [hF]; decide
  set W := minusSp i with hW
  have hQ' : (polarBilin (Q.restrict W)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_minusSp h2 hQ hi hii)
  have hQ'' : (Q.restrict W).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ'
  obtain ⟨T₃, hT₃d, hT₃Q⟩ :=
    exists_totallySingular_of_two_mul_add_one_le hodd 3 (Q.restrict W) hQ' (by omega)
  have hT₃ : 3 ≤ Module.finrank F T₃ := hT₃d.ge
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_hypPairs hQ' hT₃ hT₃Q
  set E' := elementaryGroup (Q.restrict W) with hE'
  set O' := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict W) with hO'
  have hOE : ⁅O', O'⁆ = E' :=
    commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ' h₁₂ h₁₃ h₂₃
  have hperfE' : Group.IsPerfect E' := ⟨commutator_elementaryGroup_eq_top' hQ' hT₃ hT₃Q⟩
  have hqE' : CFSG.IsQuasisimple E' := by
    have hsimple := isSimpleGroup_projElementary hQ' hT₃ hT₃Q
    have hZ : (scalars F W).subgroupOf E' ≤ Subgroup.center E' := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (commute_of_mem_scalars hx y).symm
    have hnc : ∃ a b : ProjElementary (Q.restrict W), a * b ≠ b * a := by
      by_contra h
      push Not at h
      have : IsMulCommutative (ProjElementary (Q.restrict W)) := ⟨⟨h⟩⟩
      have : Group.IsPerfect (ProjElementary (Q.restrict W)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.not_isMulCommutative _ ‹_›
    exact CFSG.LieType.CurtisTits.isQuasisimple_of_isSimpleGroup_quotient _ hZ hperfE' hsimple hnc
  set ext := extGrp h2 hii with hext
  have hinj : Function.Injective ext := extGrp_injective h2 hii
  have hφc : ∀ g, φ g * i = i * φ g := fun g => (hφn g).2.1
  let ψ := restrictMinusHom φ hφc
  have hψext : ∀ g, ext (ψ g) = φ g := fun g => by
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    rw [hext, extGrp_apply_add h2 hii _ hu hv, restrictMinusHom_apply, map_add,
      (hφn g).2.2 u hu, add_comm]
  have hψinj : Function.Injective ψ := fun g g' h => hφinj (by rw [← hψext g, ← hψext g', h])
  have hψO : ∀ g, ψ g ∈ O' := fun g =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem (hφn g).1 (x : V)
  have hψE : ∀ g, ψ g ∈ E' := by
    intro g
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2Three_exists_cubes g
    have key : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → ψ x ∈ E' := fun x hx => by
      rw [← hOE]
      exact mem_commutator_orthogonalGroup_of_pow_three hQ'' (hψO x)
        (by rw [← map_pow, hx, map_one])
    rw [map_mul, map_mul]
    exact E'.mul_mem (E'.mul_mem (key a ha) (key b hb)) (key c hc)
  have hBT : E'.map ext ≤ T := by
    rw [Subgroup.map_le_iff_le_comap]
    refine elementaryGroup_le_of_eichler_mem fun u w _ _ => ?_
    rw [Subgroup.mem_comap]
    have hmem := extGrp_mem_nM h2 hii hi (eichler_mem_orthogonalGroup (Q.restrict W) u w)
    exact hT3 _ hmem.1 hmem.2.1 (by rw [← map_pow, Small.eichler_pow_three h3, map_one])
  have hφB : φ.range ≤ E'.map ext := by
    rintro _ ⟨g, rfl⟩
    exact ⟨ψ g, hψE g, hψext g⟩
  have hsubB : IsSubnormal φ.range (E'.map ext) := by
    have := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf hsub hBT
    rwa [inf_eq_left.mpr hφB] at this
  have hsub₀ : IsSubnormal ψ.range E' := by
    have h1 := isSubnormal_comap ext hsubB
    have h2' : (E'.map ext).comap ext = E' := Subgroup.comap_map_eq_self_of_injective hinj E'
    have h3' : φ.range.comap ext = ψ.range := by
      ext x
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, hinj (by rw [hψext, hg])⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g, (hψext g).symm⟩
    rwa [h2', h3'] at h1
  exact not_isQuasisimple_of_member3 (MonoidHom.ofInjective hψinj)
    (fun x ⟨g, hg⟩ => hg ▸ hψE g) hsub₀ (open_isQuasisimple hqE')

end CFSG.ClassicalInvolution.Q3
