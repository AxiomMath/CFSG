module

public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedMaps
import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.ClassicalGroups.Orthogonal.FramedPlanes

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace mem_omegaGroup omegaGroup)

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

private theorem commSpace_eq_map_of_isCompl {A B : Submodule F V} (hc : IsCompl A B)
    {g : V ≃ₗ[F] V} (hgA : ∀ a ∈ A, g a ∈ A) (hB : ∀ b ∈ B, g b = b)
    {h : A ≃ₗ[F] A} (hh : ∀ a : A, ((h a : A) : V) = g a) :
    commSpace g = (commSpace h).map A.subtype := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := suppExists_add_of_isCompl hc z
    change g (a + b) - (a + b) ∈ (commSpace h).map A.subtype
    have hz : g (a + b) - (a + b) = g a - a := by
      rw [map_add, hB b hb]
      abel
    rw [hz]
    refine Submodule.mem_map.mpr ⟨⟨g a - a, A.sub_mem (hgA a ha) ha⟩, ?_, rfl⟩
    refine mem_commSpace.mpr ⟨⟨a, ha⟩, ?_⟩
    refine Subtype.ext ?_
    rw [Submodule.coe_sub, hh]
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, rfl⟩ := mem_commSpace.mp hy
    refine mem_commSpace.mpr ⟨(a : V), ?_⟩
    change g (a : V) - (a : V) = ((h a - a : A) : V)
    rw [Submodule.coe_sub, hh]

private theorem mem_orthogonalGroup_comp_of_apply {A : Submodule F V}
    {g : V ≃ₗ[F] V} (hO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {h : A ≃ₗ[F] A} (hh : ∀ a : A, ((h a : A) : V) = g a) :
    h ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro a
  change Q ((h a : A) : V) = Q ((a : A) : V)
  rw [hh a]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hO (a : V)

private theorem maps_mem_of_mem_orthogonalGroup_of_fixes_suppPerp [FiniteDimensional F V]
    {A : Submodule F V} (hQ : (polarBilin Q).Nondegenerate) {g : V ≃ₗ[F] V}
    (hO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ v ∈ suppPerp Q A, g v = v) : ∀ a ∈ A, g a ∈ A := by
  intro a ha
  have hmem : g a ∈ suppPerp Q (suppPerp Q A) := by
    rw [mem_suppPerp]
    intro v hv
    rw [← hfix v hv,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO v a, polar_comm]
    exact mem_suppPerp.mp hv a ha
  rwa [show suppPerp Q (suppPerp Q A) = A from
    LinearMap.BilinForm.orthogonal_orthogonal hQ
      (QuadraticMap.isSymm_polarBilin Q).isRefl A] at hmem

private theorem exists_totallySingular_comap_of_le {A : Submodule F V}
    (hT : ∃ T : Submodule F V, T ≤ A ∧ finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ T' : Submodule F A, finrank F T' = 3 ∧
      ∀ x ∈ T', (Q.comp A.subtype) x = 0 := by
  obtain ⟨T, hTA, hT3, hTs⟩ := hT
  refine ⟨T.comap A.subtype, ?_, ?_⟩
  · rw [(Submodule.comapSubtypeEquivOfLe hTA).finrank_eq]
    exact hT3
  · intro x hx
    exact hTs x.val hx

theorem mem_supportedDerived_iff_mem_orthDerived [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hQ : (polarBilin Q).Nondegenerate) {A : Submodule F V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hT : ∃ T : Submodule F V, T ≤ A ∧ finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {g : V ≃ₗ[F] V} :
    g ∈ supportedDerived Q A ↔ g ∈ orthDerived Q ∧ ∀ v ∈ suppPerp Q A, g v = v := by
  have hcompl : IsCompl A (suppPerp Q A) :=
    isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)
  constructor
  · intro hg
    exact ⟨supportedDerived_le_orthDerived_of_regular hA hg, (mem_supportedDerived.mp hg).1⟩
  · rintro ⟨hg, hfix⟩
    have hOmega := orthDerived_le_omegaGroup hQ hg
    have hO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hOmega.1
    have hgEven : Even (finrank F (commSpace g)) := (mem_omegaGroup.mp hOmega).2
    have hgA : ∀ a ∈ A, g a ∈ A :=
      maps_mem_of_mem_orthogonalGroup_of_fixes_suppPerp hQ hO hfix
    have hmaple : A.map (g : V →ₗ[F] V) ≤ A := by
      rintro - ⟨a, ha, rfl⟩
      exact hgA a ha
    have hmap : A.map (g : V →ₗ[F] V) = A :=
      Submodule.eq_of_le_of_finrank_eq hmaple (LinearEquiv.finrank_map_eq g A)
    let φ : A ≃ₗ[F] A := LinearEquiv.ofSubmodules g A A hmap
    have hφact : ∀ a : A, ((φ a : A) : V) = g a := fun a =>
      LinearEquiv.ofSubmodules_apply g hmap a
    have hcomm : commSpace g = (commSpace φ).map A.subtype :=
      commSpace_eq_map_of_isCompl hcompl hgA hfix hφact
    have hfin : finrank F (commSpace g) = finrank F (commSpace φ) := by
      rw [hcomm, Submodule.finrank_map_subtype_eq]
    have hφEven : Even (finrank F (commSpace φ)) := by
      rw [← hfin]
      exact hgEven
    have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp A.subtype) :=
      mem_orthogonalGroup_comp_of_apply hO hφact
    have hφOmega : φ ∈ omegaGroup (Q.comp A.subtype) hA :=
      mem_omegaGroup.mpr ⟨hφO, hφEven⟩
    have hTA' := exists_totallySingular_comap_of_le hT
    refine mem_supportedDerived.mpr ⟨hfix, φ,
      omegaGroup_le_orthDerived hA hTA' hφOmega, hφact⟩

end CFSG.ClassicalGroups.Orthogonal.FramedPlanes
