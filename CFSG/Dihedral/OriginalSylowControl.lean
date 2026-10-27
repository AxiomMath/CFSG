module

public import CFSG.Dihedral.BlueprintDefs
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements

public noncomputable section

namespace CFSG.DihedralBlueprint

open SignalizerFunctor.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSylowIn_map (p : ℕ) (H : Subgroup G) (P : Sylow p H) :
    IsSylowIn p ((P : Subgroup H).map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map H.subtype, ?_⟩
  intro Q hQ hQp hPQ
  have hPQ' : (P : Subgroup H) ≤ Q.subgroupOf H := by
    intro x hx
    exact hPQ (Subgroup.mem_map_of_mem H.subtype hx)
  have hQp' : IsPGroup p (Q.subgroupOf H) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
  have heq := congrArg (Subgroup.map H.subtype) (P.is_maximal' hQp' hPQ')
  rwa [Subgroup.map_subgroupOf_eq_of_le hQ] at heq

omit [Finite G] in
theorem isSylowIn_iff_exists_sylow (p : ℕ) (P H : Subgroup G) :
    IsSylowIn p P H ↔ ∃ Q : Sylow p H, (Q : Subgroup H).map H.subtype = P := by
  constructor
  · rintro ⟨hPH, hPp, hmax⟩
    have hPp' : IsPGroup p (P.subgroupOf H) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    obtain ⟨Q, hQ⟩ := hPp'.exists_le_sylow
    refine ⟨Q, hmax _ (Subgroup.map_subtype_le _) (Q.isPGroup'.map H.subtype) ?_⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hPH]
    exact Subgroup.map_mono hQ
  · rintro ⟨Q, rfl⟩
    exact isSylowIn_map p H Q

theorem normalized_exists_sylow (q p : ℕ) (hq : q.Prime) (hp : p.Prime)
    (A H : Subgroup G) (hA : IsPGroup q A) (hH : NormalizedBy H A)
    (hcop : Nat.Coprime q (Nat.card H)) :
    ∃ P : Subgroup G, IsSylowIn p P H ∧ NormalizedBy P A := by
  obtain ⟨P, hP⟩ := normalized_subgroup_invariant_sylow q p hq hp A H hA hH hcop
  exact ⟨(P : Subgroup H).map H.subtype, isSylowIn_map p H P, hP⟩

theorem normalized_sylow_containing (q p : ℕ) (hq : q.Prime) (hp : p.Prime)
    (A H P : Subgroup G) (hA : IsPGroup q A) (hH : NormalizedBy H A)
    (hcop : Nat.Coprime q (Nat.card H)) (hPH : P ≤ H)
    (hP : IsPGroup p P) (hPA : NormalizedBy P A) :
    ∃ Q : Subgroup G, IsSylowIn p Q H ∧ P ≤ Q ∧ NormalizedBy Q A := by
  let _action := conjugationAction A H hH
  have hP' : IsPGroup p (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hinv : ∀ a : A, ∀ x ∈ P.subgroupOf H, a • x ∈ P.subgroupOf H :=
    normalized_subgroup_invariant_subgroup A H P hH hPA
  obtain ⟨Q, hPQ, hQ⟩ := invariant_sylow_containing q p hq hp hA hcop
    (P.subgroupOf H) hP' hinv
  refine ⟨(Q : Subgroup H).map H.subtype, isSylowIn_map p H Q, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hPH]
    exact Subgroup.map_mono hPQ
  · apply invariant_subgroup_map_normalized A H hH
    change ∀ a : A, ∀ x ∈ (Q : Subgroup H), a • x ∈ (Q : Subgroup H)
    intro a x hx
    have heq : a • (Q : Subgroup H) = (Q : Subgroup H) := by
      rw [← Sylow.pointwise_smul_def, hQ a]
    rw [← heq]
    exact Subgroup.smul_mem_pointwise_smul x a _ hx

end CFSG.DihedralBlueprint
