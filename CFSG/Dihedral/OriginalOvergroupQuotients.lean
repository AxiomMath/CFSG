module

public import CFSG.Dihedral.OriginalNormalizerCore

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

theorem not_alternatingQuotient_of_normalIndexTwo (H : Subgroup G)
    (hindex : HasNormalIndexTwo H) : ¬ HasAlternatingQuotient H := by
  obtain ⟨K, hKH, hKnormal, hKindex⟩ := hindex
  let L := K.subgroupOf H
  let _ : L.Normal := hKnormal
  have hcard : Nat.card (H ⧸ L) = 2 := by
    simpa only [Subgroup.index_eq_card] using hKindex
  have htwo : IsPGroup 2 (H ⧸ L) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hcoreK : oddCoreOf H ≤ K := by
    have h := odd_le_normal_of_two_quotient (oddCoreOf H) H (oddCoreOf_le H)
      L (oddCoreOf_odd H) htwo
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at h
  have hcoreL : Assembly.oddCore H ≤ L := by
    intro x hx
    exact hcoreK (Subgroup.mem_map_of_mem H.subtype hx)
  let f := QuotientGroup.mk' L
  let phi := QuotientGroup.lift (Assembly.oddCore H) f
    (by simpa only [f, QuotientGroup.ker_mk'] using hcoreL)
  have hphi : Function.Surjective phi :=
    QuotientGroup.lift_surjective_of_surjective _ f (QuotientGroup.mk'_surjective L) _
  rintro ⟨e⟩
  let _ : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  let psi := phi.comp e.symm.toMonoidHom
  have hpsi : Function.Surjective psi := hphi.comp e.symm.surjective
  let _ : Group.IsPerfect (H ⧸ L) := Group.IsPerfect.ofSurjective hpsi
  let _ : IsCyclic (H ⧸ L) := isCyclic_of_prime_card hcard
  let _ : IsMulCommutative (H ⧸ L) := inferInstance
  have hone : Nat.card (H ⧸ L) = 1 := Nat.card_unique
  omega

namespace OriginalData

variable [IsSimpleGroup G] (d : OriginalData G)

theorem not_sylowTwoQuotient_of_strict_overgroup (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hCH : d.C < H) : ¬ HasSylowTwoQuotient H := by
  rintro ⟨T, ⟨e⟩⟩
  have htwo : IsPGroup 2 (H ⧸ Assembly.oddCore H) := T.isPGroup'.of_equiv e.symm
  exact hCH.ne' (d.eq_centralizer_of_two_quotient hc H hCH.le htwo)

theorem strict_overgroup_quotients (hc : d.CanonicalNormalizers)
    (H : Subgroup G) (hH : H ≠ ⊤) (hCH : d.C < H) :
    HasCoordinates H ∧ ¬ HasAlternatingQuotient H ∧ ¬ HasSylowTwoQuotient H := by
  have hA := not_alternatingQuotient_of_normalIndexTwo H (d.index_two H hH hCH.le)
  have hT := d.not_sylowTwoQuotient_of_strict_overgroup hc H hCH
  refine ⟨?_, hA, hT⟩
  rcases d.proper_quotients H hH with hcoord | halt | htwo
  · exact hcoord
  · exact (hA halt).elim
  · exact (hT htwo).elim

theorem normalizer_eq_centralizer_or_coordinates (hc : d.CanonicalNormalizers)
    (hR : d.R ≠ ⊥) : d.N = d.C ∨ HasCoordinates d.N := by
  by_cases hNC : d.N = d.C
  · exact Or.inl hNC
  · exact Or.inr (d.strict_overgroup_quotients hc d.N (d.normalizer_ne_top hR)
      (lt_of_le_of_ne d.centralizer_le_normalizer (Ne.symm hNC))).1

end OriginalData
end CFSG.DihedralBlueprint
