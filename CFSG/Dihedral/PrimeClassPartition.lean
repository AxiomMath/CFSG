module

public import CFSG.Dihedral.PrimeClassTransport
public import CFSG.Dihedral.OriginalSylowControl

public noncomputable section

namespace CFSG.DihedralBlueprint

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sigma_iff (j : Fin 4) (p : ℕ) (R : Subgroup G) :
    p ∈ sigma j R ↔ p ∈ primeSupport R ∧
      ∃ P : Subgroup G, IsSylowIn p P R ∧ primeClassPredicate j p P := Iff.rfl

omit [Finite G] in
theorem exists_isSylowIn (p : ℕ) (R : Subgroup G) :
    ∃ P : Subgroup G, IsSylowIn p P R := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p R))
  exact ⟨(P : Subgroup R).map R.subtype, isSylowIn_map p R P⟩

theorem isSylowIn_exists_conjugating_mem (p : ℕ) (hp : p.Prime)
    (P Q R : Subgroup G) (hP : IsSylowIn p P R) (hQ : IsSylowIn p Q R) :
    ∃ r ∈ R, P.map (MulAut.conj r).toMonoidHom = Q := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨P0, hP0⟩ := (isSylowIn_iff_exists_sylow p P R).mp hP
  obtain ⟨Q0, hQ0⟩ := (isSylowIn_iff_exists_sylow p Q R).mp hQ
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq R P0 Q0
  refine ⟨r, r.2, ?_⟩
  have heq : (P0 : Subgroup R).map (MulAut.conj r).toMonoidHom = (Q0 : Subgroup R) := by
    change MulAut.conj r • (P0 : Subgroup R) = (Q0 : Subgroup R)
    rw [← Sylow.coe_subgroup_smul, hr]
  calc
    P.map (MulAut.conj (r : G)).toMonoidHom =
        ((P0 : Subgroup R).map (MulAut.conj r).toMonoidHom).map R.subtype := by
      rw [← hP0, Subgroup.map_map, Subgroup.map_map]
      congr 1
    _ = Q := by rw [heq, hQ0]

theorem primeClassPredicate_iff_of_isSylowIn (j : Fin 4) (p : ℕ) (hp : p.Prime)
    (P Q R : Subgroup G) (hP : IsSylowIn p P R) (hQ : IsSylowIn p Q R) :
    primeClassPredicate j p P ↔ primeClassPredicate j p Q := by
  obtain ⟨r, _hr, heq⟩ := isSylowIn_exists_conjugating_mem p hp P Q R hP hQ
  have h := primeClassPredicate_map_equiv_iff (MulAut.conj r) j p P
  rw [heq] at h
  exact h.symm

theorem mem_sigma_iff_of_isSylowIn (j : Fin 4) (p : ℕ)
    (P R : Subgroup G) (hP : IsSylowIn p P R) :
    p ∈ sigma j R ↔ p ∈ primeSupport R ∧ primeClassPredicate j p P := by
  rw [mem_sigma_iff]
  constructor
  · rintro ⟨hp, Q, hQ, hpred⟩
    exact ⟨hp, (primeClassPredicate_iff_of_isSylowIn j p hp.1 Q P R hQ hP).mp hpred⟩
  · rintro ⟨hp, hpred⟩
    exact ⟨hp, P, hP, hpred⟩

omit [Finite G] in
theorem primeClassPredicate_exists_unique (p : ℕ) (P : Subgroup G) :
    ∃! j : Fin 4, primeClassPredicate j p P := by
  by_cases hstationary : IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G)))
  · by_cases hcomplement : HasNormalTwoComplement (Subgroup.normalizer (P : Set G))
    · refine ⟨0, ⟨hstationary, hcomplement⟩, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [primeClassPredicate]
    · refine ⟨1, ⟨hstationary, hcomplement⟩, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [primeClassPredicate]
  · by_cases hcyclic : IsCyclic P
    · refine ⟨2, ⟨hcyclic, hstationary⟩, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [primeClassPredicate]
    · refine ⟨3, ⟨hcyclic, hstationary⟩, ?_⟩
      intro j hj
      fin_cases j <;> simp_all [primeClassPredicate]

theorem primeSupport_iff_exists_unique_sigma (p : ℕ) (R : Subgroup G) :
    p ∈ primeSupport R ↔ ∃! j : Fin 4, p ∈ sigma j R := by
  constructor
  · intro hp
    obtain ⟨P, hP⟩ := exists_isSylowIn p R
    obtain ⟨j, hj, hunique⟩ := primeClassPredicate_exists_unique p P
    refine ⟨j, (mem_sigma_iff_of_isSylowIn j p P R hP).mpr ⟨hp, hj⟩, ?_⟩
    intro k hk
    exact hunique k ((mem_sigma_iff_of_isSylowIn k p P R hP).mp hk).2
  · rintro ⟨j, hj, _⟩
    exact ((mem_sigma_iff j p R).mp hj).1

theorem sigma_pairwise_disjoint (R : Subgroup G) :
    Pairwise (fun i j : Fin 4 => Disjoint (sigma i R) (sigma j R)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hp := ((mem_sigma_iff i p R).mp hi).1
  obtain ⟨k, _hk, hunique⟩ := (primeSupport_iff_exists_unique_sigma p R).mp hp
  exact hij ((hunique i hi).trans (hunique j hj).symm)

variable {H : Type} [Group H] [Finite H]

end CFSG.DihedralBlueprint
