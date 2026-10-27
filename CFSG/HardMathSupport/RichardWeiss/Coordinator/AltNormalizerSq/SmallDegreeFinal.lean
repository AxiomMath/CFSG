module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegree
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeSix
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.SmallDegreeDegrees
public import CFSG.HardMathSupport.RichardWeiss.Coordinator.AltNormalizerSq.PerfectCyclic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_blockCentralizer_eq_index_comap {M L U : Subgroup G} (hUM : U ≤ M) :
    (U ⊓ blockCentralizer M L).relIndex U =
      ((Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM))).index := by
  have hsub : (U ⊓ blockCentralizer M L).subgroupOf U =
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).comap
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM)) := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have key := mem_blockCentralizer_iff (M := M) (L := L) ⟨(u : G), hUM u.2⟩
    constructor
    · rintro ⟨-, hB⟩
      exact key.mp hB
    · intro h
      exact ⟨u.2, key.mpr h⟩
  exact congrArg Subgroup.index hsub

omit [Finite G] in
theorem le_normalizer_normalizer_inf {S L U : Subgroup G}
    (hUS : U ≤ Subgroup.normalizer (S : Set G)) (hUL : U ≤ Subgroup.normalizer (L : Set G)) :
    U ≤ Subgroup.normalizer ((Subgroup.normalizer (S : Set G) ⊓ L : Subgroup G) : Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (hUL hu) x
  have h2 : x ∈ Subgroup.normalizer (S : Set G) ↔
      u * x * u⁻¹ ∈ Subgroup.normalizer (S : Set G) := by
    constructor
    · intro hx
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hUS hu) hx) (Subgroup.inv_mem _ (hUS hu))
    · intro hx
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUS hu)) hx) (hUS hu)
      simpa [mul_assoc] using this
  simp only [Subgroup.mem_inf]
  exact and_congr h2 h1

theorem altNormalizerSq_deg6_three
    {M S L U : Subgroup G} (hL : IsWeakSBlock M S L)
    (hdeg6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hJ3 : Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin 3)))
    (hUK : U ≤ M ⊓ Subgroup.normalizer (S : Set G)) (hUL : U ≤ Subgroup.normalizer (L : Set G))
    (hUp : IsPGroup 3 U) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ 3 := by
  obtain ⟨eL⟩ := hdeg6
  obtain ⟨eJ⟩ := hJ3
  have hUM : U ≤ M := fun u hu => (hUK hu).1
  have hUS : U ≤ Subgroup.normalizer (S : Set G) := fun u hu => (hUK hu).2
  rw [relIndex_blockCentralizer_eq_index_comap hUM]
  have hmem : ∀ u : ↥U, ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hUM)) u ∈
      barM M U := fun u => ⟨⟨(u : G), hUM u.2⟩, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
  exact index_centralizer_le_three_of_alt6 (Γ := ↥M ⧸ CFSG.pCore 2 ↥M)
    hL.component.2.2.1 eL (barM_mono inf_le_right) eJ hUp _
    (fun u => barM_le_normalizer_barM hUL (hmem u))
    (fun u => barM_le_normalizer_barM (le_normalizer_normalizer_inf hUS hUL) (hmem u))

theorem altNormalizerSq_small_or_degree
    {M S L : Subgroup G} {p : ℕ} (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h678 : NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hJ : PerfectCyclicSylow p (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    {U : Subgroup G} (hUK : U ≤ M ⊓ Subgroup.normalizer (S : Set G))
    (hUL : U ≤ Subgroup.normalizer (L : Set G)) (hUp : IsPGroup p U) :
    (U ⊓ blockCentralizer M L).relIndex U ≤ p ∨
      ∃ m : ℕ, 10 ≤ m ∧
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)) := by
  have hUM : U ≤ M := fun u hu => (hUK hu).1
  have hp35 : p = 3 ∨ 5 ≤ p := by
    by_contra h
    push Not at h
    have : p < 5 := by omega
    interval_cases p <;> simp_all (config := { decide := true })
  rcases degree_cases hL h678 with hbig | ⟨hdeg6, hJ3⟩ | ⟨⟨e8⟩, f, hf⟩
  · exact Or.inr hbig
  · refine Or.inl ?_
    rcases hp35 with rfl | hp5
    · exact altNormalizerSq_deg6_three hL hdeg6 hJ3 hUK hUL hUp
    · exact altNormalizerSq_deg6_of_five_le hp hp5 hA hL hdeg6 hUK hUL hUp
  · refine Or.inl ?_
    rcases hp35 with rfl | hp5
    · exfalso
      have := lt_two_mul_of_perfect_cyclic (X := ↥M ⧸ CFSG.pCore 2 ↥M) Nat.prime_three
        (by decide) hJ f hf
      omega
    · exact relIndex_le_of_alt_fin (k := 8) hp (by omega) (by omega) (by omega) hUM hUL hUp e8

end CFSG.HardMathSupport.RichardWeiss.Coordinator
