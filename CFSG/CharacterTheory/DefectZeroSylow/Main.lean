module

public import CFSG.CharacterTheory.DefectZeroSylow.Integrality
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped Classical

namespace CFSG.DefectZeroSylow

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem character_eq_zero_of_finrank_dvd {G : Type} [Group G] [Fintype G] {p : ℕ}
    [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (hdeg : p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V) {g : G}
    (hg : p ∣ orderOf g) : ρ.character g = 0 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence p hp.out).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) p :=
    (CFSG.BlockBasics.residue_prime_existence p hp.out).2 ideal hmax hmem
  let data : FiniteComplexRepresentation.{0, 0} G := { vector := V, representation := ρ }
  obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr
  have hdim : Module.finrank ℂ (basis.representation label).vector = Module.finrank ℂ V := by
    have h1 := congrFun hlabel 1
    simp only [FiniteComplexRepresentation.character, Representation.char_one, data] at h1
    exact_mod_cast h1
  have hzero := (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal
    p label (hdim ▸ hdeg)).2 g hg
  rw [← hzero]
  exact (congrFun hlabel g).symm

theorem dvd_orderOf_of_mem_sylow {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (Q : Sylow p G)
    {x : G} (hx : x ∈ (Q : Subgroup G)) (hx1 : x ≠ 1) : p ∣ orderOf x := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) hx1
  · rw [hk]
    exact dvd_pow_self p (Nat.succ_ne_zero k)

theorem trace_averageOperator_eq_one {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p G) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (hdim : Module.finrank ℂ V = Nat.card Q) :
    LinearMap.trace ℂ V (averageOperator ρ Q) = 1 := by
  have hsum : ∑ x : (Q : Subgroup G), ρ.character x = ρ.character 1 := by
    refine Finset.sum_eq_single (1 : (Q : Subgroup G)) (fun x _ hx1 => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    refine character_eq_zero_of_finrank_dvd ρ hirr ?_
      (dvd_orderOf_of_mem_sylow Q x.2 (fun h => hx1 (Subtype.ext h)))
    rw [hdim, Sylow.card_eq_multiplicity]
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [trace_averageOperator, hsum, Representation.char_one, hdim]
  exact inv_mul_cancel₀ hQ

theorem exists_sylow_inf_eq_bot_of_degree_eq_card {G : Type} [Group G] [Fintype G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G) {χ : G → ℂ} (hχ : χ ∈ CFSG.BlocksIrr G)
    (hdeg : χ 1 = (Nat.card Q : ℂ)) :
    ∃ Q₁ : Sylow p G, (Q : Subgroup G) ⊓ (Q₁ : Subgroup G) = ⊥ := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  have hdim : Module.finrank ℂ V = Nat.card Q := by
    rw [Representation.char_one] at hdeg
    exact_mod_cast hdeg
  obtain ⟨g, hg⟩ := exists_inf_map_conj_eq_bot (trace_averageOperator_eq_one Q ρ hirr hdim)
    hirr hdim
  exact ⟨g • Q, by rw [Sylow.coe_subgroup_smul]; exact hg⟩

end CFSG.DefectZeroSylow
