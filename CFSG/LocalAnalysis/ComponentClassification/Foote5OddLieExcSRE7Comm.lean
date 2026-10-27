module

public import CFSG.RankThree.SteinbergR3EOddE7RationalStructure

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Group

variable {A : Type*} [Group A]

theorem commutator_mem_of_index_dvd_two {N M : Subgroup A} [hN : N.Normal] [hM : M.Normal]
    (h : (N.subgroupOf M).index ∣ 2) (z : A) {m : A} (hm : m ∈ M) :
    z * m * z⁻¹ * m⁻¹ ∈ N := by
  have hzm : z * m * z⁻¹ ∈ M := hM.conj_mem m hm z
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
    exact mul_mem (h1 hzm) (inv_mem (h1 hm))
  · have key := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨z * m * z⁻¹, hzm⟩)
      (b := ⟨m⁻¹, inv_mem hm⟩)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
    refine key.2 ⟨fun hc => inv_mem ?_, fun hc => hN.conj_mem m (inv_mem_iff.1 hc) z⟩
    have h3 := hN.conj_mem _ hc z⁻¹
    rwa [show z⁻¹ * (z * m * z⁻¹) * z⁻¹⁻¹ = m by group] at h3

theorem commutator_mem_of_quotient_cyclic {H : Type*} [Group H] [IsCyclic H]
    {N M : Subgroup A} [hN : N.Normal] [M.Normal] (hNM : N ≤ M)
    (h : (N.subgroupOf M).index ∣ 2) (π : A →* H) (hπ : π.ker = M) (a b : A) :
    a * b * a⁻¹ * b⁻¹ ∈ N := by
  have hNk : N ≤ π.ker := hπ ▸ hNM
  set f : A ⧸ N →* H := QuotientGroup.lift N π hNk with hf
  have hker : f.ker ≤ center (A ⧸ N) := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have hxM : x ∈ M := by
      rw [← hπ, MonoidHom.mem_ker]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 := commutator_mem_of_index_dvd_two h y⁻¹ hxM
    have h2 := hN.conj_mem _ h1 x⁻¹
    convert h2 using 1
    group
  have hc : (a : A ⧸ N) * b = b * a :=
    (f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm _ _
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hc]
  group

end Group

theorem commutator_mem_range_conj_E7
    {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (a b : MulAut (adjointGroup .E7 K)) :
    a * b * a⁻¹ * b⁻¹ ∈
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, n, hℓ, hcard⟩ := FiniteField.card' K
  have hK : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    rw [hK] at hodd
    exact Nat.not_even_iff_odd.2 hodd ((Nat.even_pow' n.ne_zero).2 even_two)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow hcard
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : ExpChar L ℓ := ExpChar.prime hℓ
  have hFr : ∀ c : L, iterateFrobenius L ℓ n c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  obtain ⟨-, -, -, -, ρ, -, -, hinner, hnorm, hidx, -, -, ⟨π, -, hker, -⟩, -⟩ :=
    RankThree.OddE7Rational.odd_E7_rational_inner_diagonal_field_automorphism_structure hℓ hℓ2
      n.pos K hK L (iterateFrobenius L ℓ n) hFr _ _ rfl rfl
  have : IsCyclic (K ≃+* K) :=
    (LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK).2
  have : ρ.range.Normal := hnorm
  have hNM : inner (adjointGroup .E7 K) ≤ ρ.range := hinner ▸ Subgroup.map_le_range ρ _
  exact commutator_mem_of_quotient_cyclic hNM hidx π hker a b

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRE7
