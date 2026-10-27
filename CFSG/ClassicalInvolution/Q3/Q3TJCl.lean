module

public import CFSG.ClassicalInvolution.Q3.Q3TJExc
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification

variable {X : Type} [Group X]

theorem exists_eq_conj_of_card_outer_dvd {G : Type*} [Group G] {k : ℕ}
    (h : Nat.card (OuterAutomorphisms.Outer G) ∣ 2 ^ k) (α : MulAut G)
    (hodd : Odd (orderOf α)) : ∃ g : G, α = MulAut.conj g := by
  set a : OuterAutomorphisms.Outer G := (α : MulAut G ⧸ OuterAutomorphisms.inner G) with ha
  have h1 : orderOf a ∣ 2 ^ k := (orderOf_dvd_natCard a).trans h
  have h2 : orderOf a ∣ orderOf α := orderOf_dvd_of_pow_eq_one (by
    rw [ha, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hodd' : Odd (orderOf a) := hodd.of_dvd_nat h2
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).mp hj
  exact ⟨g, hg.symm⟩

theorem nonempty_mulEquiv_of_ker_eq_center {K C : Type*} [Group K] [Group C] (f : K →* X)
    (hf : Function.Surjective f) (hfk : f.ker ≤ Subgroup.center K)
    (hZX : Subgroup.center X = ⊥) (π : K →* C) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center K) : Nonempty (X ≃* C) := by
  have hk : f.ker = π.ker := by
    rw [hπk]
    exact le_antisymm hfk (ModelFacts.ChevAut.center_le_ker_of_surjective hf hZX)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ))⟩

theorem exists_eq_conj_PSL {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n 3 1)
    (hZ : Subgroup.center X = ⊥) (f : (Generic.modelUniv .PSL n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .PSL n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  have hn : 3 ≤ n := by
    have h2 : 2 ≤ n := hadm.2.2.1
    have h23 : (n, 3 ^ 1) ≠ (2, 3) := hadm.2.2.2.2
    by_contra h
    exact h23 (by rw [show n = 2 by omega]; norm_num)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let S := Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 3 1)
  let f' : S →* X := f
  have hker' : f'.ker ≤ Subgroup.center S := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' (Subgroup.center S)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  have hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL (m + 1) 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance,
      by rw [natCard_galoisField_three, pow_one],
      ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m + 1)
        (GaloisField 3 1))⟩⟩
  have hout := (linear_model_outer_two_part_bound X (m + 1) 3 1 hT).2.2.2.2 hn
  refine exists_eq_conj_of_card_outer_dvd (k := 2) (hout.trans ?_) α hodd
  have hg : Nat.gcd (m + 1) (3 ^ 1 - 1) ∣ 2 := by
    simpa using Nat.gcd_dvd_right (m + 1) 2
  calc 2 * 1 * Nat.gcd (m + 1) (3 ^ 1 - 1) ∣ 2 * 1 * 2 := Nat.mul_dvd_mul_left _ hg
    _ = 2 ^ 2 := by norm_num

theorem exists_eq_conj_PSp {n : ℕ} (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp n 3 1)
    (hZ : Subgroup.center X = ⊥) (f : (Generic.modelUniv .PSp n 3 1 Nat.prime_three).K →* X)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .PSp n 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  let f' : ↥(CFSG.Assembly.LowTwoRank.StatedSp n (GaloisField 3 1)) →* X := f
  have hker' : f'.ker ≤ Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSp n (GaloisField 3 1)) :=
    hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ker_eq_center f' hf hker' hZ
    (QuotientGroup.mk' ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin n ⊕ Fin n)
      (GaloisField 3 1)).subgroupOf (CFSG.Assembly.LowTwoRank.StatedSp n (GaloisField 3 1))))
    (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (LieType.Universal.Symplectic.center_eq n _).symm)
  have hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp n 3 1 :=
    ⟨hadm, GaloisField 3 1, inferInstance, inferInstance,
      by rw [natCard_galoisField_three, pow_one], ⟨e⟩⟩
  have hout := (symplectic_model_outer_two_part_bound X n 3 1 hT).2.1
  exact exists_eq_conj_of_card_outer_dvd (k := 2) (hout.trans (by norm_num)) α hodd

theorem mem_inner_of_odd_adjoint_G2 (K : Type) [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = 3) (α : MulAut (adjointGroup .G2 K)) (hodd : Odd (orderOf α)) :
    α ∈ OuterAutomorphisms.inner (adjointGroup .G2 K) := by
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := (inferInstance : CharP K 3)
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    G2_three_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK, pow_one])
  have h1 : orderOf (Θ α) ∣ 2 := by
    have h := orderOf_dvd_natCard (Θ α)
    simpa [Nat.card_eq_fintype_card] using h
  have hodd' : Odd (orderOf (Θ α)) := hodd.of_dvd_nat (orderOf_map_dvd Θ α)
  have h3 : orderOf (Θ α) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  rw [orderOf_eq_one_iff] at h3
  have hmem : α ∈ Θ.ker := h3
  rw [hker] at hmem
  exact hmem

theorem exists_eq_conj_G2 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .G2 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .G2 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (MonoidHom.id ↥(adjointGroup Tag.G2 (GaloisField 3 1))) Function.surjective_id
    (ker_id_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_adjoint_G2 _ natCard_galoisField_three β hβ) α hodd

end CFSG.ClassicalInvolution.Q3.Q3T
