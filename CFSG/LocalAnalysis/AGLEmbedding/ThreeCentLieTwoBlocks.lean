module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeLin
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.Assembly.Defs

public section

namespace CFSG.AGLEmbedding

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem exists_ne_one_mem_of_iSupIndep {G ι : Type*} [Group G] [Finite ι] {H : ι → Subgroup G}
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) {y : G} (hy : y ∈ ⨆ i, H i) {p : ℕ} (hyp : y ^ p = 1) (hy1 : y ≠ 1) :
    ∃ i, ∃ g ∈ H i, g ^ p = 1 ∧ g ≠ 1 := by
  have := Fintype.ofFinite ι
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hy
  obtain ⟨w, rfl⟩ := hy
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hwp : w ^ p = 1 := hinj (by rw [map_pow, hyp, map_one])
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 1 := by
    by_contra h
    push Not at h
    exact hy1 (by rw [show w = 1 from funext h, map_one])
  refine ⟨i, w i, (w i).2, ?_, fun h => hi (Subtype.ext h)⟩
  have h1 := congrFun hwp i
  rw [Pi.pow_apply, Pi.one_apply] at h1
  exact congrArg Subtype.val h1

theorem perfect_map_of_isQuasisimple {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {P : Subgroup G} (hP : CFSG.IsQuasisimple P) :
    ⁅P.map f, P.map f⁆ = P.map f ∧ P.map f ≠ ⊥ := by
  refine ⟨by rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hP.1], fun h => ?_⟩
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hP
  rw [(Subgroup.map_eq_bot_iff_of_injective P hf).mp h] at hnt
  exact not_nontrivial _ hnt

theorem not_dvd_card_sesqUnitaryGroup_small {f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 f E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : (f = 1 ∧ 1 ≤ finrank E W ∧ finrank E W ≤ 3) ∨ (f = 3 ∧ finrank E W = 1))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (sesqUnitaryGroup Hf) := by
  have hm1 : 1 ≤ finrank E W := by rcases hsmall with ⟨-, h, -⟩ | ⟨-, h⟩ <;> omega
  have hcard := (CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl hm1).1
  rcases hsmall with ⟨rfl, -, hm3⟩ | ⟨rfl, hm⟩
  · interval_cases hm : finrank E W
    · have h3 : Nat.card (sesqUnitaryGroup Hf) = 2 ^ 0 * 3 ^ 1 := by
        have h1 : (Nat.card (sesqUnitaryGroup Hf) : ℤ) = ((2 ^ 0 * 3 ^ 1 : ℕ) : ℤ) := by
          rw [hcard]; decide
        exact_mod_cast h1
      rw [h3]
      exact not_dvd_two_pow_mul_three_pow hp hp5 0 1
    · have h3 : Nat.card (sesqUnitaryGroup Hf) = 2 ^ 1 * 3 ^ 2 := by
        have h1 : (Nat.card (sesqUnitaryGroup Hf) : ℤ) = ((2 ^ 1 * 3 ^ 2 : ℕ) : ℤ) := by
          rw [hcard]; decide
        exact_mod_cast h1
      rw [h3]
      exact not_dvd_two_pow_mul_three_pow hp hp5 1 2
    · have h3 : Nat.card (sesqUnitaryGroup Hf) = 2 ^ 3 * 3 ^ 4 := by
        have h1 : (Nat.card (sesqUnitaryGroup Hf) : ℤ) = ((2 ^ 3 * 3 ^ 4 : ℕ) : ℤ) := by
          rw [hcard]; decide
        exact_mod_cast h1
      rw [h3]
      exact not_dvd_two_pow_mul_three_pow hp hp5 3 4
  · have h3 : Nat.card (sesqUnitaryGroup Hf) = 2 ^ 0 * 3 ^ 2 := by
      rw [hm] at hcard
      have h1 : (Nat.card (sesqUnitaryGroup Hf) : ℤ) = ((2 ^ 0 * 3 ^ 2 : ℕ) : ℤ) := by
        rw [hcard]; decide
      exact_mod_cast h1
    rw [h3]
    exact not_dvd_two_pow_mul_three_pow hp hp5 0 2

theorem isQuasisimple_sesqSU_of_prime_order {f : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData 2 f E) (hf : f = 1 ∨ f = 3) {W : Type*} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) {g : sesqUnitaryGroup Hf} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hg : g ^ p = 1) (hg1 : g ≠ 1) : CFSG.IsQuasisimple (sesqSpecialUnitaryGroup Hf) := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hg hg1
  have hdvd : p ∣ Nat.card (sesqUnitaryGroup Hf) := hord ▸ orderOf_dvd_natCard g
  have hm0 : finrank E W ≠ 0 := by
    intro h0
    have : Subsingleton W := Module.finrank_zero_iff.mp h0
    apply hg1
    refine Subtype.ext (Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _))
  have hbig : (f = 1 ∧ 4 ≤ finrank E W) ∨ (f = 3 ∧ 2 ≤ finrank E W) := by
    by_contra hcon
    refine not_dvd_card_sesqUnitaryGroup_small hE hHf hHfl ?_ hp hp5 hdvd
    rcases hf with rfl | rfl
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  refine CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
    hHfl (by omega) ⟨fun h2 => ?_, fun h3 => ?_⟩
  · rcases hbig with ⟨-, h⟩ | ⟨rfl, -⟩
    · omega
    · norm_num
  · rcases hbig with ⟨-, h⟩ | ⟨rfl, -⟩
    · omega
    · norm_num

theorem exists_perfect_of_prime_order_alt {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {B : LinearMap.BilinForm K W} (hB : B.IsAlt) (hn : B.Nondegenerate)
    {g : sesqUnitaryGroup B} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ^ p = 1)
    (hg1 : g ≠ 1) : ∃ Q : Subgroup (sesqUnitaryGroup B), ⁅Q, Q⁆ = Q ∧ Q ≠ ⊥ := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB hn
  have hnt : Nontrivial (sesqUnitaryGroup B) := ⟨⟨g, 1, hg1⟩⟩
  rcases (show s ≤ 1 ∨ s = 2 ∨ 3 ≤ s by omega) with hs1 | rfl | hs3
  · exfalso
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (e g) = p := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hg hg1
    have hdvd : p ∣ Nat.card (StatedSp s K) := hord ▸ orderOf_dvd_natCard (e g)
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK] at hdvd
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs1 with rfl | rfl
    · exact not_dvd_two_pow_mul_three_pow hp hp5 0 0 (by simpa using hdvd)
    · exact not_dvd_two_pow_mul_three_pow hp hp5 1 1 (by simpa using hdvd)
  · obtain ⟨e4⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK hB hn (by omega)
    have hQ := (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour e4).1
    refine ⟨commutator (sesqUnitaryGroup B), Subgroup.isPerfect_iff.mp hQ.1, fun h => ?_⟩
    have hnt' := CFSG.LocalCores.isQuasisimple_nontrivial hQ
    rw [h] at hnt'
    exact not_nontrivial _ hnt'
  · have hperf : Group.IsPerfect (StatedSp s K) :=
      CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp s K (Or.inr (Or.inr ⟨hK, hs3⟩))
    have : Group.IsPerfect (sesqUnitaryGroup B) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact ⟨⊤, Group.IsPerfect.commutator_eq_top, top_ne_bot⟩

end CFSG.AGLEmbedding
