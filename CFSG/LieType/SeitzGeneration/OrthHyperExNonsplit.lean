module

public import CFSG.LieType.SeitzGeneration.OrthNonsplitLow
public import CFSG.LieType.SeitzGeneration.OrthHyperExSplit

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank TauCeti OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Cover

variable {d : ValidLieTypeIndex} {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_hyperGen_nonsplit_of_cover {π : elementaryGroup Q →* Cat d}
    (hc : IsOrthogonalCover Q π) (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : orthDerived Q = elementaryGroup Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : (p : K) ≠ 0) (hpKd : ¬ p ∣ Nat.card K) (hpq1 : ¬ p ∣ Nat.card K - 1)
    (hpq2 : ¬ p ∣ Nat.card K + 1) {E₀ : Subgroup (Cat d)} (hE₀ : IsElemAbelian p E₀)
    (hc₀ : Nat.card E₀ = p ^ 3) :
    ∃ E : Subgroup (Cat d), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      HyperGen p (⊤ : Subgroup (Cat d)) E := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have : Nontrivial V := nontrivial_of_three_singular hT
  have hfinV : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, -, -, hAcomm, hAexp, hAcard⟩ := exists_lift_elemAbelian π hc.surjective
    (not_dvd_card_ker_of_scalar hc hp hp2) hcomm hE₀.2
  have hF : ElemAbOrth Q p (A.map (elementaryGroup Q).subtype) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact elementaryGroup_le_orthogonalGroup Q x.2
    · rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hAexp x hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hAcomm x hx y hy)
  have hpq : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    obtain ⟨t, ht⟩ : ∃ t, Nat.card K = t + 1 :=
      ⟨Nat.card K - 1, by have := Finite.card_pos (α := K); omega⟩
    rw [ht, Nat.add_sub_cancel] at hpq1
    rw [ht] at hpq2 ⊢
    have h1 : (t + 1) ^ 2 - 1 = t * (t + 1 + 1) := by
      have : (t + 1) ^ 2 = t * (t + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [h1]
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hpq1 h
    · exact hpq2 h
  refine exists_hyperGen_nonsplit hc hT hE hp hp2 hpK hpKd hpq hF (le_of_eq ?_)
  rw [Subgroup.card_map_of_injective (elementaryGroup Q).subtype_injective, hAcard, hc₀]

end Cover

section Residual

theorem orthHyperExNonsplit : OrthHyperExNonsplit := by
  rintro ⟨d, hv⟩ p hp hp2 hpd - ⟨E₀, hE₀, hc₀, hO, r₀, q₀, hd₀, hq1, hq2⟩
  have hfp : Fact p.Prime := ⟨hp⟩
  rcases hO with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq₀ : q₀ = q := by
      rcases hd₀ with h | h | h <;> cases h
      rfl
    rw [hq₀] at hq1 hq2
    have hq' : p ≠ q.p := by simpa using hpd
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.B r q, hv⟩ (q := q) (by simp)
    have hcard' : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent := by
      rw [hcard, PrimePower.card_def]
    have h2 : (2 : ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard'
      have : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p := ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have hpKd : ¬ p ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) := by
      rw [hcard']
      exact not_dvd_pow_of_ne hp q.prime_p hq'
    have hpK := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpKd
    have hreg := regular_quadOdd (K := ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) h2 hr3
    have hEq := commutator_orthogonalGroup_quadOdd
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) h2 hr3
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadOdd r _) hEq hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3)
    exact exists_hyperGen_nonsplit_of_cover hπ hreg.2 hEq hp hp2 hpK hpKd
      (by rw [hcard]; exact hq1) (by rw [hcard]; exact hq2) hE₀ hc₀
  ·
    have hq₀ : q₀ = q := by
      rcases hd₀ with h | h | h <;> cases h
      rfl
    rw [hq₀] at hq1 hq2
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1)
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.D r q, hv⟩ (q := q) (by simp)
    have hpKd : ¬ p ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) := by
      rw [hcard, PrimePower.card_def]
      exact not_dvd_pow_of_ne hp q.prime_p hq'
    have hpK := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpKd
    have hreg := regular_quadPlus (K := ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r)
      (by omega)
    have hEq := commutator_orthogonalGroup_quadPlus
      (K := ↥(ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)) (n := r) (by omega)
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadPlus r _) hEq hreg.1
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv)
    exact exists_hyperGen_nonsplit_of_cover hπ hreg.2 hEq hp hp2 hpK hpKd
      (by rw [hcard]; exact hq1) (by rw [hcard]; exact hq2) hE₀ hc₀
  ·
    have hq₀ : q₀ = q := by
      rcases hd₀ with h | h | h <;> cases h
      rfl
    rw [hq₀] at hq1 hq2
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1
      ((LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard := card_fixedField_eq_card ⟨.twistedD r q, hv⟩ (q := q) (by simp)
    have hpKd : ¬ p ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) := by
      rw [hcard, PrimePower.card_def]
      exact not_dvd_pow_of_ne hp q.prime_p hq'
    have hpK := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpKd
    have hreg := regular_quadMinus (n := r) hr4 hirr
    have hEq := commutator_orthogonalGroup_quadMinus (n := r) hr4 hirr
    obtain ⟨π, hπ⟩ := exists_orthCover (coe_quadMinus r _ b c) hEq hreg.1 e
    exact exists_hyperGen_nonsplit_of_cover hπ hreg.2 hEq hp hp2 hpK hpKd
      (by rw [hcard]; exact hq1) (by rw [hcard]; exact hq2) hE₀ hc₀

theorem hyperExFor_orthogonal_of_small (hS : OrthHyperExSmall) :
    HyperExFor fun d => IsOrthogonalIndex d.1 :=
  hyperExFor_orthogonal_of_residuals orthHyperExNonsplit hS

end Residual

end CFSG.LieType.SeitzGeneration
