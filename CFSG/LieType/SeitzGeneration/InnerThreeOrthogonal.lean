module

public import CFSG.LieType.SeitzGeneration.ClassicalThreeLeaves
public import CFSG.LieType.SeitzGeneration.OrthManyParabolic

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthMasterThree : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → 7 ≤ Module.finrank K V →
      3 ≠ ringChar K → OrthPlaneGen Q 3

theorem orthPlaneGen_three_of_singular_stable {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hpl : 3 ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2)
    (hsing : ∃ W : Submodule K V, W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ e ∈ E, ∀ w ∈ W, ((e : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) :
    Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
  obtain ⟨W, hW0, hW, hstab⟩ := hsing
  exact closure_eq_top_of_singular_stable hQ hT Nat.prime_three (by norm_num) hpl E hcomm hexp
    hcard hW0 hW hstab

theorem orthogonalOddPlanes_three_of_master (hM : OrthMasterThree) (r : ℕ) (K : Type)
    [Field K] [Finite K] (hr : 3 ≤ r) (hpK : ¬ 3 ∣ Nat.card K) (h2 : (2 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K))))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadOdd r K)
    (commutator_orthogonalGroup_quadOdd h2 hr) hreg.1 Nat.prime_three (by omega)
    (hM K _ (quadOdd r K) hreg.1 hreg.2 hdim (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthogonalPlusPlanes_three_of_master (hM : OrthMasterThree) (r : ℕ) (K : Type)
    [Field K] [Finite K] (hr : 4 ≤ r) (hpK : ¬ 3 ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K))))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 Nat.prime_three (by omega)
    (hM K _ (quadPlus r K) hreg.1 hreg.2 hdim (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthogonalMinusPlanes_three_of_master (hM : OrthMasterThree) (r : ℕ) (K : Type)
    [Field K] [Finite K] (b c : K) (hr : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hpK : ¬ 3 ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c))))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 Nat.prime_three (by omega)
    (hM K _ (quadMinus r K b c) hreg.1 hreg.2 hdim (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem seitzInnerThreeOrthogonal_of_master (h : OrthMasterThree) :
    SeitzInnerThreeOrthogonal := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, horth⟩
  subst hp3
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : 3 ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero
        h2 hr3
    have : IsSimpleGroup (Cat ⟨.B r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.B r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalOddPlanes_three_of_master h r _ hr3
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') h2 E₁ hE₁ hcard₁
  ·
    have hq' : 3 ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
    have : IsSimpleGroup (Cat ⟨.D r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.D r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalPlusPlanes_three_of_master h r _ hr4
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') E₁ hE₁ hcard₁
  ·
    have hq' : 3 ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hr4 hirr
    have : IsSimpleGroup (Cat ⟨.twistedD r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedD r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalMinusPlanes_three_of_master h r _ b c hr4 hirr
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') E₁ hE₁ hcard₁

end CFSG.LieType.SeitzGeneration
