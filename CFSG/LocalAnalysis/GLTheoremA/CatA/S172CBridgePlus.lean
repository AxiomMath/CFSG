module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11d.OrthLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.GroupTheory.WeirSylow CFSG.LieType.Universal.Spin
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne TauCeti

theorem nonempty_statedProjOmegaPlus_equiv_orthDerived {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] :
    Nonempty (StatedProj (StatedOmega (StatedQuadPlus n K)) ≃* ↥(orthDerived (quadPlus n K))) := by
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K
  have : Inhabited (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Nontrivial (Fin n ⊕ Fin n → K) := Pi.nontrivial
  exact ⟨(statedProjOrthEquiv (coe_quadPlus n K)).trans
    (MulEquiv.ofBijective (piOrth (quadPlus n K))
      ⟨piOrth_injective hnd, piOrth_surjective⟩).symm⟩

private theorem exists_omegaPlus_model_aux1 {q : PrimePower} {k : ℕ} (hk : 1 ≤ k) (h : q.card = 2 ^ k) :
    q = ⟨2, k, Nat.prime_two, hk⟩ := by
  rw [PrimePower.card_def] at h
  have h1 : q.p ∣ 2 ^ k := h ▸ dvd_pow_self q.p (Nat.pos_iff_ne_zero.mp q.exponent_pos)
  have hp2 : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
  rw [hp2] at h
  exact PrimePower.ext hp2 (Nat.pow_right_injective le_rfl h)

theorem exists_omegaPlus_model {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      Nat.card F = 2 ^ k ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧
        Module.finrank F V = 2 * n ∧ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧
        ∀ (X : Type) [Group X], catalogIs X (isOmPA n (2 ^ k)) →
          Nonempty (X ≃* ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  let q₀ : PrimePower := ⟨2, k, Nat.prime_two, hk⟩
  have hv : (LieTypeIndex.D n q₀).Valid := by
    simp only [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  let φ := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj n q₀ hv rfl
  have hfin : Finite ↥(ValidLieTypeIndex.fixedField ⟨.D n q₀, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.D n q₀, hv⟩) = 2 ^ k := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, q₀]
  haveI : Fintype ↥(ValidLieTypeIndex.fixedField ⟨.D n q₀, hv⟩) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP ↥(ValidLieTypeIndex.fixedField ⟨.D n q₀, hv⟩) 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hn1 : 1 ≤ n := by omega
  refine ⟨_, inferInstance, hfin, hchar, Fin n ⊕ Fin n → _, inferInstance, inferInstance,
    inferInstance, quadPlus n _, hcard, nondegenerate_polarBilin_quadPlus n _,
    finrank_quadPlus_space n, isPlusType_quadPlus _ n, ?_⟩
  intro X _ ⟨i, hi, ⟨e⟩⟩
  rcases hi with hi | ⟨h3, -⟩
  · cases i with
    | lie j =>
      obtain ⟨x, hv'⟩ := j
      cases x
      case D r q =>
        obtain ⟨rfl, hq⟩ := hi
        have hqq : q = q₀ := exists_omegaPlus_model_aux1 hk hq
        subst hqq
        refine ⟨(e.trans φ).trans ?_⟩
        exact (nonempty_statedProjOmegaPlus_equiv_orthDerived hn1).some
      all_goals exact hi.elim
    | _ => exact hi.elim
  · omega

end CFSG.LocalAnalysis.GLTheoremA.S172C

end
