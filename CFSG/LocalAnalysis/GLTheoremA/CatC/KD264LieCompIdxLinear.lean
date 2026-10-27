module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open Matrix

theorem exists_eq_scalar_of_conjAut_eq_one {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k] [Finite k]
    {A : GL (Fin n) k} (h : conjAut n k A = 1) :
    ∃ c : kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  haveI : Fintype k := Fintype.ofFinite k
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have hn2 : n = 2 := by omega
    subst hn2
    have hcongr : MulAut.congr (psl2Equiv k) (pglAction k (Matrix.ProjGenLinGroup.mk A)) =
        conjAut 2 k A := congr_pglAction_mk (K := k) A
    have h2 : pglAction k (Matrix.ProjGenLinGroup.mk A) = 1 := by
      apply (MulAut.congr (psl2Equiv k)).injective
      rw [hcongr, h, map_one]
    have h3' : Matrix.ProjGenLinGroup.mk A = 1 := by
      apply pglAction_injective k
      rw [h2, map_one]
    have h3'' : A ∈ Subgroup.center (GL (Fin 2) k) := Matrix.ProjGenLinGroup.mk_eq_one.1 h3'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h3''
    obtain ⟨c, hc⟩ := h3''
    exact ⟨c, hc.symm⟩
  · obtain ⟨f, hℓ, hf⟩ := FiniteField.card k (ringChar k)
    have hmem : A ∈ (conjAut n k).ker := MonoidHom.mem_ker.2 h
    have hker := (CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
      (n := n) (K := k) hℓ
      (Nat.pos_of_ne_zero f.ne_zero) h3 (by rw [Nat.card_eq_fintype_card]; exact hf)).1
    rw [hker] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩

theorem exists_commutator_eq_scalar_of_commute_conjAut {n : ℕ} (hn : 2 ≤ n) {k : Type}
    [Field k] [Finite k] {A B : GL (Fin n) k}
    (h : conjAut n k A * conjAut n k B = conjAut n k B * conjAut n k A) :
    ∃ z : kˣ, A * B * A⁻¹ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) z := by
  refine exists_eq_scalar_of_conjAut_eq_one hn ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [h]
  group

theorem compIdxAt_projectiveSL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {k : Type 0} [Field k] [Finite k] {q : TauCeti.PrimePower} (hcard : Nat.card k = q.card)
    (hpq : p ≠ q.p) : CompIdxAt p (.A (n - 1) q) (projectiveSL n k) := by
  intro β hβmem hβp _ K hK
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1
    (innAutDerived_projectiveSL_le_linearAutGroup hn hβmem)
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card k (ringChar k)
  have hchark : ringChar k = q.p := by
    have hdvd : ringChar k ∣ q.p ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def q, ← hcard, Nat.card_eq_fintype_card, hf]
      exact dvd_pow_self _ f.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hℓ q.prime_p).1 (hℓ.dvd_of_dvd_pow hdvd)
  have hpk : (p : k) ≠ 0 := by
    intro h0
    have hd : ringChar k ∣ p := (CharP.cast_eq_zero_iff k (ringChar k) p).1 h0
    exact hpq (by rw [← hchark]; exact ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 hd).symm)
  have hAp : conjAut n k (A ^ p) = 1 := by
    rw [map_pow, hβp]
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_conjAut_eq_one hn hAp
  obtain ⟨E, hE, hFE, m, j, hm, hj, hcharE, hcardE, hbig, g, hg, hker⟩ :=
    linear_inner_component_type_card hpk hc K hK
  have hbig' : m = 2 → 4 ≤ Fintype.card E := fun h2 => by
    rw [@Fintype.card_eq_nat_card E hFE]
    exact hbig h2
  have hcovK : CatalogueOver (ringChar E) (Fintype.card E) ↥K :=
    catalogueOver_of_surjective_sl hm hbig' g hg hker
  obtain ⟨i, ⟨φ⟩, hidx⟩ := hcovK
  refine ⟨i, ⟨φ⟩, compRelC_of_idxOver hj ?_⟩
  have hchar : (TauCeti.LieTypeIndex.A (n - 1) q).characteristic = ringChar E := by
    rw [TauCeti.LieTypeIndex.characteristic_A, ← hchark, ← hcharE]
  have hfs : fieldSize (TauCeti.LieTypeIndex.A (n - 1) q) = Nat.card k := hcard.symm
  have hcardE' : Fintype.card E = Nat.card k ^ j := by
    rw [@Fintype.card_eq_nat_card E hFE]
    exact hcardE
  rw [hchar, hfs, ← hcardE']
  exact hidx

theorem lieCompIdx_linear : LieCompIdx isLinearIdx := by
  intro d p hp hp2 hpc hP
  obtain ⟨e, hd⟩ := d
  cases e with
  | A n q =>
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1
    have hn1 : 1 ≤ n := hrange.1
    have hpq : p ≠ q.p := by
      rw [TauCeti.LieTypeIndex.characteristic_A] at hpc
      exact hpc
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let k := GaloisField q.p q.exponent
    have hcard : Nat.card k = q.card := by
      dsimp only [k]
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
      exact (TauCeti.PrimePower.card_def q).symm
    have eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hd⟩).Group ≃*
        LinearFlag.projectiveSL (n + 1) k :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
    exact compIdxAt_of_mulEquiv eModel.symm
      (compIdxAt_projectiveSL (n := n + 1) hp hp2 (by omega) (q := q) hcard hpq)
  | _ => exact absurd hP (by simp [isLinearIdx])

theorem eq_one_of_pow_three_eq_one_card_eight {k : Type} [Field k] (hk : Nat.card k = 8)
    {c : k} (h : c ^ 3 = 1) : c = 1 := by
  rcases eq_or_ne c 0 with rfl | h0
  · rw [zero_pow (by norm_num)] at h
    exact absurd h (by norm_num)
  · have hcard : Nat.card kˣ = 7 := by rw [Nat.card_units, hk]
    let u : kˣ := Units.mk0 c h0
    have hu : u ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
      exact h
    have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu
    have hdvd' : orderOf u ∣ 7 := by rw [← hcard]; exact orderOf_dvd_natCard u
    have hone : orderOf u = 1 := by
      have := Nat.dvd_gcd hdvd hdvd'
      rw [show Nat.gcd 3 7 = 1 by norm_num] at this
      exact Nat.dvd_one.1 this
    have hu1 : u = 1 := orderOf_eq_one_iff.1 hone
    have hval : ((u : kˣ) : k) = ((1 : kˣ) : k) := congrArg (fun x : kˣ => (x : k)) hu1
    simpa [u] using hval

theorem mul_comm_of_commute_conjAut_pow_three {n : ℕ} (hn : 2 ≤ n) {k : Type} [Field k]
    [Finite k] (hk : Nat.card k = 8) {A X : GL (Fin n) k} (hX : conjAut n k X ^ 3 = 1)
    (hAX : conjAut n k A * conjAut n k X = conjAut n k X * conjAut n k A) : A * X = X * A := by
  have hX3 : conjAut n k (X ^ 3) = 1 := by rw [map_pow, hX]
  obtain ⟨ν, hν⟩ := exists_eq_scalar_of_conjAut_eq_one hn hX3
  obtain ⟨μ, hμ⟩ := exists_commutator_eq_scalar_of_commute_conjAut hn hAX
  have hAX' : A * X = Matrix.GeneralLinearGroup.scalar (Fin n) μ * (X * A) := by
    calc A * X = (A * X * A⁻¹ * X⁻¹) * (X * A) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) μ * (X * A) := by rw [hμ]
  have hXA : X * A = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (A * X) := by
    rw [hAX', ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hcen : ∀ (B : GL (Fin n) k),
      Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B =
        B * Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ := fun B =>
    Matrix.GeneralLinearGroup.scalar_commute μ⁻¹ B
  have hconjA : MulAut.conj X A = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * A := by
    rw [MulAut.conj_apply, hXA]
    group
  have hconj_mul : ∀ B : GL (Fin n) k,
      MulAut.conj X (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B) =
        Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * MulAut.conj X B := by
    intro B
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc X * (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B) * X⁻¹ =
          (X * Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) * (B * X⁻¹) := by group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * X) * (B * X⁻¹) := by
            rw [← hcen X]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (X * (B * X⁻¹)) := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (X * B * X⁻¹) := by group
  have hiter : ∀ (m : ℕ) (B : GL (Fin n) k),
      (MulAut.conj X ^ m) (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B) =
        Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * (MulAut.conj X ^ m) B := by
    intro m
    induction m with
    | zero => intro B; simp
    | succ m ih =>
        intro B
        rw [pow_succ, MulAut.mul_apply, hconj_mul, ih]
        rfl
  have hpow : ∀ m : ℕ, (MulAut.conj X ^ m) A =
      Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ ^ m * A := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, MulAut.mul_apply, hconjA, hiter, ih, ← mul_assoc, ← pow_succ']
  have h3 : A = Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ ^ 3 * A := by
    have h1 := hpow 3
    rw [show MulAut.conj X ^ 3 = MulAut.conj (X ^ 3) from
      (map_pow (MulAut.conj : GL (Fin n) k →* MulAut (GL (Fin n) k)) X 3).symm] at h1
    have h2 : MulAut.conj (X ^ 3) A = A := by
      rw [hν, MulAut.conj_apply,
        Matrix.GeneralLinearGroup.scalar_commute ν A, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2] at h1
    exact h1
  have hc3 : (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) ^ 3 = 1 := by
    have h := h3
    calc (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) ^ 3
        = (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) ^ 3 * 1 := (mul_one _).symm
      _ = (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) ^ 3 * (A * A⁻¹) := by
            rw [mul_inv_cancel, mul_one]
      _ = ((Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) ^ 3 * A) * A⁻¹ := by rw [mul_assoc]
      _ = A * A⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel A
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ →* GL (Fin n) k) := by
    intro a b hab
    have h := congrArg (fun g : GL (Fin n) k =>
      ((g : Matrix (Fin n) (Fin n) k)) ⟨0, by omega⟩ ⟨0, by omega⟩) hab
    exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using h)
  have hmu3 : μ ^ 3 = 1 := by
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin n) ((μ⁻¹) ^ 3) = 1 := by
      rw [map_pow]
      exact hc3
    have h2 : (μ⁻¹) ^ 3 = 1 := by
      apply hscalar_inj
      rw [h1, map_one]
    rwa [inv_pow, inv_eq_one] at h2
  have hmu1 : μ = 1 := by
    apply Units.ext
    have h : ((μ : kˣ) : k) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hmu3, Units.val_one]
    exact eq_one_of_pow_three_eq_one_card_eight hk h
  rw [hAX', hmu1, map_one, one_mul]

@[expose] def LinearCompAlgEight : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (k : Type 0) [Field k] [Finite k], Nat.card k = 8 →
    CompAlgAt (LinearFlag.projectiveSL n k)

theorem lieCompAlg_linear_of_eight (h : LinearCompAlgEight) : LieCompAlg isLinearIdx := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  cases e with
  | A n q =>
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    let k := GaloisField q.p q.exponent
    have hq8 : q.p ^ q.exponent = 8 := by
      rw [← TauCeti.PrimePower.card_def q]
      exact hfield
    have hcard : Nat.card k = 8 := by
      dsimp only [k]
      rw [GaloisField.card q.p q.exponent q.exponent_pos.ne']
      exact hq8
    have eModel : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A n q, hv⟩).Group ≃*
        LinearFlag.projectiveSL (n + 1) k :=
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) k)
    have hn : 1 ≤ n := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    exact compAlgAt_of_mulEquiv eModel.symm (h (n + 1) (by omega) k hcard)
  | _ => exact absurd hP (by simp [isLinearIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
