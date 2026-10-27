module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem exists_card_eq_pow_ringChar {K : Type} [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

private theorem linear_cases_three_of_three_le {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL n K)) (hβ : β ^ 3 = 1) :
    (∃ (A : GL (Fin n) K) (c : Kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL n K)) (σ : K ≃+* K), orderOf σ = 3 ∧
      β = h * LinearFlag.fieldAut n K σ * h⁻¹) := by
  obtain ⟨f, hf, hℓ, hK⟩ := exists_card_eq_pow_ringChar (K := K)
  have hdesc := CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent
    hℓ hf hn hK
  by_cases hlin : β ∈ LinearFlag.linearAutGroup n K
  · left
    have hrange : LinearFlag.linearAutGroup n K = (LinearFlag.conjAut n K).range := by
      rw [LinearFlag.linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
    rw [hrange] at hlin
    obtain ⟨A, rfl⟩ := hlin
    have hAp : A ^ 3 ∈ (LinearFlag.conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, rfl⟩
  · right
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (by decide : Odd 3) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 := fun h =>
      hlin (h ▸ one_mem _)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = 3 :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hℓ hf hn hK Nat.prime_three
        hmem hlin hord
    exact ⟨h, τ, hτ, hβτ⟩

private theorem linear_cases_three_two {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL 2 K)) (hβ : β ^ 3 = 1) :
    (∃ (A : GL (Fin 2) K) (c : Kˣ), A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      β = LinearFlag.conjAut 2 K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL 2 K)) (σ : K ≃+* K), orderOf σ = 3 ∧
      β = h * LinearFlag.fieldAut 2 K σ * h⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K), MulAut.congr (psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv K)).symm β, (MulAut.congr (psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ 3 = 1 :=
    (MulAut.congr (psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  by_cases hD : β₀ ∈ (pglAction K).range
  · left
    obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact congr_pglAction_mk A
    have hAp : A ^ 3 ∈ Subgroup.center (GL (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ 3)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, hβA⟩
  · right
    have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = 3 := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, hσ, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hcongr : MulAut.congr (psl2Equiv K)
        (pglAction K (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 K A :=
      congr_pglAction_mk A
    refine ⟨LinearFlag.conjAut 2 K A, σ, hσ, ?_⟩
    rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]

private theorem exists_unipotent_of_cube_scalar {n : ℕ} {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) = 0) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ u : Matrix.SpecialLinearGroup (Fin n) K, u ^ 3 = 1 ∧
      LinearFlag.conjAut n K A = MulAut.conj (LinearFlag.proj n K u) := by
  haveI : CharP K 3 :=
    (CharP.charP_iff_prime_eq_zero (R := K) Nat.prime_three).2 (by exact_mod_cast h3)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : K, l ^ 3 = c := by
    obtain ⟨l, hl⟩ := Finite.surjective_of_injective (frobenius_inj K 3) (c : K)
    exact ⟨l, hl⟩
  have hl0 : l₀ ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hl₀]; simp)
  set l : Kˣ := Units.mk0 l₀ hl0 with hl
  have hlc : l ^ 3 = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hl₀
  set s : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) l with hs
  have hscomm : ∀ B : GL (Fin n) K, s * B = B * s := fun B =>
    Matrix.GeneralLinearGroup.scalar_commute l B
  set U : GL (Fin n) K := s⁻¹ * A with hU
  have hcomm : Commute s⁻¹ A := (show Commute s A from hscomm A).inv_left
  have hUcube : U ^ 3 = 1 := by
    rw [hU, hcomm.mul_pow, hA, inv_pow, hs, ← map_pow, hlc, inv_mul_cancel]
  have hdetU : (U : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U) ^ 3 = 1 := by
      rw [← map_pow, hUcube, map_one]
    have h2 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) ^ 3 = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h1
      simpa using this
    have h3' : (((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) - 1) ^ 3 =
        0 := by
      rw [sub_pow_char, h2]
      simp
    have h4 := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h3'
    have h5 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) = 1 :=
      sub_eq_zero.1 h4
    simpa using h5
  let u : Matrix.SpecialLinearGroup (Fin n) K := ⟨(U : Matrix (Fin n) (Fin n) K), hdetU⟩
  have hu : Matrix.SpecialLinearGroup.toGL u = U := Units.ext rfl
  refine ⟨u, ?_, ?_⟩
  · apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, hu, hUcube, map_one]
  · have hA' : A = s * U := by rw [hU, mul_inv_cancel_left]
    have hconj : LinearFlag.conjAut n K A = LinearFlag.conjAut n K U := by
      rw [hA', map_mul, hs, LinearFlag.conjAut_scalar, one_mul]
    rw [hconj]
    ext x
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective n K x
    rw [LinearFlag.conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
      map_mul, map_mul, map_inv, hu]

private theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem lieCompCase_linear
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) : LieCompExport q.p β ∨ NoThreeComponents β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact Or.inl (lieCompExport_one hna ⟨.A r q, hv⟩ he (isEmpty_mulEquiv_alternating_six hb _ he))
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ q.p
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hcases := (Nat.lt_or_ge r 2).elim
    (fun hr2 => by
      obtain rfl : r = 1 := by omega
      exact linear_cases_three_two (MulAut.congr e' β) hβ')
    (fun hr2 => linear_cases_three_of_three_le (by omega) (MulAut.congr e' β) hβ')
  rcases hcases with ⟨A, c, hA, hβA⟩ | ⟨h, σ, hσ, hβh⟩
  · by_cases h3 : (3 : GaloisField q.p q.exponent) = 0
    ·
      right
      obtain ⟨u, hu3, hu⟩ := exists_unipotent_of_cube_scalar h3 hA
      have hq3 : q.p = 3 := by
        have h0 : ((3 : ℕ) : GaloisField q.p q.exponent) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at h0
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h0
      have hS : IsChevOfChar 3 S :=
        ⟨⟨.A r q, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq (by
          show q.p = 3
          exact hq3), ⟨e⟩⟩
      set s' := LinearFlag.proj (r + 1) (GaloisField q.p q.exponent) u with hs'
      have hβs : β = MulAut.conj (e'.symm s') := by
        apply (MulAut.congr e').injective
        rw [hβA, hu, congr_conj_apply, MulEquiv.apply_symm_apply]
      have hs1 : e'.symm s' ≠ 1 := by
        intro h1
        apply hβ1
        rw [hβs, h1, map_one]
      have hs3 : (e'.symm s') ^ 3 = 1 := by
        rw [← map_pow, hs', ← map_pow, hu3, map_one, map_one]
      rw [hβs]
      exact noThreeComponents_of_conj hQ hs hna hS hs1 hs3
    · left
      have h1 := lieCompExport_conjAut hSL hA6 h3 hA
      rw [← hβA, hchar] at h1
      exact LieCompExport.of_congr e' h1
  · left
    have h1 := lieCompExport_fieldAut hSL hA6 (n := r + 1) (by omega) σ hσ
    rw [hchar] at h1
    refine LieCompExport.of_congr e' ?_
    refine LieCompExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβh]
    have : h⁻¹ * (h * LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ * h⁻¹) * h⁻¹⁻¹ =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by group
    rw [this]
    exact h1

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
