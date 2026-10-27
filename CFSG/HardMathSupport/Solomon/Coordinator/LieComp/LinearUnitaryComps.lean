module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsInterface
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInnerComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearFieldComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnAut
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem LieCompsExport.of_congr {q : ℕ} {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (h : LieCompsExport q (MulAut.congr e β)) : LieCompsExport q β := by
  have hfix : fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* G) := by
    ext x
    rw [mem_fixSubgroup]
    refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
    rw [mem_fixSubgroup]
    show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
    exact e.eq_symm_apply.symm
  have hmapc : ∀ {K : Subgroup S}, IsComponentOf K (fixSubgroup β) →
      IsComponentOf (K.map (e : S →* G)) (fixSubgroup (MulAut.congr e β)) := fun hK => by
    rw [hfix]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
  refine ⟨LieSemisimple.perfectInLayer_of_congr e β h.layer, fun K hK => ?_⟩
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps _ (hmapc hK)
  let g : ↥(K.map (e : S →* G)) ≃* ↥K :=
    (K.equivMapOfInjective (e : S →* G) e.injective).symm
  refine ⟨X, inferInstance, inferInstance, hX, (g : _ →* ↥K).comp f, g.surjective.comp hf, ?_⟩
  intro x hx
  apply hfk
  rw [MonoidHom.mem_ker] at hx ⊢
  apply g.injective
  rw [map_one]
  exact hx

private theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem exists_card_eq_pow_ringChar {K : Type} [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

private theorem linear_cases_of_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL n K)) (hβ : β ^ p = 1) :
    (∃ (A : GL (Fin n) K) (c : Kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c ∧
      β = LinearFlag.conjAut n K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL n K)) (σ : K ≃+* K), orderOf σ = p ∧
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
    have hAp : A ^ p ∈ (LinearFlag.conjAut n K).ker := by rw [MonoidHom.mem_ker, map_pow, hβ]
    rw [hdesc.1] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, rfl⟩
  · right
    obtain ⟨A, σ, rfl⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.Ln.exists_conj_field_of_odd hn
      (hp.odd_of_ne_two hp2) hβ
    have hmem : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ∈
        LinearFlag.semilinearAutGroup n K :=
      mul_mem (LinearFlag.linearAutGroup_le_semilinearAutGroup
        (LinearFlag.conjAut_mem_linearAutGroup A))
        (LinearFlag.fieldAut_mem_semilinearAutGroup σ)
    have hne : LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ ≠ 1 := fun h =>
      hlin (h ▸ one_mem _)
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ) = p :=
      orderOf_eq_prime hβ hne
    obtain ⟨-, τ, hτ, ⟨h, -, hβτ⟩, -⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linear_prime_descent_char hℓ hf hn hK hp
        hmem hlin hord
    exact ⟨h, τ, hτ, hβτ⟩

private theorem linear_cases_two {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (β : MulAut (LinearFlag.projectiveSL 2 K)) (hβ : β ^ p = 1) :
    (∃ (A : GL (Fin 2) K) (c : Kˣ), A ^ p = Matrix.GeneralLinearGroup.scalar (Fin 2) c ∧
      β = LinearFlag.conjAut 2 K A) ∨
    (∃ (h : MulAut (LinearFlag.projectiveSL 2 K)) (σ : K ≃+* K), orderOf σ = p ∧
      β = h * LinearFlag.fieldAut 2 K σ * h⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨β₀, hββ₀⟩ : ∃ β₀ : MulAut (PSL2 K), MulAut.congr (psl2Equiv K) β₀ = β :=
    ⟨(MulAut.congr (psl2Equiv K)).symm β, (MulAut.congr (psl2Equiv K)).apply_symm_apply β⟩
  have hβ₀p : β₀ ^ p = 1 :=
    (MulAut.congr (psl2Equiv K)).injective (by rw [map_pow, hββ₀, hβ, map_one])
  by_cases hD : β₀ ∈ (pglAction K).range
  · left
    obtain ⟨g, hg⟩ := hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hβA : β = LinearFlag.conjAut 2 K A := by
      rw [← hββ₀, ← hg]
      exact congr_pglAction_mk A
    have hAp : A ^ p ∈ Subgroup.center (GL (Fin 2) K) := by
      have h1 : pglAction K (Matrix.ProjGenLinGroup.mk (A ^ p)) = pglAction K 1 := by
        rw [map_pow, map_pow, hg, hβ₀p, map_one]
      exact Matrix.ProjGenLinGroup.mk_eq_one.1
        (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective K h1)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hAp
    obtain ⟨c, hc⟩ := hAp
    exact ⟨A, c, hc.symm, hβA⟩
  · right
    have hne : β₀ ≠ 1 := fun h => hD ⟨1, by rw [map_one, h]⟩
    have hord : orderOf β₀ = p := orderOf_eq_prime hβ₀p hne
    obtain ⟨σ, hσ, g, hgσ⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent hp β₀ hord hD
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hcongr : MulAut.congr (psl2Equiv K)
        (pglAction K (Matrix.ProjGenLinGroup.mk A)) = LinearFlag.conjAut 2 K A :=
      congr_pglAction_mk A
    refine ⟨LinearFlag.conjAut 2 K A, σ, hσ, ?_⟩
    rw [← hββ₀, hgσ, map_mul, map_mul, map_inv, hcongr, congr_psl2FieldAut]

private theorem exists_conj_proj_of_pow_scalar {p n : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [Finite K] (hpK : (p : K) = 0) {A : GL (Fin n) K} {c : Kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ u : Matrix.SpecialLinearGroup (Fin n) K,
      LinearFlag.conjAut n K A = MulAut.conj (LinearFlag.proj n K u) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (R := K) hp).2 hpK
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : K, l ^ p = c := by
    obtain ⟨l, hl⟩ := Finite.surjective_of_injective (frobenius_inj K p) (c : K)
    exact ⟨l, hl⟩
  have hl0 : l₀ ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hl₀]; simp [hp.ne_zero])
  set l : Kˣ := Units.mk0 l₀ hl0 with hl
  have hlc : l ^ p = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hl₀
  set s : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) l with hs
  have hscomm : ∀ B : GL (Fin n) K, s * B = B * s := fun B =>
    Matrix.GeneralLinearGroup.scalar_commute l B
  set U : GL (Fin n) K := s⁻¹ * A with hU
  have hcomm : Commute s⁻¹ A := (show Commute s A from hscomm A).inv_left
  have hUp : U ^ p = 1 := by
    rw [hU, hcomm.mul_pow, hA, inv_pow, hs, ← map_pow, hlc, inv_mul_cancel]
  have hdetU : (U : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U) ^ p = 1 := by
      rw [← map_pow, hUp, map_one]
    have h2 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) ^ p = 1 := by
      have := congrArg (fun x : Kˣ => (x : K)) h1
      simpa using this
    have h3' : (((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) - 1) ^ p =
        0 := by
      rw [sub_pow_char, h2]
      simp
    have h4 := pow_eq_zero_iff hp.ne_zero |>.1 h3'
    have h5 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) = 1 :=
      sub_eq_zero.1 h4
    simpa using h5
  let u : Matrix.SpecialLinearGroup (Fin n) K := ⟨(U : Matrix (Fin n) (Fin n) K), hdetU⟩
  have hu : Matrix.SpecialLinearGroup.toGL u = U := Units.ext rfl
  refine ⟨u, ?_⟩
  have hA' : A = s * U := by rw [hU, mul_inv_cancel_left]
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

private theorem lieCompsCase_linear {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ p = 1) (hout : q.p ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β) :
    LieCompsExport q.p β := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨e⟩ := he
  let e' : S ≃* LinearFlag.projectiveSL (r + 1) (GaloisField q.p q.exponent) :=
    e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (r + 1) _))
  have hchar : ringChar (GaloisField q.p q.exponent) = q.p := ringChar.eq _ q.p
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hcases := (Nat.lt_or_ge r 2).elim
    (fun hr2 => by
      obtain rfl : r = 1 := by omega
      exact linear_cases_two hp (MulAut.congr e' β) hβ')
    (fun hr2 => linear_cases_of_three_le hp hp2 (by omega) (MulAut.congr e' β) hβ')
  rcases hcases with ⟨A, c, hA, hβA⟩ | ⟨h, σ, hσ, hβh⟩
  · by_cases hpK : (p : GaloisField q.p q.exponent) = 0
    ·
      exfalso
      have hqp : q.p = p := by
        rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at hpK
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 hpK
      have hout' : ∀ a : S, MulAut.conj a ≠ β := hout.resolve_left (fun h => h hqp)
      obtain ⟨u, hu⟩ := exists_conj_proj_of_pow_scalar hp hpK hA
      refine hout' (e'.symm (LinearFlag.proj (r + 1) (GaloisField q.p q.exponent) u)) ?_
      apply (MulAut.congr e').injective
      rw [hβA, hu, congr_conj_apply, MulEquiv.apply_symm_apply]
    · have h1 := lieCompsExport_conjAut slFactorFacts_holds hpK hA
      rw [← hβA, hchar] at h1
      exact LieCompsExport.of_congr e' h1
  · have h1 := lieCompsExport_fieldAut slFactorFacts_holds hp hp2 (n := r + 1) (by omega) σ hσ
    rw [hchar] at h1
    refine LieCompsExport.of_congr e' ?_
    refine LieCompsExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβh]
    have : h⁻¹ * (h * LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ * h⁻¹) * h⁻¹⁻¹ =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by group
    rw [this]
    exact h1

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private theorem eq_one_of_pow_eq_one_char {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [CharP K p]
    {x : K} (hx : x ^ p = 1) : x = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : (x - 1) ^ p = 0 := by
    rw [sub_pow_char, hx]
    simp
  exact sub_eq_zero.1 (pow_eq_zero_iff hp.ne_zero |>.1 h)

private theorem det_eq_one_of_pow_eq_one_char {p n : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [CharP K p] {U : GL (Fin n) K} (hU : U ^ p = 1) : (U : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 : (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U) ^ p = 1 := by
    rw [← map_pow, hU, map_one]
  have h2 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) ^ p = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) h1
    simpa using this
  have h3 := eq_one_of_pow_eq_one_char hp h2
  simpa using h3

private theorem primeFormConjHom_scalar_eq_one {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (c : Kˣ) (hc : h.norm (c : K) = 1) :
    primeFormConjHom h (idGram K n)
      ⟨Matrix.GeneralLinearGroup.scalar (Fin n) c, scalar_mem_primeFormUnitary_one h hc⟩ = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.scalar (Fin n) c * (g : GL (Fin n) K) *
    (Matrix.GeneralLinearGroup.scalar (Fin n) c)⁻¹ = g
  rw [Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem primeFormConjHom_eq_conj {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (u : gramSU h (idGram K n)) :
    primeFormConjHom h (idGram K n) ⟨(u : GL (Fin n) K), u.2.1⟩ =
      MulAut.conj (u : primeFormP h (idGram K n)) := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply]
  rfl

private theorem exists_conj_of_pow_scalar {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hℓ : ℓ = p)
    (A : primeFormUnitary h (idGram K n)) {c : Kˣ} (hc : h.norm (c : K) = 1)
    (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ u : gramSU h (idGram K n),
      primeFormConjHom h (idGram K n) A = MulAut.conj (u : primeFormP h (idGram K n)) := by
  haveI : Finite K := h.finite
  haveI : CharP K p := hℓ ▸ h.charP
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l : K, l ^ p = c := by
    obtain ⟨l, hl⟩ := Finite.surjective_of_injective (frobenius_inj K p) (c : K)
    exact ⟨l, hl⟩
  have hl0 : l₀ ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hl₀]; simp [hp.ne_zero])
  set l : Kˣ := Units.mk0 l₀ hl0 with hl
  have hlc : l ^ p = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hl₀
  have hNl : h.norm (l : K) = 1 := by
    apply eq_one_of_pow_eq_one_char hp
    have hN : h.norm ((l : K) ^ p) = (h.norm (l : K)) ^ p := by
      simp only [UnitaryFieldData.norm, map_pow, mul_pow]
    rw [← hN, ← Units.val_pow_eq_pow_val, hlc]
    exact hc
  have hs := scalar_mem_primeFormUnitary_one (n := n) h hNl
  set s : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) l with hsdef
  set U : GL (Fin n) K := s⁻¹ * (A : GL (Fin n) K) with hU
  have hUmem : U ∈ primeFormUnitary h (idGram K n) := mul_mem (inv_mem hs) A.2
  have hcomm : Commute s⁻¹ (A : GL (Fin n) K) :=
    (show Commute s (A : GL (Fin n) K) from Matrix.GeneralLinearGroup.scalar_commute l _).inv_left
  have hUp : U ^ p = 1 := by
    rw [hU, hcomm.mul_pow, hA, inv_pow, hsdef, ← map_pow, hlc, inv_mul_cancel]
  have hdetU := det_eq_one_of_pow_eq_one_char hp hUp
  let u : gramSU h (idGram K n) := ⟨U, hUmem, hdetU⟩
  refine ⟨u, ?_⟩
  have hAU : A = ⟨s, hs⟩ * ⟨U, hUmem⟩ := by
    apply Subtype.ext
    change (A : GL (Fin n) K) = s * (s⁻¹ * A)
    rw [mul_inv_cancel_left]
  rw [hAU, map_mul, primeFormConjHom_scalar_eq_one h l hNl, one_mul]
  exact primeFormConjHom_eq_conj h u

private theorem lieCompsCase_unitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ p = 1) (hout : q.p ≠ p ∨ ∀ a : S, MulAut.conj a ≠ β) :
    LieCompsExport q.p β := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := he
  obtain ⟨⟨hℓ, hf, hn3, hq⟩, K, _, _, hK, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e' : S ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h3 => hq (Prod.ext h3.1 h3.2)
  have hC : IsPrimeFormGram (1 : GL (Fin (r + 1)) K) := isPrimeFormGram_idGram
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, hc1, hc⟩ := (hker1 _).1 h1
    have hAp : (A : GL (Fin (r + 1)) K) ^ p =
        Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    by_cases hqp : q.p = p
    ·
      exfalso
      have hout' : ∀ a : S, MulAut.conj a ≠ β := hout.resolve_left (fun h => h hqp)
      obtain ⟨u, hu⟩ := exists_conj_of_pow_scalar h hp hqp A hc1 hAp
      refine hout' (e'.symm (u : primeFormP h (idGram K (r + 1)))) ?_
      apply (MulAut.congr e').injective
      rw [← hA, hu, congr_conj_apply, MulEquiv.apply_symm_apply]
    · have h1 := lieCompsExport_primeFormConjHom slFactorFacts_holds suFactorFacts_holds hp h
        (Ne.symm hqp) A hAp
      rw [hA] at h1
      exact LieCompsExport.of_congr e' h1
  ·
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' hp hp2
        (MulAut.congr e' β) hord _ rfl hσp
    have h1 := lieCompsExport_primeFormFieldHom suFactorFacts_holds hp hp2 h hn3 hC
      (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) hσp
    refine LieCompsExport.of_congr e' ?_
    refine LieCompsExport.of_congr ((primeFormConjHom h (idGram K (r + 1)) M)⁻¹ : MulAut _) ?_
    rw [congr_self_eq, inv_inv, hM]
    exact h1

end Unitary

theorem lieCompsOn_linearUnitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    LieCompsOn p .linearUnitary := by
  intro S _ _ hs hna idx hF he β hβ _ hout
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q => exact lieCompsCase_linear hp hp2 r q hv he β hβ hout
  | twistedA r q => exact lieCompsCase_unitary hp hp2 r q hv he β hβ hout
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
