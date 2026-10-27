module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrderSix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

private theorem eq_one_of_pow_three_eq_one {K : Type} [Field K] [CharP K 3] {x : K}
    (hx : x ^ 3 = 1) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : (x - 1) ^ 3 = 0 := by
    rw [sub_pow_char, hx]
    simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)

private theorem det_eq_one_of_pow_three_eq_one {n : ℕ} {K : Type} [Field K] [CharP K 3]
    {U : GL (Fin n) K} (hU : U ^ 3 = 1) : (U : Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 : (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U) ^ 3 = 1 := by
    rw [← map_pow, hU, map_one]
  have h2 : ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := K) U : Kˣ) : K) ^ 3 = 1 := by
    have := congrArg (fun x : Kˣ => (x : K)) h1
    simpa using this
  have h3 := eq_one_of_pow_three_eq_one h2
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

private theorem exists_conj_of_cube_scalar {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 3) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hc : h.norm (c : K) = 1)
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    ∃ u : gramSU h (idGram K n), u ^ 3 = 1 ∧
      primeFormConjHom h (idGram K n) A = MulAut.conj (u : primeFormP h (idGram K n)) := by
  haveI : Finite K := h.finite
  haveI : CharP K 3 := hℓ ▸ h.charP
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
  have hNl : h.norm (l : K) = 1 := by
    apply eq_one_of_pow_three_eq_one
    have hN : h.norm ((l : K) ^ 3) = (h.norm (l : K)) ^ 3 := by
      simp only [UnitaryFieldData.norm, map_pow, mul_pow]
    rw [← hN, ← Units.val_pow_eq_pow_val, hlc]
    exact hc
  have hs := scalar_mem_primeFormUnitary_one (n := n) h hNl
  set s : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) l with hsdef
  set U : GL (Fin n) K := s⁻¹ * (A : GL (Fin n) K) with hU
  have hUmem : U ∈ primeFormUnitary h (idGram K n) := mul_mem (inv_mem hs) A.2
  have hcomm : Commute s⁻¹ (A : GL (Fin n) K) :=
    (show Commute s (A : GL (Fin n) K) from Matrix.GeneralLinearGroup.scalar_commute l _).inv_left
  have hUcube : U ^ 3 = 1 := by
    rw [hU, hcomm.mul_pow, hA, inv_pow, hsdef, ← map_pow, hlc, inv_mul_cancel]
  have hdetU := det_eq_one_of_pow_three_eq_one hUcube
  let u : gramSU h (idGram K n) := ⟨U, hUmem, hdetU⟩
  refine ⟨u, ?_, ?_⟩
  · apply Subtype.ext
    exact hUcube
  · have hAU : A = ⟨s, hs⟩ * ⟨U, hUmem⟩ := by
      apply Subtype.ext
      change (A : GL (Fin n) K) = s * (s⁻¹ * A)
      rw [mul_inv_cancel_left]
    rw [hAU, map_mul, primeFormConjHom_scalar_eq_one h l hNl, one_mul]
    exact primeFormConjHom_eq_conj h u

private theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem lieCompCase_unitary (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) (hSU : SUFactorFacts) (hSU6 : SUAltSixFacts)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) : LieCompExport q.p β ∨ NoThreeComponents β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact Or.inl (lieCompExport_one hna ⟨.twistedA r q, hv⟩ he
      (isEmpty_mulEquiv_alternating_six hb _ he))
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
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq'
  by_cases hσ : primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β) = 1
  ·
    have hβD : MulAut.congr e' β ∈ (primeFormFieldFactor h hC hn3 hq').ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, hA⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ 3, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hA, hβ', map_one, one_mul]
    obtain ⟨-, c, hc1, hc⟩ := (hker1 _).1 h1
    have hA3 : (A : GL (Fin (r + 1)) K) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c := by
      rwa [SubgroupClass.coe_pow] at hc
    by_cases hq3 : q.p = 3
    ·
      right
      obtain ⟨u, hu3, hu⟩ := exists_conj_of_cube_scalar h hq3 A hc1 hA3
      have hS : IsChevOfChar 3 S :=
        ⟨⟨.twistedA r q, hv⟩, YS08.isChevIndexOfChar_of_lieIndexChar_eq (by
          show q.p = 3
          exact hq3), ⟨e⟩⟩
      set s' := (u : primeFormP h (idGram K (r + 1))) with hs'
      have hβs : β = MulAut.conj (e'.symm s') := by
        apply (MulAut.congr e').injective
        rw [← hA, hu, congr_conj_apply, MulEquiv.apply_symm_apply]
      have hs1 : e'.symm s' ≠ 1 := by
        intro h1
        apply hβ1
        rw [hβs, h1, map_one]
      have hs3 : (e'.symm s') ^ 3 = 1 := by
        rw [← map_pow, hs', ← QuotientGroup.mk_pow, hu3, QuotientGroup.mk_one, map_one]
      rw [hβs]
      exact noThreeComponents_of_conj hQ hs hna hS hs1 hs3
    · left
      have h1 := lieCompExport_primeFormConjHom hSL hA6 hSU hSU6 h hq3 A hA3
      rw [hA] at h1
      exact LieCompExport.of_congr e' h1
  ·
    left
    have hne : MulAut.congr e' β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (MulAut.congr e' β) = 3 := orderOf_eq_prime hβ' hne
    have hσp : orderOf (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hβ', map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hq' Nat.prime_three
        (by norm_num) (MulAut.congr e' β) hord _ rfl hσp
    have h1 := lieCompExport_primeFormFieldHom hSU hSU6 h hn3 hC
      (primeFormFieldFactor h hC hn3 hq' (MulAut.congr e' β)) hσp
    refine LieCompExport.of_congr e' ?_
    refine LieCompExport.of_congr ((primeFormConjHom h (idGram K (r + 1)) M)⁻¹ : MulAut _) ?_
    rw [congr_self_eq, inv_inv, hM]
    exact h1

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
