module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MAmbig
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L4Desc
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoPglFaithful

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.I142M

section D4

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

theorem d4OuterExport_ne3 {G : Type} [Group G] [Finite G] {ℓ f : ℕ} (hℓ3 : ℓ ≠ 3)
    (hG : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaPlus 4 ℓ f) (β : MulAut G)
    (hβ : β ^ 3 = 1) (hout : ∀ a : G, MulAut.conj a ≠ β) : LieCompExport ℓ β := by
  have hG' := hG
  obtain ⟨⟨hℓ, hf, -⟩, F, _, _, hF, ⟨eG⟩⟩ := hG'
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ : G ≃* ↥(adjointGroup Tag.D4 F) := eG.trans eC
  refine lieCompExport_of_compsFine (perfectInLayer_omega_D4_three hG hℓ3 β hβ) ?_
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ MulAut.congr e₂ β := fun h hh => by
    apply hout (e₂.symm h)
    have hc : MulAut.congr e₂.symm (MulAut.conj h) = MulAut.conj (e₂.symm h) := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    rw [← hc, hh]
    ext y
    simp [MulAut.congr_apply]
  exact (compsFine_d4_outer (trialityOddA2Comps_of_toral TriA2.a2PlusComps_holds
      TriA2.a2MinusComps_holds) hℓ3 hf hF (MulAut.congr e₂ β) hα hout').of_mulEquiv
    (fixSubgroupCongrEquiv e₂ β)

end D4

section Lin

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem exists_card_eq_pow_ringChar {K : Type} [Field K] [Finite K] :
    ∃ f : ℕ, 1 ≤ f ∧ (ringChar K).Prime ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨f, hℓ, hK⟩ := FiniteField.card K (ringChar K)
  exact ⟨f, f.pos, hℓ, by rw [Nat.card_eq_fintype_card, hK]⟩

theorem linear_cases_three_of_three_le {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
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

theorem linear_cases_three_two {K : Type} [Field K] [Finite K]
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

theorem congr_conj_apply {S G : Type} [Group S] [Group G] (e : S ≃* G) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_self_eq {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem lieCompCase_linear_ne3
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) (hc3 : q.p ≠ 3) : LieCompExport q.p β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact (lieCompExport_one hna ⟨.A r q, hv⟩ he (isEmpty_mulEquiv_alternating_six hb _ he))
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
    · exfalso
      apply hc3
      have h0 : ((3 : ℕ) : GaloisField q.p q.exponent) = 0 := by exact_mod_cast h3
      rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p] at h0
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h0
    · have h1 := lieCompExport_conjAut hSL hA6 h3 hA
      rw [← hβA, hchar] at h1
      exact LieCompExport.of_congr e' h1
  · have h1 := lieCompExport_fieldAut hSL hA6 (n := r + 1) (by omega) σ hσ
    rw [hchar] at h1
    refine LieCompExport.of_congr e' ?_
    refine LieCompExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβh]
    have : h⁻¹ * (h * LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ * h⁻¹) * h⁻¹⁻¹ =
        LinearFlag.fieldAut (r + 1) (GaloisField q.p q.exponent) σ := by group
    rw [this]
    exact h1

end Lin

section Un

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem lieCompCase_unitary_ne3 (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hSL : SLFactorFacts) (hA6 : SLAltSixFacts) (hSU : SUFactorFacts) (hSU6 : SUAltSixFacts)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) (hc3 : q.p ≠ 3) : LieCompExport q.p β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact (lieCompExport_one hna ⟨.twistedA r q, hv⟩ he
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
    · exact absurd hq3 hc3
    · have h1 := lieCompExport_primeFormConjHom hSL hA6 hSU hSU6 h hq3 A hA3
      rw [hA] at h1
      exact LieCompExport.of_congr e' h1
  ·
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

end Un

section Sp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem exists_statedClassicalModel_psp {S : Type} [Group S]
    (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ r q, idx.1 = .B r q ∧ (q.p = 2 ∨ r = 2)) ∨ ∃ r q, idx.1 = .C r q)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ r f : ℕ, StatedClassicalModel S .PSp r (lieIndexChar idx.1) f := by
  obtain ⟨d, hv⟩ := idx
  rcases hsp with ⟨r, q, hd, hq⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact ⟨2, q.exponent, CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e⟩
    · have hq2 : q.p = 2 := hq.resolve_right (by omega)
      exact ⟨r, q.exponent,
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr3 e⟩
  · dsimp only at hd
    subst hd
    exact ⟨r, q.exponent, CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e⟩

theorem ringChar_eq_of_card {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) : ringChar K = ℓ := by
  haveI := Fintype.ofFinite K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ringChar.eq K ℓ

theorem lieCompCase_symplectic_ne3
    (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (idx : TauCeti.ValidLieTypeIndex)
    (hsp : (∃ r q, idx.1 = .B r q ∧ (q.p = 2 ∨ r = 2)) ∨ ∃ r q, idx.1 = .C r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1) (hc3 : lieIndexChar idx.1 ≠ 3) :
    LieCompExport (lieIndexChar idx.1) β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact (lieCompExport_one hna idx he (isEmpty_mulEquiv_alternating_six hb _ he))
  obtain ⟨e⟩ := he
  obtain ⟨r, f, ⟨hℓ, hf, hr, hne⟩, K, _, _, hK, ⟨e'⟩⟩ :=
    exists_statedClassicalModel_psp idx hsp e
  have hne' : ¬(r = 2 ∧ lieIndexChar idx.1 ^ f = 2) := fun h => hne (Prod.ext h.1 h.2)
  have hβ' : MulAut.congr e' β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf (MulAut.congr e' β)) :=
    (Nat.prime_three.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : MulAut.congr e' β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : MulAut.congr e' β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel
      Nat.prime_three (by norm_num) hD hβ'
    have hβs : β = MulAut.conj (e'.symm t) := by
      apply (MulAut.congr e').injective
      rw [← ht, congr_conj_apply, MulEquiv.apply_symm_apply]
    have hs3 : (e'.symm t) ^ 3 = 1 := by
      have hc : (e'.symm t) ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj ((e'.symm t) ^ 3) = 1 by rw [map_pow, ← hβs]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * (e'.symm t) ^ 3
            = (e'.symm t) ^ 3 * g * ((e'.symm t) ^ 3)⁻¹ * (e'.symm t) ^ 3 := by rw [h1]
          _ = (e'.symm t) ^ 3 * g := by group
      rw [b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    by_cases hℓ3 : lieIndexChar idx.1 = 3
    · exact absurd hℓ3 hc3
    · have ht3 : t ^ 3 = 1 := by
        have := congrArg e' hs3
        rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
      obtain ⟨x, hx, hx3⟩ := LieSemisimple.exists_proj_eq_pow_eq_one_sp (by omega)
        Nat.prime_three (by norm_num) ht3
      have h1 := lieCompExport_conj_sp slFactorFacts_holds slAltSixFacts_holds
        suFactorFacts_holds suAltSixFacts_holds spFactorFacts_holds spAltSixFacts_holds
        spFourTwoFacts_holds hℓ hf hK hr hne' hℓ3 x hx3
      rw [hx, ht] at h1
      exact LieCompExport.of_congr e' h1
  ·
    have hne1 : MulAut.congr e' β ≠ 1 := fun h1 => hD (h1 ▸ one_mem _)
    have hord : orderOf (MulAut.congr e' β) = 3 := orderOf_eq_prime hβ' hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 3 Nat.prime_three _ hE hD hord
    have h1 := lieCompExport_fieldAut_sp spFactorFacts_holds spAltSixFacts_holds
      spFourTwoFacts_holds hr σ hσ
    rw [ringChar_eq_of_card hℓ hK] at h1
    refine LieCompExport.of_congr e' ?_
    refine LieCompExport.of_congr (h⁻¹ : MulAut _) ?_
    rw [congr_self_eq, hβeq]
    have : h⁻¹ * (h * SymplecticHigher.fieldAut r K σ * h⁻¹) * h⁻¹⁻¹ =
        SymplecticHigher.fieldAut r K σ := by group
    rw [this]
    exact h1

end Sp

section Or

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.LowTwoRank

theorem exists_statedClassicalModel_orth {S : Type} [Group S]
    (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t n (lieIndexChar idx.1) f := by
  obtain ⟨d, hv⟩ := idx
  rcases hor with ⟨r, q, hd, hq2, hr3⟩ | ⟨r, q, hd⟩ | ⟨r, q, hd⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaOdd, r, q.exponent, Or.inl rfl,
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq2 hr3 e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaPlus, r, q.exponent, Or.inr (Or.inl rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e⟩
  · dsimp only at hd
    subst hd
    exact ⟨.POmegaMinus, r, q.exponent, Or.inr (Or.inr rfl),
      CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e⟩

theorem lieCompCase_orthogonal_ne3 (hb : LieOrderBridge) (hQ : YS08.LieQ.LieQConstrainedInner 3)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hor : (∃ r q, idx.1 = .B r q ∧ q.p ≠ 2 ∧ 3 ≤ r) ∨ (∃ r q, idx.1 = .D r q) ∨
      ∃ r q, idx.1 = .twistedD r q)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 3 = 1) (hc3 : lieIndexChar idx.1 ≠ 3) :
    LieCompExport (lieIndexChar idx.1) β := by
  haveI := hs
  by_cases hβ1 : β = 1
  · subst hβ1
    exact (lieCompExport_one hna idx he (isEmpty_mulEquiv_alternating_six hb _ he))
  obtain ⟨e⟩ := he
  obtain ⟨t, n, f, ht, hG⟩ := exists_statedClassicalModel_orth idx hor e
  by_cases hin : ∃ a : S, MulAut.conj a = β
  ·
    obtain ⟨a, rfl⟩ := hin
    have ha3 : a ^ 3 = 1 := by
      have hc : a ^ 3 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut S => φ g)
          (show MulAut.conj (a ^ 3) = 1 by rw [map_pow]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * a ^ 3 = a ^ 3 * g * (a ^ 3)⁻¹ * a ^ 3 := by rw [h1]
          _ = a ^ 3 * g := by group
      rw [b3Lie_center_eq_bot hna, Subgroup.mem_bot] at hc
      exact hc
    by_cases hℓ3 : lieIndexChar idx.1 = 3
    · exact absurd hℓ3 hc3
    · exact lieCompExport_conj_omega slFactorFacts_holds slAltSixFacts_holds suFactorFacts_holds
        suAltSixFacts_holds omegaFactorFacts_holds omegaAltSixFacts_holds ht hG hℓ3 a ha3
  ·
    have hout : ∀ a : S, MulAut.conj a ≠ β := fun a h => hin ⟨a, h⟩
    by_cases hd4 : t = .POmegaPlus ∧ n = 4
    · obtain ⟨rfl, rfl⟩ := hd4
      exact d4OuterExport_ne3 hc3 hG β hβ hout
    · exact lieCompExport_omega_outer omegaFactorFacts_holds omegaAltSixFacts_holds ht hG hd4 β hβ
        hout

end Or

section Ex

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md42047359a2a

theorem lieCompExport_exceptional_ne3 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hF : lieFamily idx.1 = .exceptional) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (h3 : lieIndexChar idx.1 ≠ 3) (β : MulAut S) (hβ : β ^ 3 = 1) :
    LieCompExport (lieIndexChar idx.1) β := by
  classical
  have hres : ExcRationalLieTypes :=
    excRationalLieTypes_of_residualsD excRationalLieTypesOuterD_proved excRationalLieTypesF4Two_holds
  have hout : TrialityOuterExport := trialityOuterExport_of (trialityOddA2Comps_of_toral
      TriA2.a2PlusComps_holds TriA2.a2MinusComps_holds)
  have hnotree : ∀ m, idx.1 ≠ .reeG2 m := fun m h => by simp [lieFamily, h] at hF
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨e⟩ := he
    haveI := hs
    exact (lieCompExport_one hna idx ⟨e⟩
      ⟨fun f => (isEmpty_cat_alt6 idx (Or.inl hF)).false (e.symm.trans f)⟩)
  obtain ⟨e⟩ := he
  have hlayer : PerfectInLayer β :=
    lieSemisimpleCentExceptional S hs hna idx hF ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (fun h => h3 (by rw [← characteristic_eq_lieIndexChar]; exact h.symm)) β hβ hβ1
  have hmon : ∀ {τ : Tag}, (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      MonomialToralAt τ 3 := fun hτ =>
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ Nat.prime_three
      (by norm_num)
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | E7 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | E8 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | F4 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .F4) (Or.inr (Or.inl rfl))
      (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | G2 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .G2) (Or.inl rfl)
      (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
      (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
      (fun q hv => isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | twistedE6 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_twE6 hres
      (fun q hv => isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩ (Or.inl rfl))
      (hmon (by simp)) q hv hq3 e β hβ hβ1 hlayer
  | trialityD4 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_triD4 hres hout (hmon (by simp)) q hv hq3 e β hβ hβ1 hlayer
  | _ => simp [lieFamily] at hF

end Ex

section SRT

open CFSG.Open CFSG.Blueprint CFSG.Yardstones.Md42047359a2a

theorem lieCompExport_srt_ne3 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hF : lieFamily idx.1 = .suzukiReeTits) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (h3 : lieIndexChar idx.1 ≠ 3) (β : MulAut S) (hβ : β ^ 3 = 1) :
    LieCompExport (lieIndexChar idx.1) β := by
  classical
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨e⟩ := he
    haveI := hs
    refine (lieCompExport_one hna idx ⟨e⟩ ⟨fun f => ?_⟩)
    obtain ⟨d, hv⟩ := idx
    cases d with
    | reeG2 m => exact (isEmpty_cat_alt6_reeG2 m hv).false (e.symm.trans f)
    | _ =>
      exact (isEmpty_cat_alt6 ⟨_, hv⟩ (Or.inr ⟨hF, fun m h => by simp at h⟩)).false
        (e.symm.trans f)
  obtain ⟨d, hv⟩ := idx
  cases d with
  | suzuki m =>
    exact (srtOut_suzuki m hv he Nat.prime_three (by norm_num) hβ hβ1).full lieOrderBridge_holds
  | tits =>
    haveI := hs
    exact (srtOut_tits hv hna he Nat.prime_three (by norm_num) hβ hβ1).full lieOrderBridge_holds
  | reeF4 m =>
    exact lieCompExport_reeF4 m hv he hβ hβ1
  | reeG2 m =>
    exact absurd (by simp [lieIndexChar]) h3
  | _ => simp [lieFamily] at hF

end SRT

section Fin

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem lieCompExportNe3_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
        lieIndexChar idx.1 ≠ 3 → ∀ β : MulAut S, β ^ 3 = 1 → LieCompExport (lieIndexChar idx.1) β := by
  intro S _ _ hs hna idx he h3 β hβ
  have hb := lieOrderBridge_holds
  have hQ := YS08.LieQ.lieQConstrainedInner_three_holds
  match hF : CFSG.Yardstones.Md42047359a2a.lieFamily idx.1 with
  | .exceptional => exact lieCompExport_exceptional_ne3 hs hna idx hF he h3 β hβ
  | .suzukiReeTits => exact lieCompExport_srt_ne3 hs hna idx hF he h3 β hβ
  | .linearUnitary =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      exact lieCompCase_linear_ne3 hb hQ slFactorFacts_holds slAltSixFacts_holds hs hna r q hv he β hβ
        (by simpa [lieIndexChar] using h3)
    | twistedA r q =>
      exact lieCompCase_unitary_ne3 hb hQ slFactorFacts_holds slAltSixFacts_holds suFactorFacts_holds
        suAltSixFacts_holds hs hna r q hv he β hβ (by simpa [lieIndexChar] using h3)
    | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF
  | .symplecticOrthogonal =>
    obtain ⟨d, hv⟩ := idx
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    cases d with
    | B r q =>
      by_cases hsp : q.p = 2 ∨ r = 2
      · exact lieCompCase_symplectic_ne3 hb hQ hs hna ⟨_, hv⟩ (Or.inl ⟨r, q, rfl, hsp⟩) he β hβ h3
      · push_neg at hsp
        exact lieCompCase_orthogonal_ne3 hb hQ hs hna ⟨_, hv⟩
          (Or.inl ⟨r, q, rfl, hsp.1, by simp only at hr; omega⟩) he β hβ h3
    | C r q => exact lieCompCase_symplectic_ne3 hb hQ hs hna ⟨_, hv⟩ (Or.inr ⟨r, q, rfl⟩) he β hβ h3
    | D r q =>
      exact lieCompCase_orthogonal_ne3 hb hQ hs hna ⟨_, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩)) he β hβ h3
    | twistedD r q =>
      exact lieCompCase_orthogonal_ne3 hb hQ hs hna ⟨_, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩)) he β hβ h3
    | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end Fin

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.I142M

namespace CFSG.LocalAnalysis.GLTheoremA.I142M.Three

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I142
open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def ChevCompTypes : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple 2 S → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 →
      ∀ K : Subgroup S, IsComponentOf K (centFix (Subgroup.zpowers β)) →
        IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)

theorem chevCompTypes_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hchar : idx.1.characteristic = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) (K : Subgroup S)
    (hK : IsComponentOf K (centFix (Subgroup.zpowers β))) :
    IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) := by
  have hq : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar idx.1 = 2 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieIndexChar_eq_characteristic, hchar]
  have h := CFSG.LocalAnalysis.GLTheoremA.lieCompsOn_holds hp hp5 (CFSG.Yardstones.Md42047359a2a.lieFamily idx.1) S hS hnc
    idx rfl he β hβ hβ1 (Or.inl (by rw [hq]; omega))
  rw [centFix_zpowers] at hK
  obtain ⟨X, _, _, hX, f, hf, hk⟩ := h.comps K hK
  have := (hX.lieCompData f hf hk).chev
  rwa [hq] at this

theorem chevCompTypes_three (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hchar : idx.1.characteristic = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (β : MulAut S) (hβ : β ^ 3 = 1) (K : Subgroup S)
    (hK : IsComponentOf K (centFix (Subgroup.zpowers β))) :
    IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) := by
  have hq : CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar idx.1 = 2 := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieIndexChar_eq_characteristic, hchar]
  have h := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.I142M.lieCompExportNe3_holds S hS hnc
    idx he (by rw [hq]; norm_num) β hβ
  rw [centFix_zpowers] at hK
  obtain ⟨X, _, _, hX, f, hf, hk⟩ := h.comps K hK
  have := (hX.lieCompData f hf hk).chev
  rwa [hq] at this

theorem chevCompTypes_onLie {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S : Type) [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (hchar : idx.1.characteristic = 2) (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group))
    (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) (K : Subgroup S)
    (hK : IsComponentOf K (centFix (Subgroup.zpowers β))) :
    IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K) := by
  by_cases h3 : p = 3
  · subst h3
    exact chevCompTypes_three S hS hnc idx hchar he β hβ K hK
  · have hp5 : 5 ≤ p := by
      have := hp.two_le
      rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h h3
      · exact absurd (h ▸ hp) (by decide)
      · exact h
    exact chevCompTypes_ge_five hp hp5 S hS hnc idx hchar he β hβ hβ1 K hK

def ChevCompTypesAmbig : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (ambiguousChev 2) → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 →
      ∀ K : Subgroup S, IsComponentOf K (centFix (Subgroup.zpowers β)) →
        IsChevSimple 2 (↥K ⧸ Subgroup.center ↥K)

theorem chevCompTypes_of_ambig (hA : ChevCompTypesAmbig) : ChevCompTypes := by
  intro S _ _ hS hnc hchev p hp hp2 β hβ hβ1 K hK
  rcases hchev with ⟨i, hi, he⟩ | hamb
  · cases i with
    | lie idx =>
      exact chevCompTypes_onLie hp hp2 S hS hnc idx hi he β hβ hβ1 K hK
    | _ => simp [onLie] at hi
  · exact hA S hS hnc hamb p hp hp2 β hβ hβ1 K hK

section Full

theorem chevCompTypes_holds : ChevCompTypes :=
  chevCompTypes_of_ambig CFSG.LocalAnalysis.GLTheoremA.I142M.Ambig.chevCompTypesAmbig_holds'

end Full

end CFSG.LocalAnalysis.GLTheoremA.I142M.Three
