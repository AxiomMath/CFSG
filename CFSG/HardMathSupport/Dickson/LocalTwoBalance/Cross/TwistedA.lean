module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Split
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniHeisSplit
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossUniOuter

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem uniHeisenbergPlaneBalanceOdd_holds :
    ∀ (ℓ f n : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K), 3 ≤ n →
      ¬(n = 3 ∧ ℓ ^ f = 2) → ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ ℓ → p ∣ ℓ ^ f + 1 → 3 < ℓ ^ f →
        p ∣ n → n ≠ p → UniHeisPlane h n p := by
  intro ℓ f n K _ h hn hne p hp hp2 hpℓ hpq hq3 hpn hnp A B c hc1 hcp hAB hAp hBp hA1 hBA H hH _hN
  have hn2p : 2 * p ≤ n := by
    obtain ⟨s, hs⟩ := hpn
    have hs0 : s ≠ 0 := by rintro rfl; omega
    have hs1 : s ≠ 1 := by rintro rfl; omega
    have : 2 ≤ s := by omega
    rw [hs]
    calc 2 * p ≤ s * p := Nat.mul_le_mul_right p this
      _ = p * s := Nat.mul_comm s p
  obtain ⟨A0, B0, c', hc'1, hc'p, hAB', hA0p, hA01, hA0E, hB0E⟩ :=
    exists_split_heis_pair hn hne hp hp2 hpq hc1 hcp hAB hAp hBp hA1 hBA
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_localDeltaIn_heis hn hne hq3 hp hp2 hpq hn2p hc'1 hc'p hAB' hA0p hA01 hH
    hA0E hB0E hg

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem exists_fieldCore_unitary_outer_odd (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hex : p = 3 → ¬(n = 3 ∧ ℓ ^ f = 8)) (hpℓ : p ≠ ℓ)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDl : ¬ D ≤ primeFormD h (idGram K n)) :
    ∃ x ∈ D, x ∉ primeFormD h (idGram K n) ∧ FieldCoreAt p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hfin := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_idGram
  obtain ⟨x, hxD, hxl⟩ := Set.not_subset.mp hDl
  have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
  have hxp : x ^ p = 1 := hD.2 x hxD
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  set π := primeFormFieldFactor h hC hn hne with hπ
  have hσ1 : π x ≠ 1 := fun h1 => hxl (by
    rw [← ker_primeFormFieldFactor h hC hn hne]
    exact h1)
  have hσp : (π x) ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hσord : orderOf (π x) = p := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hne hp hp2
      x hxord (π x) rfl hσord
  set u := primeFormConjHom h (idGram K n) M with hu
  set σ := π x with hσ
  set δ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hδ
  have hxh : x = u * δ * u⁻¹ := by
    have : u⁻¹ * x * u = δ := hM
    rw [← this]
    group
  refine ⟨x, hxD, hxl, ?_⟩
  suffices hfc : FieldCoreAt p δ from fieldCoreAt_of_conj hfc u⁻¹ (by rw [hxh]; group)
  obtain ⟨hpf, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσord
  have hqp : ℓ ^ f = (ℓ ^ (f / p)) ^ p := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  by_cases hpg : p ∣ Nat.gcd n (ℓ ^ f + 1)
  ·
    have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
    have hnp : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have hnexc : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
      rintro ⟨h1, h2⟩
      rcases hp35 with hp3 | hp5
      · refine hex hp3 ⟨h1, ?_⟩
        rw [hqp, h2, hp3]
        norm_num
      · omega
    exact fieldCoreAt_fieldHom_of_subfield h hp hp2 hσord hn hne hnexc
      (dvd_card_range_of_dvd_q h hp hp2 hσord hn hpq)
  ·
    have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
      (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
    have hZ : ¬ p ∣ Nat.card (normOneScalars h
        (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
      rw [card_normOneScalars_one h (by omega)]
      exact hpg
    obtain ⟨-, -, -, -, -, -, hrange, -, -, -, hexc⟩ :=
      prime_subfield_fixed_group_package h hp hp2 hσord n hn hne hZ
    have hDpow : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hD.2 x x.2)
    have : IsCyclic (K ≃+* K) :=
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
    set π' : D →* (K ≃+* K) := π.comp D.subtype with hπ'
    have hπne : π' ≠ 1 := by
      intro h1
      apply hσ1
      have := congrArg (fun φ : D →* (K ≃+* K) => φ ⟨x, hxD⟩) h1
      simpa [hπ'] using this
    obtain ⟨hker, -⟩ := CFSG.RankThree.PartOne.card_ker_eq_prime_of_ne_one hp hDpow hcard π' hπne
    obtain ⟨y', hy'k, hy'1⟩ : ∃ y' ∈ π'.ker, y' ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : π'.ker = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
      rw [hbot, Subgroup.card_bot] at hker
      exact hp.one_lt.ne hker
    set y : MulAut (primeFormP h (idGram K n)) := (y' : MulAut (primeFormP h (idGram K n)))
      with hy
    have hyD : y ∈ D := y'.2
    have hy1 : y ≠ 1 := fun h1 => hy'1 (Subtype.ext h1)
    have hyp : y ^ p = 1 := hD.2 y hyD
    have hyDu : y ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h hC hn hne]
      exact hy'k
    have hyin : y ∈ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range :=
      CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn hne hp hpg hyDu hyp
    have hcomm : y * x = x * y := congrArg Subtype.val
      (hD.1.is_comm.comm ⟨y, hyD⟩ ⟨x, hxD⟩)
    obtain ⟨k, hkδ, hkord⟩ := exists_fixed_orderOf_of_canonical_conj hp hinj hxh hyin hy1 hyp hcomm
    have hkJ : k ∈ fieldFixedPSU h n σ := hkδ
    have hnexc : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := by
      intro hex'
      rcases hp35 with hp3 | hp5
      ·
        refine hpg ?_
        rw [hqp, hex'.2, hex'.1, hp3]
        norm_num
      · obtain ⟨-, hord72⟩ := hexc hex' (by omega)
        exact hord72 k hkJ hkord
    have hJp : p ∣ Nat.card (primeSubfieldPSU h hp hp2 hσord n).range := by
      rw [hrange]
      have : orderOf (⟨k, hkJ⟩ : fieldFixedPSU h n σ) = p := by
        rw [Subgroup.orderOf_mk]
        exact hkord
      rw [← this]
      exact orderOf_dvd_natCard _
    exact fieldCoreAt_fieldHom_of_subfield h hp hp2 hσord hn hne hnexc hJp

theorem localDeltaIn_eq_bot_of_le_primeFormD_plane_odd (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {h : UnitaryFieldData ℓ f K} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5)
    (hq2 : p = 3 → ℓ ^ f ≠ 2) (hpℓ : p ≠ ℓ)
    (hHeis : p ∣ ℓ ^ f + 1 → p ∣ n → UniHeisPlane h n p)
    {D : Subgroup (MulAut (primeFormP h (idGram K n)))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDl : D ≤ primeFormD h (idGram K n))
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hDH : D ≤ Subgroup.normalizer (H : Set (MulAut (primeFormP h (idGram K n))))) :
    localDeltaIn p H D = ⊥ := by
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  by_cases hpg : p ∣ Nat.gcd n (ℓ ^ f + 1)
  · have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
    have hq3 : 3 < ℓ ^ f := by
      have := Nat.le_of_dvd (by omega) hpq
      rcases hp35 with hp3 | hp5
      · have := hq2 hp3
        rw [hp3] at hpq
        omega
      · omega
    obtain ⟨A, B, c, hAD, hBD, hA1, hBA, hAB, hcp, -, -⟩ :=
      exists_plane_lifts_unitary hn hne hp hD hcard hDl
    have hED : Subgroup.closure {primeFormConjHom h (idGram K n) A,
        primeFormConjHom h (idGram K n) B} ≤ D := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hAD
      · exact hBD
    have hAp : primeFormConjHom h (idGram K n) A ^ p = 1 := hD.2 _ hAD
    have hBp : primeFormConjHom h (idGram K n) B ^ p = 1 := hD.2 _ hBD
    by_cases hc1 : c = 1
    · subst hc1
      have hABc : A * B = B * A := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hAB, map_one, mul_one]
      have hbot := localDeltaIn_eq_bot_of_unitary_plane hn hne hq3 hp hp2 hpq hABc hAp hBp hA1
        hBA hH
      exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)
    · have hbot := hHeis hpq hpn A B c hc1 hcp hAB hAp hBp hA1 hBA H hH (hED.trans hDH)
      exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)
  · have hDin : D ≤ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range := fun d hd =>
      mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin n) K) hp hpg (hDl hd) (hD.2 d hd)
    have hEel : CFSG.IsElementaryAbelian p D :=
      { toIsMulCommutative := hD.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hD.2 x x.2) }
    exact localDeltaIn_eq_bot_primeFormP h hn hne hp hp2 hpℓ hpg
      (fun ⟨h3, h4⟩ => hq2 h3 h4) D hDin hEel hcard hH

theorem isLocallyBalancedAbs_two_primeFormP_odd (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime) (hp35 : p = 3 ∨ p = 5) (hq2 : p = 3 → ℓ ^ f ≠ 2)
    (hex : p = 3 → ¬(n = 3 ∧ ℓ ^ f = 8)) (hpℓ : p ≠ ℓ)
    (hHeis : p ∣ ℓ ^ f + 1 → p ∣ n → UniHeisPlane h n p) :
    IsLocallyBalancedAbs p 2 (primeFormP h (idGram K n)) := by
  classical
  have hfin := h.finite
  have : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hinj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
  intro D hD hcard H hH hDH
  by_cases hDl : D ≤ primeFormD h (idGram K n)
  · exact localDeltaIn_eq_bot_of_le_primeFormD_plane_odd hn hne hp hp35 hq2 hpℓ hHeis hD hcard
      hDl hH hDH
  · obtain ⟨x, hxD, hxl, hfc⟩ :=
      exists_fieldCore_unitary_outer_odd h hn hne hp hp35 hex hpℓ hD hcard hDl
    have hx1 : x ≠ 1 := fun h1 => hxl (h1 ▸ one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore hp hinj hH hxD hx1 hfc

@[expose] def regimeUOdd (p : ℕ) (idx : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (m : ℕ) (q : TauCeti.PrimePower), idx.1 = .twistedA m q ∧ (p = 3 → q.card ≠ 2)

theorem localTwoCrossFamAt_twistedA_odd (p : ℕ) (hp : p = 3 ∨ p = 5) :
    LocalTwoCrossFamAt p .twistedA (regimeUOdd p) := by
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  rintro ⟨d, hv⟩ hk hR hc hnexc
  obtain ⟨r, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  obtain ⟨r', q', hd', hq2c⟩ := hR
  obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj hd'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (CatT ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  have hq2 : p = 3 → q.p ^ q.exponent ≠ 2 := fun h3 h2 =>
    hq2c h3 (by rw [TauCeti.PrimePower.card_def]; exact h2)
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : CatT ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hex : p = 3 → ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 8) := by
    rintro hp3 ⟨h1, h2⟩
    have hLp : IsLpEpsIndex p (TauCeti.LieTypeIndex.twistedA r q) :=
      Or.inr ⟨q, by rw [hp3, show r = 2 by omega], by
        rw [TauCeti.PrimePower.card_def, h2, hp3]⟩
    exact (hnexc ⟨.twistedA r q, hv⟩ hLp).false (MulEquiv.refl _)
  refine IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_primeFormP_odd h (by omega) hq' hpp hp hq2 hex hpq ?_)
  intro h1 h2
  have hrp : r + 1 ≠ p := by
    intro hrp
    have hLp : IsLpEpsIndex p (TauCeti.LieTypeIndex.twistedA r q) :=
      Or.inr ⟨q, by rw [show r = p - 1 by omega], Nat.mod_eq_zero_of_dvd (by
        rw [TauCeti.PrimePower.card_def]; exact h1)⟩
    exact (hnexc ⟨.twistedA r q, hv⟩ hLp).false (MulEquiv.refl _)
  have hq3 : 3 < q.p ^ q.exponent := by
    have := Nat.le_of_dvd (by omega) h1
    rcases hp with hp3 | hp5
    · have := hq2 hp3
      rw [hp3] at h1
      omega
    · omega
  exact uniHeisenbergPlaneBalanceOdd_holds q.p q.exponent (r + 1) K h
    (by have := Nat.le_of_dvd (by omega) h2; omega) hq' p hpp (by omega) hpq h1 hq3 h2 hrp

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
