module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433Reduction
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankCarrier

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

open CFSG.Open CFSG.Assembly.RankThreeEven CFSG.Yardstones.Md42047359a2a TauCeti
open scoped MatrixGroups

theorem card_center_eq_three_pow {K : Type} [Group K] [Finite K] (h : GLAPPrimeCore 3 K = ⊥) :
    ∃ a : ℕ, Nat.card (Subgroup.center K) = 3 ^ a := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro ℓ hℓ hdvd
  by_contra hne
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) ℓ hdvd
  have hz' : orderOf (z : K) = ℓ := by rw [Subgroup.orderOf_coe]; exact hz
  have hnorm : (Subgroup.zpowers (z : K)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ z.2 m) g, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers_iff.2 ⟨m, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers (z : K))) := by
    rw [Nat.card_zpowers, hz']
    exact (Nat.coprime_primes Nat.prime_three hℓ).2 (Ne.symm hne)
  have hle : Subgroup.zpowers (z : K) ≤ GLAPPrimeCore 3 K := le_sSup ⟨hnorm, hcop⟩
  rw [h] at hle
  have hz1 : (z : K) = 1 := by simpa using hle (Subgroup.mem_zpowers (z : K))
  rw [hz1, orderOf_one] at hz'
  exact hℓ.one_lt.ne hz'

def centerThree (K : Type) [Group K] : Subgroup K where
  carrier := {x | x ∈ Subgroup.center K ∧ x ^ 3 = 1}
  mul_mem' {a b} ha hb :=
    ⟨mul_mem ha.1 hb.1, by
      rw [Commute.mul_pow (Subgroup.mem_center_iff.1 hb.1 a), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow 3⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem centerThree_le_center (K : Type) [Group K] : centerThree K ≤ Subgroup.center K :=
  fun _ hx => hx.1

theorem false_of_cover_lift {X : Type} [Group X] [Finite X] {K Q₁ Q J : Subgroup X} {t : X}
    {q : ℕ} (c : I1433Cfg K Q₁ Q J t q) {S : Type} [Group S] {π : ↥K →* S}
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center ↥K) (hL : LiftDatum S 3) :
    False := by
  obtain ⟨a, ha⟩ := card_center_eq_three_pow c.primeCore_K
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker, ha]
    exact Odd.pow (by decide)
  have hdvd : Nat.card (centerThree ↥K) ∣ 3 ^ a :=
    ha ▸ Subgroup.card_dvd_of_le (centerThree_le_center ↥K)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hrank : 3 + 1 + k ≤ localRank 3 ↥K :=
    hL.cover_localRank hπ hker.le hodd (A := centerThree ↥K)
      (by rw [hker]; exact centerThree_le_center _) (fun x hx => hx.2) hk
  have hZx : Nat.card ((centerThree ↥K).map K.subtype) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hk
  have hp : CFSG.Open.pRank 3 ((Subgroup.center ↥K).map K.subtype) ≤ k := by
    unfold CFSG.Open.pRank
    refine csSup_le' ?_
    rintro j ⟨E, hEle, hE, hEj⟩
    have hEA : E ≤ (centerThree ↥K).map K.subtype := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 (hEle hx)
      refine Subgroup.mem_map.2 ⟨z, ⟨hz, K.subtype_injective ?_⟩, rfl⟩
      rw [map_pow, map_one]
      exact hE.2 _ hx
    have hd : Nat.card E ∣ Nat.card ((centerThree ↥K).map K.subtype) :=
      Subgroup.card_dvd_of_le hEA
    rw [hEj, hZx] at hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
  have h1 : localRank 3 ↥K ≤ CFSG.Open.pRank 3 ((Subgroup.center ↥K).map K.subtype) + 3 :=
    c.rank_le
  omega

theorem exists_cover {K S : Type} [Group K] [Group S] (e : (K ⧸ Subgroup.center K) ≃* S) :
    ∃ π : K →* S, Function.Surjective π ∧ π.ker = Subgroup.center K := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext y
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (Subgroup.center K) y) = 1 ↔ _
  rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem card_fixedField_eq (d : ValidLieTypeIndex) [Fintype d.fixedField] :
    Fintype.card d.fixedField = d.fieldOrder := by
  rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]

theorem ringChar_fixedField_eq (d : ValidLieTypeIndex) [Fintype d.fixedField] :
    ringChar d.fixedField = d.characteristic := by
  haveI : Fact d.characteristic.Prime := ⟨d.characteristic_prime⟩
  haveI : CharP d.fixedField d.characteristic :=
    charP_of_card_eq_prime_pow (f := d.fieldExponent)
      (by rw [card_fixedField_eq, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow])
  exact ringChar.eq _ _

theorem liftDatum_of_commuting_SL2 (d : ValidLieTypeIndex) [Fintype d.fixedField] {S : Type*}
    [Group S] {m : ℕ} (φ : Fin (m + 1) → SL(2, d.fixedField) →* S)
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.fixedField), φ i A * φ j B = φ j B * φ i A)
    (h3 : d.characteristic ≠ 3) (hcond : d.characteristic ≠ 2 ∨ 3 ∣ d.fieldOrder - 1) :
    LiftDatum S m := by
  rcases hcond with h2 | h2
  · exact liftDatum_of_commuting_SL2_odd (by rwa [ringChar_fixedField_eq]) (by
      rwa [ringChar_fixedField_eq]) φ hφ hcomm
  · by_cases hc : d.characteristic = 2
    · refine liftDatum_of_commuting_SL2_even (by rwa [ringChar_fixedField_eq]) ?_ φ hφ hcomm
      rwa [card_fixedField_eq]
    · exact liftDatum_of_commuting_SL2_odd (by rwa [ringChar_fixedField_eq]) (by
        rwa [ringChar_fixedField_eq]) φ hφ hcomm

theorem three_dvd_two_pow_sub_one_of_even {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have := Nat.one_le_two_pow (n := k + k)
  omega

theorem pow_mod_three_of_not_dvd {q : PrimePower} (h2 : q.p = 2)
    (hn3 : ¬ 3 ∣ q.p ^ q.exponent - 1) : q.p ^ q.exponent % 3 = 2 := by
  rcases Nat.even_or_odd q.exponent with he | ⟨k, hk⟩
  · exact absurd (by rw [h2]; exact three_dvd_two_pow_sub_one_of_even he) hn3
  · rw [h2, hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num

theorem split_cond_of_not_small (q : PrimePower) (h : ¬ (q.p = 2 ∧ Odd q.exponent)) :
    q.p ≠ 2 ∨ 3 ∣ q.p ^ q.exponent - 1 := by
  by_cases hp : q.p = 2
  · right
    have he : Even q.exponent := by
      rcases Nat.even_or_odd q.exponent with h' | h'
      · exact h'
      · exact absurd ⟨hp, h'⟩ h
    rw [hp]
    exact three_dvd_two_pow_sub_one_of_even he
  · exact Or.inl hp

section Families


theorem e6_liftDatum (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) (hp3 : q.p ≠ 3) :
    LiftDatum (CFSGIndex.lie ⟨.E6 q, hv⟩).Group 3 := by
  set d : ValidLieTypeIndex := ⟨.E6 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_E6 q
  by_cases h2 : q.p = 2
  · exact e6_liftDatum_even' q hv (by rw [ringChar_fixedField_eq, hchar]; exact h2)
  · obtain ⟨φ, hinj, hcomm⟩ := e6_commuting_SL2' q hv
    exact liftDatum_of_commuting_SL2 d (m := 3) φ hinj hcomm (by rwa [hchar])
      (Or.inl (by rwa [hchar]))

theorem e7_liftDatum (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) (hp3 : q.p ≠ 3) :
    LiftDatum (CFSGIndex.lie ⟨.E7 q, hv⟩).Group 3 := by
  set d : ValidLieTypeIndex := ⟨.E7 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_E7 q
  obtain ⟨φ, hinj, hcomm⟩ := e7_commuting_SL2' q hv
  by_cases h2 : q.p = 2
  · exact liftDatum_of_five_commuting_SL2_even
      (by rw [ringChar_fixedField_eq, hchar]; exact h2) φ hinj hcomm
  · exact liftDatum_of_commuting_SL2 d (m := 3) (fun i => φ i.castSucc) (fun i => hinj _)
      (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B)
      (by rwa [hchar]) (Or.inl (by rwa [hchar]))

theorem e8_liftDatum (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hp3 : q.p ≠ 3) :
    LiftDatum (CFSGIndex.lie ⟨.E8 q, hv⟩).Group 3 := by
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_E8 q
  obtain ⟨φ, hinj, hcomm⟩ := e8_commuting_SL2 q hv
  by_cases h2 : q.p = 2
  · exact liftDatum_of_five_commuting_SL2_even
      (by rw [ringChar_fixedField_eq, hchar]; exact h2) φ hinj hcomm
  · exact liftDatum_of_commuting_SL2 d (m := 3) (fun i => φ i.castSucc) (fun i => hinj _)
      (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B)
      (by rwa [hchar]) (Or.inl (by rwa [hchar]))

theorem f4_liftDatum (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) (hp3 : q.p ≠ 3)
    (hq : ¬ (q.p = 2 ∧ Odd q.exponent)) : LiftDatum (CFSGIndex.lie ⟨.F4 q, hv⟩).Group 3 := by
  set d : ValidLieTypeIndex := ⟨.F4 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_F4 q
  have hfo : d.fieldOrder = q.p ^ q.exponent :=
    (LieTypeIndex.fieldOrder_F4 q).trans (PrimePower.card_def q)
  obtain ⟨φ, hinj, hcomm⟩ := f4_commuting_SL2 q hv
  exact liftDatum_of_commuting_SL2 d (m := 3) φ hinj hcomm (by rwa [hchar])
    (by rw [hchar, hfo]; exact split_cond_of_not_small q hq)

theorem twistedE6_liftDatum (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hp3 : q.p ≠ 3) : LiftDatum (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group 3 := by
  set d : ValidLieTypeIndex := ⟨.twistedE6 q, hv⟩ with hd
  haveI := finite_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  have hchar : d.characteristic = q.p := LieTypeIndex.characteristic_twistedE6 q
  have hfo : d.fieldOrder = q.p ^ q.exponent :=
    (LieTypeIndex.fieldOrder_twistedE6 q).trans (PrimePower.card_def q)
  by_cases hcond : q.p ≠ 2 ∨ 3 ∣ q.p ^ q.exponent - 1
  · obtain ⟨φ, hinj, hcomm⟩ := twistedE6_commuting_SL2' q hv
    exact liftDatum_of_commuting_SL2 d (m := 3) φ hinj hcomm (by rwa [hchar])
      (by rwa [hchar, hfo])
  · push Not at hcond
    obtain ⟨h2, hn3⟩ := hcond
    exact twistedE6_liftDatum_even' q hv (by rw [ringChar_fixedField_eq, hchar]; exact h2)
      (pow_mod_three_of_not_dvd h2 hn3)

end Families

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Assembly.RankThreeEven
  CFSG.Yardstones.Md42047359a2a TauCeti
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

@[expose] def ExcSmallIndex : TauCeti.LieTypeIndex → Prop
  | .G2 _ => True
  | .trialityD4 _ => True
  | .F4 q => q.p = 2 ∧ Odd q.exponent
  | _ => False

@[expose] def NonD4LieContraOnExcSmall : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K Q₁ Q J : Subgroup X) (t : X) (q p : ℕ),
    I1433Cfg K Q₁ Q J t q → p.Prime → p ≠ 3 →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .exceptional → ExcSmallIndex idx.1 →
      IsChevIndexOfChar p idx.1 →
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ¬ IsD4Simple (↥K ⧸ Subgroup.center ↥K) → False

section Final


theorem nonD4LieContraOn_exceptional_of_small (h : NonD4LieContraOnExcSmall) :
    NonD4LieContraOn .exceptional := by
  intro X _ _ K Q₁ Q J t q p c hp hp3 idx hfam hchev he hnD4
  by_cases hs : ExcSmallIndex idx.1
  · exact h X K Q₁ Q J t q p c hp hp3 idx hfam hs hchev he hnD4
  · obtain ⟨e⟩ := he
    obtain ⟨π, hπs, hker⟩ := exists_cover e
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A n q' => simp [lieFamily] at hfam
    | twistedA n q' => simp [lieFamily] at hfam
    | B n q' => simp [lieFamily] at hfam
    | C n q' => simp [lieFamily] at hfam
    | D n q' => simp [lieFamily] at hfam
    | twistedD n q' => simp [lieFamily] at hfam
    | suzuki m => simp [lieFamily] at hfam
    | reeG2 m => simp [lieFamily] at hfam
    | reeF4 m => simp [lieFamily] at hfam
    | tits => simp [lieFamily] at hfam
    | G2 q' => exact absurd (by simp [ExcSmallIndex]) hs
    | trialityD4 q' => exact absurd (by simp [ExcSmallIndex]) hs
    | E6 q' =>
      have hp' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
      exact false_of_cover_lift c hπs hker (e6_liftDatum q' hv (hp' ▸ hp3))
    | E7 q' =>
      have hp' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
      exact false_of_cover_lift c hπs hker (e7_liftDatum q' hv (hp' ▸ hp3))
    | E8 q' =>
      have hp' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
      exact false_of_cover_lift c hπs hker (e8_liftDatum q' hv (hp' ▸ hp3))
    | F4 q' =>
      have hp' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
      have hsm : ¬ (q'.p = 2 ∧ Odd q'.exponent) := fun hsm => hs hsm
      exact false_of_cover_lift c hπs hker (f4_liftDatum q' hv (hp' ▸ hp3) hsm)
    | twistedE6 q' =>
      have hp' : q'.p = p := by simpa [IsChevIndexOfChar, lieIndexChar] using hchev
      exact false_of_cover_lift c hπs hker (twistedE6_liftDatum q' hv (hp' ▸ hp3))

end Final

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
