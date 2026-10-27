module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {J D : Subgroup Ω}

private noncomputable def pquotEquiv (hZ : Subgroup.center (PQuot 3 J) = ⊥) :
    PSimple 3 J ≃* PQuot 3 J :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

private theorem not_dvd_card_core (J : Subgroup Ω) : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf Nat.prime_three J
  unfold GLAPPrimeCoreOf at h
  rwa [Subgroup.card_map_of_injective J.subtype_injective] at h

private theorem map_inf_eq_bot (hZ : Subgroup.center (PQuot 3 J) = ⊥)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) {E : Subgroup ↥J} (hE : IsPGroup 3 E) :
    E.map J.subtype ⊓ D = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨j, hjE, rfl⟩, hjD⟩
  have hjc : j ∈ Subgroup.center ↥J := Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 (hDJ hjD) y y.2)
  have hq : (QuotientGroup.mk j : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hjc y]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hq
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hcop : Nat.Coprime (Nat.card E) (Nat.card (GLAPPrimeCore 3 ↥J)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (not_dvd_card_core J))
  have hj : j ∈ E ⊓ GLAPPrimeCore 3 ↥J := ⟨hjE, hq⟩
  rw [Subgroup.inf_eq_bot_of_coprime hcop, Subgroup.mem_bot] at hj
  rw [Subgroup.mem_bot, hj, map_one]

private theorem sup_facts (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hD : IsElemAbelian 3 D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) {S : Subgroup ↥J} (hS : IsElemAbelian 3 S) :
    IsElemAbelian 3 (S.map J.subtype ⊔ D) ∧
      Nat.card ↥(S.map J.subtype ⊔ D) = Nat.card S * Nat.card D := by
  have hc : ∀ a ∈ S.map J.subtype, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hDJ hb) a (Subgroup.map_subtype_le S ha)
  refine ⟨(hS.map J.subtype).sup_of_commute hD hc, ?_⟩
  have hN : D ≤ Subgroup.normalizer ((S.map J.subtype : Subgroup Ω) : Set Ω) := fun d hd =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha d hd)
  have h := card_sup_mul_card_inf_of_le_normalizer hN
  rwa [map_inf_eq_bot hZ hDJ hS.isPGroup, Subgroup.card_bot, mul_one,
    Subgroup.card_map_of_injective J.subtype_injective] at h

theorem exists_lift_sup (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hD : IsElemAbelian 3 D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) {Eb : Subgroup (PSimple 3 J)}
    (hEb : IsElemAbelian 3 Eb) :
    ∃ E : Subgroup Ω, E ≤ J ∧ IsElemAbelian 3 (E ⊔ D) ∧
      Nat.card ↥(E ⊔ D) = Nat.card Eb * Nat.card D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS, -, hScard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift
    (GLAPPrimeCore 3 ↥J) (not_dvd_card_core J) (hEb.map (pquotEquiv hZ).toMonoidHom)
  obtain ⟨h1, h2⟩ := sup_facts hZ hD hDJ hS
  refine ⟨S.map J.subtype, Subgroup.map_subtype_le S, h1, ?_⟩
  rw [h2, hScard, Subgroup.card_map_of_injective (pquotEquiv hZ).injective]

theorem exists_lift_sup_normalizing (hZ : Subgroup.center (PQuot 3 J) = ⊥)
    (hD : IsElemAbelian 3 D) (hDJ : D ≤ Subgroup.centralizer (J : Set Ω))
    {Eb Ub : Subgroup (PSimple 3 J)} (hEb : IsElemAbelian 3 Eb) (hUb : IsPGroup 2 Ub)
    (hUb1 : Ub ≠ ⊥) (hEU : Eb ≤ Subgroup.normalizer (Ub : Set (PSimple 3 J))) :
    ∃ E U : Subgroup Ω, E ≤ J ∧ U ≤ J ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ IsElemAbelian 3 (E ⊔ D) ∧
      Nat.card ↥(E ⊔ D) = Nat.card Eb * Nat.card D ∧
      E ⊔ D ≤ Subgroup.normalizer (U : Set Ω) := by
  set φ := (pquotEquiv hZ).toMonoidHom
  have hφ : Function.Injective φ := (pquotEquiv hZ).injective
  obtain ⟨T, S, hT, hT2, hS, hScard, hST⟩ := T263.lift_normalizing Nat.prime_three (by norm_num)
    (GLAPPrimeCore 3 ↥J) (not_dvd_card_core J) (Pb := Ub.map φ) (Eb := Eb.map φ)
    ((Subgroup.map_eq_bot_iff_of_injective Ub hφ).not.2 hUb1) (hUb.map φ) (hEb.map φ)
    ((Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map φ))
  obtain ⟨h1, h2⟩ := sup_facts hZ hD hDJ hS
  have hTJ : T.map J.subtype ≤ J := Subgroup.map_subtype_le T
  refine ⟨S.map J.subtype, T.map J.subtype, Subgroup.map_subtype_le S, hTJ,
    (Subgroup.map_eq_bot_iff_of_injective T J.subtype_injective).not.2 hT, hT2.map _, h1, ?_,
    sup_le ((Subgroup.map_mono hST).trans (Subgroup.le_normalizer_map _)) ?_⟩
  · rw [h2, hScard, Subgroup.card_map_of_injective hφ]
  · exact (hDJ.trans (Subgroup.centralizer_le hTJ)).trans (Subgroup.centralizer_le_normalizer _)

theorem card_mul_card_le_rank (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hD : IsElemAbelian 3 D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set Ω)) {Eb Ub : Subgroup (PSimple 3 J)}
    (hEb : IsElemAbelian 3 Eb) (hUb : IsPGroup 2 Ub) (hUb1 : Ub ≠ ⊥)
    (hEU : Eb ≤ Subgroup.normalizer (Ub : Set (PSimple 3 J))) :
    Nat.card Eb * Nat.card D ≤ 3 ^ GLATwoLocalRank 3 Ω := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, U, -, -, hU1, hU2, hED, hcard, hN⟩ :=
    exists_lift_sup_normalizing hZ hD hDJ hEb hUb hUb1 hEU
  rw [← hcard]
  exact T263.card_le_of_normalizes hU1 hU2 hED hN

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
