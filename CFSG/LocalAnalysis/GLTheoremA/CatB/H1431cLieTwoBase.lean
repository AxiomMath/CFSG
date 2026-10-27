module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem lieSTwo_card_sp6two (hLO : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    (hcat : catalogIs Q S9.isSp6two) : Nat.card Q = 1451520 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 2 := hi
        rw [hLO ⟨_, hv⟩ Q ⟨f⟩]
        show orderBC 3 q.card = 1451520
        rw [hq]
        decide +kernel
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem lieSTwo_card_sp48 (hLO : LieOrderBridge) {Q : Type} [Group Q] [Finite Q]
    (hcat : catalogIs Q S8.L84.isSp48) : Nat.card Q = 1056706560 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 8 := hi
        rw [hLO ⟨_, hv⟩ Q ⟨f⟩]
        show orderBC 2 q.card = 1056706560
        rw [hq]
        decide +kernel
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem lieSTwo_card_pSimple_dvd {S : Type} [Group S] [Finite S] (J : Subgroup S) :
    Nat.card (PSimple 3 J) ∣ Nat.card S :=
  (I1431C2.cl_card_psimple_dvd J).trans (Subgroup.card_subgroup_dvd_card J)

theorem lieSTwo_not_sp6two_of_not_dvd (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : ¬ 1451520 ∣ Nat.card S) : ¬ CompOfType S α S9.isSp6two := by
  rintro ⟨J, -, hT⟩
  exact h ((lieSTwo_card_sp6two hLO hT).symm ▸ lieSTwo_card_pSimple_dvd J)

theorem lieSTwo_not_sp48_of_not_dvd (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : ¬ 1056706560 ∣ Nat.card S) : ¬ CompOfType S α S8.L84.isSp48 := by
  rintro ⟨J, -, hT⟩
  exact h ((lieSTwo_card_sp48 hLO hT).symm ▸ lieSTwo_card_pSimple_dvd J)

theorem lieSTwo_pump_of_sp6two (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : CompOfType S α S9.isSp6two) :
    ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J ∧ 3 ^ 4 ∣ Nat.card (PSimple 3 J) := by
  obtain ⟨J, hJ, hT⟩ := h
  exact ⟨J, hJ, by rw [lieSTwo_card_sp6two hLO hT]; norm_num⟩

theorem lieSTwo_pump_of_sp48 (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S]
    {α : MulAut S} (h : CompOfType S α S8.L84.isSp48) :
    ∃ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J ∧ 3 ^ 4 ∣ Nat.card (PSimple 3 J) := by
  obtain ⟨J, hJ, hT⟩ := h
  exact ⟨J, hJ, by rw [lieSTwo_card_sp48 hLO hT]; norm_num⟩

theorem lieSTwo_of_no_pump (hLO : LieOrderBridge) {S : Type} [Group S] [Finite S] {α : MulAut S}
    {R : Prop}
    (h : ∀ J : Subgroup S, GLAPComponent 3 (fixSubgroup α) J → 3 ^ 4 ∣ Nat.card (PSimple 3 J) →
      False) :
    (CompOfType S α S9.isSp6two → R) ∧ ¬ CompOfType S α S8.L84.isSp48 :=
  ⟨fun hc => by
      obtain ⟨J, hJ, h4⟩ := lieSTwo_pump_of_sp6two hLO hc
      exact (h J hJ h4).elim,
    fun hc => by
      obtain ⟨J, hJ, h4⟩ := lieSTwo_pump_of_sp48 hLO hc
      exact h J hJ h4⟩

theorem lieSTwo_concl_of_not {S : Type} [Group S] {α : MulAut S} {R : Prop}
    (h6 : ¬ CompOfType S α S9.isSp6two) (h48 : ¬ CompOfType S α S8.L84.isSp48) :
    (CompOfType S α S9.isSp6two → R) ∧ ¬ CompOfType S α S8.L84.isSp48 :=
  ⟨fun h => (h6 h).elim, h48⟩

theorem lieSTwo_three_pow_five_dvd {S : Type} [Group S] [Finite S] {x : S} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (J : Subgroup S) (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J)
    (h4 : 3 ^ 4 ∣ Nat.card (PSimple 3 J)) : 3 ^ 5 ∣ Nat.card S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJc : J ≤ Subgroup.centralizer ({x} : Set S) := by
    rw [← I1431C2.cl_fixSubgroup_conj_eq_centralizer]
    exact hJ.1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hd1 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have hd2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have hJS : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  have hcomm : ∀ j : J, x * (j : S) = (j : S) * x := fun j =>
    Subgroup.mem_centralizer_iff.1 (hJc j.2) x rfl
  by_cases hxJ : x ∈ J
  · set y : J := ⟨x, hxJ⟩ with hy
    have hyo : orderOf y = 3 := by rw [← Subgroup.orderOf_coe, hy]; exact hxo
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    have hcen : (QuotientGroup.mk y : PQuot 3 J) ∈ Subgroup.center (PQuot 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (hcomm j).symm
    have hne : (QuotientGroup.mk y : PQuot 3 J) ≠ 1 := by
      intro h
      have hmem : y ∈ GLAPPrimeCore 3 ↥J := (QuotientGroup.eq_one_iff y).1 h
      have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
        have := orderOf_dvd_natCard (⟨y, hmem⟩ : GLAPPrimeCore 3 ↥J)
        rwa [Subgroup.orderOf_mk, hyo] at this
      have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) :=
        CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
      exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
    have h3bar : (QuotientGroup.mk y : PQuot 3 J) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one]
    have hordbar : orderOf (QuotientGroup.mk y : PQuot 3 J) = 3 := orderOf_eq_prime h3bar hne
    have h3Z : 3 ∣ Nat.card (Subgroup.center (PQuot 3 J)) := by
      have := orderOf_dvd_natCard
        (⟨(QuotientGroup.mk y : PQuot 3 J), hcen⟩ : Subgroup.center (PQuot 3 J))
      rwa [Subgroup.orderOf_mk, hordbar] at this
    have hsplit : Nat.card (PQuot 3 J) =
        Nat.card (PSimple 3 J) * Nat.card (Subgroup.center (PQuot 3 J)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h5 : 3 ^ 5 ∣ Nat.card (PQuot 3 J) := by
      rw [hsplit, show (3 : ℕ) ^ 5 = 3 ^ 4 * 3 by norm_num]
      exact Nat.mul_dvd_mul h4 h3Z
    exact h5.trans (hd1.trans hJS)
  · have h3J : 3 ^ 4 ∣ Nat.card J := h4.trans (hd2.trans hd1)
    set Z : Subgroup S := Subgroup.zpowers x with hZ
    have hcommZ : ∀ (j : J) (z : Z), Commute (J.subtype j) (Z.subtype z) := by
      rintro j ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact Commute.zpow_right (show Commute (j : S) x from (hcomm j).symm) k
    have hZcard : Nat.card Z = 3 := by rw [hZ, Nat.card_zpowers, hxo]
    haveI : Fact (Nat.card Z).Prime := ⟨by rw [hZcard]; exact Nat.prime_three⟩
    have hJZ : ∀ z : Z, (z : S) ∈ J → z = 1 := by
      intro z hz
      rcases (J.subgroupOf Z).eq_bot_or_eq_top_of_prime_card with h | h
      · have : z ∈ J.subgroupOf Z := hz
        rw [h] at this
        exact this
      · exfalso
        have : (⟨x, Subgroup.mem_zpowers x⟩ : Z) ∈ J.subgroupOf Z := by rw [h]; trivial
        exact hxJ this
    let φ : J × Z →* S := J.subtype.noncommCoprod Z.subtype hcommZ
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨j, z⟩ h
      have h1 : (j : S) * (z : S) = 1 := h
      have hzJ : (z : S) ∈ J := by
        have : (z : S) = (j : S)⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact J.inv_mem j.2
      have hz1 : z = 1 := hJZ z hzJ
      have hj1 : (j : S) = 1 := by rw [hz1] at h1; simpa using h1
      exact Prod.ext (Subtype.ext hj1) hz1
    have hdvd : Nat.card (J × Z) ∣ Nat.card S := Subgroup.card_dvd_of_injective φ hinj
    rw [Nat.card_prod, hZcard] at hdvd
    exact (by norm_num : 3 ^ 5 = 3 ^ 4 * 3) ▸ (Nat.mul_dvd_mul_right h3J 3).trans hdvd

theorem lieSTwo_false_of_inner {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    {α : MulAut S} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) (h4 : 3 ^ 4 ∣ Nat.card (PSimple 3 J))
    (hinn : α ∈ inner S) (h5 : ¬ 3 ^ 5 ∣ Nat.card S) : False := by
  obtain ⟨x, rfl⟩ := hinn
  have hx3 : x ^ 3 = 1 := by
    have h : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hα3
    exact CFSG.mulAutConj_injective_of_center_eq_bot hZ (h.trans (map_one _).symm)
  have hx1 : x ≠ 1 := fun h => hα1 (by rw [h, map_one])
  exact h5 (lieSTwo_three_pow_five_dvd hx3 hx1 J hJ h4)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
