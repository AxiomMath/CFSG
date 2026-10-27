module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56PartB

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement Frame SylowFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sylow_ne_bot56 {M J : Subgroup G} {g : G} {T : Subgroup G} (hgood : Good56 M J g)
    (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g)) : T ≠ ⊥ := by
  obtain ⟨W, hWle, hW2, hW4⟩ := hgood.2
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW4
    omega
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
  exact ne_bot_of_isSylowOf_even hT (even_card_of_isPGroup hWp hW1 hWle)

theorem X_decomp {J T S : Subgroup G} (hS : SylowFrame J T S) {x : G}
    (hx : x ∈ S ⊓ Subgroup.normalizer (T : Set G)) :
    ∃ t ∈ T, ∃ q ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J, x = t * q := by
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hS.le_normalizer
  have hTX : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hS.le Subgroup.le_normalizer
  have hxS : x ∈ S := (Subgroup.mem_inf.1 hx).1
  have hxTA : x ∈ T ⊔ J := by
    rw [sup_comm]
    exact hS.sylow.le hxS
  obtain ⟨t, ht, a, ha, hta⟩ := exists_mul_of_mem_sup hTN hxTA
  have haX : a ∈ S ⊓ Subgroup.normalizer (T : Set G) := by
    have : a = t⁻¹ * x := by rw [← hta]; group
    rw [this]
    exact (S ⊓ Subgroup.normalizer (T : Set G)).mul_mem
      ((S ⊓ Subgroup.normalizer (T : Set G)).inv_mem (hTX ht)) hx
  exact ⟨t, ht, a, Subgroup.mem_inf.2 ⟨haX, ha⟩, hta.symm⟩

omit [Finite G] in
theorem inf_comm_T {J T S : Subgroup G} (hS : SylowFrame J T S) :
    ∀ q ∈ S ⊓ Subgroup.normalizer (T : Set G) ⊓ J, ∀ t ∈ T, q * t = t * q := by
  intro q hq t ht
  obtain ⟨hqX, hqA⟩ := Subgroup.mem_inf.1 hq
  have hqN : q ∈ Subgroup.normalizer (T : Set G) := (Subgroup.mem_inf.1 hqX).2
  have h1 : q * t * q⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hqN t).1 ht
  have h2 : t * q⁻¹ * t⁻¹ ∈ J :=
    (Subgroup.mem_normalizer_iff.1 (hS.le_normalizer ht) q⁻¹).1 (J.inv_mem hqA)
  have hc : q * t * q⁻¹ * t⁻¹ ∈ T ⊓ J := ⟨T.mul_mem h1 (T.inv_mem ht), by
    have := J.mul_mem hqA h2
    simpa [mul_assoc] using this⟩
  rw [hS.inf_eq_bot, Subgroup.mem_bot] at hc
  calc q * t = (q * t * q⁻¹ * t⁻¹) * (t * q) := by group
    _ = t * q := by rw [hc, one_mul]

theorem relIndex_le_card_inf {J T S : Subgroup G} (hS : SylowFrame J T S) :
    T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤
      Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) := by
  have hTX : T ≤ S ⊓ Subgroup.normalizer (T : Set G) := le_inf hS.le Subgroup.le_normalizer
  let f : ↥T × ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) →
      ↥(S ⊓ Subgroup.normalizer (T : Set G)) := fun p => ⟨(p.1 : G) * (p.2 : G),
      (S ⊓ Subgroup.normalizer (T : Set G)).mul_mem (hTX p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hxX⟩
    obtain ⟨t, ht, q, hq, hxtq⟩ := X_decomp hS hxX
    exact ⟨(⟨t, ht⟩, ⟨q, hq⟩), Subtype.ext hxtq.symm⟩
  have hXcard : Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G)) ≤
      Nat.card T * Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) := by
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at this
  have hmul := Subgroup.relIndex_mul_card T (S ⊓ Subgroup.normalizer (T : Set G))
  rw [inf_eq_left.2 hTX] at hmul
  have hTpos : 0 < Nat.card T := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hTpos
  rw [hmul, mul_comm]
  exact hXcard

theorem exists_of_not_tight {J T : Subgroup G} (hfr : Frame J T) (hT1 : T ≠ ⊥)
    (hnt : ¬ TightlyEmbedded (T.subgroupOf (J ⊔ T))) :
    ∃ x ∈ J, x ∉ Subgroup.normalizer (T : Set G) ∧ ∃ u ∈ T, u ≠ 1 ∧ x * u = u * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : Even (Nat.card ↥(T.subgroupOf (J ⊔ T))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : T ≤ J ⊔ T)).toEquiv]
    exact even_card_of_isPGroup hfr.isPGroup hT1 le_rfl
  have hnot : ¬ ∀ y : ↥(J ⊔ T), y ∉ Subgroup.normalizer
      ((T.subgroupOf (J ⊔ T) : Subgroup ↥(J ⊔ T)) : Set ↥(J ⊔ T)) →
      Odd (Nat.card ↥(T.subgroupOf (J ⊔ T) ⊓ rightConjugate (T.subgroupOf (J ⊔ T)) y)) :=
    fun h => hnt ⟨heven, h⟩
  push Not at hnot
  obtain ⟨y, hyN, hyodd⟩ := hnot
  have hyeven := Nat.not_odd_iff_even.1 hyodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(T.subgroupOf (J ⊔ T) ⊓ rightConjugate (T.subgroupOf (J ⊔ T)) y)) 2
    (even_iff_two_dvd.1 hyeven)
  set u : G := ((z : ↥(J ⊔ T)) : G)
  have hzT : u ∈ T := (Subgroup.mem_inf.1 z.2).1
  have hzTy := (mem_rightConjugate_iff _ y _).1 (Subgroup.mem_inf.1 z.2).2
  have hconj : (y : G) * u * (y : G)⁻¹ ∈ T := hzTy
  have hz1 : u ≠ 1 := by
    intro h1
    have h2 : (z : ↥(J ⊔ T)) = 1 := Subtype.ext h1
    have hz' : z = 1 := Subtype.ext h2
    rw [hz', orderOf_one] at hz
    omega
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hfr.le_normalizer
  have hyTJ : (y : G) ∈ T ⊔ J := by
    rw [sup_comm]
    exact y.2
  obtain ⟨t, ht, j, hj, hyj⟩ := exists_mul_of_mem_sup hTN hyTJ
  have h1 : j * u * j⁻¹ ∈ T := by
    rw [← hyj] at hconj
    have e : t * j * u * (t * j)⁻¹ = t * (j * u * j⁻¹) * t⁻¹ := by group
    rw [e] at hconj
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hconj) ht
    have e2 : t⁻¹ * (t * (j * u * j⁻¹) * t⁻¹) * t = j * u * j⁻¹ := by group
    rwa [e2] at this
  have hcomm : ⁅j, u⁆ ∈ T ⊓ J := by
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact T.mul_mem h1 (T.inv_mem hzT)
    · have h2 : u * j⁻¹ * u⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.1 (hTN hzT) j⁻¹).1 (J.inv_mem hj)
      have : ⁅j, u⁆ = j * (u * j⁻¹ * u⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact J.mul_mem hj h2
  rw [hfr.inf_eq_bot, Subgroup.mem_bot] at hcomm
  refine ⟨j, hj, ?_, u, hzT, hz1, commutatorElement_eq_one_iff_mul_comm.1 hcomm⟩
  intro hjN
  apply hyN
  have hyN' : (y : G) ∈ Subgroup.normalizer (T : Set G) := by
    rw [← hyj]
    exact (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer ht) hjN
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact Subgroup.mem_normalizer_iff.1 hyN' (h : G)

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem card_inf_le (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G} {T S : Subgroup G}
    (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) :
    Nat.card ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) ≤ Nat.card T := by
  have hT1 : T ≠ ⊥ := sylow_ne_bot56 hgood hT
  have hTJg : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hnc := c.exists_noncentral hA hz hgood.1 hT hT1
  have hQN : S ⊓ Subgroup.normalizer (T : Set G) ⊓ J ≤
      Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := fun q hq =>
    c.mem_normalizer_conj_of_centralizes hTJg hT2 hT1 hnc (inf_comm_T hS q hq)
  have hQ2 : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (T : Set G) ⊓ J) :=
    hS.sylow.isPGroup.to_le (inf_le_left.trans inf_le_left)
  exact c.card_le_of_le_normalizer hA hz hgood hT hmax inf_le_right hQN hQ2

theorem exists_x (h3 : Theorem3Statement) (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    {T S : Subgroup G} (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2)
    (hS : SylowFrame J T S) :
    ∃ x ∈ J, x ∉ Subgroup.normalizer (T : Set G) ∧ ∃ u ∈ T, u ≠ 1 ∧ x * u = u * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg : g ∉ M := hgood.1
  have hT1 : T ≠ ⊥ := sylow_ne_bot56 hgood hT
  have hTJg : T ≤ rightConjugate J g := hT.le.trans inf_le_left
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hidx : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T :=
    (relIndex_le_card_inf hS).trans (c.card_inf_le hA hz hgood hT hmax hS)
  have hTself : ABGLocalTools.IsSylowOf 2 T T :=
    isSylowOf_iff.2 ⟨le_rfl, hT2, by rw [Subgroup.relIndex_self]; norm_num⟩
  have hnt : ¬ TightlyEmbedded (T.subgroupOf (J ⊔ T)) := by
    intro htight
    have hcomm := lemma_5_1 h3 c.block hT1 hS hTself le_sup_right htight hidx
    have hTC : T ≤ Subgroup.centralizer (J : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have : T = ⊥ := c.eq_bot_of_centralizes hg M.one_mem hTJg hT2 (fun t ht y hy => by
      rw [rightConjugate_one] at hy
      exact (Subgroup.mem_centralizer_iff.1 (hTC ht) y hy).symm)
    exact hT1 this
  exact exists_of_not_tight hS.toFrame hT1 hnt

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
