module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma54Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54Abstract

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open CFSG.ComponentClassification.SemisimpleComponentStructure

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem commute_of_mem_zpowers_of_mem_centZ {c y : G} (hc : c ∈ zpowers z) (hy : y ∈ centZ z) :
    c * y = y * c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  exact (Commute.zpow_left (show Commute z y from (mem_centralizer_singleton_iff.1 hy).symm) k).eq

theorem Level55.zpowers_central_exp_two (d : Level55 G t z) :
    ∀ c ∈ (zpowers z).subgroupOf (centZ z),
      (∀ y : ↥(centZ z), c * y = y * c) ∧ c * c = 1 := by
  intro c hc
  have hc' : (c : G) ∈ zpowers z := hc
  refine ⟨fun y => Subtype.ext (commute_of_mem_zpowers_of_mem_centZ hc' y.2), ?_⟩
  apply Subtype.ext
  show (c : G) * (c : G) = 1
  rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord hc' with h | h
  · rw [h, one_mul]
  · rw [h]
    exact d.z_mul_self

theorem center_component_mem_zpowers
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (i : ComponentIndex ↥(centZ z)) (c : ↥i.val) (hc : c ∈ Subgroup.center ↥i.val) :
    ((c : ↥(centZ z)) : G) ∈ zpowers z := by
  have hodd' : CFSG.pPrimeCore 2 ↥(centZ z) = ⊥ := by
    rw [← standardComponentOddCore_eq_pPrimeCore]
    exact hodd
  have hp := Layer54.center_layer_le_pCore hodd' (Layer54.center_component_le i c hc)
  have h2 : ((c : ↥(centZ z)) : G) ∈ Psub z :=
    (mem_pCore_iff_mem_O2In (H := centZ z) (c : ↥(centZ z))).1 hp
  rwa [hP] at h2

theorem conj_mem_map_component
    (hKE : centPair z t ≤ (layer ↥(centZ z)).map (centZ z).subtype)
    (i : ComponentIndex ↥(centZ z)) {k : G} (hk : k ∈ centPair z t) {n : G}
    (hn : n ∈ i.val.map (centZ z).subtype) : k * n * k⁻¹ ∈ i.val.map (centZ z).subtype := by
  obtain ⟨e, he, rfl⟩ := hKE hk
  obtain ⟨q, hq, rfl⟩ := hn
  have he' : e ∈ ComponentClassification.Layer.subgroup ↥(centZ z) := by
    rwa [← layer_eq_componentClassification]
  have hq' : q ∈ ComponentClassification.Layer.subgroup ↥(centZ z) :=
    ComponentClassification.Layer.component_le i.property hq
  have h := (ComponentClassification.Layer.normal_component i.property).conj_mem ⟨q, hq'⟩
    (mem_subgroupOf.2 hq) ⟨e, he'⟩
  exact ⟨e * q * e⁻¹, mem_subgroupOf.1 h, rfl⟩

theorem exists_quotient_simple_of_le_component {K : Subgroup G}
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (i : ComponentIndex ↥(centZ z)) (hi : K ≤ i.val.map (centZ z).subtype) :
    ∃ (Q : Subgroup G) (_ : Q ≤ centZ z), K ≤ Q ∧
      ∃ (_ : ((zpowers z).subgroupOf Q).Normal),
        IsSimpleGroup (↥Q ⧸ (zpowers z).subgroupOf Q) ∧
        ∃ a b : ↥Q ⧸ (zpowers z).subgroupOf Q, a * b ≠ b * a := by
  have hQC : i.val.map (centZ z).subtype ≤ centZ z := Subgroup.map_subtype_le _
  have hnorm : ((zpowers z).subgroupOf (i.val.map (centZ z).subtype)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 := commute_of_mem_zpowers_of_mem_centZ hn (hQC g.2)
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ zpowers z
    rw [← h1, mul_inv_cancel_right]
    exact hn
  refine ⟨i.val.map (centZ z).subtype, hQC, hi, hnorm, ?_⟩
  let e : ↥i.val ≃* ↥(i.val.map (centZ z).subtype) :=
    Subgroup.equivMapOfInjective i.val (centZ z).subtype (centZ z).subtype_injective
  have he : ∀ u : ↥i.val, ((e u : ↥(i.val.map (centZ z).subtype)) : G) = (((u : ↥(centZ z))) : G) :=
    fun u => rfl
  have hmap : (Subgroup.center ↥i.val).map e.toMonoidHom =
      (zpowers z).subgroupOf (i.val.map (centZ z).subtype) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      show ((e u : ↥(i.val.map (centZ z).subtype)) : G) ∈ zpowers z
      rw [he]
      exact center_component_mem_zpowers hodd hP i u hu
    · intro hv
      have hvz : (v : G) ∈ zpowers z := hv
      refine ⟨e.symm v, ?_, by simp⟩
      refine Subgroup.mem_center_iff.2 (fun w => ?_)
      have hu : ((e.symm v : ↥i.val) : G) = (v : G) := by
        have := he (e.symm v)
        rw [e.apply_symm_apply] at this
        exact this.symm
      apply Subtype.ext
      apply Subtype.ext
      show ((w : ↥(centZ z)) : G) * ((e.symm v : ↥i.val) : ↥(centZ z)) =
        ((e.symm v : ↥i.val) : ↥(centZ z)) * ((w : ↥(centZ z)) : G)
      rw [show (((e.symm v : ↥i.val) : ↥(centZ z)) : G) = (v : G) from hu]
      exact (commute_of_mem_zpowers_of_mem_centZ hvz w.1.2).symm
  have hq := i.property.2.2
  have hQuo := QuotientGroup.congr (Subgroup.center ↥i.val)
    ((zpowers z).subgroupOf (i.val.map (centZ z).subtype)) e hmap
  have : IsSimpleGroup (↥i.val ⧸ Subgroup.center ↥i.val) := hq.2
  refine ⟨hQuo.symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥i.val hq
  refine ⟨hQuo a, hQuo b, fun h => hab ?_⟩
  apply hQuo.injective
  rw [map_mul, map_mul]
  exact h

section Certified


theorem Level55.exists_order23_mem_K (d : Level55 G t z) :
    ∃ σ ∈ centPair z t, orderOf σ = 23 := by
  have h23 : 23 ∣ Nat.card (centPair z t) := by
    obtain ⟨e⟩ := d.quot
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(centPair z t))
    have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [Nat.card_congr e.toEquiv, hco] at h2
    rw [h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centPair z t)) 23 h23
  exact ⟨(σ : G), σ.2, by rw [Subgroup.orderOf_coe]; exact hσ⟩

theorem Level55.false_of_no_component (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (hKE : centPair z t ≤ (layer ↥(centZ z)).map (centZ z).subtype)
    (hex : ¬ ∃ i : ComponentIndex ↥(centZ z), centPair z t ≤ i.val.map (centZ z).subtype) :
    False := by
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have htK : t ∈ centPair z t := mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩
  have hN : ∀ i : ComponentIndex ↥(centZ z),
      centPair z t ⊓ i.val.map (centZ z).subtype ≤ O2In (centPair z t) := by
    intro i
    by_contra hnle
    have hinv : ∀ k ∈ centPair z t, ∀ n ∈ centPair z t ⊓ i.val.map (centZ z).subtype,
        k * n * k⁻¹ ∈ centPair z t ⊓ i.val.map (centZ z).subtype := fun k hk n hn =>
      mem_inf.2 ⟨mul_mem (mul_mem hk (mem_inf.1 hn).1) (inv_mem hk),
        conj_mem_map_component hKE i hk (mem_inf.1 hn).2⟩
    have heq := d.eq_K_of_not_le_O2K inf_le_left hinv hnle
    exact hex ⟨i, heq.ge.trans inf_le_right⟩
  set tH : ↥(centZ z) := ⟨t, hKC htK⟩ with htH
  have htlayer : tH ∈ ComponentClassification.Layer.subgroup ↥(centZ z) := by
    obtain ⟨e, he, het⟩ := hKE htK
    have : e = tH := Subtype.ext het
    rw [← this, ← layer_eq_componentClassification]
    exact he
  have hd : ∀ (i : ComponentIndex ↥(centZ z)) (a : ↥(centZ z)), a ∈ i.val →
      a * tH = tH * a → ∃ k : ℕ, a ^ 2 ^ k = 1 := by
    intro i a ha hat
    have haK : (a : G) ∈ centPair z t := by
      refine mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 a.2).symm, ?_⟩
      exact (congrArg Subtype.val hat).symm
    have haY : (a : G) ∈ O2In (centPair z t) := hN i ⟨haK, ⟨a, ha, rfl⟩⟩
    obtain ⟨k, hk⟩ := isPGroup_O2In (centPair z t) ⟨(a : G), haY⟩
    refine ⟨k, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hk
  have hall : ∀ x ∈ centPair z t, ∃ m : ℕ, x ^ 2 ^ m = 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := hKE hx
    have he' : e ∈ ComponentClassification.Layer.subgroup ↥(centZ z) := by
      rwa [← layer_eq_componentClassification]
    have hxt : e * tH = tH * e := by
      apply Subtype.ext
      exact ((mem_centPair_iff.1 hx).2).symm
    obtain ⟨m, hm⟩ := Layer54.exists_two_pow_eq_one_of_layer ((zpowers z).subgroupOf (centZ z))
      d.zpowers_central_exp_two (fun i c hc => center_component_mem_zpowers hodd hP i c hc)
      htlayer hd he' hxt
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨σ, hσK, hσ⟩ := d.exists_order23_mem_K
  obtain ⟨m, hm⟩ := hall σ hσK
  have hdvd : orderOf σ ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  rw [hσ] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 23) hdvd
  omega

theorem Level55.exists_quotient_simple_of_K_le_layer (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) (hP : Psub z = zpowers z)
    (hKE : centPair z t ≤ (layer ↥(centZ z)).map (centZ z).subtype) :
    ∃ (Q : Subgroup G) (_ : Q ≤ centZ z), centPair z t ≤ Q ∧
      ∃ (_ : ((zpowers z).subgroupOf Q).Normal),
        IsSimpleGroup (↥Q ⧸ (zpowers z).subgroupOf Q) ∧
        ∃ a b : ↥Q ⧸ (zpowers z).subgroupOf Q, a * b ≠ b * a := by
  by_cases hex : ∃ i : ComponentIndex ↥(centZ z), centPair z t ≤ i.val.map (centZ z).subtype
  · obtain ⟨i, hi⟩ := hex
    exact exists_quotient_simple_of_le_component hodd hP i hi
  · exact (d.false_of_no_component hodd hP hKE hex).elim

end Certified

end CFSG.EvenSporadicStandard.TwoB
