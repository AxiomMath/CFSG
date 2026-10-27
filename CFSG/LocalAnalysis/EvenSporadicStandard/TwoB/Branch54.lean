module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.K54Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Lemma54Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {t z : G}

section Certified


theorem Level55.exists_order23_centralizes_P (d : Level55 G t z)
    (hnot : ¬ O2In (centPair z t) ≤ Psub z) :
    ∃ σ ∈ centPair z t, orderOf σ = 23 ∧ ∀ p ∈ Psub z, σ * p = p * σ := by
  have hW : O2In (centPair z t) ⊓ Psub z ≤ pair z t :=
    (d.inf_le_pair_or_le).resolve_right hnot
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hPC : Psub z ≤ centZ z := O2In_le _
  have hPK : Psub z ⊓ centPair z t ≤ pair z t := by
    have hn : ((Psub z ⊓ centPair z t).subgroupOf (centPair z t)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      refine mem_inf.2 ⟨?_, (centPair z t).mul_mem ((centPair z t).mul_mem g.2 hn.2)
        ((centPair z t).inv_mem g.2)⟩
      have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨(n : G), hPC hn.1⟩
        (by rw [mem_subgroupOf]; exact hn.1) ⟨(g : G), hKC g.2⟩
      exact this
    have hp : IsPGroup 2 (Psub z ⊓ centPair z t : Subgroup G) :=
      (isPGroup_O2In _).to_le inf_le_left
    have hle := le_O2In inf_le_right hn hp
    exact fun x hx => hW (mem_inf.2 ⟨hle hx, hx.1⟩)
  have htK : t ∈ centPair z t := mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩
  have htC : t ∈ centZ z := hKC htK
  have hX : IsPGroup 2 ↥(Psub z ⊔ zpowers t) :=
    isPGroup_sup_zpowers hPC (normal_subgroupOf_O2In _) (isPGroup_O2In _) htC d.t_ord
  have htX : t ∈ Psub z ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hLE : zpowers t ≤ normalizer ((Psub z : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_O2In htC
  have hXc : (Psub z ⊔ zpowers t) ⊓ centralizer ({t} : Set G) ≤ pair z t := by
    intro x hx
    have hxX := hx.1
    have hxt := hx.2
    have hmul : x ∈ ((Psub z : Subgroup G) : Set G) * ((zpowers t : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLE]
      exact hxX
    obtain ⟨p, hp, b, hb, rfl⟩ := hmul
    have hbt : b * t = t * b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact ((Commute.zpow_left (show Commute t t from rfl) k).eq)
    have hpt : p * t = t * p := by
      have h1 : p * b * t = t * (p * b) := mem_centralizer_singleton_iff.1 hxt
      have h2 : p * t * b = t * p * b := by
        calc p * t * b = p * (t * b) := by rw [mul_assoc]
          _ = p * (b * t) := by rw [hbt]
          _ = p * b * t := by rw [mul_assoc]
          _ = t * (p * b) := h1
          _ = t * p * b := by rw [mul_assoc]
      exact mul_right_cancel h2
    have hpK : p ∈ centPair z t :=
      mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 (hPC hp)).symm, hpt.symm⟩
    exact mul_mem (hPK (mem_inf.2 ⟨hp, hpK⟩)) (mem_sup_right hb)
  have hhom : Nat.card (↥(Psub z ⊔ zpowers t) →* Multiplicative (ZMod 2)) < 23 := by
    have h1 := RankLemma.card_hom_le_card_inf_centralizer_of_mem htX
    have h2 : Nat.card ↥((Psub z ⊔ zpowers t) ⊓ centralizer ({t} : Set G)) ≤
        Nat.card (pair z t) := Subgroup.card_le_of_le hXc
    have h3 := card_pair_le d.z_ord d.t_ord d.zt_comm
    omega
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
  have hσ' : orderOf (σ : G) = 23 := by rw [Subgroup.orderOf_coe]; exact hσ
  have hσt : (σ : G) * t = t * σ := by
    have := (mem_centPair_iff.1 σ.2).2
    exact this.symm
  have hnorm : ∀ x ∈ Psub z ⊔ zpowers t, (σ : G) * x * (σ : G)⁻¹ ∈ Psub z ⊔ zpowers t := by
    refine conj_mem_sup_of_invariant ?_ ?_
    · intro a ha
      have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨a, hPC ha⟩
        (by rw [mem_subgroupOf]; exact ha) ⟨(σ : G), hKC σ.2⟩
      exact this
    · intro b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      have hc : (σ : G) * t ^ k = t ^ k * σ := (Commute.zpow_right (show Commute (σ : G) t from
        hσt) k).eq
      rw [hc, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers t) k
  have hcomm := commute_of_card_hom_lt hX (q := 23) (by norm_num) (by norm_num) hσ' hnorm hhom
  exact ⟨(σ : G), σ.2, hσ', fun p hp => hcomm p (mem_sup_left hp)⟩

theorem Level55.centPair_comm_Psub (d : Level55 G t z) (hnot : ¬ O2In (centPair z t) ≤ Psub z) :
    ∀ k ∈ centPair z t, ∀ p ∈ Psub z, k * p = p * k := by
  obtain ⟨σ, hσK, hσ, hσP⟩ := d.exists_order23_centralizes_P hnot
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  set N : Subgroup G := centPair z t ⊓ centralizer ((Psub z : Subgroup G) : Set G) with hNdef
  have hN : ∀ k ∈ centPair z t, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hk n hn
    refine mem_inf.2 ⟨mul_mem (mul_mem hk (mem_inf.1 hn).1) (inv_mem hk), ?_⟩
    rw [mem_centralizer_iff]
    intro p hp
    have hp' : k⁻¹ * p * k ∈ Psub z := by
      have h := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨p, O2In_le _ hp⟩
        (mem_subgroupOf.2 hp) ⟨k⁻¹, inv_mem (hKC hk)⟩
      have h' : k⁻¹ * p * k⁻¹⁻¹ ∈ O2In (centZ z) := h
      rwa [inv_inv] at h'
    have h1 : (k⁻¹ * p * k) * n = n * (k⁻¹ * p * k) := mem_centralizer_iff.1 (mem_inf.1 hn).2 _ hp'
    calc p * (k * n * k⁻¹) = k * ((k⁻¹ * p * k) * n) * k⁻¹ := by group
      _ = k * (n * (k⁻¹ * p * k)) * k⁻¹ := by rw [h1]
      _ = (k * n * k⁻¹) * p := by group
  have hσN : σ ∈ N := mem_inf.2 ⟨hσK, mem_centralizer_iff.2 fun p hp => (hσP p hp).symm⟩
  have hσY : σ ∉ O2In (centPair z t) := by
    intro hσY
    obtain ⟨k, hk⟩ := isPGroup_O2In (centPair z t) ⟨σ, hσY⟩
    have hk' : σ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hdvd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hσ] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 23) hdvd
    omega
  have hNe : N = centPair z t :=
    d.eq_K_of_not_le_O2K inf_le_left hN fun h => hσY (h hσN)
  intro k hk p hp
  have hkN : k ∈ N := by rw [hNe]; exact hk
  exact (mem_centralizer_iff.1 (mem_inf.1 hkN).2 p hp).symm

theorem Level55.Psub_le_pair (d : Level55 G t z) (hnot : ¬ O2In (centPair z t) ≤ Psub z) :
    Psub z ≤ pair z t := by
  intro p hp
  have hcomm := d.centPair_comm_Psub hnot
  have hpK : p ∈ centPair z t := by
    refine mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 (O2In_le _ hp)).symm, ?_⟩
    exact hcomm t (mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩) p hp
  exact d.central_K_le_pair hpK fun k hk => (hcomm k hk p hp).symm

theorem Level55.layer_eq_bot_of_O2K_le_P (d : Level55 G t z) (hY : O2In (centPair z t) ≤ Psub z) :
    layer ↥(centZ z) = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  set Dm : Subgroup G := (layer ↥(centZ z)).map (centZ z).subtype with hDm
  have hDnorm : (layer ↥(centZ z)).Normal := by
    rw [layer_eq_componentClassification]
    exact ComponentClassification.Layer.normal _
  have hPD : ∀ x ∈ Dm, ∀ p ∈ Psub z, x * p = p * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨p, hp, rfl⟩
    have hsolv : Group.IsSolvable (CFSG.pCore 2 ↥(centZ z)) := by
      have : Group.IsNilpotent (CFSG.pCore 2 ↥(centZ z)) := (CFSG.pCore_isPGroup).isNilpotent
      infer_instance
    have hsub : Open.IsSubnormal (CFSG.pCore 2 ↥(centZ z)) ⊤ :=
      Open.IsSubnormal.step le_top (Subgroup.Normal.subgroupOf CFSG.pCore_normal _)
        (Open.IsSubnormal.refl _)
    have hcomm := ComponentClassification.Layer.commutes_with_solvable_subnormal
      (CFSG.pCore 2 ↥(centZ z)) hsub
    rw [← layer_eq_componentClassification] at hcomm
    have h1 : ⁅x, p⁆ ∈ ⁅layer ↥(centZ z), CFSG.pCore 2 ↥(centZ z)⁆ :=
      Subgroup.commutator_mem_commutator hx hp
    rw [hcomm, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 h1)
  have hDmK : Dm ≤ centPair z t := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt : (x : G) * t = t * x :=
      hPD x ⟨x, hx, rfl⟩ t (hY (d.pair_le_O2K (t_mem_pair z t)))
    exact mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 x.2).symm, hxt.symm⟩
  have hDmN : ∀ k ∈ centPair z t, ∀ x ∈ Dm, k * x * k⁻¹ ∈ Dm := by
    rintro k hk _ ⟨x, hx, rfl⟩
    exact ⟨⟨k, hKC hk⟩ * x * ⟨k, hKC hk⟩⁻¹, hDnorm.conj_mem x hx _, rfl⟩
  have hDmnle : ¬ Dm ≤ O2In (centPair z t) := by
    intro hle
    have hp2 : IsPGroup 2 (layer ↥(centZ z)) := by
      intro x
      obtain ⟨n, hn⟩ := isPGroup_O2In (centPair z t) ⟨((x : ↥(centZ z)) : G), hle ⟨x, x.2, rfl⟩⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    have : Group.IsNilpotent (layer ↥(centZ z)) := hp2.isNilpotent
    have hnt : Nontrivial (layer ↥(centZ z)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have hperf : Group.IsPerfect (layer ↥(centZ z)) := by
      rw [layer_eq_componentClassification]
      exact ComponentClassification.Layer.perfect _
    exact Group.IsPerfect.not_isSolvable (layer ↥(centZ z)) inferInstance
  have hDmeq : Dm = centPair z t := d.eq_K_of_not_le_O2K hDmK hDmN hDmnle
  obtain ⟨y, hyY, hyp⟩ := d.exists_mem_O2K_not_mem_pair
  refine hyp (d.central_K_le_pair (O2In_le _ hyY) fun k hk => ?_)
  have hkD : k ∈ Dm := by rw [hDmeq]; exact hk
  exact (hPD k hkD y (hY hyY)).symm

theorem Level55.isTwoConstrained_of_O2K_le_P (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥)
    (hY : O2In (centPair z t) ≤ Psub z) : IsTwoConstrained (centZ z) :=
  (isTwoConstrained_iff_layer_eq_bot _ hodd).2 (d.layer_eq_bot_of_O2K_le_P hY)

theorem Level55.isTwoConstrained_iff_O2K_le_P (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) :
    IsTwoConstrained (centZ z) ↔ O2In (centPair z t) ≤ Psub z :=
  ⟨fun h => d.O2K_le_P h, d.isTwoConstrained_of_O2K_le_P hodd⟩

theorem Level55.O2K_le_P_of_t_mem (d : Level55 G t z) (hP : Psub z ≤ pair z t)
    (htP : t ∈ Psub z) : O2In (centPair z t) ≤ Psub z := by
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hzP : z ∈ Psub z := self_mem_O2In_centZ d.z_ord
  have hcpair : ∀ c ∈ centZ z, ∀ a ∈ pair z t, c * a * c⁻¹ ∈ pair z t := by
    intro c hc
    have hz : c * z * c⁻¹ = z := by
      rw [mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
    have ht : c * t * c⁻¹ ∈ pair z t := hP ((normal_subgroupOf_O2In (centZ z)).conj_mem
      ⟨t, O2In_le _ htP⟩ (mem_subgroupOf.2 htP) ⟨c, hc⟩)
    refine conj_mem_sup_of_conj_mem (S := pair z t) ?_ ?_
    · exact conj_mem_zpowers_of_conj_mem (by rw [hz]; exact z_mem_pair z t)
    · exact conj_mem_zpowers_of_conj_mem ht
  have hcK : ∀ c ∈ centZ z, ∀ k ∈ centPair z t, c * k * c⁻¹ ∈ centPair z t := by
    intro c hc k hk
    rw [mem_centralizer_iff]
    intro a ha
    have ha' : c⁻¹ * a * c ∈ pair z t := by
      have := hcpair c⁻¹ (inv_mem hc) a ha
      rwa [inv_inv] at this
    have hcomm : (c⁻¹ * a * c) * k = k * (c⁻¹ * a * c) := mem_centralizer_iff.1 hk _ ha'
    calc a * (c * k * c⁻¹) = c * ((c⁻¹ * a * c) * k) * c⁻¹ := by group
      _ = c * (k * (c⁻¹ * a * c)) * c⁻¹ := by rw [hcomm]
      _ = (c * k * c⁻¹) * a := by group
  have hcY : ∀ c ∈ centZ z, ∀ y ∈ O2In (centPair z t), c * y * c⁻¹ ∈ O2In (centPair z t) := by
    intro c hc y hy
    set Y' : Subgroup G := (O2In (centPair z t)).map (MulAut.conj c).toMonoidHom with hY'
    have hY'K : Y' ≤ centPair z t := by
      rintro _ ⟨y', hy', rfl⟩
      exact hcK c hc y' (O2In_le _ hy')
    have hn : (Y'.subgroupOf (centPair z t)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨y', hy', hyn⟩ := hn
      have hg : (c⁻¹ * (g : G) * c) ∈ centPair z t := by
        have := hcK c⁻¹ (inv_mem hc) g g.2
        rwa [inv_inv] at this
      refine ⟨(c⁻¹ * (g : G) * c) * y' * (c⁻¹ * (g : G) * c)⁻¹, d.conj_O2K hg y' hy', ?_⟩
      have : (MulAut.conj c) y' = (n : G) := hyn
      rw [MulAut.conj_apply] at this
      show c * ((c⁻¹ * (g : G) * c) * y' * (c⁻¹ * (g : G) * c)⁻¹) * c⁻¹ =
        (g : G) * (n : G) * (g : G)⁻¹
      rw [← this]
      group
    have hp : IsPGroup 2 Y' := (isPGroup_O2In (centPair z t)).of_equiv
      (Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)
    exact le_O2In hY'K hn hp ⟨y, hy, rfl⟩
  have hnormal : ((O2In (centPair z t)).subgroupOf (centZ z)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hcY g g.2 n hn
  exact le_O2In ((O2In_le _).trans hKC) hnormal (isPGroup_O2In _)

theorem Level55.Psub_eq_zpowers (d : Level55 G t z) (hnot : ¬ O2In (centPair z t) ≤ Psub z) :
    Psub z = zpowers z := by
  have hP := d.Psub_le_pair hnot
  have hzP : z ∈ Psub z := self_mem_O2In_centZ d.z_ord
  have htP : t ∉ Psub z := fun htP => hnot (d.O2K_le_P_of_t_mem hP htP)
  refine le_antisymm (fun p hp => ?_) (zpowers_le.2 hzP)
  have hzz := d.z_mul_self
  rcases mem_pair_cases d.z_ord d.t_ord d.zt_comm (hP hp) with h | h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact mem_zpowers z
  · exact absurd (h ▸ hp) htP
  · exfalso
    apply htP
    have : t = z * p := by rw [h, ← mul_assoc, hzz, one_mul]
    rw [this]
    exact mul_mem hzP hp

theorem Level55.isTwoConstrained_iff_Psub_ne (d : Level55 G t z)
    (hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥) :
    IsTwoConstrained (centZ z) ↔ Psub z ≠ zpowers z := by
  rw [d.isTwoConstrained_iff_O2K_le_P hodd]
  constructor
  · intro hY hP
    have htP : t ∈ Psub z := hY (d.pair_le_O2K (t_mem_pair z t))
    rw [hP] at htP
    rcases eq_one_or_eq_of_mem_zpowers_two d.z_ord htP with h | h
    · have := d.t_ord
      rw [h, orderOf_one] at this
      omega
    · exact d.z_ne_t h.symm
  · intro hne
    by_contra hnot
    exact hne (d.Psub_eq_zpowers hnot)

end Certified

end CFSG.EvenSporadicStandard.TwoB
