module

public import CFSG.GH74.KGroups.Generic8
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.CoverJ2Tables
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverLift
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.KGroups.J2

open CFSG.ComponentClassification.J2Cover.Models CFSG.ComponentClassification.CentralCover

@[expose] noncomputable def gR
    (p : ℕ × ℕ) : RfN := ⟨(p.1 : ZMod 2), eS.symm (elt p.2)⟩

theorem gR_mul
    {p q : ℕ × ℕ} (hp : p.2 < 128) (hq : q.2 < 128) :
    gR p * gR q = gR (mulM p q) := by
  have hm := mulIdx_spec (a := p.2) hq
  have h1 : fN (eS.symm (elt p.2)) (eS.symm (elt q.2)) =
      if bitAt fRows p.2 q.2 then 1 else 0 := by
    rw [fN_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, fCoc]
    exact tbl_elt fRows hp hq
  have h2 : eS.symm (elt p.2) * eS.symm (elt q.2) = eS.symm (elt (mulIdx p.2 q.2)) := by
    rw [hm.2, map_mul]
  unfold gR
  rw [CocycleExtension.mk_mul_mk, h1, h2]
  refine CocycleExtension.ext ?_ rfl
  show (p.1 : ZMod 2) + (q.1 : ZMod 2) + (if bitAt fRows p.2 q.2 then 1 else 0) =
    (((p.1 + q.1 + if bitAt fRows p.2 q.2 then 1 else 0) % 2 : ℕ) : ZMod 2)
  rw [ZMod.natCast_mod]
  split_ifs <;> simp

theorem gR_zero : gR (0, 0) = 1 := by
  unfold gR
  rw [CocycleExtension.one_def]
  simp [elt_zero]

theorem gR_injective
    {p q : ℕ × ℕ} (hp : p.1 < 2 ∧ p.2 < 128) (hq : q.1 < 2 ∧ q.2 < 128)
    (h : gR p = gR q) : p = q := by
  have h1 : ((p.1 : ℕ) : ZMod 2) = (q.1 : ℕ) := congrArg CocycleExtension.fst h
  have h2 : eS.symm (elt p.2) = eS.symm (elt q.2) := congrArg CocycleExtension.snd h
  have h3 : elt p.2 = elt q.2 := eS.symm.injective h2
  have h4 : p.2 = q.2 := elt_injective hp.2 hq.2 h3
  have h5 : p.1 = q.1 := by
    have := (ZMod.natCast_eq_natCast_iff' p.1 q.1 2).1 h1
    rwa [Nat.mod_eq_of_lt hp.1, Nat.mod_eq_of_lt hq.1] at this
  exact Prod.ext h5 h4

@[expose] noncomputable def Usub
    : Subgroup RfN where
  carrier := {x | ∃ p ∈ uList, x = gR p}
  mul_mem' := by
    rintro _ _ ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
    exact ⟨mulM p q, uList_mul p hp q hq, gR_mul (uList_lt p hp).2 (uList_lt q hq).2⟩
  one_mem' := ⟨(0, 0), uList_one, gR_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := uList_inv p hp
    refine ⟨q, hq, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [gR_mul (uList_lt p hp).2 (uList_lt q hq).2, hpq, gR_zero]

theorem mem_Usub
    {x : RfN} : x ∈ Usub ↔ ∃ p ∈ uList, x = gR p := Iff.rfl

theorem gR_nElt_sq
    : gR nElt * gR nElt = 1 := by
  rw [gR_mul (uList_lt _ nElt_mem).2 (uList_lt _ nElt_mem).2, nElt_sq, gR_zero]

@[expose] noncomputable def Nsub
    : Subgroup RfN where
  carrier := {x | x = 1 ∨ x = gR nElt}
  mul_mem' := by
    rintro _ _ (rfl | rfl) (rfl | rfl)
    · left; simp
    · right; simp
    · right; simp
    · left; exact gR_nElt_sq
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro _ (rfl | rfl)
    · left; simp
    · right; exact inv_eq_of_mul_eq_one_right gR_nElt_sq

theorem Nsub_le
    : Nsub ≤ Usub := by
  rintro x (rfl | rfl)
  · exact Usub.one_mem
  · exact ⟨nElt, nElt_mem, rfl⟩

theorem gR_nElt_ne_one
    : gR nElt ≠ 1 := by
  intro h
  rw [← gR_zero] at h
  exact nElt_ne (gR_injective (uList_lt _ nElt_mem) ⟨by norm_num, by norm_num⟩ h)

theorem gR_nElt_central
    {x : RfN} (hx : x ∈ Usub) : x * gR nElt = gR nElt * x := by
  obtain ⟨p, hp, rfl⟩ := hx
  rw [gR_mul (uList_lt p hp).2 (uList_lt _ nElt_mem).2,
    gR_mul (uList_lt _ nElt_mem).2 (uList_lt p hp).2, nElt_central p hp]

theorem card_Usub
    : Nat.card Usub = 64 := by
  have hbij : Function.Bijective (fun p : {p : ℕ × ℕ // p ∈ uList} =>
      (⟨gR p.1, ⟨p.1, p.2, rfl⟩⟩ : Usub)) := by
    constructor
    · intro p q h
      exact Subtype.ext (gR_injective (uList_lt _ p.2) (uList_lt _ q.2) (congrArg Subtype.val h))
    · rintro ⟨x, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  have e : {p : ℕ × ℕ // p ∈ uList} ≃ {p : ℕ × ℕ // p ∈ uList.toFinset} :=
    Equiv.subtypeEquivRight fun p => List.mem_toFinset.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup uList_nodup, uList_length]

theorem card_Nsub
    : Nat.card Nsub = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Or.inl rfl⟩, ⟨gR nElt, Or.inr rfl⟩, ?_, ?_⟩
  · intro h
    exact gR_nElt_ne_one (congrArg (fun z : Nsub => (z : RfN)) h).symm
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases z.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem five_le_rank_Usub
    : 5 ≤ Group.rank Usub := by
  let N : Subgroup Usub := Nsub.subgroupOf Usub
  have hle : N ≤ Subgroup.center Usub := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hn' : (n : RfN) ∈ Nsub := hn
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rcases hn' with h | h
    · rw [h, mul_one, one_mul]
    · rw [h]; exact gR_nElt_central g.2
  have : N.Normal := Subgroup.normal_of_le_center hle
  have hsq : ∀ x : Usub, x ^ 2 ∈ N := by
    intro x
    obtain ⟨p, hp, hx⟩ := x.2
    show ((x ^ 2 : Usub) : RfN) ∈ Nsub
    rw [Subgroup.coe_pow, pow_two, hx, gR_mul (uList_lt p hp).2 (uList_lt p hp).2]
    rcases u_sq p hp with h | h
    · rw [h, gR_zero]; exact Nsub.one_mem
    · rw [h]; exact Or.inr rfl
  have hcomm : ∀ x y : Usub, x * y * (y * x)⁻¹ ∈ N := by
    intro x y
    obtain ⟨p, hp, hx⟩ := x.2
    obtain ⟨q, hq, hy⟩ := y.2
    show ((x * y * (y * x)⁻¹ : Usub) : RfN) ∈ Nsub
    have hqp : (mulM q p).2 < 128 := (uList_lt _ (uList_mul q hq p hp)).2
    have hxy : (x : RfN) * (y : RfN) = gR (mulM p q) := by
      rw [hx, hy, gR_mul (uList_lt p hp).2 (uList_lt q hq).2]
    have hyx : (y : RfN) * (x : RfN) = gR (mulM q p) := by
      rw [hx, hy, gR_mul (uList_lt q hq).2 (uList_lt p hp).2]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hxy, hyx]
    rcases u_comm p hp q hq with h | h
    · have h0 : ((0, 0) : ℕ × ℕ).2 < 128 := by norm_num
      rw [h, ← gR_mul h0 hqp, gR_zero, one_mul, mul_inv_cancel]
      exact Nsub.one_mem
    · have hn : nElt.2 < 128 := (uList_lt _ nElt_mem).2
      rw [h, ← gR_mul hn hqp, mul_assoc, mul_inv_cancel, mul_one]
      exact Or.inr rfl
  have hcardN : Nat.card N = 2 := by
    rw [show Nat.card N = Nat.card Nsub from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Nsub_le).toEquiv, card_Nsub]
  exact rank_ge_of_quotient N hsq hcomm 5 (by rw [hcardN, card_Usub]; norm_num)

theorem not_genLE4_of_J2Cover
    {C : Type} [Group C] [Finite C]
    (hLq : CFSG.Assembly.IsQuasisimple C) (hZ : Nat.card (Subgroup.center C) = 2)
    (eP : C ⧸ Subgroup.center C ≃* CFSG.ComponentClassification.J2Cover.P) : ¬ GenLE4 C := by
  intro hG
  obtain ⟨t, htZ, ht1, htall⟩ := exists_unique_ne_one_of_card_two (Subgroup.center C) hZ
  have ht2 : t ^ 2 = 1 := sq_eq_one_of_card_two (Subgroup.center C) hZ t htZ
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hZ' : Subgroup.center C = Subgroup.zpowers t := by
    apply le_antisymm
    · intro z hz
      rcases htall z hz with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]; exact htZ
  let π : C →* CFSG.ComponentClassification.J2Cover.P :=
    eP.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center C))
  have hπ : Function.Surjective π := eP.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = Subgroup.center C := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = Subgroup.zpowers t := hkerZ.trans hZ'
  obtain ⟨⟨ι, -, -⟩, -, -, -⟩ :=
    CFSG.ComponentClassification.J2Cover.ctss_j2_actual_double_cover_native_sylow_map_and_lift_orders
      hLq ht hZ' π hπ hker
  let φ : RfN →* C := (Subgroup.subtype _).comp ι.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp ι.symm.injective
  have hUc : Nat.card (Usub.map φ) = 64 := by
    rw [Subgroup.card_map_of_injective hφ, card_Usub]
  have hp : IsPGroup 2 (Usub.map φ) := IsPGroup.of_card (n := 6) (by rw [hUc]; norm_num)
  obtain ⟨s, hs, hcl⟩ := hG _ hp
  have hrk : Group.rank (Usub.map φ) ≤ 4 := by
    have h1 := Subgroup.rank_closure_finset_le_card s
    have h2 : Group.rank (Subgroup.closure (s : Set C)) = Group.rank (Usub.map φ) :=
      Subgroup.rank_congr hcl
    omega
  let e : Usub ≃* Usub.map φ := Subgroup.equivMapOfInjective Usub φ hφ
  have h6 : Group.rank Usub ≤ Group.rank (Usub.map φ) :=
    Group.rank_le_of_surjective e.symm.toMonoidHom e.symm.surjective
  have h5 := five_le_rank_Usub
  omega

theorem not_genLE4_of_perfect_double_cover {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) (hJ : Subgroup.center (K ⧸ Subgroup.center K) = ⊥)
    (H : ∀ (C : Type) [Group C] [Finite C], commutator C = ⊤ → Nat.card (Subgroup.center C) = 2 →
      Nonempty (C ⧸ Subgroup.center C ≃* K ⧸ Subgroup.center K) → ¬ GenLE4 C) :
    ¬ GenLE4 K := by
  intro hK
  obtain ⟨C, _, _, φ, hφ, hker, hperfC, hcard, ⟨eC⟩⟩ := exists_double_cover hperf hZ2 hZ hJ
  exact H C hperfC hcard ⟨eC⟩ (sectional_le_of_surjective φ hφ hker 4 hK)

theorem cover_not_gen4_J2
    (K : Type) [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center K))
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2)
    (hZ : Subgroup.center K ≠ ⊥) : ¬ CFSG.GH74.Gen4 K := by
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨e⟩ := h
  exact not_genLE4_of_perfect_double_cover hperf hZ2 hZ hJ
    (fun C _ _ hperfC hC ⟨eC⟩ => not_genLE4_of_J2Cover
      ⟨hperfC, (MulEquiv.isSimpleGroup_congr eC).2 hsimple⟩ hC
      ((eC.trans (e : K ⧸ Subgroup.center K ≃* CFSG.Blueprint.NativeSporadic.J2)).trans
        CFSG.ComponentClassification.J2Cover.nativeEquivP))

end CFSG.GH74.KGroups.J2
