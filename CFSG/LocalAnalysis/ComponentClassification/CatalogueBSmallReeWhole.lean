module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.LieType.Simplicity.ReeSmall
public import CFSG.LieType.Ree.SmallReeThreeDerived

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr quasisimple_subnormal_subgroups)

theorem pComponent_eq_top_of_isSimpleGroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x) {p : ℕ} (J : Subgroup S)
    (hJ : CFSG.IsPComponent p J) : J = ⊤ := by
  have hquasi := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hZ : Subgroup.center S = ⊥ := by
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hJnt := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hJ
  obtain ⟨-, -, hJsub, -, -⟩ := hJ
  rcases quasisimple_subnormal_subgroups hquasi hJsub with h | h
  · exact h
  · rw [hZ] at h
    exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hJnt
    apply hab
    have ha' := le_bot_iff.1 h ▸ ha
    have hb' := le_bot_iff.1 h ▸ hb
    rw [Subgroup.mem_bot] at ha' hb'
    exact Subtype.ext (ha'.trans hb'.symm)

theorem isSolvable_quotient_commutator (G : Type*) [Group G] :
    Group.IsSolvable (G ⧸ commutator G) :=
  Group.isSolvable_of_comm fun x y => @mul_comm (Abelianization G) _ x y

theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem reeGamma_G2_simple {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    commutator (ReeTag.G2.reeGamma K a) = ⊤ ∧ IsSimpleGroup (ReeTag.G2.reeGamma K a) ∧
      ∃ x y : ReeTag.G2.reeGamma K a, x * y ≠ y * x := by
  have hK' : Nat.card K = ReeTag.G2.prime ^ (2 * a + 1) := hK
  have hperf := (ReeTag.ree_generic_fixed_group_perfect ReeTag.G2 a ha K hK').2.1
  have hZ := (small_Ree_fixed_group_center_trivial a K hK).1
  have h1 : ReeTag.G2.reeGamma K a =
      (reeFixed ReeTag.G2 K a).map (adjointGroup ReeTag.G2.tag K).subtype :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.G2) (K := K) (a := a)).trans
      (reeFixedGroup_eq_map_reeFixed ReeTag.G2 K a)
  let e : reeFixed ReeTag.G2 K a ≃* ReeTag.G2.reeGamma K a :=
    ((reeFixed ReeTag.G2 K a).equivMapOfInjective _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr h1.symm)
  have hQfix := CFSG.LieType.Simplicity.isQuasisimple_commutator_reeFixed_G2 (K := K) a ha hK'
  let e' : commutator (reeFixed ReeTag.G2 K a) ≃* commutator (ReeTag.G2.reeGamma K a) :=
    ((commutator (reeFixed ReeTag.G2 K a)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_mulEquiv e))
  have hQ' : CFSG.IsQuasisimple (commutator (ReeTag.G2.reeGamma K a)) :=
    (isQuasisimple_congr e').1 hQfix
  have hQ : CFSG.IsQuasisimple (ReeTag.G2.reeGamma K a) :=
    (isQuasisimple_congr ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv)).1 hQ'
  have : IsSimpleGroup (ReeTag.G2.reeGamma K a ⧸ Subgroup.center (ReeTag.G2.reeGamma K a)) :=
    hQ.2.1
  refine ⟨hperf,
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup,
    ?_⟩
  obtain ⟨x, y, hxy⟩ := hQ.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x', y', fun h => hxy (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem small_Ree_whole_group_p_components (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    IsSimpleGroup (commutator (ReeTag.G2.reeGamma K a)) ∧
    (∃ x y : commutator (ReeTag.G2.reeGamma K a), x * y ≠ y * x) ∧
    Group.IsSolvable (ReeTag.G2.reeGamma K a ⧸ commutator (ReeTag.G2.reeGamma K a)) ∧
    (1 ≤ a → commutator (ReeTag.G2.reeGamma K a) = ⊤) ∧
    (a = 0 → ∀ w₀ : WeylGroup ReeTag.G2.tag, (∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
        (coxeterSystem ReeTag.G2.tag).length w₀) →
      (commutator (ReeTag.G2.reeGamma K a)).map (ReeTag.G2.reeGamma K a).subtype =
          Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
        Nat.card (commutator (ReeTag.G2.reeGamma K a)) = 504 ∧
        (commutator (ReeTag.G2.reeGamma K a)).index = 3) ∧
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (ReeTag.G2.reeGamma K a),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L ∧ L = commutator (ReeTag.G2.reeGamma K a) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  have hsolv : Group.IsSolvable (Γ ⧸ commutator Γ) := isSolvable_quotient_commutator Γ
  have hzero : a = 0 → ∀ w₀ : WeylGroup ReeTag.G2.tag, (∀ w, (coxeterSystem ReeTag.G2.tag).length
      w ≤ (coxeterSystem ReeTag.G2.tag).length w₀) →
      (commutator Γ).map Γ.subtype =
          Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
        Nat.card (commutator Γ) = 504 ∧ (commutator Γ).index = 3 ∧
        IsSimpleGroup (commutator Γ) ∧ ∃ x y : commutator Γ, x * y ≠ y * x := by
    rintro rfl w₀ hw₀
    have hK3 : Nat.card K = 3 := by simpa using hK
    obtain ⟨-, hDΓ, -, hD504, hDidx, hDsimp, hDnab, hcomm⟩ :=
      small_Ree_three_derived_simple K hK3 w₀ hw₀
    set D := Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}
      with hD
    have hmap : (commutator Γ).map Γ.subtype = D := by
      rw [Subgroup.map_subtype_commutator, hcomm]
    let e : commutator Γ ≃* D :=
      ((commutator Γ).equivMapOfInjective Γ.subtype Γ.subtype_injective).trans
        (MulEquiv.subgroupCongr hmap)
    have hsub : commutator Γ = D.subgroupOf Γ := by
      apply Subgroup.map_injective Γ.subtype_injective
      rw [hmap, Subgroup.subgroupOf_map_subtype, inf_of_le_left hDΓ]
    refine ⟨hmap, by rw [Nat.card_congr e.toEquiv, hD504], by rw [hsub, hDidx],
      e.isSimpleGroup, ?_⟩
    obtain ⟨x, y, hxy⟩ := hDnab
    exact ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  have hsimple : IsSimpleGroup (commutator Γ) ∧ ∃ x y : commutator Γ, x * y ≠ y * x := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
      obtain ⟨-, -, -, h1, h2⟩ := hzero rfl w₀ hw₀
      exact ⟨h1, h2⟩
    · obtain ⟨hperf, hΓs, x, y, hxy⟩ := reeGamma_G2_simple ha K hK
      let e : commutator Γ ≃* Γ := (MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv
      have : IsSimpleGroup Γ := hΓs
      exact ⟨e.isSimpleGroup, e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
  obtain ⟨hs, hnc⟩ := hsimple
  refine ⟨hs, hnc, hsolv, fun ha => (reeGamma_G2_simple ha K hK).1,
    fun h0 w₀ hw₀ => (hzero h0 w₀ hw₀).elim fun h1 h2 => ⟨h1, h2.1, h2.2.1⟩, ?_⟩
  intro p hp L hL
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hle, hL'⟩ := pComponent_in_normal_of_solvable_quotient p (commutator Γ) L hL
  have htop := pComponent_eq_top_of_isSimpleGroup hnc _ hL'
  have hq := pComponent_quasisimple_of_isSimpleGroup hnc _ hL'
  refine ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hle)).1 hq,
    le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)⟩

end CFSG.ComponentClassification.CatalogueBSmallRee
