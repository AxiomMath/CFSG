module

public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.E2.CompCerts
public import CFSG.GH74.Orders.LieType
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.Assembly.LowTwoRank

section Generic

variable {K : Type} [Group K]

theorem center_eq_bot_of_simple_of_not_prime [IsSimpleGroup K] (h : ¬ (Nat.card K).Prime) :
    center K = ⊥ := by
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h1 | h1
  · exact h1
  · exfalso
    have hc : ∀ x y : K, x * y = y * x := fun x y => by
      have : y ∈ center K := h1 ▸ Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp this x
    let : CommGroup K := { ‹Group K› with mul_comm := hc }
    exact h IsSimpleGroup.prime_card

theorem isCyclic_of_group_rank_le_one {G : Type} [Group G] [Finite G] (h : Group.rank G ≤ 1) :
    IsCyclic G := by
  obtain ⟨S, hS, hcl⟩ := Group.rank_spec G
  have hcard : S.card ≤ 1 := hS ▸ h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
  · rw [Finset.card_eq_zero] at h0
    subst h0
    have hbot : (⊥ : Subgroup G) = ⊤ := by simpa using hcl
    have : Subsingleton G := ⟨fun a b => by
      have ha : a ∈ (⊥ : Subgroup G) := by rw [hbot]; exact Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup G) := by rw [hbot]; exact Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]⟩
    infer_instance
  · obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure] at hcl
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, hcl⟩

theorem exists_twoSubgroup_rank_gt [Finite K] {r : ℕ} (h : ¬ CFSG.GH74.SectionalTwoRankLE K r) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ r < Group.rank U := by
  by_contra hcon
  push Not at hcon
  apply h
  intro P hP
  obtain ⟨s, hs, hcl⟩ := Group.rank_spec P
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_⟩
  · rw [Finset.card_map, hs]
    exact hcon P hP
  · have himg : (⇑(Function.Embedding.subtype fun x => x ∈ P) '' (s : Set P)) =
        P.subtype '' (s : Set P) := rfl
    rw [Finset.coe_map, himg, ← MonoidHom.map_closure, hcl, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

theorem exists_twoSubgroup_rank_ge_of_quotient [Finite K] (N : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) {r : ℕ}
    (h : ∃ U : Subgroup (K ⧸ N), IsPGroup 2 U ∧ r ≤ Group.rank U) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ r ≤ Group.rank U := by
  obtain ⟨U, hU, hr⟩ := h
  let π : K →* K ⧸ N := QuotientGroup.mk' N
  refine ⟨U.comap π, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hU ⟨π x, hx⟩
    have h1 : x ^ (2 ^ k) ∈ N := by
      have : π (x ^ (2 ^ k)) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨m, hm⟩ := hN ⟨x ^ (2 ^ k), h1⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have := congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using this
  · let f : ↥(U.comap π) →* ↥U := (π.comp (U.comap π).subtype).codRestrict U (fun x => x.2)
    have hf : Function.Surjective f := by
      rintro ⟨u, hu⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨⟨x, hu⟩, rfl⟩
    exact hr.trans (Group.rank_le_of_surjective f hf)

theorem exists_twoSubgroup_rank_two_of_simple [Finite K] [IsSimpleGroup K]
    (hn : ¬ (Nat.card K).Prime) (he : Even (Nat.card K)) :
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := inferInstance
  refine ⟨S, S.isPGroup', ?_⟩
  by_contra hlt
  have hcyc : IsCyclic S := isCyclic_of_group_rank_le_one (by omega)
  obtain ⟨N, hN, hNS⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hcyc
  have hcard := hNS.card_mul_card
  rcases hN.eq_bot_or_eq_top with h0 | h0
  · subst h0
    have h1 : Nat.card S = Nat.card K := by simpa using hcard
    have hS : (S : Subgroup K) = ⊤ := Subgroup.eq_top_of_card_eq _ h1
    have : IsCyclic K := by
      have e : (S : Subgroup K) ≃* K := (MulEquiv.subgroupCongr hS).trans Subgroup.topEquiv
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    let : CommGroup K := IsCyclic.commGroup
    exact hn IsSimpleGroup.prime_card
  · subst h0
    have h1 : Nat.card S = 1 := by
      have : Nat.card (⊤ : Subgroup K) = Nat.card K := Subgroup.card_top
      rw [this] at hcard
      have hpos : 0 < Nat.card K := Nat.card_pos
      nlinarith
    have hS : (S : Subgroup K) = ⊥ := Subgroup.card_eq_one.mp h1
    have hdvd : ¬ 2 ∣ (S : Subgroup K).index := S.not_dvd_index
    rw [hS, Subgroup.index_bot] at hdvd
    exact hdvd (even_iff_two_dvd.mp he)

end Generic

section Nine

variable {K : Type} [Group K]

private theorem facts_of_card (hs : IsSimpleGroup K) {m : ℕ} (hc : Nat.card K = m)
    (he : Even m) (hp : ¬ m.Prime) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  rw [hc]
  exact ⟨hs, he, hp⟩

private theorem facts_of_psl {n p f : ℕ} (hn : n ≠ 0) (h : LieModel K .PSL n p f) {m : ℕ}
    (hc : Nat.card K = m) (he : Even m) (hp : ¬ m.Prime) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_card (CFSG.LieType.Simplicity.fam_PSL_simplicity K n p f
    (CFSG.GH74.statedClassicalModel_of_lieModel hn h)).2 hc he hp

private theorem facts_of_psu {n p f : ℕ} (hn : n ≠ 0) (h : LieModel K .PSU n p f) {m : ℕ}
    (hc : Nat.card K = m) (he : Even m) (hp : ¬ m.Prime) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_card (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity K n p f
    (CFSG.GH74.statedClassicalModel_of_lieModel hn h)).2 hc he hp

private theorem facts_of_twistedB2 (h : LieModel K .twistedB2 0 2 3) {m : ℕ}
    (hc : Nat.card K = m) (he : Even m) (hp : ¬ m.Prime) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  rcases h with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact facts_of_card (CFSG.LieType.Simplicity.fam_2b2_simplicity K 2 3 h).2 hc he hp

private theorem facts_of_equiv {L : Type} [Group L] (e : K ≃* L) (hs : IsSimpleGroup L) {m : ℕ}
    (hc : Nat.card L = m) (he : Even m) (hp : ¬ m.Prime) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_card (e.isSimpleGroup_congr.2 hs) (by rw [Nat.card_congr e.toEquiv, hc]) he hp

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

private theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem ShapeA5.facts (h : ShapeA5 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  rcases h with he | h | h
  · obtain ⟨e⟩ := he
    exact facts_of_equiv e (alternatingGroup.isSimpleGroup (by simp)) card_alt_five
      (by decide) (by norm_num)
  · exact facts_of_psl (by norm_num) h (m := 60)
      (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)
  · exact facts_of_psl (by norm_num) h (m := 60)
      (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeL27.facts (h : ShapeL27 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  rcases h with h | h
  · exact facts_of_psl (by norm_num) h (m := 168)
      (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)
  · exact facts_of_psl (by norm_num) h (m := 168)
      (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeA6.facts (h : ShapeA6 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  rcases h with he | h
  · obtain ⟨e⟩ := he
    exact facts_of_equiv e (alternatingGroup.isSimpleGroup (by simp)) card_alt_six
      (by decide) (by norm_num)
  · exact facts_of_psl (by norm_num) h (m := 360)
      (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeL217.facts (h : ShapeL217 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_psl (by norm_num) h (m := 2448)
    (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeL28.facts (h : ShapeL28 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_psl (by norm_num) h (m := 504)
    (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeL33.facts (h : ShapeL33 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_psl (by norm_num) h (m := 5616)
    (by rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]; decide) (by decide) (by norm_num)

theorem ShapeU33.facts (h : ShapeU33 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_psu (by norm_num) h (m := 6048)
    (by rw [CFSG.GH74.card_of_lieModel_PSU (by norm_num) (by norm_num) h]; decide) (by decide)
    (by norm_num)

theorem ShapeSz8.facts (h : ShapeSz8 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime :=
  facts_of_twistedB2 h (m := 29120)
    (by rw [CFSG.GH74.card_of_lieModel_twistedB2 h]; decide) (by decide) (by norm_num)

theorem ShapeM11.facts (h : ShapeM11 K) :
    IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime := by
  obtain ⟨e⟩ := h
  have e' : K ≃* NativeSporadic.M11 := e
  exact facts_of_equiv e' CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    CFSG.Sporadic.Mathieu.card_M11 (by decide) (by norm_num)

end Nine

section Consequences

variable {K : Type} [Group K]

private theorem center_eq_bot_of_facts
    (hf : IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime) : center K = ⊥ := by
  have := hf.1
  exact center_eq_bot_of_simple_of_not_prime hf.2.2

theorem center_eq_bot_of_simpleShapes
    (h : ShapeL28 K ∨ ShapeU33 K ∨ ShapeA6 K ∨ ShapeL33 K ∨ ShapeM11 K ∨ ShapeA5 K ∨ ShapeL27 K ∨
      ShapeL217 K ∨ ShapeSz8 K) : center K = ⊥ := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts
  · exact center_eq_bot_of_facts h.facts

theorem card_center_le_two_of_K0Shape
    (h : K0Shape K) : Nat.card (center K) ≤ 2 := by
  have hbot : center K = ⊥ → Nat.card (center K) ≤ 2 := fun hb => by
    rw [hb, Subgroup.card_bot]
    norm_num
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact hbot (center_eq_bot_of_facts h.facts)
  · exact h.2.1.le
  · exact h.2.1.le

theorem shape2_of_K0Shape_center_ne_bot
    (h : K0Shape K) (hc : center K ≠ ⊥) : Shape2M12 K ∨ Shape2Sz8 K := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact absurd (center_eq_bot_of_facts h.facts) hc
  · exact Or.inl h
  · exact Or.inr h

end Consequences

section ConsequencesFinite

variable {K : Type} [Group K] [Finite K]

private theorem exists_twoSubgroup_rank_two_of_facts
    (hf : IsSimpleGroup K ∧ Even (Nat.card K) ∧ ¬ (Nat.card K).Prime) :
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T := by
  have := hf.1
  exact exists_twoSubgroup_rank_two_of_simple hf.2.2 hf.2.1

theorem exists_twoSubgroup_rank_two_of_K0Shape
    (h : K0Shape K) (hc : center K = ⊥) :
    ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T := by
  have hcover : Nat.card (center K) = 2 → ∃ T : Subgroup K, IsPGroup 2 T ∧ 2 ≤ Group.rank T :=
    fun hn => by
      rw [hc, Subgroup.card_bot] at hn
      exact absurd hn (by norm_num)
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact exists_twoSubgroup_rank_two_of_facts h.facts
  · exact hcover h.2.1
  · exact hcover h.2.1

theorem rank_ge3_of_shapeL28 (h : ShapeL28 K) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U := by
  obtain ⟨U, hU, hr⟩ := exists_twoSubgroup_rank_gt (rank2_L2_8 h).not_sectionalTwoRankLE
  exact ⟨U, hU, by omega⟩

theorem rank_ge3_of_shapeU33 (h : ShapeU33 K) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U := by
  obtain ⟨U, hU, hr⟩ := exists_twoSubgroup_rank_gt (rank2_U3_3 h).not_sectionalTwoRankLE
  exact ⟨U, hU, by omega⟩

theorem rank_ge3_of_shapeSz8 (h : ShapeSz8 K) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U := by
  obtain ⟨U, hU, hr⟩ := exists_twoSubgroup_rank_gt (rank2_Sz8 h).not_sectionalTwoRankLE
  exact ⟨U, hU, by omega⟩

theorem rank_ge4_of_shape2M12 (h : Shape2M12 K) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 4 ≤ Group.rank U := by
  obtain ⟨-, hc, hM⟩ := h
  have hZ : IsPGroup 2 (center K) := IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  refine exists_twoSubgroup_rank_ge_of_quotient (center K) hZ ?_
  obtain ⟨U, hU, hr⟩ := exists_twoSubgroup_rank_gt (rank3_M12 hM).not_sectionalTwoRankLE
  exact ⟨U, hU, by omega⟩

theorem rank_ge3_of_shape2Sz8 (h : Shape2Sz8 K) :
    ∃ U : Subgroup K, IsPGroup 2 U ∧ 3 ≤ Group.rank U := by
  obtain ⟨-, hc, hS⟩ := h
  have hZ : IsPGroup 2 (center K) := IsPGroup.of_card (n := 1) (by rw [hc]; norm_num)
  exact exists_twoSubgroup_rank_ge_of_quotient (center K) hZ (rank_ge3_of_shapeSz8 hS)

end ConsequencesFinite

end CFSG.GH74.E2
