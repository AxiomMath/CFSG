module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

@[expose] noncomputable def sylowComponentPreimage (hz : IsCentralInvolution (S : Subgroup G) z)
    (J : Subgroup (EscapingQuotient z)) : Subgroup (S : Subgroup G) :=
  J.comap (sylowBar hz)

variable {H : Subgroup G} (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J) {D : Subgroup (EscapingQuotient z)} {q : ℕ}
  (hlin : LinearSylowData J ((sylowBar hz).range ⊓ J) D q)
include hset hz hesc hJ hzJ hlin

theorem caseOne_commute_R {a : EscapingQuotient z} (ha : a ∈ (sylowBar hz).range) :
    ∀ x ∈ (sylowBar hz).range ⊓ J, a * x = x * a := by
  have hq := caseOne_quotientData hset hz hesc
  intro x hx
  rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin ha with h | h
  · exact hlin.comm a ⟨ha, h⟩ x hx
  · have haR : escapingBar z * a ∈ (sylowBar hz).range ⊓ J :=
      ⟨(sylowBar hz).range.mul_mem (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) ha, h⟩
    have h2 : Commute (escapingBar z * a) x := hlin.comm _ haR x hx
    have h3 := ((hq.commute_bar x).symm.inv_left).mul_left h2
    rwa [inv_mul_cancel_left] at h3

theorem caseOne_sylowBar_comm {a b : EscapingQuotient z} (ha : a ∈ (sylowBar hz).range)
    (hb : b ∈ (sylowBar hz).range) : a * b = b * a := by
  have hq := caseOne_quotientData hset hz hesc
  rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin hb with h | h
  · exact caseOne_commute_R hset hz hesc hJ hzJ hlin ha b ⟨hb, h⟩
  · have hbR : escapingBar z * b ∈ (sylowBar hz).range ⊓ J :=
      ⟨(sylowBar hz).range.mul_mem (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) hb, h⟩
    have h2 : Commute a (escapingBar z * b) := caseOne_commute_R hset hz hesc hJ hzJ hlin ha _ hbR
    have h3 := ((hq.commute_bar a).inv_right).mul_right h2
    rwa [inv_mul_cancel_left] at h3

theorem caseOne_sylowBar_sq {a : EscapingQuotient z} (ha : a ∈ (sylowBar hz).range) :
    a * a = 1 := by
  have hq := caseOne_quotientData hset hz hesc
  rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin ha with h | h
  · exact hlin.sq a ⟨ha, h⟩
  · rw [← central_involution_mul_mul_self hq.commute_bar (escapingBar_mul_self hz.2.1) a]
    exact hlin.sq _ ⟨(sylowBar hz).range.mul_mem (by rw [← sylowBar_self hz]; exact ⟨_, rfl⟩) ha, h⟩

theorem caseOne_sylow_comm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a :=
  fun a ha b hb => commute_of_sylowBar hz (s := ⟨a, ha⟩) (t := ⟨b, hb⟩)
    (caseOne_sylowBar_comm hset hz hesc hJ hzJ hlin ⟨_, rfl⟩ ⟨_, rfl⟩)

theorem caseOne_sylow_sq : ∀ a ∈ (S : Subgroup G), a * a = 1 :=
  fun a ha => mul_self_eq_one_of_sylowBar hz (s := ⟨a, ha⟩)
    (caseOne_sylowBar_sq hset hz hesc hJ hzJ hlin ⟨_, rfl⟩)

theorem isCompl_zpowers_sylowComponentPreimage :
    IsCompl (Subgroup.zpowers (⟨z, hz.1⟩ : (S : Subgroup G))) (sylowComponentPreimage hz J) := by
  have hz2 : orderOf (⟨z, hz.1⟩ : (S : Subgroup G)) = 2 := by rw [Subgroup.orderOf_mk, hz.2.1]
  constructor
  · rw [Subgroup.disjoint_def]
    intro x hx hxW
    rcases eq_one_or_eq_of_mem_zpowers hz2 hx with h | h
    · exact h
    · rw [h] at hxW
      exact absurd hxW hzJ
  · rw [codisjoint_iff, eq_top_iff]
    intro s _
    rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin ⟨s, rfl⟩ with h | h
    · exact Subgroup.mem_sup_right h
    · have hzs : (⟨z, hz.1⟩ : (S : Subgroup G)) * s ∈ sylowComponentPreimage hz J := by
        change sylowBar hz (⟨z, hz.1⟩ * s) ∈ J
        rw [map_mul, sylowBar_self]
        exact h
      have hzz : (⟨z, hz.1⟩ : (S : Subgroup G)) * ⟨z, hz.1⟩ = 1 :=
        Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hz.2.1)
      have hs : s = ⟨z, hz.1⟩ * (⟨z, hz.1⟩ * s) := by rw [← mul_assoc, hzz, one_mul]
      rw [hs]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) hzs

omit hset hesc hJ hzJ in
theorem card_sylowComponentPreimage : Nat.card (sylowComponentPreimage hz J) = q := by
  rw [← hlin.card, ← Subgroup.map_comap_eq,
    ← Subgroup.card_map_of_injective (sylowBar_injective hz)]
  rfl

theorem caseOne_card_sylow : Nat.card (S : Subgroup G) = 2 * q := by
  have hJn := caseOne_component_normal hset hz hesc hJ hzJ
  have : (sylowComponentPreimage hz J).Normal := hJn.comap (sylowBar hz)
  have hc := isCompl_zpowers_sylowComponentPreimage hset hz hesc hJ hzJ hlin
  have hindex : (sylowComponentPreimage hz J).index = 2 := by
    rw [← Subgroup.relIndex_top_right, ← hc.sup_eq_top, Subgroup.relIndex_sup_right,
      ← Subgroup.inf_relIndex_right, inf_comm, hc.inf_eq_bot, Subgroup.relIndex_bot_left,
      Nat.card_zpowers, Subgroup.orderOf_mk, hz.2.1]
  rw [← Subgroup.card_mul_index (sylowComponentPreimage hz J), hindex,
    card_sylowComponentPreimage hz hlin, mul_comm]

theorem caseOne_sylow_transitive : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a ≠ 1 →
    b ≠ 1 → ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G), n⁻¹ * a * n = b := by
  have hcentral : ∀ a ∈ (S : Subgroup G), a ≠ 1 → IsCentralInvolution (S : Subgroup G) a := by
    intro a ha ha1
    have haa := caseOne_sylow_sq hset hz hesc hJ hzJ hlin a ha
    exact ⟨ha, orderOf_eq_prime (by rw [pow_two]; exact haa) ha1,
      fun s hs => caseOne_sylow_comm hset hz hesc hJ hzJ hlin s hs a ha⟩
  intro a ha b hb ha1 hb1
  obtain ⟨na, hna, hnaz⟩ :=
    caseOne_exists_normalizer_conj_eq hset hz hesc hJ hzJ hlin (hcentral a ha ha1)
  obtain ⟨nb, hnb, hnbz⟩ :=
    caseOne_exists_normalizer_conj_eq hset hz hesc hJ hzJ hlin (hcentral b hb hb1)
  refine ⟨na⁻¹ * nb, Subgroup.mul_mem _ (Subgroup.inv_mem _ hna) hnb, ?_⟩
  rw [← hnaz, ← hnbz]
  group

end CFSG.ProperTwoGeneratedCore.Lemma37
