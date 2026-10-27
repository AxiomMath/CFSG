module

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.Cen
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.E2

open Subgroup

theorem assembly_pRank_attained {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ Assembly.IsElemAbelian p E ∧
      Nat.card E = p ^ Assembly.pRank p H := CFSG.SectionRank.exists_pRank hp.one_lt H

theorem elemAb_of_assembly {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : Assembly.IsElemAbelian p E) : ElemAb p E :=
  ⟨fun a ha b hb => by
    have := h.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this,
   h.2⟩

theorem exists_rank_three_of_evenRank {G : Type*} [Group G] [Finite G]
    (h : 3 ≤ Assembly.evenRank G) :
    ∃ (p : ℕ) (A R : Subgroup G), p.Prime ∧ p ≠ 2 ∧ ElemAb p A ∧ Nat.card A = p ^ 3 ∧
      R ≠ ⊥ ∧ IsPGroup 2 R ∧ A ≤ normalizer (R : Set G) := by
  have h3 : ∃ k ∈ {k | ∃ (p : ℕ) (H : Subgroup G), p.Prime ∧ p ≠ 2 ∧ Assembly.IsTwoLocal H ∧
      Assembly.pRank p H = k}, 3 ≤ k := by
    by_contra hcon
    push Not at hcon
    have : Assembly.evenRank G ≤ 2 := by
      refine csSup_le' (fun k hk => ?_)
      have := hcon k hk
      omega
    omega
  obtain ⟨k, ⟨p, H, hp, hp2, ⟨P, hP1, hP2, rfl⟩, rfl⟩, hk⟩ := h3
  obtain ⟨E, hEH, hE, hEcard⟩ := assembly_pRank_attained hp (normalizer (P : Set G))
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ 3 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p hdvd
  have hEab := elemAb_of_assembly hE
  refine ⟨p, K.map E.subtype, P, hp, hp2, ⟨?_, ?_⟩, ?_, hP1, hP2, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hEab.1 a a.2 b b.2
  · rintro _ ⟨a, ha, rfl⟩
    exact hEab.2 a a.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  · rintro _ ⟨a, ha, rfl⟩
    exact hEH a.2

@[expose] def centerOmega1 {G : Type*} [Group G] (R : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ R ∧ (∀ r ∈ R, r * z = z * r) ∧ z ^ 2 = 1}
  one_mem' := ⟨one_mem _, fun r _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haR, haC, ha2⟩ ⟨hbR, hbC, hb2⟩
    have hab : Commute a b := (haC b hbR).symm
    refine ⟨mul_mem haR hbR, fun r hr => ?_, ?_⟩
    · rw [← mul_assoc, haC r hr, mul_assoc, hbC r hr, mul_assoc]
    · rw [hab.mul_pow, ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haR, haC, ha2⟩
    refine ⟨inv_mem haR, fun r hr => ?_, ?_⟩
    · have := haC r hr
      calc r * a⁻¹ = a⁻¹ * (a * r) * a⁻¹ := by group
        _ = a⁻¹ * (r * a) * a⁻¹ := by rw [this]
        _ = a⁻¹ * r := by group
    · rw [inv_pow, ha2, inv_one]

theorem mem_centerOmega1 {G : Type*} [Group G] {R : Subgroup G} {z : G} :
    z ∈ centerOmega1 R ↔ z ∈ R ∧ (∀ r ∈ R, r * z = z * r) ∧ z ^ 2 = 1 := Iff.rfl

theorem centerOmega1_le {G : Type*} [Group G] (R : Subgroup G) : centerOmega1 R ≤ R :=
  fun _ hz => hz.1

theorem centerOmega1_elemAb {G : Type*} [Group G] (R : Subgroup G) : ElemAb 2 (centerOmega1 R) :=
  ⟨fun _ ha _ hb => (ha.2.1 _ hb.1).symm, fun _ ha => ha.2.2⟩

theorem centerOmega1_normalized {G : Type*} [Group G] {R : Subgroup G} {a : G}
    (ha : a ∈ normalizer (R : Set G)) {v : G} (hv : v ∈ centerOmega1 R) :
    a * v * a⁻¹ ∈ centerOmega1 R := by
  obtain ⟨hvR, hvC, hv2⟩ := hv
  have hR : ∀ r, r ∈ R ↔ a * r * a⁻¹ ∈ R := fun r => mem_normalizer_iff.1 ha r
  refine ⟨(hR v).1 hvR, fun r hr => ?_, ?_⟩
  · have hr' : a⁻¹ * r * a ∈ R := by
      have h2 : a * (a⁻¹ * r * a) * a⁻¹ = r := by group
      exact (hR (a⁻¹ * r * a)).2 (by rw [h2]; exact hr)
    have := hvC _ hr'
    calc r * (a * v * a⁻¹) = a * ((a⁻¹ * r * a) * v) * a⁻¹ := by group
      _ = a * (v * (a⁻¹ * r * a)) * a⁻¹ := by rw [this]
      _ = (a * v * a⁻¹) * r := by group
  · calc (a * v * a⁻¹) ^ 2 = a * (v * v) * a⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [← pow_two, hv2]; group

theorem centerOmega1_ne_bot {G : Type*} [Group G] [Finite G] {R : Subgroup G} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) : centerOmega1 R ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR
  have hZ : Nontrivial (Subgroup.center R) := hR2.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center R) := by
    have hZ2 : IsPGroup 2 (Subgroup.center R) := hR2.to_subgroup _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
    have hpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso
        have : Nat.card (Subgroup.center R) = 1 := by rw [hk, h0]; rfl
        have := Nat.card_eq_one_iff_unique.1 this
        exact not_subsingleton _ this.1
      · exact h0
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center R) 2 hdvd
  intro hbot
  have hzV : (z : R).1 ∈ centerOmega1 R := by
    refine ⟨(z : R).2, fun r hr => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 z.2 ⟨r, hr⟩
      exact congrArg Subtype.val this
    · have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg (fun x : Subgroup.center R => ((x : R) : G)) this
  rw [hbot, Subgroup.mem_bot] at hzV
  have : (z : R) = 1 := Subtype.ext hzV
  have hz1 : z = 1 := Subtype.ext this
  rw [hz1, orderOf_one] at hz
  omega

theorem centerOmega1_card_le {G : Type*} [Group G] [Finite G] (hG : Gen4 G) (R : Subgroup G) :
    Nat.card (centerOmega1 R) ≤ 16 := by
  have := SectionalTwoRankLE.card_le_of_elementary hG (centerOmega1 R)
    ⟨⟨⟨fun a b => Subtype.ext ((a.2.2.1 b.1 b.2.1).symm)⟩⟩, fun x hx => hx.2.2⟩
  simpa using this

theorem exists_centralizing_subgroup {G : Type*} [Group G] [Finite G] (hgen : Gen4 G) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {A V : Subgroup G} (hA : ElemAb p A)
    (hAcard : Nat.card A = p ^ 3) (hV2 : IsPGroup 2 V)
    (hnormV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) :
    ∃ B : Subgroup G, B ≤ A ∧ (∀ b ∈ B, ∀ v ∈ V, b * v = v * b) ∧ p ^ 2 ≤ Nat.card B := by
  have hp2 : p ≠ 2 := by omega
  have hnorm := le_normalizer_of_normalizes hnormV
  let φ : A →* MulAut V := conjAction A V hnorm
  let K : Subgroup A := φ.ker
  have hQcomm : ∀ a b : A ⧸ K, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | _ a => ?_
    induction b using QuotientGroup.induction_on with | _ b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hA.1 a a.2 b b.2)
  have hQpow : ∀ a : A ⧸ K, a ^ p = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | _ a => ?_
    rw [← QuotientGroup.mk_pow]
    have : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
    rw [this]; rfl
  have hQcard : Nat.card (A ⧸ K) ∣ p ^ 3 := by
    rw [← hAcard]
    exact ⟨Nat.card K, (Subgroup.card_eq_card_quotient_mul_card_subgroup K)⟩
  obtain ⟨r, hr3, hr⟩ := (Nat.dvd_prime_pow hp).1 hQcard
  have hF1 := ord_mul_card_le_rank_hom (X := V) hV2 (A := A ⧸ K) (QuotientGroup.kerLift φ)
    (QuotientGroup.kerLift_injective φ) hp hp2 hQcomm hQpow hr
  have hrank : Group.rank V ≤ 4 := Gen4.rank_le_four hgen hV2
  have hr1 : r ≤ 1 := (rank_bounds hp hp2 hF1 hrank).2.1 hp5
  have hcardK : Nat.card A = Nat.card (A ⧸ K) * Nat.card K :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K
  refine ⟨K.map A.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · rintro _ ⟨a, ha, rfl⟩ v hv
    have h1 : φ a = 1 := ha
    have h2 := congrArg (fun f : MulAut V => ((f ⟨v, hv⟩ : V) : G)) h1
    have h3 : ((φ a ⟨v, hv⟩ : V) : G) = (a : G) * v * (a : G)⁻¹ := rfl
    simp only [h3] at h2
    have h4 : ((1 : MulAut V) ⟨v, hv⟩ : V) = ⟨v, hv⟩ := rfl
    rw [h4] at h2
    change (a : G) * v * (a : G)⁻¹ = v at h2
    calc (a : G) * v = (a * v * (a : G)⁻¹) * a := by group
      _ = v * a := by rw [h2]
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    have h1 : p ^ 3 = p ^ r * Nat.card K := by rw [← hAcard, hcardK, hr]
    have hpos : 0 < p := hp.pos
    have h2 : p ^ r ≤ p := by
      calc p ^ r ≤ p ^ 1 := Nat.pow_le_pow_right hpos hr1
        _ = p := pow_one p
    by_contra hlt
    push Not at hlt
    have : p ^ r * Nat.card K < p * p ^ 2 := by
      calc p ^ r * Nat.card K ≤ p * Nat.card K := Nat.mul_le_mul_right _ h2
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hpos
    have h3 : p * p ^ 2 = p ^ 3 := by ring
    omega

theorem exists_involution_of_ne_bot {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hV : ElemAb 2 V) (hne : V ≠ ⊥) : ∃ v ∈ V, orderOf v = 2 := by
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  refine ⟨v, v.2, orderOf_eq_prime ?_ ?_⟩
  · exact hV.2 v v.2
  · intro h
    exact hv1 (Subtype.ext h)

theorem lemma24 {G : Type*} [Group G] [Finite G] (hgen : Gen4 G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A R : Subgroup G} (hA : ElemAb p A) (hAcard : Nat.card A = p ^ 3)
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hnorm : A ≤ normalizer (R : Set G)) :
    (5 ≤ p ∧ ∃ t : G, orderOf t = 2 ∧ ∃ B : Subgroup G, B ≤ Cen t ∧ ElemAb p B ∧
        p ^ 2 ≤ Nat.card B) ∨
      (p = 3 ∧ ∃ t : G, CaseI t A) ∨
      (p = 3 ∧ ∃ (t t' a : G) (B : Subgroup G), CaseII t t' a A B) := by
  have hVne := centerOmega1_ne_bot hR hR2
  have hV2 : IsPGroup 2 (centerOmega1 R) :=
    fun g => ⟨1, Subtype.ext (by simpa using g.2.2.2)⟩
  have hVnorm : ∀ a ∈ A, ∀ v ∈ centerOmega1 R, a * v * a⁻¹ ∈ centerOmega1 R :=
    fun a ha v hv => centerOmega1_normalized (hnorm ha) hv
  by_cases h5 : 5 ≤ p
  · left
    refine ⟨h5, ?_⟩
    obtain ⟨t, htV, ht2⟩ := exists_involution_of_ne_bot (centerOmega1_elemAb R) hVne
    obtain ⟨B, hBA, hBV, hBcard⟩ := exists_centralizing_subgroup hgen hp h5 hA hAcard hV2 hVnorm
    refine ⟨t, ht2, B, ?_, ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb),
      fun a ha => hA.2 a (hBA ha)⟩, hBcard⟩
    intro b hb
    rw [mem_Cen']
    exact hBV b hb t htV
  · right
    have hp3 : p = 3 := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · have := hp.two_le
        rcases (by omega : p = 3 ∨ 4 ≤ p) with h3 | h4
        · exact h3
        · exfalso
          have hp4 : p ≠ 4 := by
            rintro rfl; exact absurd hp (by decide)
          omega
    subst hp3
    have hA27 : Nat.card A = 27 := by rw [hAcard]; norm_num
    by_cases hI : ∃ t : G, orderOf t = 2 ∧ A ≤ Cen t
    · left
      obtain ⟨t, ht, hc⟩ := hI
      exact ⟨rfl, t, ht, hc, hA, hA27⟩
    · right
      refine ⟨rfl, ?_⟩
      push Not at hI
      have hfix : ∀ v ∈ centerOmega1 R, (∀ a ∈ A, a * v = v * a) → v = 1 := by
        intro v hv hfixed
        by_contra hv1
        have hord : orderOf v = 2 := orderOf_eq_prime hv.2.2 hv1
        refine hI v hord (fun a ha => ?_)
        rw [mem_Cen']
        exact hfixed a ha
      obtain ⟨t, t', a, B, hord, hord', hne, hcomm, -, -, haA, hord_a, hat, hat', hBA, hBcard, hBt, hBt'⟩ :=
        exists_fourgroup_of_no_fixed A (centerOmega1 R) hA hA27 (centerOmega1_elemAb R)
          (centerOmega1_card_le hgen R) hVnorm hfix hVne
      refine ⟨t, t', a, B, ⟨hord, hord', hne, hcomm, hord_a, hat, hat', hA, hA27, haA, hBA, hBcard,
        hBt, hBt', hI⟩⟩

end CFSG.GH74.E2
