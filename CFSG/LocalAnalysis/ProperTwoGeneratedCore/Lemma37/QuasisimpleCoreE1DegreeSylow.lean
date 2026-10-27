module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1DegreeOmega
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSub
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUBasic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.DisconnectedInvolutionGraph.Helpers

theorem card_e1Gen_typeD :
    (Finset.univ.filter fun v : Fin 64 => e1Gen true true v = true ∧ v ≠ 0).card = 17 := by
  decide

theorem mem_map_stabilizer_iff {G α : Type*} [Group G] [MulAction G α] (K : Subgroup G) (a : α)
    (g : G) : g ∈ (MulAction.stabilizer K a).map K.subtype ↔ g ∈ K ∧ g • a = a := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hg, hga⟩
    exact ⟨⟨g, hg⟩, hga, rfl⟩

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem exists_forall_smul_eq_self :
    ∃ a : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)),
      ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)), s • a = a :=
  d.setting.exists_forall_smul_eq_self (S.isPGroup'.map _)

theorem eq_one_of_genuine_of_smul_eq_self
    {a β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (ha : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)), s • a = a)
    (hβ : β ≠ a) {s : J ⧸ Subgroup.center J}
    (hs : s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) (hsβ : s • β = β)
    (hgen : CaseC3.Genuine (Subgroup.center J) s) : s = 1 := by
  by_contra hs1
  exact hβ (d.setting.eq_of_smul_eq_self hgen hs1 hsβ (ha s hs))

theorem pow_eight_eq_one {s : J} (hs : (s : J ⧸ Subgroup.center J) ∈
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) :
    s ^ 8 = 1 := by
  have hb := d.caseC3BCD
  obtain ⟨v, hv⟩ := hb.exists_caseC3Word hs
  have h4 : ((s ^ 4 : J) : J ⧸ Subgroup.center J) = 1 := by
    rw [QuotientGroup.mk_pow, ← hv, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two,
      hb.caseC3Word_mul, hb.caseC3Word_mul, c3_exponent_four, CaseC3BCD.caseC3Word_zero]
  rw [show (8 : ℕ) = 4 + 4 from rfl, pow_add]
  rcases d.setting.mem_center_iff.mp ((QuotientGroup.eq_one_iff _).mp h4) with h1 | h1
  · rw [h1, one_mul]
  · rw [h1, d.setting.centralElt_mul_self]

theorem card_stabilizer_le_eight
    {a β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (ha : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)), s • a = a)
    (hβ : β ≠ a) :
    Nat.card (MulAction.stabilizer
      ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) β) ≤ 8 := by
  have h := d.setting
  set Sb := (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) with hSb
  set H := (MulAction.stabilizer Sb β).map Sb.subtype with hH
  have hmem : ∀ p : J, p ∈ H.comap (QuotientGroup.mk' (Subgroup.center J)) ↔
      (p : J ⧸ Subgroup.center J) ∈ Sb ∧ (p : J ⧸ Subgroup.center J) • β = β :=
    fun p => mem_map_stabilizer_iff Sb β _
  have hinv : ∀ t ∈ H.comap (QuotientGroup.mk' (Subgroup.center J)), orderOf t = 2 →
      t = centralElt J := by
    intro t ht ht2
    by_contra hte
    have htZ : t ∉ Subgroup.center J := (h.not_mem_center_iff ht2).mpr hte
    have ht1 : (t : J ⧸ Subgroup.center J) ≠ 1 := fun h1 =>
      htZ ((QuotientGroup.eq_one_iff t).mp h1)
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    obtain ⟨htS, htβ⟩ := (hmem t).mp ht
    exact ht1 (d.eq_one_of_genuine_of_smul_eq_self ha hβ htS htβ ⟨t, rfl, htt⟩)
  have hrank : NoCommutingDistinctInvolutions (H.comap (QuotientGroup.mk' (Subgroup.center J))) :=
    fun a b _ => Subtype.ext (Subtype.ext ((hinv a.1 a.1.2 ((Subgroup.orderOf_coe a.1).trans
      a.2)).trans (hinv b.1 b.1.2 ((Subgroup.orderOf_coe b.1).trans b.2)).symm))
  have h8 : ∀ p : H.comap (QuotientGroup.mk' (Subgroup.center J)), p ^ 8 = 1 := fun p =>
    Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact d.pow_eight_eq_one ((hmem p).mp p.2).1)
  have h16 := card_le_sixteen_of_pow_eight hrank h8
  have h1 := (H.comap (QuotientGroup.mk' (Subgroup.center J))).card_mul_index
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  have h2 := H.card_mul_index
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)
  rw [h.center_card] at h3
  have hidx : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hPH : Nat.card (H.comap (QuotientGroup.mk' (Subgroup.center J))) = 2 * Nat.card H := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) ?_
    rw [h1, h3, ← h2]
    ring
  have hHcard : Nat.card H = Nat.card (MulAction.stabilizer Sb β) :=
    Subgroup.card_map_of_injective Sb.subtype_injective
  omega

theorem index_modEq_one : (B.map (QuotientGroup.mk' (Subgroup.center J))).index ≡ 1 [MOD 8] := by
  obtain ⟨a, ha⟩ := d.exists_forall_smul_eq_self
  rw [Subgroup.index_eq_card]
  refine card_modEq_one_of_dvd_card_orbit
    (G := (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) (a := a)
    (fun g => ha g g.2) (fun β hβ => ?_)
  have h1 := (MulAction.stabilizer
    ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) β).card_mul_index
  rw [MulAction.index_stabilizer, d.caseC3BCD.card_map_top, ← Nat.card_coe_set_eq] at h1
  have h2 := d.card_stabilizer_le_eight ha hβ
  generalize Nat.card (MulAction.stabilizer
    ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) β) = c at h1 h2
  generalize Nat.card (MulAction.orbit
    ((S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))) β) = k at h1 ⊢
  interval_cases c <;> omega

theorem card_genuine_mem_sylow (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s) :
    Nat.card {s : J ⧸ Subgroup.center J // (CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1) ∧
      s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J))} = 17 := by
  rw [d.caseC3BCD.card_subtype_eq (R := fun v => e1Gen true true v = true ∧ v ≠ 0)
    (fun s hs => hs.2) fun v => ?_, card_e1Gen_typeD]
  rw [d.caseC3BCD.genuine_iff_of_typeD htype v, Ne, d.caseC3BCD.caseC3Word_eq_one_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, d.caseC3BCD.caseC3Word_mem v⟩⟩

theorem seventeen_le_card_genuine_mem (htype : ∀ s ∈ (S : Subgroup J).map
      (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s) :
    17 ≤ Nat.card {s : J ⧸ Subgroup.center J // (CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1) ∧
      s ∈ B.map (QuotientGroup.mk' (Subgroup.center J))} := by
  obtain ⟨a, ha⟩ := d.exists_forall_smul_eq_self
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← d.card_genuine_mem_sylow htype]
  refine Nat.card_le_card_of_injective (fun s => ⟨g⁻¹ * s.1 * g,
    ⟨CaseC3.genuine_conj _ s.2.1.1 g, fun h1 => s.2.1.2 ?_⟩,
      (smul_mk_eq_mk_iff _ _ g).mp (ha _ s.2.2)⟩) fun s t hst => Subtype.ext ?_
  · rw [show s.1 = g * (g⁻¹ * s.1 * g) * g⁻¹ by group, h1]
    group
  · have := Subtype.ext_iff.mp hst
    simpa using this

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
