module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3TypeA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Degree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreSetting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J}

omit [Finite J] in
theorem CaseC3.mul_self_of_genuine {s : J ⧸ Subgroup.center J}
    (hs : CaseC3.Genuine (Subgroup.center J) s) : s * s = 1 := by
  obtain ⟨t, rfl, htt⟩ := hs
  rw [← QuotientGroup.mk_mul, htt, QuotientGroup.mk_one]

namespace Setting

theorem mem_map_of_conj_mem_of_genuine (h : Setting J Q B) {s x : J ⧸ Subgroup.center J}
    (hs : CaseC3.Genuine (Subgroup.center J) s) (hs1 : s ≠ 1)
    (hsB : s ∈ B.map (QuotientGroup.mk' (Subgroup.center J)))
    (hx : x * s * x⁻¹ ∈ B.map (QuotientGroup.mk' (Subgroup.center J))) :
    x ∈ B.map (QuotientGroup.mk' (Subgroup.center J)) := by
  obtain ⟨t, rfl, htt⟩ := hs
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  have ht1 : t ≠ 1 := fun h1 => hs1 (by rw [h1, QuotientGroup.mk_one])
  have htZ : t ∉ Subgroup.center J := fun hZ => hs1 ((QuotientGroup.eq_one_iff t).mpr hZ)
  rw [h.mk_mem_map_iff] at hsB ⊢
  refine h.mem_of_conj_mem hsB (orderOf_eq_prime (by rw [pow_two]; exact htt) ht1) htZ ?_
  rw [← h.mk_mem_map_iff]
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hx

theorem exists_forall_smul_eq_self (h : Setting J Q B) {K : Subgroup (J ⧸ Subgroup.center J)}
    (hK : IsPGroup 2 K) :
    ∃ ω : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)),
      ∀ k ∈ K, k • ω = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hK.exists_le_sylow
  set Q' := Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (J ⧸ Subgroup.center J) P Q'
  refine ⟨((g⁻¹ : J ⧸ Subgroup.center J) :
    (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))), fun k hk => ?_⟩
  rw [smul_mk_eq_mk_iff, inv_inv]
  have h1 : g * k * g⁻¹ ∈ (Q' : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, mul_assoc] using hP hk
  rw [Sylow.coe_mapSurjective] at h1
  exact Subgroup.map_mono h.sylow_le h1

theorem exists_smul_eq_self (h : Setting J Q B) {s : J ⧸ Subgroup.center J} (hss : s * s = 1) :
    ∃ ω : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)), s • ω = ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers s) := by
    by_cases hs1 : s = 1
    · rw [hs1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1)
  obtain ⟨ω, hω⟩ := h.exists_forall_smul_eq_self hp
  exact ⟨ω, hω s (Subgroup.mem_zpowers s)⟩

theorem eq_of_smul_eq_self (h : Setting J Q B) {s : J ⧸ Subgroup.center J}
    (hs : CaseC3.Genuine (Subgroup.center J) s) (hs1 : s ≠ 1)
    {ω₁ ω₂ : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (h₁ : s • ω₁ = ω₁) (h₂ : s • ω₂ = ω₂) : ω₁ = ω₂ := by
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective ω₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective ω₂
  rw [smul_mk_eq_mk_iff] at h₁ h₂
  have hne : g₁⁻¹ * s * g₁ ≠ 1 := fun h1 => hs1 (by
    rw [show s = g₁ * (g₁⁻¹ * s * g₁) * g₁⁻¹ by group, h1]
    group)
  have hmem := h.mem_map_of_conj_mem_of_genuine (CaseC3.genuine_conj _ hs g₁) hne h₁
    (x := g₂⁻¹ * g₁) (by
      rw [show g₂⁻¹ * g₁ * (g₁⁻¹ * s * g₁) * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * s * g₂ by group]
      exact h₂)
  rw [QuotientGroup.eq]
  have := (B.map (QuotientGroup.mk' (Subgroup.center J))).inv_mem hmem
  rwa [mul_inv_rev, inv_inv] at this

theorem existsUnique_smul_eq_self (h : Setting J Q B) {s : J ⧸ Subgroup.center J}
    (hs : CaseC3.Genuine (Subgroup.center J) s) (hs1 : s ≠ 1) :
    ∃! ω : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)), s • ω = ω := by
  obtain ⟨ω, hω⟩ := h.exists_smul_eq_self (CaseC3.mul_self_of_genuine hs)
  exact ⟨ω, hω, fun ω' hω' => h.eq_of_smul_eq_self hs hs1 hω' hω⟩

theorem smul_eq_self_of_mem_centralizer (h : Setting J Q B) {s c : J ⧸ Subgroup.center J}
    (hs : CaseC3.Genuine (Subgroup.center J) s) (hs1 : s ≠ 1)
    (hc : c ∈ Subgroup.centralizer {s})
    {ω : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hω : s • ω = ω) : c • ω = ω :=
  smul_eq_self_of_commute_of_existsUnique (h.existsUnique_smul_eq_self hs hs1)
    (Subgroup.mem_centralizer_singleton_iff.mp hc).symm hω

theorem card_genuine_eq_index_mul (h : Setting J Q B) :
    Nat.card {s : J ⧸ Subgroup.center J // CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1} =
      (B.map (QuotientGroup.mk' (Subgroup.center J))).index *
        Nat.card {s : J ⧸ Subgroup.center J //
          (CaseC3.Genuine (Subgroup.center J) s ∧ s ≠ 1) ∧
            s ∈ B.map (QuotientGroup.mk' (Subgroup.center J))} :=
  card_eq_index_mul_card_of_existsUnique _ _
    (fun c g hc => ⟨by simpa using CaseC3.genuine_conj _ hc.1 g⁻¹,
      fun h1 => hc.2 (conj_eq_one_iff.mp h1)⟩)
    (fun c hc => h.existsUnique_smul_eq_self hc.1 hc.2)

end Setting

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
