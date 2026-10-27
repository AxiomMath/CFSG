module

public import CFSG.GH74.Generic.S3.Lem33

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

namespace Nbhd3

variable {G : Type} [Group G] [Finite G] {t t' : StatedLieTag} {p f : ℕ} {x y : G}
  {Iw Iv Ivw T : Subgroup G} (h : Nbhd3 G t t' p f x y Iw Iv Ivw T)

include h

theorem x_notin_Ivw : x ∉ Ivw := by
  intro hx
  have hyx : y * x ∈ Ivw := Ivw.mul_mem (h.Iv_le_vw h.y_Iv) hx
  exact not_central_involution_of_odd h.odd_vw hyx h.yx_mul_self h.yx_ne_one
    (fun i hi => mem_centralizer_singleton_iff.1 (h.comp_vw.1.1 hi))

theorem yx_notin_Iw : y * x ∉ Iw := by
  intro hyx
  have hx : x ∈ Iw := by
    have := Iw.mul_mem (Iw.inv_mem (h.Iv_le h.y_Iv)) hyx
    simpa using this
  exact not_central_involution_of_odd h.odd_w hx h.x_mul_self h.x_ne_one h.x_comm_Iw

theorem T_conj_Ivw : ∀ s ∈ T, ∀ i ∈ Ivw, s * i * s⁻¹ ∈ Ivw := fun s hs i hi =>
  h.comp_vw.conj s (h.T_le_vw hs) i hi

theorem T_conj_Qxy : ∀ s ∈ T, ∀ q ∈ T ⊓ centralizer (Ivw : Set G),
    s * q * s⁻¹ ∈ T ⊓ centralizer (Ivw : Set G) := by
  intro s hs q hq
  refine ⟨T.mul_mem (T.mul_mem hs hq.1) (T.inv_mem hs), ?_⟩
  apply mem_centralizer_iff.2
  intro i hi
  have hi' : s⁻¹ * i * s ∈ Ivw := by
    have := h.T_conj_Ivw s⁻¹ (T.inv_mem hs) i hi
    simpa using this
  have hq' : (s⁻¹ * i * s) * q = q * (s⁻¹ * i * s) := mem_centralizer_iff.1 hq.2 _ hi'
  calc i * (s * q * s⁻¹) = s * ((s⁻¹ * i * s) * q) * s⁻¹ := by group
    _ = s * (q * (s⁻¹ * i * s)) * s⁻¹ := by rw [hq']
    _ = s * q * s⁻¹ * i := by group

theorem yx_Qxy : y * x ∈ T ⊓ centralizer (Ivw : Set G) := by
  refine ⟨T.mul_mem h.y_R.1 h.x_T, ?_⟩
  apply mem_centralizer_iff.2
  intro i hi
  exact mem_centralizer_singleton_iff.1 (h.comp_vw.1.1 hi)

theorem Qxy_involution : ∀ a ∈ T ⊓ centralizer (Ivw : Set G), a * a = 1 → a = 1 ∨ a = y * x := by
  have hne : T ⊓ centralizer (Ivw : Set G) ≠ ⊥ := fun hb => by
    have := h.yx_Qxy
    rw [hb, Subgroup.mem_bot] at this
    exact h.yx_ne_one this
  have hrk : NoCommInv (T ⊓ centralizer (Ivw : Set G)) := fun a ha b hb haa hbb hab =>
    h.rank_vw a ⟨h.T_le_vw ha.1, ha.2⟩ b ⟨h.T_le_vw hb.1, hb.2⟩ haa hbb hab
  obtain ⟨z, hz, hzz, hz1, hzu⟩ := unique_involution_of_noCommInv
    (h.T_pGroup.to_inf_left (K := centralizer (Ivw : Set G))) hne hrk
  have hxz : y * x = z := by
    rcases hzu _ h.yx_Qxy h.yx_mul_self with h1 | h1
    · exact absurd h1 h.yx_ne_one
    · exact h1
  intro a ha haa
  rcases hzu a ha haa with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (h1.trans hxz.symm)

theorem Q_inf_Qxy : (T ⊓ centralizer (Iw : Set G)) ⊓ (T ⊓ centralizer (Ivw : Set G)) = ⊥ := by
  apply inf_eq_bot_of_no_involution
    (h.T_pGroup.to_le (show (T ⊓ centralizer (Iw : Set G)) ⊓ (T ⊓ centralizer (Ivw : Set G)) ≤ T from
      fun a ha => ha.1.1))
  intro a ha hb haa
  by_contra ha1
  have h1 := h.Q_involution a ha haa
  have h2 := h.Qxy_involution a hb haa
  rcases h1 with h1 | h1
  · exact ha1 h1
  rcases h2 with h2 | h2
  · exact ha1 h2
  have : x = y * x := h1.symm.trans h2
  apply h.y_ne_one
  have e : y = (y * x) * x⁻¹ := by group
  rw [e, ← this]
  group

theorem Rxy_sylow (hclass : B_L3_class) (hsyl : B_L3_sylow) : IsSylowOf 2 (T ⊓ Ivw) Ivw := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (h.T_sylow_vw hclass hsyl).inf_of_le_normalizer h.comp_vw.1.1 h.comp_vw.le_normalizer

theorem lem34 (hclass : B_L3_class) (hsyl : B_L3_sylow) :
    IsCyclic ↥(T ⊓ centralizer (Iw : Set G)) ∧
      (t' = .PSL → ∀ a ∈ T ⊓ centralizer (Iw : Set G), orderOf a ∣ p ^ f - 1) ∧
      (t' = .PSU → ∀ a ∈ T ⊓ centralizer (Iw : Set G), orderOf a ∣ p ^ f + 1) ∧
      ∃ ψ : ↥(T ⊓ centralizer (Iw : Set G)) →* G, Function.Injective ψ ∧
        ∀ a, ψ a ∈ T ⊓ centralizer (Ivw : Set G) := by
  have hq := h.comp_vw.1.isQuasisimple
  obtain ⟨hcyc, hnL, hnU, hksplit⟩ := hsyl G t' p f h.tag' h.prime.1 h.prime.2.1 h.prime.2.2 Ivw hq
    h.odd_vw h.model_vw _ (h.Rxy_sylow hclass hsyl)
  have key : ∀ n : ℕ, (∀ z ∈ (T ⊓ Ivw) ⊓ centralizer ((T ⊓ Ivw : Subgroup G) : Set G), orderOf z ∣ n) →
      IsCyclic ↥(T ⊓ centralizer (Iw : Set G)) ∧
        (∀ a ∈ T ⊓ centralizer (Iw : Set G), orderOf a ∣ n) ∧
        ∃ ψ : ↥(T ⊓ centralizer (Iw : Set G)) →* G, Function.Injective ψ ∧
          ∀ a, ψ a ∈ T ⊓ centralizer (Ivw : Set G) := fun n hn =>
    side_lemma h.T_pGroup h.T_conj_Ivw h.odd_vw hcyc hksplit inf_le_left h.T_conj_Q
      h.Q_involution h.x_notin_Ivw h.Q_inf_Qxy hn
  rcases h.tag' with ht | ht
  · obtain ⟨c, hc1, hc2⟩ := key (p ^ f - 1) (hnL ht)
    exact ⟨c, fun _ => hc1, fun hh => absurd (ht.symm.trans hh) (by decide), hc2⟩
  · obtain ⟨c, hc1, hc2⟩ := key (p ^ f + 1) (hnU ht)
    exact ⟨c, fun hh => absurd (ht.symm.trans hh) (by decide), fun _ => hc1, hc2⟩

theorem lem35 (hsyl : B_L3_sylow) :
    IsCyclic ↥(T ⊓ centralizer (Ivw : Set G)) ∧
      (t = .PSL → ∀ a ∈ T ⊓ centralizer (Ivw : Set G), orderOf a ∣ p ^ f - 1) ∧
      (t = .PSU → ∀ a ∈ T ⊓ centralizer (Ivw : Set G), orderOf a ∣ p ^ f + 1) ∧
      ∃ ψ : ↥(T ⊓ centralizer (Ivw : Set G)) →* G, Function.Injective ψ ∧
        ∀ a, ψ a ∈ T ⊓ centralizer (Iw : Set G) := by
  have hq := h.comp_w.1.isQuasisimple
  obtain ⟨hcyc, hnL, hnU, hksplit⟩ := hsyl G t p f h.tag h.prime.1 h.prime.2.1 h.prime.2.2 Iw hq
    h.odd_w h.model_w _ h.R_sylow
  have key : ∀ n : ℕ, (∀ z ∈ (T ⊓ Iw) ⊓ centralizer ((T ⊓ Iw : Subgroup G) : Set G), orderOf z ∣ n) →
      IsCyclic ↥(T ⊓ centralizer (Ivw : Set G)) ∧
        (∀ a ∈ T ⊓ centralizer (Ivw : Set G), orderOf a ∣ n) ∧
        ∃ ψ : ↥(T ⊓ centralizer (Ivw : Set G)) →* G, Function.Injective ψ ∧
          ∀ a, ψ a ∈ T ⊓ centralizer (Iw : Set G) := fun n hn =>
    side_lemma h.T_pGroup h.T_conj_Iw h.odd_w hcyc hksplit inf_le_left h.T_conj_Qxy
      h.Qxy_involution h.yx_notin_Iw (by rw [inf_comm]; exact h.Q_inf_Qxy) hn
  rcases h.tag with ht | ht
  · obtain ⟨c, hc1, hc2⟩ := key (p ^ f - 1) (hnL ht)
    exact ⟨c, fun _ => hc1, fun hh => absurd (ht.symm.trans hh) (by decide), hc2⟩
  · obtain ⟨c, hc1, hc2⟩ := key (p ^ f + 1) (hnU ht)
    exact ⟨c, fun hh => absurd (ht.symm.trans hh) (by decide), fun _ => hc1, hc2⟩

theorem lem37_Q_iso (hclass : B_L3_class) (hsyl : B_L3_sylow) :
    Nonempty (↥(T ⊓ centralizer (Iw : Set G)) ≃* ↥(T ⊓ centralizer (Ivw : Set G))) := by
  obtain ⟨hc4, -, -, ψ4, hψ4, hψ4mem⟩ := h.lem34 hclass hsyl
  obtain ⟨hc5, -, -, ψ5, hψ5, hψ5mem⟩ := h.lem35 hsyl
  have h1 : Nat.card ↥(T ⊓ centralizer (Iw : Set G)) ≤ Nat.card ↥(T ⊓ centralizer (Ivw : Set G)) :=
    Nat.card_le_card_of_injective (ψ4.codRestrict (T ⊓ centralizer (Ivw : Set G)) hψ4mem)
      (fun a b hab => hψ4 (congrArg Subtype.val hab))
  have h2 : Nat.card ↥(T ⊓ centralizer (Ivw : Set G)) ≤ Nat.card ↥(T ⊓ centralizer (Iw : Set G)) :=
    Nat.card_le_card_of_injective (ψ5.codRestrict (T ⊓ centralizer (Iw : Set G)) hψ5mem)
      (fun a b hab => hψ5 (congrArg Subtype.val hab))
  have := hc4
  have := hc5
  exact ⟨mulEquivOfCyclicCardEq (le_antisymm h1 h2)⟩

end Nbhd3

end CFSG.GH74.Generic.S3
