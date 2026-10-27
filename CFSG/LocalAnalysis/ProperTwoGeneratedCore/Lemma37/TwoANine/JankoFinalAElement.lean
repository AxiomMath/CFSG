module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveM

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer_of_inv {g u : G} (hg : g * u * g⁻¹ = u⁻¹) :
    g ∈ normalizer (centralizer ({u} : Set G) : Set G) := by
  refine mem_normalizer_iff.mpr fun x => ?_
  simp only [mem_centralizer_singleton_iff, ← commute_iff_eq]
  rw [← Commute.inv_right_iff (a := g * x * g⁻¹), ← hg]
  exact ⟨fun hc => by simpa using hc.map (MulAut.conj g),
    fun hc => by simpa [mul_assoc] using hc.map (MulAut.conj g⁻¹)⟩

variable [Finite G] {z : G} {fr : JankoFrame G z} {m : G}

omit [Finite G] in
theorem card_E_sup_m (hm : JankoChoiceM fr m) :
    Nat.card (fr.E ⊔ zpowers m : Subgroup G) = 81 := by
  have hle : zpowers m ≤ normalizer (fr.E : Set G) :=
    zpowers_le.mpr (fr.K_le_normalizer hm.mem_K)
  have hbot : zpowers m ⊓ fr.E = ⊥ := by
    rw [eq_bot_iff, ← fr.E_inf_K, inf_comm]
    exact inf_le_inf_left _ (zpowers_le.mpr hm.mem_K)
  rw [sup_comm, card_sup_of_inf_eq_bot hle hbot, Nat.card_zpowers, hm.orderOf_m, fr.card_E]

omit [Finite G] in
theorem dvd_card_of_mem (hm : JankoChoiceM fr m) {x : G}
    (hx : x ∈ fr.E ⊓ centralizer ({m} : Set G)) :
    81 ∣ Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  rw [← card_E_sup_m hm]
  refine card_dvd_of_le (sup_le (le_inf ?_ fr.E_le) (zpowers_le.mpr ⟨?_, fr.K_le hm.mem_K⟩))
  · exact fun e he => mem_centralizer_singleton_iff.mpr (fr.E_comm e he x hx.1)
  · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx.2).symm

theorem card_eq_of_dvd (h : Hyp fr) {x : G} (hxH : x ∈ centralizer ({z} : Set G))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (h81 : 81 ∣ Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G)) :
    Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 := by
  rcases h.p7.isConj_of_mem_centralizer z h.set.orderOf_z x hxH hx3 hx1 with h1 | h2 | h3
  · rw [(h.p7.isConj_s₁_iff z h.set.orderOf_z x hxH hx3).mp h1] at h81
    norm_num at h81
  · rw [(h.p7.isConj_s₂_iff z h.set.orderOf_z x hxH hx3).mp h2] at h81
    norm_num at h81
  · exact (h.p7.isConj_s₃_iff z h.set.orderOf_z x hxH hx3).mp h3

theorem exists_zpowers_eq (h : Hyp fr) (hm : JankoChoiceM fr m) :
    ∃ s : G, fr.E ⊓ centralizer ({m} : Set G) = zpowers s ∧ orderOf s = 3 := by
  have hP : IsPGroup 3 (fr.E ⊔ zpowers m : Subgroup G) :=
    IsPGroup.of_card (n := 4) (by rw [card_E_sup_m hm]; norm_num)
  have hEbot : fr.E ≠ ⊥ := fun hE => by
    have := fr.card_E
    rw [hE, card_bot] at this
    norm_num at this
  obtain ⟨s, hsE, hs1, hsC⟩ := exists_mem_ne_one_mem_centralizer hP le_sup_left
    (sup_le le_normalizer (zpowers_le.mpr (fr.K_le_normalizer hm.mem_K))) hEbot
  have hsX : s ∈ fr.E ⊓ centralizer ({m} : Set G) := ⟨hsE, mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hsC) m ((le_sup_right : zpowers m ≤ _) (mem_zpowers m))).symm⟩
  have h162 : ∀ x ∈ fr.E ⊓ centralizer ({m} : Set G), x ≠ 1 → Nat.card (centralizer ({x} :
      Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 := fun x hx hx1 =>
    card_eq_of_dvd h (fr.E_le hx.1) (fr.E_pow_three x hx.1) hx1 (dvd_card_of_mem hm hx)
  have hs3 : orderOf s = 3 := orderOf_eq_prime (fr.E_pow_three s hsE) hs1
  refine ⟨s, ?_, hs3⟩
  have hdvd : Nat.card (fr.E ⊓ centralizer ({m} : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    simpa [fr.card_E] using card_dvd_of_le
      (inf_le_left : fr.E ⊓ centralizer ({m} : Set G) ≤ fr.E)
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · rw [pow_zero, card_eq_one] at hcard
    exact absurd (hcard ▸ hsX) (by simpa using hs1)
  · refine (eq_of_le_of_card_ge (zpowers_le.mpr hsX) ?_).symm
    simp only [hcard, Nat.card_zpowers, hs3, pow_one, le_refl]
  · obtain ⟨x, hx, hx1, hne⟩ := fr.exists_ne_type_s₃ _ inf_le_left hcard
    exact absurd (h162 x hx hx1) hne
  · have hEq : fr.E ⊓ centralizer ({m} : Set G) = fr.E :=
      eq_of_le_of_card_ge inf_le_left (by rw [hcard, fr.card_E]; norm_num)
    have h1 := h162 fr.s₁ (by rw [hEq]; exact h.s₁_mem_E) h.s₁_ne_one
    rw [fr.card_centralizer_s₁] at h1
    norm_num at h1

section Element

variable {s : G} (h : Hyp fr) (hm : JankoChoiceM fr m)
  (hs : fr.E ⊓ centralizer ({m} : Set G) = zpowers s) (hs3 : orderOf s = 3)
include hs

omit [Finite G] in
theorem s_mem : s ∈ fr.E ⊓ centralizer ({m} : Set G) := hs ▸ mem_zpowers s

omit [Finite G] in
theorem s_mem_E : s ∈ fr.E := (s_mem hs).1

omit [Finite G] in
theorem m_mul_s : m * s = s * m := (mem_centralizer_singleton_iff.mp (s_mem hs).2).symm

include hs3

omit [Finite G] in
theorem s_ne_one : s ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hs3
  norm_num at hs3

include h hm in
theorem card_centralizer_s :
    Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 162 :=
  card_eq_of_dvd h (fr.E_le (s_mem_E hs)) (fr.E_pow_three s (s_mem_E hs)) (s_ne_one hs hs3)
    (dvd_card_of_mem hm (s_mem hs))

include h hm in
theorem isConj_s : IsConj s fr.s₃ :=
  (h.p7.isConj_s₃_iff z h.set.orderOf_z s (fr.E_le (s_mem_E hs))
    (fr.E_pow_three s (s_mem_E hs))).mpr (card_centralizer_s h hm hs hs3)

include h hm in
theorem s_not_mem_P₁ : s ∉ fr.P₁ := by
  intro hsP
  rw [fr.P₁_eq] at hsP
  have hinv : IsConj fr.s₁ fr.s₁⁻¹ := isConj_iff.mpr ⟨fr.t, fr.t_mul_s₁⟩
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₁ hsP with h1 | h1 | h1
  · exact s_ne_one hs hs3 h1
  · exact h.p7.not_isConj_s₁_s₃ (h1 ▸ isConj_s h hm hs hs3)
  · exact h.p7.not_isConj_s₁_s₃ (hinv.trans (h1 ▸ isConj_s h hm hs hs3))

include h hm in
theorem t_mul_s : fr.t * s * fr.t⁻¹ = s⁻¹ := by
  have htN : fr.t ∈ normalizer (zpowers s : Set G) := by
    rw [← hs]
    exact inf_mem_normalizer (fr.K_le_normalizer h.t_mem_K)
      (mem_normalizer_centralizer_of_inv hm.t_mul_m)
  refine (conj_eq_or_eq_inv hs3 htN).resolve_left fun hts => ?_
  have hsP : s ∈ fr.P₂ := by
    rw [← fr.E_inf_centralizer_t]
    refine ⟨s_mem_E hs, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at hts
    exact hts.symm
  rw [fr.P₂_eq] at hsP
  obtain ⟨b, -, -, hb⟩ := fr.exists_invert fr.s₂ (by simp)
  have hinv : IsConj fr.s₂ fr.s₂⁻¹ := isConj_iff.mpr ⟨b, hb⟩
  have hc := isConj_s h hm hs hs3
  rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₂ hsP with h1 | h1 | h1
  · exact s_ne_one hs hs3 h1
  · exact h.p7.not_isConj_s₂_s₃ (h1 ▸ hc)
  · exact h.p7.not_isConj_s₂_s₃ (hinv.trans (h1 ▸ hc))

end Element

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
