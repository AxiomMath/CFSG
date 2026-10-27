module

public import CFSG.GH74.Uniqueness.SU.SU2Step3

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

theorem exists_normal_order_seven {X : Type*} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hK : Nat.card K = 21) : ∃ E : Subgroup X, E.Normal ∧ Nat.card E = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 K) := inferInstance
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, hK]
    have : (21 : ℕ).factorization 7 = 1 := by
      rw [show (21 : ℕ) = 7 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization (show Nat.Prime 7 by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 3 by norm_num)]
    rw [this]; norm_num
  have hsub : Subsingleton (Sylow 7 K) := by
    have h1 : Nat.card (Sylow 7 K) ∣ (P : Subgroup K).index := Sylow.card_dvd_index P
    have h2 : (P : Subgroup K).index = 3 := by
      have := Subgroup.index_mul_card (P : Subgroup K)
      rw [hK, hP] at this
      omega
    have h3 := card_sylow_modEq_one 7 K
    rw [h2] at h1
    have h4 : Nat.card (Sylow 7 K) ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    have h5 : 0 < Nat.card (Sylow 7 K) := Nat.card_pos
    have h6 : Nat.card (Sylow 7 K) = 1 := by
      unfold Nat.ModEq at h3
      interval_cases h : Nat.card (Sylow 7 K) <;> simp_all
    exact Finite.card_le_one_iff_subsingleton.1 (by rw [h6])
  refine ⟨(P : Subgroup K).map K.subtype, ?_, ?_⟩
  · refine ⟨fun e he x => ?_⟩
    obtain ⟨k, hk, rfl⟩ := he
    have hchar : (P : Subgroup K).Characteristic := inferInstance
    have h := hchar.fixed (MulAut.conjNormal x)
    have : (MulAut.conjNormal x) k ∈ (P : Subgroup K) := by
      have hk' : k ∈ (P : Subgroup K).comap (MulAut.conjNormal x).toMonoidHom := by
        rw [h]; exact hk
      exact hk'
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hP]

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

theorem transitive_of_normal_order_seven [Finite X] [Finite V]
    (hfaith : ∀ x : X, (∀ v : V, x • v = v) → x = 1)
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x : X, x • v = w) {E : Subgroup X} [E.Normal]
    (hE : Nat.card E = 7) (hV : Nat.card V = 8) :
    ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, x • v = w := by
  intro v w hv hw
  have hEv : E ⊓ MulAction.stabilizer X v = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(E ⊓ MulAction.stabilizer X v) ∣ 7 := hE ▸ Subgroup.card_dvd_of_le inf_le_left
    have hc7 : Nat.card ↥(E ⊓ MulAction.stabilizer X v) = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h | h
      · exact absurd ((Subgroup.eq_bot_iff_card _).2 h) hne
      · exact h
    have hle : E ≤ MulAction.stabilizer X v := by
      have := Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ MulAction.stabilizer X v ≤ E)
        (by rw [hc7, hE])
      rw [← this]
      exact inf_le_right
    have hfix : ∀ e ∈ E, ∀ u : V, u ≠ 1 → e • u = u := by
      intro e he u hu
      obtain ⟨x, rfl⟩ := htr v u hv hu
      have hconj : x⁻¹ * e * x ∈ E := by
        have := (inferInstance : E.Normal).conj_mem e he x⁻¹
        rwa [inv_inv] at this
      calc e • x • v = (x * (x⁻¹ * e * x)) • v := by rw [← mul_smul]; group
        _ = x • ((x⁻¹ * e * x) • v) := mul_smul _ _ _
        _ = x • v := by rw [MulAction.mem_stabilizer_iff.1 (hle hconj)]
    have hE1 : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro e he
      apply hfaith
      intro u
      by_cases hu : u = 1
      · rw [hu, smul_one]
      · exact hfix e he u hu
    rw [hE1, Subgroup.card_bot] at hE
    omega
  have hcard := ncard_orbit_mul_card_inf E v
  rw [hEv, Subgroup.card_bot, mul_one, hE] at hcard
  have hsub : MulAction.orbit ↥E v ⊆ {u : V | u ≠ 1} := by
    rintro _ ⟨e, rfl⟩ h
    exact hv ((smul_eq_one_iff' (e : X) v).1 h)
  have hcard2 : ({u : V | u ≠ 1} : Set V).ncard = 7 := by
    have h1 : {u : V | u ≠ 1} = (Set.univ : Set V) \ {1} := by ext; simp
    rw [h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, hV]
  have heq : MulAction.orbit ↥E v = {u : V | u ≠ 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hcard2]) (Set.toFinite _)
  have hw' : w ∈ MulAction.orbit ↥E v := by rw [heq]; exact hw
  obtain ⟨e, he⟩ := hw'
  exact ⟨e, e.2, he⟩

theorem GOPair.faithful_of_isPGroup [Finite X] [Finite V] {Y : Subgroup X} (hGO : GOPair V Y)
    {W₁ W₂ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) {S : Subgroup X}
    (hS : S ≤ MulAction.stabilizer X (fixSub V Y)) (hS2 : IsPGroup 2 S) :
    ∀ s ∈ S, (∀ u ∈ commSub V Y, s • u = u) → s = 1 := by
  intro s hs hs1
  by_contra hne
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨s, hs⟩
  have hi' : orderOf s = 2 ^ i := (Subgroup.orderOf_coe (⟨s, hs⟩ : S)).trans hi
  have hi1 : i ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero, orderOf_eq_one_iff] at hi'
    exact hi'
  have hord : orderOf (s ^ 2 ^ (i - 1)) = 2 := by
    have hdvd : 2 ^ (i - 1) ∣ orderOf s := by rw [hi']; exact pow_dvd_pow 2 (Nat.sub_le i 1)
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hi', Nat.pow_div (Nat.sub_le i 1) (by norm_num)]
    have : i - (i - 1) = 1 := by omega
    rw [this, pow_one]
  have hs0 : s ^ 2 ^ (i - 1) • fixSub V Y = fixSub V Y :=
    MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer X (fixSub V Y)).pow_mem (hS hs) _)
  exact hGO.no_trivial_involution hW₁ hW₂ hs0 hord fun u hu => pow_smul_eq_self (hs1 u hu) _

end CFSG.GH74.Uniqueness.SU.SU2
