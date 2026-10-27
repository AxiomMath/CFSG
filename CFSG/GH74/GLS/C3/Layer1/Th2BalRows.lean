module

public import CFSG.GH74.GLS.C3.Layer1.Th2P73

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

theorem ordA_one_eq_of_odd {m : ℕ} (hm : Odd m) : CFSG.Open.ordA 1 m = m * (m ^ 2 - 1) / 2 := by
  unfold CFSG.Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  have h2 : Nat.gcd 2 (m - 1) = 2 := by
    obtain ⟨k, rfl⟩ := hm
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]
    simp
  rw [show (1 + 1 : ℕ) = 2 from rfl, h2]

theorem eq_of_ordA_one_eq {q q' : ℕ} (hq : Odd q) (hq' : Odd q')
    (h : CFSG.Open.ordA 1 q = CFSG.Open.ordA 1 q') : q = q' := by
  rw [ordA_one_eq_of_odd hq, ordA_one_eq_of_odd hq'] at h
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨k', rfl⟩ := hq'
  have e1 : ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)) = 2 * (2 * k * (k + 1) * (2 * k + 1)) := by
    have : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
      omega
    rw [this]
    ring
  have e2 : ((2 * k' + 1) * ((2 * k' + 1) ^ 2 - 1)) = 2 * (2 * k' * (k' + 1) * (2 * k' + 1)) := by
    have : (2 * k' + 1) ^ 2 - 1 = 4 * k' * (k' + 1) := by
      have : (2 * k' + 1) ^ 2 = 4 * k' * (k' + 1) + 1 := by ring
      omega
    rw [this]
    ring
  rw [e1, e2, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)] at h
  by_contra hne
  have hne' : k ≠ k' := fun e => hne (by rw [e])
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have : 2 * k * (k + 1) * (2 * k + 1) < 2 * k' * (k' + 1) * (2 * k' + 1) := by
      have h1 : k ≤ k' := hlt.le
      have h2 : k + 1 ≤ k' + 1 := by omega
      have h3 : 2 * k + 1 < 2 * k' + 1 := by omega
      calc 2 * k * (k + 1) * (2 * k + 1) ≤ 2 * k' * (k' + 1) * (2 * k + 1) := by gcongr
        _ < 2 * k' * (k' + 1) * (2 * k' + 1) := by
          apply Nat.mul_lt_mul_of_pos_left h3
          have : 1 ≤ k' := by omega
          positivity
    omega
  · have : 2 * k' * (k' + 1) * (2 * k' + 1) < 2 * k * (k + 1) * (2 * k + 1) := by
      have h1 : k' ≤ k := hlt.le
      have h2 : k' + 1 ≤ k + 1 := by omega
      have h3 : 2 * k' + 1 < 2 * k + 1 := by omega
      calc 2 * k' * (k' + 1) * (2 * k' + 1) ≤ 2 * k * (k + 1) * (2 * k' + 1) := by gcongr
        _ < 2 * k * (k + 1) * (2 * k + 1) := by
          apply Nat.mul_lt_mul_of_pos_left h3
          have : 1 ≤ k := by omega
          positivity
    omega

theorem exists_eq_of_hasL2Model {K : Type} [Group K] {P P' : ℕ → Prop} (h : HasL2Model K P)
    (h' : HasL2Model K P') (hP : ∀ q, P q → Odd q) (hP' : ∀ q, P' q → Odd q) :
    ∃ q, P q ∧ P' q := by
  obtain ⟨p, f, hp, hf, hq, hL⟩ := h
  obtain ⟨p', f', hp', hf', hq', hL'⟩ := h'
  have h1 := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL
  have h2 := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hL'
  have h3 : p ^ f = p' ^ f' := eq_of_ordA_one_eq (hP _ hq) (hP' _ hq') (by simpa using h1.symm.trans h2)
  exact ⟨p ^ f, hq, h3 ▸ hq'⟩

end CFSG.GH74.GLS.Th2.Bal

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2


@[expose] def B_prop61a : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ B : Subgroup G, IsE 4 ⊤ B → IsKBal 3 B

@[expose] def B_prop61b_unb : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ B : Subgroup G, IsE 4 ⊤ B → ¬ IsWeakKBal 2 B →
    ∃ (b d : G) (J : Subgroup G), b ∈ B ∧ d ∈ B ∧ IsUnbalancingTriple b d J ∧
      (Nonempty (kBar J ≃* alternatingGroup (Fin 7)) ∨
        HasL2Model (kBar J) (fun q => Odd q ∧ ¬ IsFM9 q))

@[expose] def B_cor67 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) (fun q => Odd q ∧ IsFM9 q) →
      ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B → IsWeakKBal 2 B

@[expose] def B_cor614 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q) →
      ¬ (IsConn2 (T ⊓ CxK x K) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)) →
        ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B → IsWeakKBal 2 B

@[expose] def B_prop615 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥(T ⊓ CxK x K) = 4 → T < S → ∀ D : Subgroup G, IsDSub K (T ⊓ K) D →
        IsWeakKBal 2 (⨆ s ∈ S, D.map (MulAut.conj s).toMonoidHom)

@[expose] def B_prop617b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → Nonempty (kBar K ≃* alternatingGroup (Fin 7)) →
      ¬ (IsConn2 (T ⊓ CxK x K) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)) →
      ¬ (Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S) →
        ∀ B : Subgroup G, IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B → IsWeakKBal 2 B

@[expose] def B_prop624b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → HasL2Model (kBar K) (fun q => q = 5) → pRank 2 ↥(T ⊓ CxK x K) = 2 →
      ∀ B : Subgroup G, IsE 4 ⊤ B → IsWeakKBal 2 B

theorem b_thm2_bal_of (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (h3b : B_thm2_A7_3b_T)
    (h61a : B_prop61a) (h67 : B_cor67) (h614 : B_cor614) (h615 : B_prop615)
    (h617 : B_prop617b) (h624 : B_prop624b) : B_thm2_bal := by
  intro G _ _ hG x y K T S h ρ hρ hrow B hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hPsh⟩ := h.centerless_and_shape hG hL34 h102
  have hQ3 : ¬ 3 ≤ pRank 2 ↥(T ⊓ CxK x K) := fun h3 => false_of_three_le_rank_Q hG h hcen hPsh h3
  have hconn : ¬ (IsConn2 (T ⊓ CxK x K) ∧ 3 ≤ pRank 2 ↥(T ⊓ CxK x K)) := fun hc => hQ3 hc.2
  rcases hρ with rfl | rfl | rfl | rfl | rfl
  ·
    simp only [Th2Row.holds] at hrow
    change IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B at hB
    exact ⟨h61a G hG B (isE_of_isSn le_top hB le_rfl),
      h614 G hG x y K T S h hrow.1 hconn B hB⟩
  ·
    simp only [Th2Row.holds] at hrow
    change IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B at hB
    obtain ⟨p, f, hp, hf, hP, hL⟩ := hrow
    exact ⟨h61a G hG B (isE_of_isSn le_top hB le_rfl),
      h67 G hG x y K T S h ⟨p, f, hp, hf, ⟨hP.1, hP.2.1⟩, hL⟩ B hB⟩
  ·
    simp only [Th2Row.holds] at hrow
    obtain ⟨h7, hQ4, hTS⟩ := hrow
    obtain ⟨D, hD, hBeq⟩ := hB
    subst hBeq
    obtain ⟨hel, hrk, -⟩ := h3b G hG x y K T S h h7 hQ4 hTS D hD
    exact ⟨h61a G hG _ ⟨le_top, hel, hrk⟩, h615 G hG x y K T S h h7 hQ4 hTS D hD⟩
  ·
    simp only [Th2Row.holds] at hrow
    obtain ⟨hB1, -⟩ := hB
    obtain ⟨h7, -, hcase⟩ := hrow
    have hnc : ¬ (Nat.card ↥(T ⊓ CxK x K) = 4 ∧ T < S) := by
      rintro ⟨h4, hlt⟩
      rcases hcase with h' | h'
      · omega
      · exact absurd hlt (by rw [h']; exact lt_irrefl _)
    exact ⟨h61a G hG B (isE_of_isSn le_top hB1 le_rfl),
      h617 G hG x y K T S h h7 hconn hnc B hB1⟩
  ·
    simp only [Th2Row.holds] at hrow
    change IsSn 4 T B at hB
    obtain ⟨hq5, -⟩ := hrow
    have hnotA7 := not_nonempty_A7_of_hasL2Model (K := K) (Pr := fun q => q = 5) hq5
    have h2 := h.two_le_pRank_of_not_A7 hnotA7
    have hQ2 : pRank 2 ↥(T ⊓ CxK x K) = 2 := by
      have := pRank_eq_of_isSylowOf h.sylow_Q
      omega
    have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
    exact ⟨h61a G hG B hE, h624 G hG x y K T S h hq5 hQ2 B hE⟩

end CFSG.GH74.GLS
