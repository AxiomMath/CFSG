module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeCentralOdd
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKlein

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic

section Generic

variable {G : Type*} [Group G]

theorem gLAPPrimeCoreOf_eq_bot_of_odd_four [Finite G] {p : ℕ} {s a b : G}
    (haC : a ∈ Subgroup.centralizer ({s} : Set G)) (hbC : b ∈ Subgroup.centralizer ({s} : Set G))
    (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)))))
    (hloc : ∀ t : G, (t = a ∨ t = b ∨ t = a * b) →
      ∀ q ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)), q * t = t * q →
        ∃ k : ℕ, q ^ (2 ^ k) = 1) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set Q := GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set G)) with hQ
  have htriv : ∀ q ∈ Q, ∀ k : ℕ, q ^ (2 ^ k) = 1 → q = 1 := by
    intro q hq k hk
    have h1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf q ∣ Nat.card Q := by
      have := orderOf_dvd_natCard (⟨q, hq⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero] at hj
      exact orderOf_eq_one_iff.1 hj
    · exfalso
      rw [hj] at h2
      have h2' : 2 ∣ Nat.card Q := (dvd_pow_self 2 hpos.ne').trans h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2')
  have hfix : ∀ t : G, (t = a ∨ t = b ∨ t = a * b) → ∀ x ∈ Q, t * x * t⁻¹ = x → x = 1 := by
    intro t ht x hx hxt
    have hc : x * t = t * x := by
      calc x * t = (t * x * t⁻¹) * t := by rw [hxt]
        _ = t * x := by group
    obtain ⟨k, hk⟩ := hloc t ht x hx hc
    exact htriv x hx k hk
  have haQ : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx => GLAPPrimeCoreOf_conj_mem a haC x hx
  have hbQ : ∀ x ∈ Q, b * x * b⁻¹ ∈ Q := fun x hx => GLAPPrimeCoreOf_conj_mem b hbC x hx
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_klein_fixedPointFree ha hb haQ hbQ (hfix a (Or.inl rfl))
    (hfix b (Or.inr (Or.inl rfl))) (hfix (a * b) (Or.inr (Or.inr rfl))) x hx

end Generic

@[expose] def BTwoBLocalThree : Prop :=
  ∀ s t : B, orderOf s = 3 → BabyInv 1 t → t ∈ Subgroup.centralizer ({s} : Set B) →
    ∀ q ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)),
      q ∈ Subgroup.centralizer ({t} : Set B) → ∃ k : ℕ, q ^ (2 ^ k) = 1

section ThreeB


theorem gLAPPrimeCoreOf_B_eq_bot_of_three_central_four (hL : BTwoBLocalThree) {s : B}
    (hs : orderOf s = 3) (h13 : 3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({s} : Set B)))
    {a b : B} (haC : a ∈ Subgroup.centralizer ({s} : Set B))
    (hbC : b ∈ Subgroup.centralizer ({s} : Set B)) (ha : BabyInv 1 a) (hb : BabyInv 1 b)
    (hab : BabyInv 1 (a * b)) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)) = ⊥ := by
  have hfin : Finite B :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.RankThree.OddKernel.card_B_eq]; norm_num)
  have hsq : ∀ t : B, BabyInv 1 t → t * t = 1 := fun t ht => by
    have := pow_orderOf_eq_one t
    rwa [ht.1, sq] at this
  refine gLAPPrimeCoreOf_eq_bot_of_odd_four haC hbC (hsq a ha) (hsq b hb)
    (odd_card_gLAPPrimeCoreOf_B_of_three_central h13) ?_
  have habC : a * b ∈ Subgroup.centralizer ({s} : Set B) := Subgroup.mul_mem _ haC hbC
  intro t ht q hq hqt
  have htC : t ∈ Subgroup.centralizer ({s} : Set B) := by
    rcases ht with rfl | rfl | rfl
    · exact haC
    · exact hbC
    · exact habC
  have htB : BabyInv 1 t := by
    rcases ht with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hab
  exact hL s t hs htB htC q hq (Subgroup.mem_centralizer_singleton_iff.2 hqt)

end ThreeB

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
