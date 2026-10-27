module

public import CFSG.LargeExtraspecial.S97RXLex
public import CFSG.LargeExtraspecial.S97RXList
public import CFSG.LargeExtraspecial.S4TwoH
public import CFSG.LargeExtraspecial.S4TwoPSL
public import CFSG.LargeExtraspecial.S4TwoD
public import CFSG.LargeExtraspecial.S97RForm2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.Assembly.LowTwoRank

@[expose] def A9WCPairFact : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ], Nonempty (Λ ≃* alternatingGroup (Fin 9)) →
    ∀ T : Subgroup Λ, IsWC T → Nat.card T = 8 →
      ∃ c : Λ, T ⊓ normalizer (conjSubgroup c T : Set Λ) = ⊥ ∧ T ⊔ conjSubgroup c T ≠ ⊤

@[expose] def M22WCPairFact : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ], CFSG.Blueprint.NativeSporadic.IsSporadic Λ .M22 →
    ∀ T : Subgroup Λ, IsWC T → Nat.card T = 16 →
      ∃ c : Λ, T ⊓ normalizer (conjSubgroup c T : Set Λ) ≠ ⊥ ∧
        4 * Nat.card (T ⊓ normalizer (conjSubgroup c T : Set Λ) : Subgroup Λ) ≤ Nat.card T

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M}

theorem Pair111.false_of_twentythree (P : Pair111 S g A h k ((m : G) * k))
    (hE : Ebar S k ((m : G) * k) ≠ ⊥) (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
    (hsimp : IsSimpleGroup (Lam97 S k m)) (hT : Nat.card (T97 S k m k) = 16)
    {c : Lam97 S k m} (hc : orderOf c = 23) : False := by
  have hd := P.finrank_le_ten hE hodd hT
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  refine P.false_of_orderOf_prime hE hodd hsimp (p := 23) (by norm_num) (fun j hj0 hj => ?_) hc
  have hj10 : j ≤ 10 := hj.trans hd
  interval_cases j <;> decide

theorem meet_of_psl {Λ : Type} [Group Λ] {T : Subgroup Λ} (hstd : StdPair Λ T) {n f : ℕ}
    (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : Λ ≃* StatedProj (StatedSL n K)) :
    ∀ c : Λ, conjSubgroup c T ⊓ normalizer (T : Set Λ) ≠ ⊥ := by
  obtain ⟨-, hTe⟩ := hstd.of_psl hn K hK e
  rcases hTe with ⟨c, hc0, hc⟩ | ⟨a, ha0, ha⟩
  · refine meet_of_mulEquiv e ?_
    rw [hc]
    exact transvCenter_meet hn hc0
  · refine meet_of_mulEquiv e ?_
    rw [ha]
    exact transvAxis_meet hn ha0

theorem not_badPair (hS : SimpleCaseStmt) (h215 : Lemma215Stmt) (hI : ListWCIdentification)
    (hA9 : A9WCPairFact) (hM22 : M22WCPairFact) (h6 : 6 ≤ S.width)
    (hex : ∃ h k m, BadPair S g A h k m) : False := by
  obtain ⟨h, k, m, B, hmax, hmin⟩ := exists_lex_badPair hex
  have P := B.1
  have hE := B.2.1
  have h4 := B.2.2
  obtain ⟨-, hodd, hsimp, hstd, -⟩ := P.form2 hS h215 hI h6 hE h4
  have hstd' : StdPair (Lam97 S k m) (T97 S k m k) := hstd
  have X := P.hyp97 hE
  have hWC : IsWC (T97 S k m k) :=
    (X.Tj97_isWC le_sup_left P.hy.hyp4 P.hy.cons
      (P.isTI97 (P.isTIModEF h6 hE))).map_quotient_central_odd _ le_rfl hodd
  have htr := hstd'.transitive
  have hcomm := fun x (hx : x ∈ T97 S k m k) y (hy : y ∈ T97 S k m k) =>
    elemAbelian_mul_comm (isElemAbelian_T97 (k := k) (m := m) P.hy.hyp4) hx hy
  rcases hstd'.listGroup with ⟨n, s, hn, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hso, hs, hmod⟩ |
      ⟨j, hj6, hj9, ⟨eA⟩⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    ·
      obtain rfl : n = 2 := by omega
      obtain ⟨-, ⟨Q, hQ⟩, -, hN⟩ := hstd'.of_psl2 hmod
      refine P.false_of_SR hE hodd h4 hsimp htr (srProp_of_sylow hWC Q (fun x hx y hy => ?_) hN)
      rw [hQ] at hx
      exact hcomm x hx y hy
    ·
      obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := hmod
      exact B.false_of_meet hmax hodd (meet_of_psl hstd' hn3 hK e)
  ·
    obtain ⟨-, ⟨Q, hQ⟩, -, hN⟩ := hstd'.of_psu3 hs hmod
    refine P.false_of_SR hE hodd h4 hsimp htr (srProp_of_sylow hWC Q (fun x hx y hy => ?_) hN)
    rw [hQ] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact congrArg Subtype.val (mem_center_iff.mp hy' ⟨x, hx⟩)
  ·
    obtain ⟨-, ⟨Q, hQ⟩, -, hN⟩ := hstd'.of_sz hso hs hmod
    refine P.false_of_SR hE hodd h4 hsimp htr (srProp_of_sylow hWC Q (fun x hx y hy => ?_) hN)
    rw [hQ] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact congrArg Subtype.val (mem_center_iff.mp hy' ⟨x, hx⟩)
  ·
    have hT := hstd'.card_alternating hj6 hj9 ⟨eA⟩
    interval_cases j
    · obtain ⟨c₀, hc₀⟩ := exists_orderOf_five_alternating_six
      have hc : orderOf (eA.symm c₀) = 5 := by rw [MulEquiv.orderOf_eq]; exact hc₀
      exact P.false_of_four hE hodd (by simpa using hT)
        (P.four_le_finrank_of_orderOf_five hE hodd hsimp hc) htr
    · obtain ⟨c₀, hc₀⟩ := exists_orderOf_five_alternating_seven
      have hc : orderOf (eA.symm c₀) = 5 := by rw [MulEquiv.orderOf_eq]; exact hc₀
      exact P.false_of_four hE hodd (by simpa using hT)
        (P.four_le_finrank_of_orderOf_five hE hodd hsimp hc) htr
    · obtain ⟨e⟩ := nonempty_mulEquiv_psl_of_alternating_eight eA
      exact B.false_of_meet hmax hodd
        (meet_of_psl hstd' (n := 4) (f := 1) (by norm_num) (by simp) e)
    ·
      have hT8 : Nat.card (T97 S k m k) = 8 := by simpa using hT
      obtain ⟨c, hc1, hc2⟩ := hA9 _ ⟨eA⟩ _ hWC hT8
      exact hc2 (B.sup_eq_top_of_inf_eq_bot hmax hmin hodd (by omega) hc1)
  ·
    have hT16 := hstd'.card_sporadic (Or.inl hM)
    obtain ⟨c, hc1, hc2⟩ := hM22 _ hM _ hWC hT16
    have h1 := B.card_le_two_mul_of_ne_bot hmax hodd hc1
    have h2 : 0 < Nat.card (T97 S k m k ⊓
        normalizer (conjSubgroup c (T97 S k m k) : Set (Lam97 S k m)) : Subgroup (Lam97 S k m)) :=
      Nat.card_pos
    omega
  ·
    obtain ⟨e⟩ := hM
    obtain ⟨c₀, hc₀⟩ := exists_orderOf_23_M23
    have hc : orderOf (e.symm c₀) = 23 := by rw [MulEquiv.orderOf_eq]; exact hc₀
    exact P.false_of_twentythree hE hodd hsimp (hstd'.card_sporadic (Or.inr (Or.inl ⟨e⟩))) hc
  ·
    obtain ⟨e⟩ := hM
    obtain ⟨c₀, hc₀⟩ := exists_orderOf_23_M24
    have hc : orderOf (e.symm c₀) = 23 := by rw [MulEquiv.orderOf_eq]; exact hc₀
    exact P.false_of_twentythree hE hodd hsimp (hstd'.card_sporadic (Or.inr (Or.inr ⟨e⟩))) hc

theorem residual97For111_of (hS : SimpleCaseStmt) (h215 : Lemma215Stmt)
    (hI : ListWCIdentification) (hA9 : A9WCPairFact) (hM22 : M22WCPairFact) :
    Residual97For111 := by
  intro G _ _ _ S g A C h6 h hh hA k m hk hkz hmk O X _ hLO hidx
  exfalso
  have P : Pair111 S g A h k ((m : G) * k) := ⟨C, hh, hA, hk, hkz, hmk, conj_ne_z' S m.2 hkz⟩
  have hO : O = O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k)) := by
    have h1 : O.subgroupOf (S.Lbar k ⊔ S.Lbar ((m : G) * k)) =
        (O2Sub (S.Lbar k ⊔ S.Lbar ((m : G) * k))).subgroupOf (S.Lbar k ⊔ S.Lbar ((m : G) * k)) :=
      X.subgroupOf_eq_pCore.trans (subgroupOf_O2Sub _).symm
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr X.le, inf_eq_left.mpr (O2Sub_le _)] at h1
    exact h1
  subst hO
  have hE : Ebar S k ((m : G) * k) ≠ ⊥ := by
    rw [← P.inf_O2Sub_eq]
    exact X.inf_ne_bot
  have h4 := X.four_mul_card_le hLO hidx
  rw [P.inf_O2Sub_eq] at h4
  exact not_badPair hS h215 hI hA9 hM22 h6 ⟨h, k, m, P, hE, h4⟩

end CFSG.LargeExtraspecial.S11
