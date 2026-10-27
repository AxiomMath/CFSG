module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

section Aux

variable {X : Type} [Group X]

theorem center_eq_bot_of_isSimple_of_isQuasisimple (hq : CFSG.IsQuasisimple X)
    (hs : IsSimpleGroup X) : Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hnt : Nontrivial (X ⧸ Subgroup.center X) := hq.2.1.toNontrivial
    obtain ⟨q, hq1⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq1 ((QuotientGroup.eq_one_iff x).mpr (by rw [h]; exact Subgroup.mem_top x))

theorem nonempty_mulEquiv_of_center_eq_bot {K : Type} [Group K] (hc : Subgroup.center X = ⊥)
    (e : (X ⧸ Subgroup.center X) ≃* K) : Nonempty (X ≃* K) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem exists_noncomm_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q] (hs : IsSimpleGroup Q)
    {N : ℕ} (hN : Nat.card Q = N) (h2 : 2 ∣ N) (h3 : 2 < N) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  have : IsMulCommutative Q := ⟨⟨fun a b => hc a b⟩⟩
  have hp : (Nat.card Q).Prime := Group.is_simple_iff_prime_card.mp hs
  rw [hN] at hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2) with h | h <;> omega

end Aux

theorem center_eq_pCore_of_sporadic
    {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hXq : CFSG.IsQuasisimple ↥X) {s : TauCeti.SporadicName} (hs : Ch1.IsLemma115SporadicName s)
    (f : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* NativeSporadic.Carrier s) :
    CFSG.pCore 2 ↥X = Subgroup.center ↥X ∧ ∃ N : ℕ, Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = N ∧
      (N = 7920 ∨ N = 95040 ∨ N = 443520 ∨ N = 10200960 ∨ N = 244823040 ∨ N = 604800 ∨
        N = 86775571046077562880 ∨ N = 44352000 ∨ N = 4030387200 ∨ N = 145926144000) := by
  obtain ⟨hsimple, hcard⟩ := sporadic_data hs
  have hsimple' : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := by
    have := hsimple
    exact f.isSimpleGroup
  have hN : Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = Nat.card (NativeSporadic.Carrier s) :=
    Nat.card_congr f.toEquiv
  have h23 : 2 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∧ 2 < Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [hN]
    rcases hcard with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> omega
  have hnc := exists_noncomm_of_isSimpleGroup hsimple' rfl h23.1 h23.2
  exact ⟨pCore_eq_center_of_simple_quotient hXq hsimple' hnc, _, hN, hcard⟩

theorem tabCover
    : TabCover := by
  intro G _ _ X K hXq ⟨z, hz⟩ hK ⟨e⟩
  have hcardK : Nat.card ↥K = Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    (Nat.card_congr e.toEquiv).symm
  rcases hz with ⟨hs, -, -⟩ | ⟨-, hZ, hM, -⟩ | hC | hD | ⟨hE, -⟩ | ⟨⟨s, hs, ⟨f⟩⟩, -⟩
  ·
    exact nonempty_mulEquiv_of_center_eq_bot
      (center_eq_bot_of_isSimple_of_isQuasisimple hXq hs) e
  ·
    exfalso
    have hcard : Nat.card ↥K = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) :=
      hcardK.trans (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv)
    rcases hM with hm | hm
    · exact not_card_isL2pType hK (Or.inl rfl) (hcard.trans (card_of_psl_three_four hm))
    · exact not_card_isL2pType hK (Or.inr (Or.inl rfl)) (hcard.trans (card_of_g2_four hm))
  ·
    exfalso
    obtain ⟨φ, -⟩ := hC
    exact not_card_isL2pType hK (Or.inr (Or.inr (Or.inl rfl)))
      (hcardK.trans ((Nat.card_congr φ.toEquiv).trans card_alternatingGroup_six))
  ·
    exfalso
    obtain ⟨φ, -⟩ := hD
    exact not_card_isL2pType hK (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (hcardK.trans ((Nat.card_congr φ.toEquiv).trans card_alternatingGroup_seven))
  ·
    have hsimple : IsSimpleGroup ↥X := by
      rcases hE with hm | ⟨p, -, hm⟩
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 hm).2
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hm).2
    exact nonempty_mulEquiv_of_center_eq_bot
      (center_eq_bot_of_isSimple_of_isQuasisimple hXq hsimple) e
  ·
    exfalso
    obtain ⟨hpc, N, hN, hlist⟩ := center_eq_pCore_of_sporadic hXq hs f
    have hcard : Nat.card ↥K = N := by
      rw [hcardK, ← hN]
      exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hpc.symm).toEquiv
    exact not_card_isL2pType hK (by omega) hcard

end CFSG.QuasithinUnique.Id2519
