module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5115
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stmt5_1_15_of_F4 (h516 : Stmt5_1_6_F4) (h5114 : Stmt5_1_14_first_F4) (hF : L2TorusFact) :
    Stmt5_1_15_F4 := by
  intro G _ _ T M L V H B D n hyp hN hV hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hH := hyp.hStar
  obtain ⟨⟨-, hU, -⟩, ⟨hZH, -⟩, -⟩ := h5114 G T M L V H B D n hyp hN hV hK
  by_cases hDM : D ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  · exact Or.inl hDM
  right
  have hD := hN.2.1
  have hO : pCoreOf 2 (D ⊔ H) = ⊥ := by
    by_contra hne
    exact hDM (le_of_pCoreOf_sup_ne_bot hU hne)
  obtain ⟨hev, hcase⟩ := h516 G T M L V H D n h hV hH hD hO

  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hH.1.1
  have hT1 : T ≠ ⊥ := by
    intro hT
    apply hH.1.2
    have := F7.isSylowTwoOf_pCoreOf_le hTH
    rw [hT] at this
    exact le_bot_iff.mp this
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le hZT
  have hZ1 : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot h.sylow.1 hT1
  have hZHle : quasithinOmegaOneCenter T ≤ H := hZT.trans hH.1.1
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
  rcases hcase with ⟨h2, hsum, -⟩ | ⟨h24, hnat, -⟩ | ⟨-, -, -, hcen⟩ | ⟨-, horth, -, hDpm⟩
  · exact Or.inl ⟨h2, hsum⟩
  · exact Or.inr (Or.inl ⟨h24, hnat⟩)
  · exfalso
    apply hZ1
    have hle : quasithinOmegaOneCenter T ≤ centerOf H := le_inf hZHle hZC
    rw [hcen] at hle
    exact le_bot_iff.mp hle
  · right
    right

    obtain ⟨m, hm⟩ := hev
    have hn2 : n / 2 = m := by omega
    have hm0 : m ≠ 0 := by have := h.two_le; omega
    obtain ⟨hcyc, hcard⟩ := h.isCyclic_card_of_isHall hF hD
    have hcard' : Nat.card D = (2 ^ (n / 2) - 1) * (2 ^ (n / 2) + 1) := by
      rw [hcard, hn2, two_pow_sub_one_mul_add_one, hm, two_mul]
    have hpos1 : 0 < 2 ^ (n / 2) - 1 := by
      have : 2 ≤ 2 ^ (n / 2) := by
        rw [hn2]
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm0)
      omega
    obtain ⟨Dp, Dm, hDp, hDm, hcDp, hcDm, hDle⟩ := exists_le_sup_of_isCyclic hcyc
      (hn2 ▸ coprime_two_pow_sub_one_add_one hm0) hcard' hpos1 (by positivity)
    have hminus : ∀ Dm' : Subgroup G, Dm' ≤ D → Nat.card Dm' = 2 ^ (n / 2) + 1 →
        Dm' ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
      intro Dm' hDm' hcDm'
      obtain ⟨hcen, -⟩ := hDpm Dp Dm' hDp hDm' hcDp hcDm'
      refine le_of_pCoreOf_sup_ne_bot hU ?_
      exact pCoreOf_ne_bot_of_le_centerOf hZ2 hZ1 (hcen.trans inf_le_left)
        (hcen.trans inf_le_right)
    refine ⟨?_, horth, hminus⟩

    have hDpM : ¬ Dp ≤ Subgroup.normalizer (oTwoUpper H : Set G) := fun hle =>
      hDM (hDle.trans (sup_le hle (hminus Dm hDm hcDm)))
    obtain ⟨-, hor⟩ := hDpm Dp Dm hDp hDm hcDp hcDm
    rcases hor with hne | h48
    · exact absurd (le_of_pCoreOf_sup_ne_bot hU hne) hDpM
    · exact h48

end CFSG.Quasithin.H13
