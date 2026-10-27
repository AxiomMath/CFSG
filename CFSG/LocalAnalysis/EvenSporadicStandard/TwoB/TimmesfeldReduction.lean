module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.OrderTwentyThree
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.Sporadic.Co2
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.Bridge Matrix
open scoped MatrixGroups

theorem exists_orderOf_23_of_co2 {M : Type} [Group M]
    (S : Subgroup M) (eS : S ≃* Carrier .Co2) {X : Type} [Group X]
    (e : M ≃* Equiv.Perm (Fin 3) × X) : ∃ x : X, orderOf x = 23 := by
  have h23 : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
  have : Finite (Carrier .Co2) := Nat.finite_of_card_ne_zero (by rw [hco]; norm_num)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Carrier .Co2) 23
    (by rw [hco]; norm_num)
  have hs : orderOf (eS.symm c) = 23 := by rw [MulEquiv.orderOf_eq]; exact hc
  have hm : orderOf ((eS.symm c : S) : M) = 23 := by rw [Subgroup.orderOf_coe]; exact hs
  set y : Equiv.Perm (Fin 3) × X := e ((eS.symm c : S) : M) with hy
  have hyo : orderOf y = 23 := by rw [hy, MulEquiv.orderOf_eq]; exact hm
  have hy23 : y ^ 23 = 1 := hyo ▸ pow_orderOf_eq_one y
  have h1 : y.1 ^ 23 = 1 := by
    have := congrArg Prod.fst hy23
    simpa using this
  have h2 : y.2 ^ 23 = 1 := by
    have := congrArg Prod.snd hy23
    simpa using this
  have h6 : y.1 ^ 6 = 1 := by
    have := pow_card_eq_one (x := y.1)
    rw [Fintype.card_perm, Fintype.card_fin] at this
    exact this
  have hσ : y.1 = 1 := by
    have h3 : orderOf y.1 ∣ Nat.gcd 23 6 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h6)
    have : orderOf y.1 = 1 := by
      have h4 : Nat.gcd 23 6 = 1 := by norm_num
      rw [h4] at h3
      exact Nat.dvd_one.1 h3
    exact orderOf_eq_one_iff.1 this
  refine ⟨y.2, orderOf_eq_prime h2 ?_⟩
  intro hone
  have : y = 1 := Prod.ext hσ hone
  rw [this, orderOf_one] at hyo
  omega

theorem no_co2_in_alt3 {M : Type} [Group M] (S : Subgroup M)
    (eS : S ≃* Carrier .Co2) (q : QuadraticForm (ZMod 2) (Fin 12 → ZMod 2))
    (hq : timmesfeldNondegenerate q)
    (X : Subgroup ((Fin 12 → ZMod 2) ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)))
    (hX : X ≤ timmesfeldIsometries q) (e : M ≃* Equiv.Perm (Fin 3) × ↥X) : False := by
  obtain ⟨x, hx⟩ := exists_orderOf_23_of_co2 S eS e
  have hg : orderOf (x : (Fin 12 → ZMod 2) ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)) = 23 := by
    rw [Subgroup.orderOf_coe]; exact hx
  have hV : Nat.card (Fin 12 → ZMod 2) = 2 ^ 12 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  exact no_order_23_isometry (K := ZMod 2) hV q hq x hg (fun v => hX x.2 v)

theorem nonempty_quotient_co1_of_mainStatement (hM : MainStatement)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (z : G) (hz : orderOf z = 2)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))))
    (hcard : Nat.card (CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = 2 ^ 25)
    (hcen : centralizer ((CFSG.pCore 2 ↥(centralizer ({z} : Set G)) :
        Subgroup ↥(centralizer ({z} : Set G))) : Set ↥(centralizer ({z} : Set G))) ≤
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)))
    (hCo2 : ∃ S : Subgroup (↥(centralizer ({z} : Set G)) ⧸
        CFSG.pCore 2 ↥(centralizer ({z} : Set G))), Nonempty (S ≃* Carrier .Co2))
    (hAlt2 : ¬ (Nonempty (G ≃* PSL(12 + 2, ZMod 2)) ∨ Nonempty (G ≃* timmesfeldPSU (12 + 2)))) :
    Nonempty (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G)) ≃*
      Carrier .Co1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Sset : CFSG.LargeExtraspecial.Setting G :=
    { z := z
      orderOf_z := hz
      Q := CFSG.pCore 2 ↥(centralizer ({z} : Set G))
      normal := CFSG.pCore_normal
      extraspecial := hext
      centralizer_le := hcen
      le_of_normal := fun P hP h2 => le_sSup ⟨hP, h2⟩ }
  have hFS : timmesfeldFStar ↥(centralizer ({z} : Set G)) =
      CFSG.pCore 2 ↥(centralizer ({z} : Set G)) := (Q_eq_timmesfeldFStar Sset).symm
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : center ↥(CFSG.pCore 2 ↥(centralizer ({z} : Set G))) = ⊤ := by
      refine (Subgroup.eq_top_iff' _).2 fun a => mem_center_iff.2 fun b => ?_
      exact Subtype.ext (Subtype.ext (hcon _ _))
    have h2 := hext.2.2.2
    rw [htop, Subgroup.card_top, hcard] at h2
    norm_num at h2
  have hw : Nat.card (timmesfeldFStar ↥(centralizer ({z} : Set G))) = 2 ^ (1 + 2 * 12) := by
    rw [hFS, hcard]
  have hMbar : timmesfeldQuotientIso (timmesfeldFStar ↥(centralizer ({z} : Set G)))
      (↥(centralizer ({z} : Set G)) ⧸ CFSG.pCore 2 ↥(centralizer ({z} : Set G))) :=
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, by
      rw [hFS]
      exact QuotientGroup.ker_mk' _⟩
  have hconc := hM G hnonab z hz (timmesfeldIsExtraspecial_fstar Sset) 12 hw _ hMbar
  rcases hCo2 with ⟨S, ⟨eS⟩⟩
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · omega
  · exact absurd h2 hAlt2
  · obtain ⟨-, -, q, hq, h | h⟩ := h3
    · obtain ⟨e⟩ := h
      exact (no_co2_in_alt3 S eS q hq _ (Subgroup.closure_le _ |>.2 fun g hg => hg.1) e).elim
    · obtain ⟨e⟩ := h
      exact (no_co2_in_alt3 S eS q hq _ le_rfl e).elim
  · omega
  · omega
  · omega
  · exact h7.2
  · rcases h8 with ⟨-, t, -, -, h | h⟩ <;> omega

end CFSG.EvenSporadicStandard.TwoB
