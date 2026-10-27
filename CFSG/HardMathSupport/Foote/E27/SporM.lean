module

public import CFSG.HardMathSupport.Foote.E27.SporBig

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Blueprint CFSG.Monster.B.Pinned CFSG.Monster.Generated

theorem factorization_monsterOrder : CFSG.Open.monsterOrder.factorization 3 = 20 := by
  have h : CFSG.Open.monsterOrder = 3 ^ 20 * (2 ^ 46 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 *
      23 * 29 * 31 * 41 * 47 * 59 * 71) := by
    unfold CFSG.Open.monsterOrder
    ring
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Certificates


theorem e27SporAt_M_of_local {q : Fin 12 → Gmat} {w b₁ b₂ : Gmat}
    {M : Matrix (Fin 12) (Fin 12) (ZMod 3)} {X Y : GL (Fin 12) (ZMod 3)} {c₁ c₂ : Fin 12 → ℕ}
    (hD : CommData 3 q w M)
    (h₁ : ∀ i, b₁⁻¹ * q i * b₁ = (List.ofFn fun j =>
      q j ^ ((X : Matrix (Fin 12) (Fin 12) (ZMod 3)) i j).val).prod * w ^ c₁ i)
    (h₂ : ∀ i, b₂⁻¹ * q i * b₂ = (List.ofFn fun j =>
      q j ^ ((Y : Matrix (Fin 12) (Fin 12) (ZMod 3)) i j).val).prod * w ^ c₂ i)
    (hK : 3 ^ 7 ∣ Nat.card (Subgroup.closure {g | g ∈ [X, Y]})) : E27SporAt .M := by
  intro X' _ _ K R T z hc hz ⟨e⟩
  have hfin : Finite Gmat :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]; norm_num [CFSG.Open.monsterOrder])
  have hbr := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .M
  have : IsSimpleGroup ↥K := hc.simple
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple (T := ↥K) (e.trans hbr.some.symm)
  obtain ⟨hLQ, hL⟩ := @local_of_rel Gmat _ hfin 12 M q w b₁ b₂ hD X Y c₁ c₂ h₁ h₂ 7 hK
  refine @E27Config.false_of_commData X' _ _ K R T z hc hz Gmat _ hfin φ 6 (by norm_num) q w M
    hD _ hLQ ?_
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, factorization_monsterOrder]
  exact hL

end Certificates

end CFSG.HardMathSupport.Foote.E27
