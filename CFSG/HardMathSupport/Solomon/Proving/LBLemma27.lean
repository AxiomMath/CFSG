module

public import CFSG.HardMathSupport.Solomon.Proving.LBLayerConj
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Proving

variable {Y : Type} [Group Y]

theorem glaPrimeCoreOf_top_eq_bot [Finite Y] {p : ℕ} (hp : p.Prime)
    (h : GLAPPrimeCore p Y = ⊥) :
    GLAPPrimeCoreOf p (⊤ : Subgroup Y) = ⊥ := by
  have hle : GLAPPrimeCoreOf p (⊤ : Subgroup Y) ≤ GLAPPrimeCore p Y := by
    refine le_sSup ⟨⟨fun n hn g => GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_top g) n hn⟩,
      coprime_card_GLAPPrimeCoreOf hp ⊤⟩
  rw [h] at hle
  exact eq_bot_iff.2 hle

theorem isPGroup_three_zpowers {x : Y} (hx3 : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  refine fun g => ⟨1, ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hx3, one_zpow]

theorem isKGroup_open_of_catalog {X : Type} [Group X] (h : CFSG.IsKGroup X) :
    CFSG.Open.IsKGroup X :=
  CFSG.KCore.KGroupAllSimple.kGroupNonab h

theorem lemma27_input14_5_of_second (hS : LocalBalance.Input14_5Second) :
    LocalBalance.Lemma27Ns.Input14_5 := by
  intro Y _ _ hK hcore x hx3
  by_cases hx1 : x = 1
  · subst hx1
    have hC : Subgroup.centralizer ({1} : Set Y) = ⊤ :=
      eq_top_iff.2 fun g _ => Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh, mul_one, one_mul]
    rw [hC, glaPrimeCoreOf_top_eq_bot Nat.prime_three hcore, Subgroup.commutator_bot_right]
  · have hQne : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.1 h)
    have hN := hS Y (isKGroup_open_of_catalog hK) hcore (Subgroup.zpowers x) hQne
      (isPGroup_three_zpowers hx3)
    exact eq_bot_iff.2
      ((Subgroup.commutator_mono (glaPLayer_centralizer_le_normalizer Nat.prime_three hx3)
        (glapPrimeCoreOf_centralizer_le_normalizer Nat.prime_three hx3)).trans hN.le)

end CFSG.HardMathSupport.Solomon.Proving

end
