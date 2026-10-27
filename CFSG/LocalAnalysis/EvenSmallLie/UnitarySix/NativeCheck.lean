
module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeCheckBase

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs
public import Certificates.Certificate3010
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Sporadic.Schreier CFSG.Certificates
open _root_.Certificates (closureU)
open scoped Pointwise

open _root_.Certificates (closureU)

theorem chains_check :
    chainsCheck = true :=
  Certificates.certificate3010.1

theorem structure_check :
    (∀ x ∈ aGens, orderOf x = 2 ∧ ∀ y ∈ aGens, x * y = y * x) ∧
      (∀ k ∈ kGens ++ tGens, ∀ a ∈ aGens, k * a * k⁻¹ ∈ closureU aGens) ∧
      ∀ g ∈ tGens, g ∈ closureU kGens :=
  Certificates.certificate3010.2.1

theorem fix_check :
    {p : Fin 693 | j3 p = p} = finSet 693 fixA ∧
      (∀ a ∈ aGens, ∀ p ∈ finSet 693 fixA, a p = p) ∧
      891 ≤ (Set.range fun g : closureU u62Letters => g • finSet 693 fixA).ncard :=
  Certificates.certificate3010.2.2.1

theorem orbit_check :
    (∀ a ∈ closureU aGens, a ≠ 1 → a ∈ conjClass (closureU kGens) j1 ∨
        a ∈ conjClass (closureU kGens) j2 ∨ a ∈ conjClass (closureU kGens) j3) ∧
      (conjClass (closureU kGens) j1).ncard = 21 ∧
      (conjClass (closureU kGens) j2).ncard = 210 ∧
      (conjClass (closureU kGens) j3).ncard = 280 ∧
      orderOf j1 = 2 ∧ orderOf j2 = 2 ∧ orderOf j3 = 2 ∧
      {p : Fin 693 | j1 p = p}.ncard = 181 ∧ {p : Fin 693 | j2 p = p}.ncard = 53 ∧
      {p : Fin 693 | j3 p = p}.ncard = 21 ∧
      ∀ k ∈ closureU kGens, (∀ a ∈ aGens, k * a = a * k) → k = 1 :=
  Certificates.certificate3010.2.2.2.1

theorem sylow_check :
    (∀ u ∈ closureU sGens, orderOf u = 2 →
        ∃ r ∈ sReps, ∃ c ∈ closureU sGens, u = c * r * c⁻¹) ∧
      (∀ r ∈ sReps, orderOf r = 2) ∧
      (∀ p ∈ List.zip sConjs sReps, p.1 * p.2 * p.1⁻¹ ∈ closureU aGens) ∧
      (∀ g ∈ sGens, j1 * g = g * j1) ∧
      (∀ x ∈ closureU sGens, (∀ g ∈ sGens, x * g = g * x) → x = 1 ∨ x = j1) ∧
      ∀ r ∈ sReps,
        ({p : Fin 693 | r p = p}.ncard = 53 → 2 ≤ (conjClass (closureU sGens) r).ncard) ∧
        ({p : Fin 693 | r p = p}.ncard = 21 → 8 ≤ (conjClass (closureU sGens) r).ncard) :=
  Certificates.certificate3010.2.2.2.2.1

theorem thompson_check :
    (∀ x ∈ closureU tGens, (∀ g ∈ tGens, x * g = g * x) ∨
        Nat.card {y : closureU tGens // (y : Equiv.Perm (Fin 693)) * x = x * y} ≤ 16) ∧
      Nat.card {x : closureU tGens // ∀ g ∈ tGens, (x : Equiv.Perm (Fin 693)) * g = g * x} ≤
        16 ∧
      (∀ x ∈ closureU tGens, x ≠ 1 →
        Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 32) ∧
      (∀ x ∈ closureU tGens, x * x ≠ 1 →
        Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * x = x * a} ≤ 16) ∧
      ∀ b ∈ closureU tGens, ∀ c ∈ closureU tGens, b ≠ c → b ≠ 1 → c ≠ 1 → b * b = 1 →
        c * c = 1 → b * c = c * b →
        Nat.card {a : closureU aGens // (a : Equiv.Perm (Fin 693)) * b = b * a ∧
          (a : Equiv.Perm (Fin 693)) * c = c * a} ≤ 16 :=
  Certificates.certificate3010.2.2.2.2.2.1

theorem square_check :
    orderOf o1 = 3 ∧ orderOf o2 = 3 ∧ o1 * j1 = j1 * o1 ∧ o2 * j1 = j1 * o2 ∧
      (o1 * o2) ^ 2 = j1 ∧ y2 ^ 2 = j2 ∧
      ∀ k ∈ closureU kGens, k * j3 = j3 * k → ∀ a ∈ closureU aGens, (a * k) ^ 2 ≠ j3 :=
  Certificates.certificate3010.2.2.2.2.2.2.1

theorem beta_check :
    betaCheck = true :=
  Certificates.certificate3010.2.2.2.2.2.2.2

end CFSG.EvenSmallLie.UnitarySix
