module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
public import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Sporadic.Bridge.Y443Relabel

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint

@[expose] def sporOrd : TauCeti.SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .HS => 44352000
  | .McL => 898128000
  | .He => 4030387200
  | .Ru => 145926144000
  | .Suz => 448345497600
  | .ONan => 460815505920
  | .Co1 => 4157776806543360000
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24Prime => 1255205709190661721292800
  | .HN => 273030912000000
  | .Ly => 51765179004000000
  | .Th => 90745943887872000
  | .B => 4154781481226426191177580544000000
  | .M => 808017424794512875886459904961710757005754368000000000

@[expose] def P1OffRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (s = .M12 ∧ p = 3) ∨ (s = .M24 ∧ p = 3) ∨ (s = .J2 ∧ p = 3) ∨ (s = .J4 ∧ p = 3) ∨
  (s = .J4 ∧ p = 11) ∨ (s = .HS ∧ p = 5) ∨ (s = .He ∧ p = 3) ∨ (s = .He ∧ p = 7) ∨
  (s = .Ru ∧ p = 3) ∨ (s = .Ru ∧ p = 5) ∨ (s = .McL ∧ p = 5) ∨ (s = .Co2 ∧ p = 5) ∨
  (s = .Co3 ∧ p = 5) ∨ (s = .Th ∧ p = 5) ∨ (s = .ONan ∧ p = 7)

private instance (p : ℕ) (s : TauCeti.SporadicName) : Decidable (P1ThreeSporList p s) := by
  unfold P1ThreeSporList
  infer_instance

private instance (s : TauCeti.SporadicName) (p : ℕ) : Decidable (P1OffRow s p) := by
  unfold P1OffRow
  infer_instance

theorem offList_table : ∀ s : TauCeti.SporadicName, ∀ p ∈ Finset.range 80, p.Prime → p ≠ 2 →
    p ^ 3 ∣ sporOrd s → P1ThreeSporList p s ∨ P1OffRow s p := by
  decide +kernel

theorem primeFactors_lt (s : TauCeti.SporadicName) : ∀ p ∈ (sporOrd s).primeFactors, p < 80 := by
  cases s <;> simp only [sporOrd] <;> norm_num [Nat.primeFactors]

theorem offList_cases (s : TauCeti.SporadicName) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 3 ∣ sporOrd s) : P1ThreeSporList p s ∨ P1OffRow s p := by
  have hN : sporOrd s ≠ 0 := by cases s <;> simp [sporOrd]
  have hmem : p ∈ (sporOrd s).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p three_ne_zero).trans h, hN⟩
  exact offList_table s p (Finset.mem_range.2 (primeFactors_lt s p hmem)) hp hp2 h

section Carrier


theorem card_carrier_eq_sporOrd
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder) (s : TauCeti.SporadicName) :
    Nat.card (NativeSporadic.Carrier s) = sporOrd s := by
  by_cases hTh : s = .Th
  · subst hTh
    exact CFSG.RankThree.PartOne.CTP.card_Th
  by_cases hM : s = .M
  · subst hM
    exact (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  · rw [CFSG.EvenSmallLie.Child3.card_carrier s hTh hM]
    cases s <;> first | rfl | exact absurd rfl hTh | exact absurd rfl hM

end Carrier

end CFSG.AGLEmbedding
