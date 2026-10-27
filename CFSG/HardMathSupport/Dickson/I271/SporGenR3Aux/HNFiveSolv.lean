module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Burnside
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

theorem isSolvable_of_card_dvd_two_five {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 5 ^ b) : Group.IsSolvable G := by
  obtain ⟨d₁, d₂, hd₁, hd₂, hd⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd₁
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hd₂
  haveI : Fintype G := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_five (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, ← hd, hi, hj])

end CFSG.HardMathSupport.Dickson.I271
