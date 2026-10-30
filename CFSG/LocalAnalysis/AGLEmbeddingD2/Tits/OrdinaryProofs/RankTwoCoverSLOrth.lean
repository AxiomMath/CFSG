module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrth

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SL

variable {m : ℕ} {F : Type} [Field F]

public theorem eq_zero_or_one_of_card_two (hF : Nat.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  obtain ⟨a, b, hab, h⟩ := Nat.card_eq_two_iff.mp hF
  have hc : c ∈ ({a, b} : Set F) := by rw [h]; trivial
  have h0 : (0 : F) ∈ ({a, b} : Set F) := by rw [h]; trivial
  have h1 : (1 : F) ∈ ({a, b} : Set F) := by rw [h]; trivial
  by_contra hne
  push Not at hne
  obtain ⟨hc0, hc1⟩ := hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc h0 h1
  rcases hc with hc | hc <;> rcases h0 with h0' | h0' <;> rcases h1 with h1' | h1' <;>
    first | exact absurd (h0'.trans h1'.symm) zero_ne_one | exact absurd (h1'.trans h0'.symm) zero_ne_one | exact hc0 (hc.trans h0'.symm) | exact hc1 (hc.trans h1'.symm) | (simp_all [zero_ne_one]; done)

public theorem mem_rootGroup_single (k : Fin m) (x : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ (rootDatum m F).rootGroup (Pi.single k 1)) :
    ∃ c : F, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.transvection k.castSucc k.succ c := by
  have hpq : k.castSucc ≠ k.succ := (Fin.castSucc_lt_succ).ne
  have e := rootGroup_eq m F hpq (toStd_single m k)
  have hx' : x ∈ rootSubgroup m F hpq := by rw [← e]; exact hx
  rw [mem_rootSubgroup] at hx'
  obtain ⟨c, rfl⟩ := hx'
  exact ⟨c, rfl⟩

public theorem mem_rootGroup_neg_single (k : Fin m) (x : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (hx : x ∈ (rootDatum m F).rootGroup (-Pi.single k 1)) :
    ∃ c : F, (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.transvection k.succ k.castSucc c := by
  have hpq : k.succ ≠ k.castSucc := (Fin.castSucc_lt_succ).ne.symm
  have e := rootGroup_eq m F hpq (toStd_neg_single k)
  have hx' : x ∈ rootSubgroup m F hpq := by rw [← e]; exact hx
  rw [mem_rootSubgroup] at hx'
  obtain ⟨c, rfl⟩ := hx'
  exact ⟨c, rfl⟩

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.RankTwoCoverSLOrth
