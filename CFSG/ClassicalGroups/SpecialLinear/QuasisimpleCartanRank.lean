module

public import CFSG.Adapters.CatalogueFieldBridges.Linear

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open CFSG.Open Matrix

theorem odd_card_sub_one_of_char_two {F : Type} [Field F] [Finite F] [CharP F 2] :
    Odd (Nat.card F - 1) := by
  have hring : ringChar F = 2 := CharP.ringChar_of_prime_eq_zero Nat.prime_two (by
    simpa using (CharP.cast_eq_zero F 2))
  letI := Fintype.ofFinite F
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two hring)
  exact Nat.Even.sub_odd (by exact Nat.card_pos) heven odd_one

instance finite_lie_A (m : ℕ) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid) :
    Finite (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  let F := GaloisField Q.p Q.exponent
  have hFcard : Nat.card F = Q.p ^ Q.exponent :=
    GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
  have hQcard : Q.card = Q.p ^ Q.exponent := TauCeti.PrimePower.card_def Q
  have hk : Nat.card F = Q.card := by rw [hFcard, hQcard]
  obtain ⟨e⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie (n := m) (k := F) Q hv hk
  exact Finite.of_equiv (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (m + 1) F)
    e.toEquiv

end CFSG.ClassicalGroups.SpecialLinear

end
