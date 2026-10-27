module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.L44AtlasBridge
public import CFSG.RankThree.PartTwo.KFacts.AS76L44
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ElimFacts

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std

theorem atlasL44FixedPoints : AtlasL44FixedPoints := by
  intro E _ ⟨e⟩ α hαα hα1
  let e' : E ≃* CFSG.RankThree.PartTwo.KFacts.KS21.L44.PL :=
    e.trans (L44Atlas.pslEquivProjectiveSL 4 (GaloisField 2 2))
  have hfin : Finite E := Finite.of_equiv _ e'.symm.toEquiv
  have hα2 : orderOf α = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [sq]) hα1
  obtain ⟨y, hy3, hfix⟩ := CFSG.RankThree.PartTwo.Sec21.AS76.L44.invFixThree_PL
    (MulAut.congr e' α) (by rw [MulEquiv.orderOf_eq]; exact hα2)
  set z : E := e'.symm y with hz
  have hz3 : orderOf z = 3 := by rw [hz, MulEquiv.orderOf_eq]; exact hy3
  have hαz : α z = z := by
    apply e'.injective
    rw [MulAut.congr_apply] at hfix
    change e' (α (e'.symm y)) = y at hfix
    rw [hfix, hz, MulEquiv.apply_symm_apply]
  have hpow : ∀ n : ℕ, α (z ^ n) = z ^ n := fun n => by rw [map_pow, hαz]
  let f : Fin 3 → {x : E // α x = x} := fun i => ⟨z ^ (i : ℕ), hpow i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : z ^ (i : ℕ) = z ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (pow_injOn_Iio_orderOf (x := z) (by rw [Set.mem_Iio, hz3]; exact i.2)
      (by rw [Set.mem_Iio, hz3]; exact j.2) h1)
  simpa using Nat.card_le_card_of_injective f hf

end CFSG.EvenSporadicStandard.M24Std
