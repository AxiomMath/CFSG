module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOSeven
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOSplitCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem ClO.split_eq_one_of_nf (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hJ1 : 1 ≤ J.card) (hJc1 : 1 ≤ Jᶜ.card) (hJ2 : J.card ≠ 2)
    (hJc2 : Jᶜ.card ≠ 2) (hNF : 3 ≤ J.card → BlockNF w J)
    (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ) :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd := card_compl_add J
  have hJd : 2 * J.card ≠ d := fun h => by
    obtain ⟨k, hk⟩ := hdodd
    omega
  have hJcd : 2 * Jᶜ.card ≠ d := fun h => by
    obtain ⟨k, hk⟩ := hdodd
    omega
  have hcc : Jᶜᶜ = J := compl_compl J
  by_cases hsmall : Nat.card K = 3 ∧ ((3 ≤ J.card ∧ J.card ≤ 4) ∨ (3 ≤ Jᶜ.card ∧ Jᶜ.card ≤ 4))
  · obtain ⟨h3, ⟨hJ3, hJ4⟩ | ⟨hJc3, hJc4⟩⟩ := hsmall
    · by_cases hJc4 : Jᶜ.card ≤ 4
      ·
        have hJc3 : 3 ≤ Jᶜ.card := by omega
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        obtain ⟨x', hx', y', hy', z', hz', hxy', hxz', hyz', hwxy', hwxz'⟩ :=
          (hNFc hJc3).exists_triple
        exact ClO.seven_split_eq_one_three h3 hK hw hker hRodd hRi hRc hsurj hJd (by omega) hJ4
          hJc4 hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      · obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        exact ClO.small_split_eq_one_three h3 hK hw hker hinj hRodd hRi hRc hsurj hJd hJ4
          ((hNFc (by omega)).blockOK (by omega) fun h => hJc4 h.2) hx hy hz hxy hxz hyz hwxy hwxz
    · by_cases hJ4 : J.card ≤ 4
      · have hJ3 : 3 ≤ J.card := by omega
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        obtain ⟨x', hx', y', hy', z', hz', hxy', hxz', hyz', hwxy', hwxz'⟩ :=
          (hNFc hJc3).exists_triple
        exact ClO.seven_split_eq_one_three h3 hK hw hker hRodd hRi hRc hsurj hJd (by omega) hJ4
          hJc4 hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      have hJ5 : 5 ≤ J.card := by omega
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNFc hJc3).exists_triple
      rw [← oκ_sgnPair_compl h2 hw J] at hRi hRc
      refine ClO.small_split_eq_one_three h3 hK hw hker hinj hRodd hRi hRc hsurj hJcd hJc4 ?_
        hx hy hz hxy hxz hyz hwxy hwxz
      rw [hcc]
      exact (hNF (by omega)).blockOK (by omega) fun h => by omega
  ·
    have hok : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockOK K w I := by
      rintro I (rfl | rfl) hI3
      · exact (hNF hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inl ⟨hI3, h.2⟩⟩
      · exact (hNFc hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inr ⟨hI3, h.2⟩⟩
    refine ClO.split_eq_one hK hw hker hinj hRodd hRi hRc hsurj hJd ?_ ?_ ?_
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (by omega)
    · by_cases hJc3 : 3 ≤ Jᶜ.card
      · exact Or.inl (hok Jᶜ (Or.inr rfl) hJc3)
      · exact Or.inr (by omega)
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (hok Jᶜ (Or.inr rfl) (by omega))

end CFSG.ComponentClassification.Foote5.OddLieCore
