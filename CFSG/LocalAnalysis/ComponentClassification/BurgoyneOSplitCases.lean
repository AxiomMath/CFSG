module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSliceProp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOInnerNF

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ}

theorem signMat_compl (J : Finset (Fin d)) : signMat K Jᶜ = -signMat K J := by
  ext i j
  simp only [signMat, Matrix.neg_apply, diagonal_apply, Finset.mem_compl]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ J <;> simp [hi]
  · simp [hij]

theorem oκ_sgnPair_compl (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J : Finset (Fin d)) : oκ _ (sgnPair h2 hw Jᶜ) = oκ _ (sgnPair h2 hw J) := by
  refine oκ_eq_of_left_eq (c := -1) rfl ?_
  apply Units.ext
  change signMat K Jᶜ = ((GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) : GL (Fin d) K) :
    Matrix (Fin d) (Fin d) K) * signMat K J
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_neg, Units.val_one,
    signMat_compl, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, neg_one_smul]

variable [Finite K]

theorem split_oddCoreIn_eq_bot_of_nf (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d) (hdodd : Odd d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJ1 : 1 ≤ J.card) (hJc1 : 1 ≤ Jᶜ.card) (hJ2 : J.card ≠ 2)
    (hJc2 : Jᶜ.card ≠ 2) (hNF : 3 ≤ J.card → BlockNF w J)
    (hNFc : 3 ≤ Jᶜ.card → BlockNF w Jᶜ) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
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
        exact seven_split_oddCoreIn_eq_bot_three h3 hK hw hker hsurj hB hJd (by omega) hJ4 hJc4
          hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      · obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        exact small_split_oddCoreIn_eq_bot_three h3 hK hw hker hsurj hinj hB hJd hJ4
          ((hNFc (by omega)).blockOK (by omega) fun h => hJc4 h.2) hx hy hz hxy hxz hyz hwxy hwxz
    · by_cases hJ4 : J.card ≤ 4
      · have hJ3 : 3 ≤ J.card := by omega
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        obtain ⟨x', hx', y', hy', z', hz', hxy', hxz', hyz', hwxy', hwxz'⟩ :=
          (hNFc hJc3).exists_triple
        exact seven_split_oddCoreIn_eq_bot_three h3 hK hw hker hsurj hB hJd (by omega) hJ4 hJc4
          hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      have hJ5 : 5 ≤ J.card := by omega
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNFc hJc3).exists_triple
      rw [← oκ_sgnPair_compl h2 hw J]
      refine small_split_oddCoreIn_eq_bot_three h3 hK hw hker
        (hsurj.of_eq (oκ_sgnPair_compl h2 hw J).symm) hinj hB hJcd hJc4 ?_
        hx hy hz hxy hxz hyz hwxy hwxz
      rw [hcc]
      exact (hNF (by omega)).blockOK (by omega) fun h => by omega
  ·
    have hok : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockOK K w I := by
      rintro I (rfl | rfl) hI3
      · exact (hNF hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inl ⟨hI3, h.2⟩⟩
      · exact (hNFc hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inr ⟨hI3, h.2⟩⟩
    refine split_oddCoreIn_eq_bot hK hw hker hsurj hinj hB hJd ?_ ?_ ?_
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (by omega)
    · by_cases hJc3 : 3 ≤ Jᶜ.card
      · exact Or.inl (hok Jᶜ (Or.inr rfl) hJc3)
      · exact Or.inr (by omega)
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (hok Jᶜ (Or.inr rfl) (by omega))

theorem slice_dichotomy (hK : ringChar K ≠ 2) (hd : 5 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a)
    (hJc : BlockOK K w jSetᶜ)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) = ⊥ ∨
      ∀ Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))), Y ≠ ⊥ →
        Y ≤ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) →
        PropAConclusionIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) Y := by
  have hJ2 : (jSet : Finset (Fin d)).card = 2 := by
    rw [show (jSet : Finset (Fin d)) = {⟨0, by omega⟩, ⟨1, by omega⟩} from by
      ext i
      simp only [mem_jSet, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega]
    exact Finset.card_pair (by simp [Fin.ext_iff])
  have hJd : 2 * (jSet : Finset (Fin d)).card ≠ d := by omega
  have hodd : Odd (Nat.card K) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  by_cases h3 : Nat.card K = 3
  · exact Or.inl (split_two_oddCoreIn_eq_bot_three h3 hK hw hker hsurj hinj hB hJ2 hJd hJc)
  · have hK5 : 5 ≤ Nat.card K := by
      have h1 : 2 ≤ Nat.card K := Finite.one_lt_card
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Or.inr fun Y hY hYO => slice_two_propAConclusionIn hK hK5 hd hw hW hker hinj hB
      (fun y hy => split_two_oddCoreIn hK hw hker hsurj hinj hB hJd hJc hy) hY hYO

end CFSG.ComponentClassification.Burgoyne.O
