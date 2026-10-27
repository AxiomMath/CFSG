module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOGenSplit
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  commute_signMat_iff commute_compInd_iff eq_bot_of_four_group)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem ClO.iso_of_blockOK (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hIok : BlockOK K w I)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hRc : ∀ s, oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g : similarityPairs (oQ (diagGL hw))} (hy : oκ _ g ∈ Ro) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩ := hIok
  obtain ⟨hτ, hDS, hiso₀, -⟩ := ClO.split_core_gen hK hw hker hinj hI hI3 hIexc hI₀ hI₀3 hI₀w
    hRodd hRi hRc hy
  have hblock := (commute_compInd_iff J _).1 ((commute_signMat_iff h2 J _).1 hDS)
  have hsep : ∀ x ∈ I, ∀ y ∉ I, (x ∈ J ↔ y ∉ J) ∧ (y ∈ J ↔ x ∉ J) := by
    intro x hxI y hyI
    rcases hI with hIJ | hIJ
    · rw [hIJ] at hxI hyI
      exact ⟨⟨fun _ => hyI, fun _ => hxI⟩, ⟨fun h => absurd h hyI, fun h => absurd hxI h⟩⟩
    · rw [hIJ, Finset.mem_compl] at hxI
      rw [hIJ, Finset.mem_compl, not_not] at hyI
      exact ⟨⟨fun h => absurd h hxI, fun h => absurd hyI h⟩, ⟨fun _ => hxI, fun _ => hyI⟩⟩
  refine ⟨hτ, hDS, fun x hx y hyx => ?_⟩
  by_cases hx₀ : x ∈ I₀
  · exact hiso₀ x hx₀ y hyx
  by_cases hy₀ : y ∈ I₀
  · exact (hiso₀ y hy₀ x (Ne.symm hyx)).symm
  by_cases hyI : y ∈ I
  · exact absurd (hI₀c y hyI x hx hy₀ hx₀) hyx
  · exact ⟨hblock x y (hsep x hx y hyI).1, hblock y x (hsep x hx y hyI).2⟩

theorem ClO.split_eq_one_gen (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
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
    (hJ : BlockOK K w J ∨ J.card ≤ 1) (hJc : BlockOK K w Jᶜ ∨ Jᶜ.card ≤ 1)
    (hone : BlockOK K w J ∨ BlockOK K w Jᶜ) :
    ∀ y ∈ Ro, y = 1 := by
  intro y hy
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  obtain ⟨g, rfl⟩ := hsurj y hy
  have hsmall : ∀ I : Finset (Fin d), I.card ≤ 1 → ∀ x ∈ I, ∀ y ∈ I, x = y := fun I hI x hx y hy =>
    Finset.card_le_one.1 hI x hx y hy
  rcases hone with hok | hok
  · obtain ⟨hτ, -, hiso⟩ := ClO.iso_of_blockOK hK hw hker hinj (Or.inl rfl) hok hRodd hRi hRc hy
    refine ClO.eq_one_of_iso hK hw hodd hτ fun x z hxz => ?_
    by_cases hx : x ∈ J
    · exact (hiso x hx z (Ne.symm hxz)).1
    by_cases hz : z ∈ J
    · exact (hiso z hz x hxz).2
    rcases hJc with hok' | hJc1
    · exact (ClO.iso_of_blockOK hK hw hker hinj (Or.inr rfl) hok' hRodd hRi hRc hy).2.2 x
        (Finset.mem_compl.2 hx) z (Ne.symm hxz) |>.1
    · exact absurd (hsmall _ hJc1 x (Finset.mem_compl.2 hx) z (Finset.mem_compl.2 hz)) hxz
  · obtain ⟨hτ, -, hiso⟩ := ClO.iso_of_blockOK hK hw hker hinj (Or.inr rfl) hok hRodd hRi hRc hy
    refine ClO.eq_one_of_iso hK hw hodd hτ fun x z hxz => ?_
    by_cases hx : x ∈ Jᶜ
    · exact (hiso x hx z (Ne.symm hxz)).1
    by_cases hz : z ∈ Jᶜ
    · exact (hiso z hz x hxz).2
    rw [Finset.mem_compl, not_not] at hx hz
    rcases hJ with hok' | hJ1
    · exact (ClO.iso_of_blockOK hK hw hker hinj (Or.inl rfl) hok' hRodd hRi hRc hy).2.2 x hx z
        (Ne.symm hxz) |>.1
    · exact absurd (hsmall _ hJ1 x hx z hz) hxz

theorem ClO.eq_one_three_gen (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2) (hd : 0 < d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J I M₁ M₂ M₃ : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) =
      oκ _ (sgnPair (Ring.two_ne_zero hK) hw J) * y)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL hw)), y = oκ _ g)
    (hiso : ∀ g : similarityPairs (oQ (diagGL hw)), oκ _ g ∈ Ro →
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0)
    (hn₁ : ∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₁) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₁))⁻¹ ∈ Ro)
    (hn₂ : ∀ y ∈ Ro, oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₂) * y *
      (oκ _ (sgnPair (Ring.two_ne_zero hK) hw M₂))⁻¹ ∈ Ro)
    (h₁₂ : signMat K M₁ * signMat K M₂ = signMat K M₃)
    (hJM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → (J ∩ M).card ≤ 2 ∧ (J \ M).card ≤ 2)
    (hJcM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) →
      (∀ x ∈ Jᶜ, x ∈ I) ∨ ((Jᶜ ∩ M).card ≤ 2 ∧ (Jᶜ \ M).card ≤ 2)) :
    ∀ y ∈ Ro, y = 1 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Finite Ro := inferInstance
  have hsq : ∀ M : Finset (Fin d), oκ (oQ (diagGL hw)) (sgnPair h2 hw M) *
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) = 1 := by
    intro M
    rw [← map_mul, sgnPair_mul_self, map_one]
  have hC : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → ∀ y ∈ Ro,
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) * y = y * oκ (oQ (diagGL hw)) (sgnPair h2 hw M) →
      y = 1 := by
    intro M hM y hy hcomm
    have hodd := ClSp.odd_orderOf_of_mem hRodd hy
    obtain ⟨g, rfl⟩ := hsurj y hy
    have hDJ := commute_sign_of_odd h2 hw hd hker J hodd (hRi _ hy)
    have hDM := commute_sign_of_odd h2 hw hd hker M hodd hcomm.symm
    exact eq_one_of_blocks_three h3 h2 hw hodd (exists_block_of_commute h2 hDJ hDM
      (hiso g hy) (hJM M hM) (hJcM M hM))
  have hRb : Ro = ⊥ := eq_bot_of_four_group (hsq M₁) (hsq M₂) hn₁ hn₂
    (hC M₁ (Or.inl rfl)) (hC M₂ (Or.inr (Or.inl rfl))) (by
      rw [← map_mul, sgnPair_mul h2 hw M₁ M₂ h₁₂]
      exact hC M₃ (Or.inr (Or.inr rfl)))
  intro y hy
  rw [hRb] at hy
  exact mem_bot.1 hy

end CFSG.ComponentClassification.Foote5.OddLieCore
