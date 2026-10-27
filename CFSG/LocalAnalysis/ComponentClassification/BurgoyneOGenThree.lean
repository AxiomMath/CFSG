module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenIso
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (compInd diagGL coe_diagGL signMat
  commute_signMat_iff commute_compInd_iff eq_bot_of_four_group conj_mem_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem iso_of_blockOK (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (hker : OKer (oQ (diagGL hw)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    {J I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hIok : BlockOK K w I)
    {g : similarityPairs (oQ (diagGL hw))}
    (hy : oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))) :
    g.val.right = 1 ∧
      signMat K J * (g.val.left : Matrix (Fin d) (Fin d) K) =
        (g.val.left : Matrix (Fin d) (Fin d) K) * signMat K J ∧
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩ := hIok
  obtain ⟨hτ, hDS, hiso₀, -⟩ := split_core_gen hK hw hker hinj hB hI hI3 hIexc hI₀ hI₀3 hI₀w hy
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

theorem split_oddCoreIn_eq_bot_gen (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJ : BlockOK K w J ∨ J.card ≤ 1) (hJc : BlockOK K w Jᶜ ∨ Jᶜ.card ≤ 1)
    (hone : BlockOK K w J ∨ BlockOK K w Jᶜ) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  obtain ⟨g, rfl⟩ := hsurj y hy
  have hsmall : ∀ I : Finset (Fin d), I.card ≤ 1 → ∀ x ∈ I, ∀ y ∈ I, x = y := fun I hI x hx y hy =>
    Finset.card_le_one.1 hI x hx y hy
  rcases hone with hok | hok
  · obtain ⟨hτ, -, hiso⟩ := iso_of_blockOK hK hw hker hinj hB (Or.inl rfl) hok hy
    refine eq_one_of_iso hK hw hy hτ fun x z hxz => ?_
    by_cases hx : x ∈ J
    · exact (hiso x hx z (Ne.symm hxz)).1
    by_cases hz : z ∈ J
    · exact (hiso z hz x hxz).2
    rcases hJc with hok' | hJc1
    · exact (iso_of_blockOK hK hw hker hinj hB (Or.inr rfl) hok' hy).2.2 x
        (Finset.mem_compl.2 hx) z (Ne.symm hxz) |>.1
    · exact absurd (hsmall _ hJc1 x (Finset.mem_compl.2 hx) z (Finset.mem_compl.2 hz)) hxz
  · obtain ⟨hτ, -, hiso⟩ := iso_of_blockOK hK hw hker hinj hB (Or.inr rfl) hok hy
    refine eq_one_of_iso hK hw hy hτ fun x z hxz => ?_
    by_cases hx : x ∈ Jᶜ
    · exact (hiso x hx z (Ne.symm hxz)).1
    by_cases hz : z ∈ Jᶜ
    · exact (hiso z hz x hxz).2
    rw [Finset.mem_compl, not_not] at hx hz
    rcases hJ with hok' | hJ1
    · exact (iso_of_blockOK hK hw hker hinj hB (Or.inl rfl) hok' hy).2.2 x hx z
        (Ne.symm hxz) |>.1
    · exact absurd (hsmall _ hJ1 x hx z hz) hxz

theorem split_two_oddCoreIn_eq_bot_three_gen (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJ2 : J.card = 2) (hJc : BlockOK K w Jᶜ) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨g, rfl⟩ := hsurj y hy
  obtain ⟨hτ, -, hiso⟩ := iso_of_blockOK hK hw hker hinj hB (Or.inr rfl) hJc hy
  have hJcne : Jᶜ.Nonempty := Finset.card_pos.1 (by have := hJc.1; omega)
  obtain ⟨R, hR, hRJ, hgR⟩ := exists_oIsoBlock_of_iso hK hw hker hJcne hy hτ hiso
  rw [hgR] at hodd ⊢
  have hRe := ((mem_oIsoBlock_iff hw).1 hRJ).2
  refine eq_one_of_blocks_three h3 h2 hw hodd fun x => ?_
  rw [linPair_left]
  by_cases hx : x ∈ J
  · refine ⟨J, hx, Or.inr hJ2, fun y z hyz => ?_⟩
    have hyz' : y ≠ z := fun h => by
      subst h
      exact (hyz.1 (hyz.2 (by tauto))) (hyz.2 (by tauto))
    by_cases hy : y ∈ J
    · rw [hRe y z (Or.inr (hyz.1 hy))]
      simp only [hyz', ↓reduceIte]
    · rw [hRe y z (Or.inl hy)]
      simp only [hyz', ↓reduceIte]
  · refine ⟨{x}, Finset.mem_singleton_self x, Or.inl (Finset.card_singleton x),
      fun y z hyz => ?_⟩
    by_cases hy : y = x
    · subst hy
      have hz : z ≠ y := fun h => (hyz.1 (Finset.mem_singleton_self y)) (h ▸
        Finset.mem_singleton_self y)
      rw [hRe y z (Or.inl hx)]
      simp only [Ne.symm hz, ↓reduceIte]
    · have hz : z = x := by
        by_contra hz
        exact hy (Finset.mem_singleton.1 (hyz.2 fun h => hz (Finset.mem_singleton.1 h)))
      subst hz
      rw [hRe y z (Or.inr hx)]
      simp only [hy, ↓reduceIte]

theorem oddCoreIn_eq_bot_three_gen (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2) (hd : 0 < d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J I M₁ M₂ M₃ : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hiso : ∀ g : similarityPairs (oQ (diagGL hw)),
      oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) →
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0)
    (hM₁ : signGL K M₁ ∈ matrixDerived (oQ (diagGL hw)))
    (hM₂ : signGL K M₂ ∈ matrixDerived (oQ (diagGL hw)))
    (h₁₂ : signMat K M₁ * signMat K M₂ = signMat K M₃)
    (hJM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → (J ∩ M).card ≤ 2 ∧ (J \ M).card ≤ 2)
    (hJcM : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) →
      (∀ x ∈ Jᶜ, x ∈ I) ∨ ((Jᶜ ∩ M).card ≤ 2 ∧ (Jᶜ \ M).card ≤ 2)) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set t := oκ (oQ (diagGL hw)) (sgnPair h2 hw J) with ht
  set O := oddCoreIn B t with hO
  have : Finite O := inferInstance
  have hM₃ : signGL K M₃ ∈ matrixDerived (oQ (diagGL hw)) := by
    have : signGL K M₁ * signGL K M₂ = signGL K M₃ := Units.ext h₁₂
    rw [← this]
    exact mul_mem hM₁ hM₂
  have hsq : ∀ M : Finset (Fin d), oκ (oQ (diagGL hw)) (sgnPair h2 hw M) *
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) = 1 := by
    intro M
    rw [← map_mul, sgnPair_mul_self, map_one]
  have hC : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → ∀ y ∈ O,
      oκ (oQ (diagGL hw)) (sgnPair h2 hw M) * y = y * oκ (oQ (diagGL hw)) (sgnPair h2 hw M) →
      y = 1 := by
    intro M hM y hy hcomm
    have hodd := odd_orderOf_of_mem_oddCoreIn hy
    obtain ⟨g, rfl⟩ := hsurj y hy
    have hDJ := commute_sign_of_odd h2 hw hd hker J hodd (commute_of_mem_oddCoreIn hy)
    have hDM := commute_sign_of_odd h2 hw hd hker M hodd hcomm.symm
    exact eq_one_of_blocks_three h3 h2 hw hodd (exists_block_of_commute h2 hDJ hDM
      (hiso g hy) (hJM M hM) (hJcM M hM))
  refine eq_bot_of_four_group (hsq M₁) (hsq M₂)
    (fun x hx => conj_mem_oddCoreIn hx (sign_mem_inf h2 hw hB J hM₁))
    (fun x hx => conj_mem_oddCoreIn hx (sign_mem_inf h2 hw hB J hM₂))
    (hC M₁ (Or.inl rfl)) (hC M₂ (Or.inr (Or.inl rfl))) ?_
  rw [← map_mul, sgnPair_mul h2 hw M₁ M₂ h₁₂]
  exact hC M₃ (Or.inr (Or.inr rfl))

end CFSG.ComponentClassification.Burgoyne.O
