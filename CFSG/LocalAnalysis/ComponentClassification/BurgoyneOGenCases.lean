module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOGenThree2
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCases
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ} [Finite K]

theorem split_oddCoreIn_eq_bot_of_nf_gen (hK : ringChar K ≠ 2) (hd7 : 7 ≤ d)
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
  have hcc : Jᶜᶜ = J := compl_compl J
  by_cases hsmall : Nat.card K = 3 ∧ ((3 ≤ J.card ∧ J.card ≤ 4) ∨ (3 ≤ Jᶜ.card ∧ Jᶜ.card ≤ 4))
  · obtain ⟨h3, ⟨hJ3, hJ4⟩ | ⟨hJc3, hJc4⟩⟩ := hsmall
    · by_cases hJc4 : Jᶜ.card ≤ 4
      ·
        have hJc3 : 3 ≤ Jᶜ.card := by omega
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        obtain ⟨x', hx', y', hy', z', hz', hxy', hxz', hyz', hwxy', hwxz'⟩ :=
          (hNFc hJc3).exists_triple
        exact seven_split_oddCoreIn_eq_bot_three_gen h3 hK hw hker hsurj hB hJ4 hJc4
          hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      · obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        exact small_split_oddCoreIn_eq_bot_three_gen h3 hK hw hker hsurj hinj hB hJ4
          ((hNFc (by omega)).blockOK (by omega) fun h => hJc4 h.2) hx hy hz hxy hxz hyz hwxy hwxz
    · by_cases hJ4 : J.card ≤ 4
      · have hJ3 : 3 ≤ J.card := by omega
        obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNF hJ3).exists_triple
        obtain ⟨x', hx', y', hy', z', hz', hxy', hxz', hyz', hwxy', hwxz'⟩ :=
          (hNFc hJc3).exists_triple
        exact seven_split_oddCoreIn_eq_bot_three_gen h3 hK hw hker hsurj hB hJ4 hJc4
          hx hy hz hxy hxz hyz hwxy hwxz hx' hy' hz' hxy' hxz' hyz' hwxy' hwxz'
      have hJ5 : 5 ≤ J.card := by omega
      obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hwxy, hwxz⟩ := (hNFc hJc3).exists_triple
      rw [← oκ_sgnPair_compl h2 hw J]
      refine small_split_oddCoreIn_eq_bot_three_gen h3 hK hw hker
        (hsurj.of_eq (oκ_sgnPair_compl h2 hw J).symm) hinj hB hJc4 ?_
        hx hy hz hxy hxz hyz hwxy hwxz
      rw [hcc]
      exact (hNF (by omega)).blockOK (by omega) fun h => by omega
  ·
    have hok : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockOK K w I := by
      rintro I (rfl | rfl) hI3
      · exact (hNF hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inl ⟨hI3, h.2⟩⟩
      · exact (hNFc hI3).blockOK hI3 fun h => hsmall ⟨h.1, Or.inr ⟨hI3, h.2⟩⟩
    refine split_oddCoreIn_eq_bot_gen hK hw hker hsurj hinj hB ?_ ?_ ?_
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (by omega)
    · by_cases hJc3 : 3 ≤ Jᶜ.card
      · exact Or.inl (hok Jᶜ (Or.inr rfl) hJc3)
      · exact Or.inr (by omega)
    · by_cases hJ3 : 3 ≤ J.card
      · exact Or.inl (hok J (Or.inl rfl) hJ3)
      · exact Or.inr (hok Jᶜ (Or.inr rfl) (by omega))


omit [Finite K] in
theorem sliceW_of_nf_gen {b : ℕ} (hab : 2 + b = d) (hb : 5 ≤ b) {R : Matrix (Fin d) (Fin d) K}
    {c : Fin 2 ⊕ Fin b → Fin d → K} {β γ : K} (hβ0 : β ≠ 0)
    (hβ1 : β = 1 ∨ ¬ IsSquare β) (hγ1 : γ = -β ∨ ¬ IsSquare (γ / -β))
    (h0 : c (.inl 0) ⬝ᵥ R *ᵥ c (.inl 0) = 1) (h1 : c (.inl 1) ⬝ᵥ R *ᵥ c (.inl 1) = β)
    (h2 : c (.inr ⟨0, by omega⟩) ⬝ᵥ R *ᵥ c (.inr ⟨0, by omega⟩) = -1)
    (hr : ∀ j : Fin b, 1 ≤ (j : ℕ) → (j : ℕ) + 1 < b → c (.inr j) ⬝ᵥ R *ᵥ c (.inr j) = -β)
    (hL : c (.inr ⟨b - 1, by omega⟩) ⬝ᵥ R *ᵥ c (.inr ⟨b - 1, by omega⟩) = γ) :
    OSliceW (by omega : 4 ≤ d) (famW R hab c) 1 β ∧
      ∃ I₀ ⊆ (jSet : Finset (Fin d))ᶜ, 3 ≤ I₀.card ∧
        (∀ i ∈ I₀, ∀ j ∈ I₀, famW R hab c i = famW R hab c j) ∧
        ∀ x ∈ (jSet : Finset (Fin d))ᶜ, x ∉ I₀ → ∀ y ∈ I₀,
          ¬ IsSquare (famW R hab c x / famW R hab c y) := by
  classical
  have hval : ∀ l : Fin d, famW R hab c l = if (l : ℕ) = 0 then 1 else if (l : ℕ) = 1 then β
      else if (l : ℕ) = 2 then -1 else if (l : ℕ) = d - 1 then γ else -β := by
    intro l
    obtain ⟨x, rfl⟩ := (sumFin hab).surjective l
    rw [famW_sumFin]
    rcases x with i | j
    · rw [sumFin_inl]
      fin_cases i
      · simpa using h0
      · simpa using h1
    · rw [sumFin_inr]
      simp only
      by_cases hj0 : (j : ℕ) = 0
      · have : j = ⟨0, by omega⟩ := Fin.ext hj0
        rw [this, h2]
        simp
      · by_cases hjL : (j : ℕ) = b - 1
        · have : j = ⟨b - 1, by omega⟩ := Fin.ext hjL
          rw [this, hL]
          have e1 : d - 1 ≠ 0 := by omega
          have e2 : d - 1 ≠ 1 := by omega
          have e3 : d - 1 ≠ 2 := by omega
          have e4 : 2 + (b - 1) = d - 1 := by omega
          simp only [e4, e1, e2, e3, ↓reduceIte]
        · rw [hr j (by omega) (by omega)]
          have e1 : 2 + (j : ℕ) ≠ 0 := by omega
          have e2 : 2 + (j : ℕ) ≠ 1 := by omega
          have e3 : 2 + (j : ℕ) ≠ 2 := by omega
          have e4 : 2 + (j : ℕ) ≠ d - 1 := by omega
          simp only [e1, e2, e3, e4, ↓reduceIte]
  have hmemc : ∀ l : Fin d, l ∈ (jSet : Finset (Fin d))ᶜ ↔ 2 ≤ (l : ℕ) := by
    intro l
    rw [Finset.mem_compl, mem_jSet]
    omega
  refine ⟨⟨one_ne_zero, hβ0, fun i => ?_⟩, ((jSet : Finset (Fin d))ᶜ.filter
    fun l => famW R hab c l = -β), Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [hval]
    have hd1 : ∀ k : ℕ, k < 4 → k ≠ d - 1 := fun k hk => by omega
    fin_cases i <;> simp [qW, hd1]
  · have hsub : ({⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩} : Finset (Fin d)) ⊆
        (jSet : Finset (Fin d))ᶜ.filter fun l => famW R hab c l = -β := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rw [Finset.mem_filter, hmemc, hval]
      rcases hl with rfl | rfl | rfl <;> simp <;> omega
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_pair (by simp [Fin.ext_iff])]
  · intro i hi j hj
    rw [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hj).2]
  · intro x hx hx₀ y hy
    rw [(Finset.mem_filter.1 hy).2]
    have hxβ : famW R hab c x ≠ -β := fun h => hx₀ (Finset.mem_filter.2 ⟨hx, h⟩)
    have hx2 := (hmemc x).1 hx
    rw [hval] at hxβ ⊢
    have e0 : (x : ℕ) ≠ 0 := by omega
    have e1 : (x : ℕ) ≠ 1 := by omega
    simp only [e0, e1, ↓reduceIte] at hxβ ⊢
    by_cases hx2' : (x : ℕ) = 2
    · simp only [hx2', ↓reduceIte] at hxβ ⊢
      have hd2 : (2 : ℕ) ≠ d - 1 := by omega
      rcases hβ1 with h | h
      · exact absurd (by rw [h]) hxβ
      · rw [neg_div_neg_eq, one_div, isSquare_inv]
        exact h
    · simp only [hx2', ↓reduceIte] at hxβ ⊢
      by_cases hxL : (x : ℕ) = d - 1
      · simp only [hxL, ↓reduceIte] at hxβ ⊢
        rcases hγ1 with h | h
        · exact absurd h hxβ
        · exact h
      · simp only [hxL, ↓reduceIte] at hxβ
        exact absurd rfl hxβ

theorem slice_dichotomy_gen (hK : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K) (hd : 5 ≤ d)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {α a : K} (hW : OSliceW (by omega : 4 ≤ d) w α a)
    {I₀ : Finset (Fin d)} (hI₀ : I₀ ⊆ (jSet : Finset (Fin d))ᶜ) (hI₀3 : 3 ≤ I₀.card)
    (hI₀w : ∀ i ∈ I₀, ∀ j ∈ I₀, w i = w j)
    (hns : ∀ x ∈ (jSet : Finset (Fin d))ᶜ, x ∉ I₀ → ∀ y ∈ I₀, ¬ IsSquare (w x / w y))
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B) :
    ∀ Y : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))), Y ≠ ⊥ →
      Y ≤ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) →
      PropAConclusionIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw jSet)) Y := by
  have hJc3 : 3 ≤ (jSet : Finset (Fin d))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, card_jSet (by omega)]
    omega
  intro Y hY hYO
  refine slice_two_propAConclusionIn hK hK5 hd hw hW hker hinj hB (fun y hy => ?_) hY hYO
  obtain ⟨g, rfl⟩ := hsurj y hy
  obtain ⟨hτ, -, hiso⟩ := iso_of_mix hK hK5 hw hker hinj hB (Or.inr rfl) hJc3 hI₀ hI₀3 hI₀w hns hy
  obtain ⟨R, hR, hRJ, hgR⟩ := exists_oIsoBlock_of_iso hK hw hker
    (Finset.card_pos.1 (by omega)) hy hτ hiso
  exact ⟨R, hR, hRJ, hgR⟩

end CFSG.ComponentClassification.Burgoyne.O
