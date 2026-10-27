module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOThreeTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOSplitCore

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self
  compInd commute_compInd_iff commute_signMat_iff eq_bot_of_four_group conj_mem_oddCoreIn)

variable {K : Type} [Field K] {d : ℕ}

theorem signGL_pair_mem_derived (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {i j : Fin d} (hij : i ≠ j) (hwij : w i = w j) :
    signGL K {i, j} ∈ matrixDerived (oQ (diagGL hw)) := by
  rw [matrixDerived_oQ h2 _ (diagGL_transpose hw)]
  exact oBlock_le hw Finset.univ
    (signGL_pair_mem_oBlock hw (Finset.mem_univ i) (Finset.mem_univ j) hij hwij)

theorem sgnPair_comm (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    (J M : Finset (Fin d)) :
    sgnPair h2 hw J * sgnPair h2 hw M = sgnPair h2 hw M * sgnPair h2 hw J := by
  apply Subtype.ext
  apply SemidirectProduct.ext
  · change signGL K J * glFieldAut (Fin d) K 1 (signGL K M) =
      signGL K M * glFieldAut (Fin d) K 1 (signGL K J)
    rw [map_one, MulAut.one_apply, MulAut.one_apply]
    exact Units.ext (signMat_mul_comm J M)
  · rfl

theorem sign_mem_inf (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (J : Finset (Fin d)) {M : Finset (Fin d)}
    (hM : signGL K M ∈ matrixDerived (oQ (diagGL hw))) :
    oκ _ (sgnPair h2 hw M) ∈ B ⊓ centralizer ({oκ _ (sgnPair h2 hw J)} : Set _) := by
  refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
  · rw [sgnPair, oκ_linPair_eq_conj _ hM]
    exact hB ⟨_, rfl⟩
  · rw [← map_mul, ← map_mul, sgnPair_comm]

theorem eq_one_of_odd_of_pow_eight {G : Type*} [Group G] {y : G} (hodd : Odd (orderOf y))
    (hy : y ^ 8 = 1) : y = 1 := by
  have hdvd : orderOf y ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.1 hk

theorem eq_one_of_blocks_three [Finite K] (h3 : Nat.card K = 3) (h2 : (2 : K) ≠ 0)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0) {g : similarityPairs (oQ (diagGL hw))}
    (hodd : Odd (orderOf (oκ _ g)))
    (hT : ∀ x, ∃ T : Finset (Fin d), x ∈ T ∧ (T.card = 1 ∨ T.card = 2) ∧
      ∀ y z, (y ∈ T ↔ z ∉ T) → (g.val.left : Matrix (Fin d) (Fin d) K) y z = 0) :
    oκ _ g = 1 := by
  have hτ : g.val.right = 1 := ringEquiv_eq_one_of_card_three h3 _
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_oQ h2 _ (diagGL_transpose hw) g.val).1 g.2
  rw [hτ, coe_diagGL] at hμ
  rw [show (diagonal w).map ⇑(1 : K ≃+* K) = diagonal w from by ext; rfl] at hμ
  set D := (g.val.left : Matrix (Fin d) (Fin d) K) with hD
  have hsim : Dᵀ * diagonal w * Dᵀᵀ = diagonal fun x => (μ : K) * w x := by
    rw [transpose_transpose, hμ, ← diagonal_smul]
    rfl
  have hD8 : Dᵀ ^ 8 = 1 := pow_eight_of_blocks h3 hw μ.ne_zero hsim fun x => by
    obtain ⟨T, hxT, hcard, hTD⟩ := hT x
    refine ⟨T, hxT, hcard, fun y z hyz => ?_⟩
    rw [transpose_apply]
    exact hTD z y ⟨fun hz hy => (hyz.1 hy) hz, fun hy => by
      by_contra hz
      exact hy (hyz.2 hz)⟩
  have hD8' : D ^ 8 = 1 := by
    rw [← transpose_transpose (D ^ 8), transpose_pow, hD8, transpose_one]
  obtain ⟨hl, hr⟩ := pow_left_of_right_eq_one hτ 8
  refine eq_one_of_odd_of_pow_eight hodd ?_
  rw [← map_pow]
  have e : g ^ 8 = 1 := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rw [hl]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← hD, hD8']
      rfl
    · rw [hr]
      rfl
  rw [e, map_one]

theorem split_two_oddCoreIn_eq_bot_three [Finite K] (h3 : Nat.card K = 3)
    (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJ2 : J.card = 2) (hJd : 2 * J.card ≠ d) (hJc : BlockOK K w Jᶜ) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨R, hR, hRJ, rfl⟩ := split_two_oddCoreIn hK hw hker hsurj hinj hB hJd hJc hy
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

theorem exists_block_of_commute (h2 : (2 : K) ≠ 0) {D : Matrix (Fin d) (Fin d) K}
    {J M I : Finset (Fin d)} (hDJ : signMat K J * D = D * signMat K J)
    (hDM : signMat K M * D = D * signMat K M)
    (hiso : ∀ x ∈ I, ∀ y, y ≠ x → D x y = 0 ∧ D y x = 0)
    (hJM : (J ∩ M).card ≤ 2 ∧ (J \ M).card ≤ 2)
    (hJcM : (∀ x ∈ Jᶜ, x ∈ I) ∨ ((Jᶜ ∩ M).card ≤ 2 ∧ (Jᶜ \ M).card ≤ 2)) (x : Fin d) :
    ∃ T : Finset (Fin d), x ∈ T ∧ (T.card = 1 ∨ T.card = 2) ∧
      ∀ y z, (y ∈ T ↔ z ∉ T) → D y z = 0 := by
  have hJb := (commute_compInd_iff J D).1 ((commute_signMat_iff h2 J D).1 hDJ)
  have hMb := (commute_compInd_iff M D).1 ((commute_signMat_iff h2 M D).1 hDM)
  have hcard : ∀ T : Finset (Fin d), x ∈ T → T.card ≤ 2 → T.card = 1 ∨ T.card = 2 := by
    intro T hxT hT
    have := Finset.card_pos.2 ⟨x, hxT⟩
    omega
  have hpiece : ∀ (A : Finset (Fin d)), (A = J ∨ A = Jᶜ) → ∀ T : Finset (Fin d),
      (T = A ∩ M ∨ T = A \ M) → x ∈ T → T.card ≤ 2 →
      ∃ T : Finset (Fin d), x ∈ T ∧ (T.card = 1 ∨ T.card = 2) ∧
        ∀ y z, (y ∈ T ↔ z ∉ T) → D y z = 0 := by
    intro A hA T hT hxT hTc
    refine ⟨T, hxT, hcard T hxT hTc, fun y z hyz => ?_⟩
    by_cases hJyz : (y ∈ J ↔ z ∈ J)
    · by_cases hMyz : (y ∈ M ↔ z ∈ M)
      · exfalso
        have hAyz : (y ∈ A ↔ z ∈ A) := by
          rcases hA with rfl | rfl
          · exact hJyz
          · simp only [Finset.mem_compl]
            exact not_congr hJyz
        have hTyz : (y ∈ T ↔ z ∈ T) := by
          rcases hT with rfl | rfl
          · simp only [Finset.mem_inter]
            exact and_congr hAyz hMyz
          · simp only [Finset.mem_sdiff]
            exact and_congr hAyz (not_congr hMyz)
        by_cases hy : y ∈ T
        · exact (hyz.1 hy) (hTyz.1 hy)
        · exact hy (hyz.2 fun hz => hy (hTyz.2 hz))
      · exact hMb y z (by tauto)
    · exact hJb y z (by tauto)
  by_cases hxI : x ∈ I
  · refine ⟨{x}, Finset.mem_singleton_self x, Or.inl (Finset.card_singleton x),
      fun y z hyz => ?_⟩
    by_cases hy : y = x
    · subst hy
      have hz : z ≠ y := fun h => (hyz.1 (Finset.mem_singleton_self y)) (h ▸
        Finset.mem_singleton_self y)
      exact (hiso y hxI z hz).1
    · have hz : z = x := by
        by_contra hz
        exact hy (Finset.mem_singleton.1 (hyz.2 fun h => hz (Finset.mem_singleton.1 h)))
      subst hz
      exact (hiso z hxI y hy).2
  by_cases hxJ : x ∈ J
  · by_cases hxM : x ∈ M
    · exact hpiece J (Or.inl rfl) _ (Or.inl rfl) (Finset.mem_inter.2 ⟨hxJ, hxM⟩) hJM.1
    · exact hpiece J (Or.inl rfl) _ (Or.inr rfl) (Finset.mem_sdiff.2 ⟨hxJ, hxM⟩) hJM.2
  · have hxJc : x ∈ Jᶜ := Finset.mem_compl.2 hxJ
    rcases hJcM with hall | hJc
    · exact absurd (hall x hxJc) hxI
    by_cases hxM : x ∈ M
    · exact hpiece Jᶜ (Or.inr rfl) _ (Or.inl rfl) (Finset.mem_inter.2 ⟨hxJc, hxM⟩) hJc.1
    · exact hpiece Jᶜ (Or.inr rfl) _ (Or.inr rfl) (Finset.mem_sdiff.2 ⟨hxJc, hxM⟩) hJc.2

theorem oddCoreIn_eq_bot_three_of_sets [Finite K] (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J I M₁ M₂ M₃ : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJd : 2 * J.card ≠ d)
    (hiso : ∀ g : similarityPairs (oQ (diagGL hw)),
      oκ _ g ∈ oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) →
      ∀ x ∈ I, ∀ y, y ≠ x → (g.val.left : Matrix (Fin d) (Fin d) K) x y = 0 ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) y x = 0)
    (hM₁ : signGL K M₁ ∈ matrixDerived (oQ (diagGL hw)))
    (hM₂ : signGL K M₂ ∈ matrixDerived (oQ (diagGL hw)))
    (h₁₂ : signMat K M₁ * signMat K M₂ = signMat K M₃)
    (hMd : ∀ M, (M = M₁ ∨ M = M₂ ∨ M = M₃) → 2 * M.card ≠ d)
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
    have hDJ := commute_sign_of_commute h2 hw hker hJd (commute_of_mem_oddCoreIn hy)
    have hDM := commute_sign_of_commute h2 hw hker (hMd M hM) hcomm.symm
    exact eq_one_of_blocks_three h3 h2 hw hodd (exists_block_of_commute h2 hDJ hDM
      (hiso g hy) (hJM M hM) (hJcM M hM))
  refine eq_bot_of_four_group (hsq M₁) (hsq M₂)
    (fun x hx => conj_mem_oddCoreIn hx (sign_mem_inf h2 hw hB J hM₁))
    (fun x hx => conj_mem_oddCoreIn hx (sign_mem_inf h2 hw hB J hM₂))
    (hC M₁ (Or.inl rfl)) (hC M₂ (Or.inr (Or.inl rfl))) ?_
  rw [← map_mul, sgnPair_mul h2 hw M₁ M₂ h₁₂]
  exact hC M₃ (Or.inr (Or.inr rfl))

theorem signMat_pair_mul {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    signMat K {a, b} * signMat K {a, c} = signMat K {b, c} := by
  rw [signMat, signMat, signMat, diagonal_mul_diagonal]
  congr 1
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hka : k = a
  · subst hka
    simp [hab, hac]
  · by_cases hkb : k = b
    · subst hkb
      simp [hka, hbc]
    · by_cases hkc : k = c
      · subst hkc
        simp [hka, hkb]
      · simp [hka, hkb, hkc]

theorem signMat_mul_of_disjoint {M N : Finset (Fin d)} (h : Disjoint M N) :
    signMat K M * signMat K N = signMat K (M ∪ N) := by
  rw [signMat, signMat, signMat, diagonal_mul_diagonal]
  congr 1
  ext k
  simp only [Finset.mem_union]
  by_cases hkM : k ∈ M
  · have hkN : k ∉ N := Finset.disjoint_left.1 h hkM
    simp [hkM, hkN]
  · by_cases hkN : k ∈ N <;> simp [hkM, hkN]

theorem card_sdiff_pair {J : Finset (Fin d)} {a b : Fin d} (ha : a ∈ J) (hb : b ∈ J)
    (hab : a ≠ b) : (J \ {a, b}).card = J.card - 2 := by
  rw [Finset.card_sdiff_of_subset (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb), Finset.card_pair hab]

theorem card_compl_add (J : Finset (Fin d)) : J.card + Jᶜ.card = d := by
  rw [Finset.card_compl, Fintype.card_fin]
  have := J.card_le_univ
  rw [Fintype.card_fin] at this
  omega

variable [Finite K]

theorem small_split_oddCoreIn_eq_bot_three (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJd : 2 * J.card ≠ d) (hJ4 : J.card ≤ 4) (hJc : BlockOK K w Jᶜ)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c) :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨hI3, hIexc, I₀, hI₀, hI₀3, hI₀w, hI₀c⟩ := hJc
  have hJc5 : 5 ≤ Jᶜ.card := by
    by_contra h
    exact hIexc ⟨h3, by omega⟩
  have hJ3 : 3 ≤ J.card := by
    have : ({a, b, c} : Finset (Fin d)) ⊆ J := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
    omega
  have hd := card_compl_add J
  have hcard : ∀ {x y : Fin d}, x ∈ J → y ∈ J → x ≠ y →
      (J ∩ {x, y}).card ≤ 2 ∧ (J \ {x, y}).card ≤ 2 := by
    intro x y hx hy hxy
    refine ⟨?_, by rw [card_sdiff_pair hx hy hxy]; omega⟩
    exact (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_le_two)
  refine oddCoreIn_eq_bot_three_of_sets h3 hK hw hker hsurj hB (I := Jᶜ) (M₁ := {a, b})
    (M₂ := {a, c}) (M₃ := {b, c}) hJd
    (fun g hg => (split_core hK hw hker hinj hB hJd (Or.inr rfl) hI3 hIexc hI₀ hI₀3 hI₀w hI₀c
      hg).2.2)
    (signGL_pair_mem_derived h2 hw hab hwab) (signGL_pair_mem_derived h2 hw hac hwac)
    (signMat_pair_mul hab hac hbc) ?_ ?_ (fun _ _ => Or.inl fun x hx => hx)
  · rintro M (rfl | rfl | rfl) <;> rw [Finset.card_pair (by assumption)] <;> omega
  · rintro M (rfl | rfl | rfl)
    · exact hcard ha hb hab
    · exact hcard ha hc hac
    · exact hcard hb hc hbc

theorem seven_split_oddCoreIn_eq_bot_three (h3 : Nat.card K = 3) (hK : ringChar K ≠ 2)
    {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {B : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {J : Finset (Fin d)} (hker : OKer (oQ (diagGL hw)))
    (hsurj : OSurjCore B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)))
    (hB : (MulAut.conj : StatedProj (matrixDerived (oQ (diagGL hw))) →*
      MulAut (StatedProj (matrixDerived (oQ (diagGL hw))))).range ≤ B)
    (hJd : 2 * J.card ≠ d) (hd8 : d ≠ 8) (hJ4 : J.card ≤ 4)
    (hJc4 : Jᶜ.card ≤ 4)
    {a b c : Fin d} (ha : a ∈ J) (hb : b ∈ J) (hc : c ∈ J) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hwab : w a = w b) (hwac : w a = w c)
    {a' b' c' : Fin d} (ha' : a' ∈ Jᶜ) (hb' : b' ∈ Jᶜ) (hc' : c' ∈ Jᶜ) (hab' : a' ≠ b')
    (hac' : a' ≠ c') (hbc' : b' ≠ c') (hwab' : w a' = w b') (hwac' : w a' = w c') :
    oddCoreIn B (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J)) = ⊥ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hdisj : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ →
      Disjoint ({x, y} : Finset (Fin d)) {x', y'} := by
    intro x y x' y' hx hy hx' hy'
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    have hzJ : z ∈ J := by rcases hz with rfl | rfl <;> assumption
    have hzJc : z ∈ Jᶜ := by rcases hz' with rfl | rfl <;> assumption
    exact Finset.mem_compl.1 hzJc hzJ
  have hmem : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ → x ≠ y → x' ≠ y' →
      w x = w y → w x' = w y' →
      signGL K ({x, y} ∪ {x', y'}) ∈ matrixDerived (oQ (diagGL hw)) := by
    intro x y x' y' hx hy hx' hy' hxy hxy' hw1 hw2
    have e : signGL K {x, y} * signGL K {x', y'} = signGL K ({x, y} ∪ {x', y'}) :=
      Units.ext (signMat_mul_of_disjoint (hdisj hx hy hx' hy'))
    rw [← e]
    exact mul_mem (signGL_pair_mem_derived h2 hw hxy hw1) (signGL_pair_mem_derived h2 hw hxy' hw2)
  have hprod : signMat K ({a, b} ∪ {a', b'}) * signMat K ({a, c} ∪ {a', c'}) =
      signMat K ({b, c} ∪ {b', c'}) := by
    rw [← signMat_mul_of_disjoint (hdisj ha hb ha' hb'),
      ← signMat_mul_of_disjoint (hdisj ha hc ha' hc'),
      ← signMat_mul_of_disjoint (hdisj hb hc hb' hc'), ← signMat_pair_mul hab hac hbc,
      ← signMat_pair_mul hab' hac' hbc']
    simp only [Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, signMat_mul_comm {a', b'} {a, c}]
  have hpiece : ∀ {x y x' y' : Fin d}, x ∈ J → y ∈ J → x' ∈ Jᶜ → y' ∈ Jᶜ → x ≠ y →
      x' ≠ y' → (J ∩ ({x, y} ∪ {x', y'})).card ≤ 2 ∧ (J \ ({x, y} ∪ {x', y'})).card ≤ 2 ∧
        (Jᶜ ∩ ({x, y} ∪ {x', y'})).card ≤ 2 ∧ (Jᶜ \ ({x, y} ∪ {x', y'})).card ≤ 2 := by
    intro x y x' y' hx hy hx' hy' hxy hxy'
    have hJM : J ∩ ({x, y} ∪ {x', y'}) ⊆ {x, y} := by
      intro z hz
      rw [Finset.mem_inter, Finset.mem_union] at hz
      rcases hz.2 with h | h
      · exact h
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact Finset.mem_compl.1 hx' hz.1
        · exact Finset.mem_compl.1 hy' hz.1
    have hJcM : Jᶜ ∩ ({x, y} ∪ {x', y'}) ⊆ {x', y'} := by
      intro z hz
      rw [Finset.mem_inter, Finset.mem_union] at hz
      rcases hz.2 with h | h
      · exfalso
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact Finset.mem_compl.1 hz.1 hx
        · exact Finset.mem_compl.1 hz.1 hy
      · exact h
    have hJs : J \ ({x, y} ∪ {x', y'}) ⊆ J \ {x, y} :=
      Finset.sdiff_subset_sdiff (le_refl _) Finset.subset_union_left
    have hJcs : Jᶜ \ ({x, y} ∪ {x', y'}) ⊆ Jᶜ \ {x', y'} :=
      Finset.sdiff_subset_sdiff (le_refl _) Finset.subset_union_right
    refine ⟨(Finset.card_le_card hJM).trans Finset.card_le_two,
      (Finset.card_le_card hJs).trans ?_, (Finset.card_le_card hJcM).trans Finset.card_le_two,
      (Finset.card_le_card hJcs).trans ?_⟩
    · have hJ3 : 3 ≤ J.card := by
        have : ({a, b, c} : Finset (Fin d)) ⊆ J := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card this
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
        omega
      rw [card_sdiff_pair hx hy hxy]
      omega
    · rw [card_sdiff_pair hx' hy' hxy']
      omega
  refine oddCoreIn_eq_bot_three_of_sets h3 hK hw hker hsurj hB (I := ∅)
    (M₁ := {a, b} ∪ {a', b'}) (M₂ := {a, c} ∪ {a', c'}) (M₃ := {b, c} ∪ {b', c'}) hJd
    (fun _ _ x hx => absurd hx (Finset.notMem_empty x))
    (hmem ha hb ha' hb' hab hab' hwab hwab') (hmem ha hc ha' hc' hac hac' hwac hwac') hprod
    ?_ ?_ ?_
  · rintro M (rfl | rfl | rfl)
    · rw [Finset.card_union_of_disjoint (hdisj ha hb ha' hb'), Finset.card_pair hab,
        Finset.card_pair hab']
      omega
    · rw [Finset.card_union_of_disjoint (hdisj ha hc ha' hc'), Finset.card_pair hac,
        Finset.card_pair hac']
      omega
    · rw [Finset.card_union_of_disjoint (hdisj hb hc hb' hc'), Finset.card_pair hbc,
        Finset.card_pair hbc']
      omega
  · rintro M (rfl | rfl | rfl)
    · exact ⟨(hpiece ha hb ha' hb' hab hab').1, (hpiece ha hb ha' hb' hab hab').2.1⟩
    · exact ⟨(hpiece ha hc ha' hc' hac hac').1, (hpiece ha hc ha' hc' hac hac').2.1⟩
    · exact ⟨(hpiece hb hc hb' hc' hbc hbc').1, (hpiece hb hc hb' hc' hbc hbc').2.1⟩
  · rintro M (rfl | rfl | rfl)
    · exact Or.inr (hpiece ha hb ha' hb' hab hab').2.2
    · exact Or.inr (hpiece ha hc ha' hc' hac hac').2.2
    · exact Or.inr (hpiece hb hc hb' hc' hbc hbc').2.2

end CFSG.ComponentClassification.Burgoyne.O
