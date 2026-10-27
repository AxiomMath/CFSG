module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOIdent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOType

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (blockP blockP_cases oBlock_le_matrixDerived
  commute_of_mem_oIsoBlock eq_or_eq_compl_of_sign_eq_mul)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat signMat_mul_self)

variable {K : Type} [Field K]

theorem symmDiff_pair_pair {d : ℕ} {a b c : Fin d} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    symmDiff ({a, b} : Finset (Fin d)) {a, c} = {b, c} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases h1 with rfl | rfl
      · exact absurd (Or.inl rfl) h2
      · exact Or.inl rfl
    · rcases h1 with rfl | rfl
      · exact absurd (Or.inl rfl) h2
      · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inr rfl, fun h => h.elim (fun h' => hab h'.symm) (fun h' => hbc h')⟩
    · exact Or.inr ⟨Or.inr rfl, fun h => h.elim (fun h' => hac h'.symm) (fun h' => hbc h'.symm)⟩

theorem compl_nonempty_of_card_le {d : ℕ} {T : Finset (Fin d)} (hT : T.card ≤ 4) (hd : 5 ≤ d) :
    Tᶜ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have := Finset.card_compl T
  rw [h, Finset.card_empty, Fintype.card_fin] at this
  omega

theorem e8Sets {d : ℕ} (hd : 5 ≤ d) {i j k l : Fin d} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∀ T ∈ ({{i, j}, {i, k}, {i, l}, symmDiff {i, j} {i, k}, symmDiff {i, j} {i, l},
      symmDiff {i, k} {i, l}, symmDiff (symmDiff {i, j} {i, k}) {i, l}} :
        Finset (Finset (Fin d))), T.Nonempty ∧ Tᶜ.Nonempty := by
  have hprop : ∀ T : Finset (Fin d), T.Nonempty → T.card ≤ 4 → T.Nonempty ∧ Tᶜ.Nonempty :=
    fun T hT hT4 => ⟨hT, compl_nonempty_of_card_le hT4 hd⟩
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hij]; omega)
  · exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hik]; omega)
  · exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hil]; omega)
  · rw [symmDiff_pair_pair hij hik hjk]
    exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hjk]; omega)
  · rw [symmDiff_pair_pair hij hil hjl]
    exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hjl]; omega)
  · rw [symmDiff_pair_pair hik hil hkl]
    exact hprop _ (Finset.insert_nonempty _ _) (by rw [Finset.card_pair hkl]; omega)
  · rw [symmDiff_pair_pair hij hik hjk]
    refine hprop _ ⟨j, by simp [Finset.mem_symmDiff, hjl, hij.symm]⟩ ?_
    calc (symmDiff ({j, k} : Finset (Fin d)) {i, l}).card ≤ ({j, k} ∪ {i, l} :
          Finset (Fin d)).card := Finset.card_le_card Finset.symmDiff_subset_union
      _ ≤ ({j, k} : Finset (Fin d)).card + ({i, l} : Finset (Fin d)).card :=
          Finset.card_union_le _ _
      _ ≤ 4 := by
          have := Finset.card_le_two (a := j) (b := k)
          have := Finset.card_le_two (a := i) (b := l)
          omega

theorem signGL_ne_scalar_mul (hK : ringChar K ≠ 2) {d : ℕ} {J I T : Finset (Fin d)}
    (hI : I = J ∨ I = Jᶜ) (hIn : I.Nonempty) (hTI : T ⊆ Iᶜ) (hTc : T ≠ Iᶜ) (c : Kˣ) :
    signGL K T ≠ GeneralLinearGroup.scalar (Fin d) c * signGL K J := by
  intro h
  have h' : signGL K T = signGL K J * GeneralLinearGroup.scalar (Fin d) c := by
    rw [h, (commute_scalar c (signGL K J)).eq]
  obtain ⟨i, hi⟩ := hIn
  have hiT : i ∉ T := fun h => Finset.mem_compl.1 (hTI h) hi
  rcases eq_or_eq_compl_of_sign_eq_mul hK h' with h1 | h1 <;> rcases hI with rfl | rfl
  · exact hiT (h1 ▸ hi)
  · exact hTc (by rw [h1, compl_compl])
  · exact hTc h1
  · exact hiT (h1 ▸ hi)

theorem false_of_sign [Finite K] (hK : ringChar K ≠ 2) {d : ℕ} (hd : 7 ≤ d) {w : Fin d → K}
    (hw : ∀ i, w i ≠ 0) (hker : OKer (oQ (diagGL hw))) {J : Finset (Fin d)} (hJ : J.Nonempty)
    (hJc : Jᶜ.Nonempty) (hNF : ∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I)
    {M : Subgroup (GL (Fin d) K)} {Q : ℕ}
    (h : X10Data (diagGL hw) (sgnPair (Ring.two_ne_zero hK) hw J) M Q) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ (diagGL hw)) with hH
  have hσ : (sgnPair h2 hw J).val.right = 1 := linPair_right _ _
  have hSl : (sgnPair h2 hw J).val.left = signGL K J := linPair_left _ _
  have hfix := h.commute_left hσ
  rw [hSl] at hfix
  obtain ⟨I, hI, hMO⟩ := DX.Dr.exists_block_of_comp hK hw h.le h.perf J hfix h.comp
  have hIn : I.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJ
    · exact hJc
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJc
    · rw [compl_compl]
      exact hJ
  have hIcI : Iᶜ = J ∨ Iᶜ = Jᶜ := by
    rcases hI with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (compl_compl J)
  have hcardI : I.card + Iᶜ.card = d := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ I
    rw [Fintype.card_fin] at this
    omega
  by_cases hIc3 : 3 ≤ Iᶜ.card
  ·
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hwab, hwac⟩ :=
      (hNF Iᶜ hIcI hIc3).exists_triple
    have hX := signGL_pair_mem_oBlock hw ha hb hab hwab
    have hY := signGL_pair_mem_oBlock hw ha hc hac hwac
    have hXH := oBlock_le_matrixDerived hw h2 Iᶜ hX
    have hYH := oBlock_le_matrixDerived hw h2 Iᶜ hY
    have hsq : ∀ T : Finset (Fin d), signGL K T * signGL K T = 1 := fun T =>
      Units.ext (by rw [Units.val_mul, coe_signGL, signMat_mul_self, Units.val_one])
    have hcommT : ∀ T U : Finset (Fin d), signGL K T * signGL K U = signGL K U * signGL K T :=
      fun T U => by rw [signGL_mul_signGL, signGL_mul_signGL, symmDiff_comm]
    have hMc : ∀ T : Finset (Fin d), signGL K T ∈ oBlock K hw Iᶜ →
        ∀ m ∈ M, signGL K T * m = m * signGL K T := fun T hT m hm =>
      (commute_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw _ (hMO hm))
        (oBlock_le_oIsoBlock hw _ hT)).symm
    have hXY : signGL K {a, b} * signGL K {a, c} = signGL K {b, c} := by
      rw [signGL_mul_signGL, symmDiff_pair_pair hab hac hbc]
    have hpair : ∀ x y : Fin d, x ≠ y → ({x, y} : Finset (Fin d)).Nonempty ∧
        ({x, y} : Finset (Fin d))ᶜ.Nonempty := fun x y hxy =>
      ⟨Finset.insert_nonempty _ _, compl_nonempty_of_card_le
        (by rw [Finset.card_pair hxy]; omega) (by omega)⟩
    have hsub : ∀ x y : Fin d, x ∈ Iᶜ → y ∈ Iᶜ → ({x, y} : Finset (Fin d)) ⊆ Iᶜ :=
      fun x y hx hy z hz => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
    have hne3 : ∀ x y z : Fin d, z ∈ Iᶜ → z ≠ x → z ≠ y →
        ({x, y} : Finset (Fin d)) ≠ Iᶜ := fun x y z hz hzx hzy he => by
      rw [← he, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h' | h'
      · exact hzx h'
      · exact hzy h'
    have hone : GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) = 1 := map_one _
    refine h.false_of_e4 hker hσ hXH hYH (a := 1) (b := 1) (e := 1) (by rw [hone]; exact hsq _)
      (by rw [hone]; exact hsq _) (by rw [hone, one_mul]; exact hcommT _ _) ?_ ?_ (hMc _ hX)
      (hMc _ hY) (fun c' => signGL_ne_scalar h2 (hpair a b hab).1 (hpair a b hab).2 c')
      (fun c' => signGL_ne_scalar h2 (hpair a c hac).1 (hpair a c hac).2 c') ?_ ?_ ?_ ?_
    · rw [hSl]
      exact hcommT _ _
    · rw [hSl]
      exact hcommT _ _
    · intro c'
      rw [hXY]
      exact signGL_ne_scalar h2 (hpair b c hbc).1 (hpair b c hbc).2 c'
    · rw [hSl]
      exact signGL_ne_scalar_mul hK hI hIn (hsub a b ha hb)
        (hne3 a b c hc (Ne.symm hac) (Ne.symm hbc))
    · rw [hSl]
      exact signGL_ne_scalar_mul hK hI hIn (hsub a c ha hc) (hne3 a c b hb (Ne.symm hab) hbc)
    · rw [hSl, hXY]
      exact signGL_ne_scalar_mul hK hI hIn (hsub b c hb hc) (hne3 b c a ha hab hac)
  ·
    have hI5 : 5 ≤ I.card := by omega
    set Qb := (M.subgroupOf H).map (projH H) with hQb
    have hQP : Qb ≤ blockP K hw I :=
      map_mono fun g hg => mem_subgroupOf.2 (hMO (mem_subgroupOf.1 hg))
    have hPs : blockP K hw I ≤ autFixed (oκ _ (sgnPair h2 hw J)) :=
      DX.Dr.blockP_le_autFixed h2 hw J I hI
    have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs h.comp
    have heq : Qb = blockP K hw I := by
      rcases blockP_cases hw hK I hIc with hsol | hqs | ⟨h4, -⟩
      · exact (C.not_le_of_isSolvable hQP hQc' hsol hQP).elim
      · exact C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqs
      · omega
    obtain ⟨I₀, hI₀, hI₀3, hI₀w, hns⟩ := hNF I hI (by omega)
    have hdiff : (I \ I₀).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_sdiff] at hx hy
      exact hns x hx.1 y hy.1 hx.2 hy.2
    have hI₀c : (I \ I₀).card = I.card - I₀.card := Finset.card_sdiff_of_subset hI₀
    have hI₀le : I₀.card ≤ I.card := Finset.card_le_card hI₀
    have hI₀4 : 4 ≤ I₀.card := by omega
    obtain ⟨T, hTI₀, hT4⟩ := Finset.exists_subset_card_eq hI₀4
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_four.1 hT4
    have hmem : ∀ x ∈ ({i, j, k, l} : Finset (Fin d)), x ∈ I₀ := fun x hx => hTI₀ hx
    have hi₀ := hmem i (by simp)
    have hj₀ := hmem j (by simp)
    have hk₀ := hmem k (by simp)
    have hl₀ := hmem l (by simp)
    have hX := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hj₀) hij (hI₀w i hi₀ j hj₀)
    have hY := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hk₀) hik (hI₀w i hi₀ k hk₀)
    have hZ := signGL_pair_mem_oBlock hw (hI₀ hi₀) (hI₀ hl₀) hil (hI₀w i hi₀ l hl₀)
    have hXH := oBlock_le_matrixDerived hw h2 I hX
    have hYH := oBlock_le_matrixDerived hw h2 I hY
    have hZH := oBlock_le_matrixDerived hw h2 I hZ
    have hin : ∀ (T : Finset (Fin d)) (hT : signGL K T ∈ oBlock K hw I),
        projH H ⟨signGL K T, oBlock_le_matrixDerived hw h2 I hT⟩ ∈ Qb := fun T hT => by
      rw [heq]
      exact ⟨_, mem_subgroupOf.2 hT, rfl⟩
    exact h.false_of_e8 (hin _ hX) (hin _ hY) (hin _ hZ)
      (e8Triple_sign h2 hXH hYH hZH (e8Sets (by omega) hij hik hil hjk hjl hkl))

end CFSG.ComponentClassification.GSThmB.X10Orth
