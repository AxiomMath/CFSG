module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.ParabLevi

section Comb

variable {m : ℕ}

@[expose] def SameBlk (I : Set (Fin m)) (p q : Fin (m + 1)) : Prop :=
  ∀ j : Fin m, j ∉ I → (p.val ≤ j.val ↔ q.val ≤ j.val)

@[expose] def SepBlk (I : Set (Fin m)) (a b : Fin (m + 1)) : Prop :=
  ∃ j : Fin m, j ∉ I ∧ a.val ≤ j.val ∧ j.val < b.val

theorem SameBlk.refl (I : Set (Fin m)) (p : Fin (m + 1)) : SameBlk I p p := fun _ _ => Iff.rfl

theorem SameBlk.symm {I : Set (Fin m)} {p q : Fin (m + 1)} (h : SameBlk I p q) : SameBlk I q p :=
  fun j hj => (h j hj).symm

theorem SameBlk.trans {I : Set (Fin m)} {p q r : Fin (m + 1)} (h1 : SameBlk I p q)
    (h2 : SameBlk I q r) : SameBlk I p r := fun j hj => (h1 j hj).trans (h2 j hj)

theorem SepBlk.lt {I : Set (Fin m)} {a b : Fin (m + 1)} (h : SepBlk I a b) : a.val < b.val := by
  obtain ⟨j, -, h1, h2⟩ := h
  omega

theorem sepBlk_or_of_not_same {I : Set (Fin m)} {p q : Fin (m + 1)} (h : ¬ SameBlk I p q) :
    SepBlk I p q ∨ SepBlk I q p := by
  unfold SameBlk at h
  push Not at h
  obtain ⟨j, hj, hjpq⟩ := h
  rcases hjpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨j, hj, h1, h2⟩
  · exact Or.inr ⟨j, hj, h2, h1⟩

theorem SepBlk.ne {I : Set (Fin m)} {a b : Fin (m + 1)} (h : SepBlk I a b) : a ≠ b := by
  intro e
  have := h.lt
  rw [e] at this
  exact lt_irrefl _ this

theorem not_sameBlk_of_sepBlk {I : Set (Fin m)} {a b : Fin (m + 1)} (h : SepBlk I a b) :
    ¬ SameBlk I a b := by
  obtain ⟨j, hj, h1, h2⟩ := h
  intro hs
  have := (hs j hj).mp h1
  omega

theorem sepBlk_zero_last {I : Set (Fin m)} (hI : I ≠ Set.univ) :
    SepBlk I (0 : Fin (m + 1)) (Fin.last m) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  exact ⟨j, hj, by simp, by simp⟩

theorem sepBlk_last_of_not_same {I : Set (Fin m)} {q : Fin (m + 1)}
    (h : ¬ SameBlk I q (Fin.last m)) : SepBlk I q (Fin.last m) := by
  rcases sepBlk_or_of_not_same h with h1 | ⟨j, -, h2, -⟩
  · exact h1
  · exfalso
    have := j.isLt
    simp at h2
    omega

theorem sepBlk_zero_of_not_same {I : Set (Fin m)} {p : Fin (m + 1)}
    (h : ¬ SameBlk I (0 : Fin (m + 1)) p) : SepBlk I (0 : Fin (m + 1)) p := by
  rcases sepBlk_or_of_not_same h with h1 | ⟨j, -, h1, h2⟩
  · exact h1
  · exfalso
    simp at h2

end Comb

section Rad

variable {m : ℕ} {F : Type} [Field F]

@[expose] def rootVec (a b : Fin (m + 1)) : Fin m → ℤ :=
  fun i => if a.val ≤ i.val ∧ i.val < b.val then 1 else 0

theorem toStd_rootVec {a b : Fin (m + 1)} (hab : a.val < b.val) :
    toStd m (rootVec a b) = Pi.single a 1 - Pi.single b 1 := by
  funext p
  simp only [toStd, rootVec, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp_all <;> omega

theorem transvection_mem_leviRad (I : Set (Fin m)) {a b : Fin (m + 1)} (hab : a ≠ b)
    (hsep : SepBlk I a b) (c : F) :
    Matrix.SpecialLinearGroup.transvection hab c ∈ leviRad (rootDatum m F) I := by
  obtain ⟨j, hjI, haj, hjb⟩ := hsep
  have hlt : a.val < b.val := by omega
  have hroot : rootVec a b ∈ (rootDatum m F).roots := by
    change rootVec a b ∈ CFSG.LieType.RootSystem.roots (isFiniteType_A m) ∅
    rw [roots_eq]
    exact ⟨a, b, hab, toStd_rootVec hlt⟩
  have hpos : 0 < rootVec a b j := by
    simp [rootVec, haj, hjb]
  have h1 : (rootDatum m F).rootGroup (rootVec a b) ≤ radical (rootDatum m F) j :=
    rootGroup_le_radical hroot hpos
  have h2 : (rootDatum m F).rootGroup (rootVec a b) = rootSubgroup m F hab :=
    rootGroup_eq m F hab (toStd_rootVec hlt)
  have h3 : Matrix.SpecialLinearGroup.transvection hab c ∈
      (rootDatum m F).rootGroup (rootVec a b) := by
    rw [h2]; exact transvection_mem_rootSubgroup hab c
  exact (radical_le_leviRad hjI) (h1 h3)

end Rad

section Matrix

variable {m : ℕ} {F : Type} [Field F]

theorem entries_of_comm_transvection {N : ℕ} {a b : Fin N} (hab : a ≠ b)
    (k : Matrix (Fin N) (Fin N) F)
    (h : k * Matrix.transvection a b (1 : F) = Matrix.transvection a b 1 * k) :
    (∀ i, i ≠ a → k i a = 0) ∧ (∀ j, j ≠ b → k b j = 0) ∧ k a a = k b b := by
  have key : ∀ i j, (k * Matrix.transvection a b (1 : F)) i j =
      (Matrix.transvection a b (1 : F) * k) i j := fun i j => by rw [h]
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · have := key i b
    simp [hi] at this
    exact this
  · have := key a j
    simp [hj] at this
    exact this
  · have := key a b
    simp at this
    exact this

@[expose] def partialMat {N : ℕ} (Y : Matrix (Fin N) (Fin N) F) (Q : Finset (Fin N × Fin N)) :
    Matrix (Fin N) (Fin N) F :=
  Matrix.of fun i j => if (i, j) ∈ Q then Y i j else 0

theorem exists_mem_leviRad_of_supported {I : Set (Fin m)} (hI : I ≠ Set.univ)
    (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hY : ∀ p q, Y p q ≠ 0 → SameBlk I 0 p ∧ SameBlk I q (Fin.last m)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F, g ∈ leviRad (rootDatum m F) I ∧
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + Y := by
  classical
  have hsep := sepBlk_zero_last hI
  have hdisj : ∀ p, SameBlk I 0 p → SameBlk I p (Fin.last m) → False := fun p h1 h2 =>
    not_sameBlk_of_sepBlk hsep (h1.trans h2)
  have key : ∀ Q : Finset (Fin (m + 1) × Fin (m + 1)),
      (∀ pq ∈ Q, SameBlk I 0 pq.1 ∧ SameBlk I pq.2 (Fin.last m)) →
      ∃ g : Matrix.SpecialLinearGroup (Fin (m + 1)) F, g ∈ leviRad (rootDatum m F) I ∧
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 + partialMat Y Q := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_mem _, ?_⟩
      ext i j
      simp [partialMat]
    | insert pq Q hpq ih =>
      intro hQ
      obtain ⟨g', hg'U, hg'⟩ := ih (fun x hx => hQ x (Finset.mem_insert_of_mem hx))
      obtain ⟨hp, hq⟩ := hQ pq (Finset.mem_insert_self _ _)
      have hne : pq.1 ≠ pq.2 := fun h => hdisj pq.2 (h ▸ hp) hq
      have hsepq : SepBlk I pq.1 pq.2 := by
        obtain ⟨j, hjI, -, -⟩ := hsep
        have h1 : pq.1.val ≤ j.val := (hp j hjI).mp (Nat.zero_le _)
        have h2 : ¬ pq.2.val ≤ j.val := fun h => by
          have h4 := (hq j hjI).mp h
          have h3 := j.isLt
          simp at h4
          omega
        exact ⟨j, hjI, h1, by omega⟩
      have hrow : ∀ jj, partialMat Y Q pq.2 jj = 0 := fun jj => by
        by_cases hmem : (pq.2, jj) ∈ Q
        · exact absurd (hQ _ (Finset.mem_insert_of_mem hmem)).1 (fun h => hdisj pq.2 h hq)
        · simp [partialMat, hmem]
      refine ⟨Matrix.SpecialLinearGroup.transvection hne (Y pq.1 pq.2) * g',
        mul_mem (transvection_mem_leviRad I hne hsepq _) hg'U, ?_⟩
      have hmul : ((Matrix.SpecialLinearGroup.transvection hne (Y pq.1 pq.2) * g' :
          Matrix.SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          Matrix.transvection pq.1 pq.2 (Y pq.1 pq.2) * (g' : Matrix _ _ F) := rfl
      rw [hmul, hg']
      have hz : Matrix.single pq.1 pq.2 (Y pq.1 pq.2) * partialMat Y Q = 0 := by
        ext i jj
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l = pq.2
        · subst hl; simp [hrow jj]
        · simp [Matrix.single_apply, Ne.symm hl]
      have hins : partialMat Y (insert pq Q) =
          partialMat Y Q + Matrix.single pq.1 pq.2 (Y pq.1 pq.2) := by
        ext i jj
        by_cases h : (i, jj) = pq
        · subst h
          simp [partialMat, hpq, Matrix.single_apply]
        · have h' : ¬ (pq.1 = i ∧ pq.2 = jj) := fun ⟨e1, e2⟩ => h (Prod.ext e1.symm e2.symm)
          have hmem : (i, jj) ∈ insert pq Q ↔ (i, jj) ∈ Q := by simp [Finset.mem_insert, h]
          by_cases hq' : (i, jj) ∈ Q
          · simp [partialMat, hq', hmem.mpr hq', Matrix.single_apply, h']
          · simp [partialMat, hq', mt hmem.mp hq', Matrix.single_apply, h']
            exact fun e => absurd e h
      rw [hins, Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hz]
      abel
  have hQ0 := key (Finset.univ.filter fun pq => Y pq.1 pq.2 ≠ 0) (fun pq hpq => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpq
    exact hY _ _ hpq)
  have hY' : partialMat Y (Finset.univ.filter fun pq => Y pq.1 pq.2 ≠ 0) = Y := by
    ext i j
    by_cases h : Y i j = 0 <;> simp [partialMat, h]
  rwa [hY'] at hQ0

theorem centOb_sl {I : Set (Fin m)} (hI : I ≠ Set.univ) : CentOb (rootDatum m F) I := by
  classical
  intro k hk
  have hsep := sepBlk_zero_last hI
  have hns : ¬ SameBlk I 0 (Fin.last m) := not_sameBlk_of_sepBlk hsep
  have hcomm : ∀ a b (hab : a ≠ b), SepBlk I a b → (∀ i, i ≠ a → (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i a = 0) ∧
      (∀ j, j ≠ b → (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) b j = 0) ∧
      (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) b b := by
    intro a b hab hs
    have h1 := hk _ (transvection_mem_leviRad I hab hs (1 : F))
    exact entries_of_comm_transvection hab _ (congrArg Subtype.val h1)
  have hdiag_sep : ∀ a b, SepBlk I a b → (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) b b :=
    fun a b hs => (hcomm a b hs.ne hs).2.2
  have hdiag_ns : ∀ a b, ¬ SameBlk I a b → (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) b b := by
    intro a b h
    rcases sepBlk_or_of_not_same h with h1 | h1
    · exact hdiag_sep a b h1
    · exact (hdiag_sep b a h1).symm
  have hdiag : ∀ p q, (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p p = (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) q q := by
    intro p q
    by_cases hpq : SameBlk I p q
    · by_cases hp0 : SameBlk I 0 p
      · have hpl : ¬ SameBlk I p (Fin.last m) := fun h => hns (hp0.trans h)
        have hql : ¬ SameBlk I q (Fin.last m) := fun h => hpl (hpq.trans h)
        exact (hdiag_ns _ _ hpl).trans (hdiag_ns _ _ hql).symm
      · have hq0 : ¬ SameBlk I q 0 := fun h => hp0 ((hpq.trans h).symm)
        have hp0' : ¬ SameBlk I p 0 := fun h => hp0 h.symm
        exact (hdiag_ns _ _ hp0').trans (hdiag_ns _ _ hq0).symm
    · exact hdiag_ns _ _ hpq
  have hoff : ∀ p q, p ≠ q → (k : Matrix (Fin (m + 1)) (Fin (m + 1)) F) p q ≠ 0 →
      SameBlk I 0 p ∧ SameBlk I q (Fin.last m) := by
    intro p q hpq hne
    constructor
    · by_contra h
      have hs := sepBlk_zero_of_not_same h
      exact hne ((hcomm 0 p hs.ne hs).2.1 q hpq.symm)
    · by_contra h
      have hs := sepBlk_last_of_not_same h
      exact hne ((hcomm q (Fin.last m) hs.ne hs).1 p hpq)
  have hdisj : ∀ p, SameBlk I 0 p → SameBlk I p (Fin.last m) → False := fun p h1 h2 =>
    hns (h1.trans h2)
  obtain ⟨kk, hkk⟩ : ∃ kk : Matrix (Fin (m + 1)) (Fin (m + 1)) F, kk = (k : Matrix _ _ F) :=
    ⟨_, rfl⟩
  rw [← hkk] at hdiag hoff
  obtain ⟨c, hc⟩ : ∃ c : F, c = kk 0 0 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (m + 1)) (Fin (m + 1)) F, X = kk - c • 1 := ⟨_, rfl⟩
  have hXentry : ∀ p q, X p q = if p = q then 0 else kk p q := by
    intro p q
    by_cases h : p = q
    · subst h
      simp [hX, hc, hdiag p 0]
    · simp [hX, h]
  have hXsupp : ∀ p q, X p q ≠ 0 → SameBlk I 0 p ∧ SameBlk I q (Fin.last m) := by
    intro p q hne
    rw [hXentry] at hne
    by_cases h : p = q
    · simp [h] at hne
    · exact hoff p q h (by simpa [h] using hne)
  have hXX : X * X = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : X i l = 0
    · simp [h1]
    · by_cases h2 : X l j = 0
      · simp [h2]
      · exact absurd (hXsupp i l h1).2 (fun h => hdisj l (hXsupp l j h2).1 h)
  have hdet : (kk).det = 1 := by rw [hkk]; exact Matrix.SpecialLinearGroup.det_coe k
  have hc0 : c ≠ 0 := by
    intro h0
    have hkX : kk = X := by rw [hX, h0]; simp
    have : X.det * X.det = 0 := by
      rw [← Matrix.det_mul, hXX]; exact Matrix.det_zero
    have hX0 : X.det = 0 := mul_self_eq_zero.mp this
    rw [hkX, hX0] at hdet
    exact zero_ne_one hdet
  obtain ⟨g, hgU, hg⟩ := exists_mem_leviRad_of_supported hI (c⁻¹ • X) (fun p q hne =>
    hXsupp p q (fun h => hne (by simp [h])))
  have hkc : kk = c • (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    rw [hg, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul, hX]
    abel
  have hcpow : c ^ (m + 1) = 1 := by
    have := congrArg Matrix.det hkc
    rw [Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe, mul_one, hdet] at this
    simpa using this.symm
  have hz_det : (Matrix.scalar (Fin (m + 1)) c).det = 1 := by
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hcpow
  let z : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨Matrix.scalar (Fin (m + 1)) c, hz_det⟩
  have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by simpa using hcpow, rfl⟩
  have hkz : k = g * z := by
    apply Subtype.ext
    rw [← hkk, hkc]
    ext p q
    change _ = ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * Matrix.scalar (Fin (m + 1)) c) p q
    simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  rw [hkz]
  exact Subgroup.mul_mem_sup hgU hzc

end Matrix

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
