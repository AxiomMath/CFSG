module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
public import CFSG.LieType.SpecialLinear.InvolutionConj

public section

namespace CFSG.LieType.SpecialLinear.ExteriorModel

open Matrix

variable {k : Type} [Field k] {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

@[expose] def bWt (ε : τ → Finset (Fin n)) (s : BIdx ε) : τ → Fin n → ℤ :=
  fun r a =>
    ((Finset.univ.filter fun j : Fin n =>
      a ∈ ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n))).card : ℤ)

@[expose] def bPerm (ε : τ → Finset (Fin n)) (π : τ → Equiv.Perm (Fin n)) (s : BIdx ε) :
    BIdx ε :=
  fun p => ⟨((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)).map
    (π p.1).toEmbedding, by
      rw [Set.powersetCard.mem_iff, Finset.card_map, Set.powersetCard.card_eq]⟩

@[expose] noncomputable def permSL [CharP k 2] (σ : Equiv.Perm (Fin n)) :
    Matrix.SpecialLinearGroup (Fin n) k :=
  ⟨σ.permMatrix k, det_permMatrix_of_charTwo σ⟩

omit [Fintype τ] [DecidableEq τ] in
theorem bPerm_one (ε : τ → Finset (Fin n)) (s : BIdx ε) : bPerm ε (fun _ => 1) s = s := by
  funext p
  apply Subtype.ext
  ext a
  have hsymm : (Equiv.symm (1 : Equiv.Perm (Fin n))) = 1 := rfl
  simp [bPerm, hsymm]

omit [Fintype τ] [DecidableEq τ] in
theorem bPerm_mul (ε : τ → Finset (Fin n)) (π π' : τ → Equiv.Perm (Fin n)) (s : BIdx ε) :
    bPerm ε (fun r => π r * π' r) s = bPerm ε π (bPerm ε π' s) := by
  funext p
  apply Subtype.ext
  ext a
  simp only [bPerm, Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hb_eq⟩
    exact ⟨π' p.1 b, ⟨b, hb, rfl⟩, by simpa [Equiv.Perm.mul_apply] using hb_eq⟩
  · rintro ⟨c, ⟨b, hb, rfl⟩, hc⟩
    exact ⟨b, hb, by simpa [Equiv.Perm.mul_apply] using hc⟩

omit [Fintype τ] [DecidableEq τ] in
theorem bPerm_injective (ε : τ → Finset (Fin n)) (π : τ → Equiv.Perm (Fin n)) :
    Function.Injective (bPerm ε π) := by
  intro s t h
  funext p
  apply Subtype.ext
  exact Finset.map_injective (π p.1).toEmbedding (Subtype.ext_iff.mp (congrFun h p))

omit [Fintype τ] [DecidableEq τ] in
theorem bWt_bPerm (ε : τ → Finset (Fin n)) (π : τ → Equiv.Perm (Fin n)) (s : BIdx ε) :
    bWt ε (bPerm ε π s) = fun r a => bWt ε s r ((π r).symm a) := by
  funext r a
  have hf : (Finset.univ.filter fun j : Fin n =>
      a ∈ ((bPerm ε π s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
        Finset (Fin n))) =
      (Finset.univ.filter fun j : Fin n =>
        (π r).symm a ∈ ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
          Finset (Fin n))) := by
    apply Finset.filter_congr
    intro j _
    simp only [bPerm]
    rw [Finset.mem_map]
    constructor
    · rintro ⟨b, hb, hb_eq⟩
      rw [← hb_eq]
      simpa using hb
    · intro h
      exact ⟨(π r).symm a, h, by simp⟩
  simp only [bWt]
  rw [hf]

theorem snd_minor_one_add_eps_single_ne_zero {R : Type*} [CommRing R] {m : ℕ}
    {a b : Fin m} (hab : a ≠ b) {d : ℕ} {s t : Set.powersetCard (Fin m) d}
    (h : (minor (1 + (DualNumber.eps : DualNumber R) •
        (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R)) s t).snd ≠ 0) :
    b ∈ (t : Finset (Fin m)) ∧ a ∉ (t : Finset (Fin m)) ∧
      (s : Finset (Fin m)) = insert a ((t : Finset (Fin m)).erase b) := by
  classical
  let e : Fin d → Fin m := Set.powersetCard.ofFinEmbEquiv.symm s
  let f : Fin d → Fin m := Set.powersetCard.ofFinEmbEquiv.symm t
  have he_inj : Function.Injective e := by
    simpa [e] using (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  have hf_inj : Function.Injective f := by
    simpa [f] using (Set.powersetCard.ofFinEmbEquiv.symm t).injective
  have he_mem : ∀ i, e i ∈ (s : Finset (Fin m)) := by
    intro i
    rw [Set.powersetCard.mem_coe_iff]
    simpa [e] using (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (e i)).mp
      (Set.mem_range_self i)
  have hf_mem : ∀ i, f i ∈ (t : Finset (Fin m)) := by
    intro i
    rw [Set.powersetCard.mem_coe_iff]
    simpa [f] using (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (f i)).mp
      (Set.mem_range_self i)
  let A : Matrix (Fin d) (Fin d) R := (1 : Matrix (Fin m) (Fin m) R).submatrix e f
  let Esub : Matrix (Fin d) (Fin d) R := (Matrix.single a b (1 : R)).submatrix e f
  have hmat : (1 + (DualNumber.eps : DualNumber R) •
      (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R)).submatrix e f =
      A.map (TrivSqZeroExt.inl : R → DualNumber R) +
        (DualNumber.eps : DualNumber R) • Esub.map (TrivSqZeroExt.inl : R → DualNumber R) := by
    apply Matrix.ext
    intro i j
    by_cases h : e i = f j
    · apply TrivSqZeroExt.ext <;>
        simp [A, Esub, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, Matrix.one_apply, Matrix.single_apply, h]
    · apply TrivSqZeroExt.ext <;>
        simp [A, Esub, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, Matrix.single_apply, h]
  have hsub : minor (1 + (DualNumber.eps : DualNumber R) •
      (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R)) s t =
      (A.map (TrivSqZeroExt.inl : R → DualNumber R) +
        (DualNumber.eps : DualNumber R) • Esub.map (TrivSqZeroExt.inl : R → DualNumber R)).det := by
    rw [minor, hmat]
  have hdet_map : ∀ M : Matrix (Fin d) (Fin d) R,
      (M.map (TrivSqZeroExt.inl : R → DualNumber R)).det =
        TrivSqZeroExt.inl M.det := by
    intro M
    have h := (RingHom.map_det (f := TrivSqZeroExt.inlHom (R := R) (M := R)) M).symm
    change (M.map (TrivSqZeroExt.inl : R → DualNumber R)).det = _ at h
    exact h
  have hzero_of_Esub_zero (hE : Esub = 0) : False := by
    have hval : minor (1 + (DualNumber.eps : DualNumber R) •
        (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R)) s t =
        (A.map (TrivSqZeroExt.inl : R → DualNumber R)).det := by
      rw [hsub, hE, Matrix.map_zero (TrivSqZeroExt.inl : R → DualNumber R)
        (TrivSqZeroExt.inl_zero (M := R)), smul_zero, add_zero]
    have hsnd0 : ((A.map (TrivSqZeroExt.inl : R → DualNumber R)).det).snd = 0 := by
      rw [hdet_map]
      exact TrivSqZeroExt.snd_inl (M := R) A.det
    exact h (by simpa [hval] using hsnd0)
  have ha : a ∈ (s : Finset (Fin m)) := by
    by_contra ha
    apply hzero_of_Esub_zero
    ext i j
    have hane : a ≠ e i := by
      intro h; exact ha (by rw [h]; exact he_mem i)
    simp [Esub, Matrix.submatrix_apply, hane]
  have hb : b ∈ (t : Finset (Fin m)) := by
    by_contra hb
    apply hzero_of_Esub_zero
    ext i j
    have hbne : b ≠ f j := by
      intro h; exact hb (by rw [h]; exact hf_mem j)
    simp [Esub, Matrix.submatrix_apply, hbne]
  obtain ⟨i0, hi0⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem s ha
  obtain ⟨j0, hj0⟩ := exists_ofFinEmbEquiv_symm_eq_of_mem t hb
  have hei0 : e i0 = a := by simpa [e] using hi0
  have hfj0 : f j0 = b := by simpa [f] using hj0
  have hEsub : Esub = Matrix.single i0 j0 (1 : R) := by
    change (Matrix.single a b (1 : R)).submatrix e f = _
    exact submatrix_single_of_injective he_inj hf_inj hei0 hfj0
  have hdet : (A.map (TrivSqZeroExt.inl : R → DualNumber R) +
      (DualNumber.eps : DualNumber R) • Esub.map (TrivSqZeroExt.inl : R → DualNumber R)).det =
      (A.map (TrivSqZeroExt.inl : R → DualNumber R)).det +
        (DualNumber.eps : DualNumber R) * (Matrix.updateRow
          (A.map (TrivSqZeroExt.inl : R → DualNumber R)) i0 (Pi.single j0 1)).det := by
    rw [hEsub]
    have hmap : (Matrix.single i0 j0 (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R) =
        Matrix.single i0 j0 (1 : DualNumber R) := by
      change (Matrix.single i0 j0 (1 : R)).map
        (TrivSqZeroExt.inlHom (R := R) (M := R) : R →+* DualNumber R) = _
      rw [Matrix.map_single, map_one]
    rw [hmap, det_add_smul_single]
  have hrow : Matrix.updateRow (A.map (TrivSqZeroExt.inl : R → DualNumber R)) i0
      (Pi.single j0 (1 : DualNumber R)) =
      (Matrix.updateRow A i0 (Pi.single j0 (1 : R))).map
        (TrivSqZeroExt.inl : R → DualNumber R) := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · by_cases hi : i = i0 <;> by_cases hj : j = j0 <;>
        simp [Matrix.updateRow_apply, Matrix.map_apply, hi, hj]
    · by_cases hi : i = i0 <;> by_cases hj : j = j0 <;>
        simp [Matrix.updateRow_apply, Matrix.map_apply, hi, hj]
  let D : R := (Matrix.updateRow A i0 (Pi.single j0 (1 : R))).det
  have hsnd : (minor (1 + (DualNumber.eps : DualNumber R) •
      (Matrix.single a b (1 : R)).map (TrivSqZeroExt.inl : R → DualNumber R)) s t).snd = D := by
    have hrow_det : (Matrix.updateRow (A.map (TrivSqZeroExt.inl : R → DualNumber R)) i0
        (Pi.single j0 (1 : DualNumber R))).det = TrivSqZeroExt.inl D := by
      rw [hrow]
      exact hdet_map _
    rw [hsub, hdet, hrow_det, hdet_map]
    simp [D, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.fst_inl, DualNumber.fst_eps, DualNumber.snd_eps]
  have hD : D ≠ 0 := by
    intro hD0
    exact h (by rw [hsnd, hD0])
  have hst : s ≠ t := by
    intro hst
    have hfe : f = e := by
      funext x
      dsimp [f, e]
      rw [hst]
    have hj0e : e j0 = b := by rw [← hfe]; exact hfj0
    have hij : i0 ≠ j0 := by
      intro h
      exact hab (by rw [← hei0, h, hj0e])
    have hA : A = 1 := by
      change (1 : Matrix (Fin m) (Fin m) R).submatrix e f = 1
      rw [hfe]
      exact submatrix_one e he_inj
    have hR : (1 : Matrix (Fin d) (Fin d) R) j0 = Pi.single j0 (1 : R) := by
      funext l
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    have hD0 : D = 0 := by
      dsimp [D]
      rw [hA, ← hR]
      exact Matrix.det_updateRow_eq_zero hij.symm
    exact hD hD0
  have hrow_of_ne : ∀ k, k ≠ i0 → ∀ l,
      Matrix.updateRow A i0 (Pi.single j0 (1 : R)) k l =
        (if e k = f l then (1 : R) else 0) := by
    intro k hk l
    rw [Matrix.updateRow_apply]
    simp [A, Matrix.submatrix_apply, Matrix.one_apply, hk]
  have hrow_i0 : ∀ l, Matrix.updateRow A i0 (Pi.single j0 (1 : R)) i0 l =
      (if l = j0 then (1 : R) else 0) := by
    intro l
    rw [Matrix.updateRow_self]
    simp [Pi.single_apply]
  have hmem_t : ∀ k, k ≠ i0 → e k ∈ (t : Finset (Fin m)) := by
    intro k hk
    by_contra hkt
    have hzero : D = 0 := by
      dsimp [D]
      apply Matrix.det_eq_zero_of_row_eq_zero k
      intro l
      rw [hrow_of_ne k hk l]
      have hne : e k ≠ f l := fun h => hkt (by rw [h]; exact hf_mem l)
      simp [hne]
    exact hD hzero
  have hne_b : ∀ k, k ≠ i0 → e k ≠ b := by
    intro k hk hkb
    have hzero : D = 0 := by
      dsimp [D]
      apply Matrix.det_zero_of_row_eq hk
      funext l
      rw [hrow_of_ne k hk l, hrow_i0 l]
      have hiff : (e k = f l) ↔ l = j0 := by
        rw [hkb, ← hfj0]
        exact ⟨fun h => (hf_inj h).symm, fun h => by rw [h]⟩
      simp [hiff]
    exact hD hzero
  have hsub_erase : (s : Finset (Fin m)).erase a ⊆ (t : Finset (Fin m)).erase b := by
    intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨hxa, hxs⟩ := hx
    obtain ⟨k, hk⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x).mpr
      (Set.powersetCard.mem_coe_iff.mp hxs)
    have hk' : e k = x := by simpa [e] using hk
    have hk_ne : k ≠ i0 := by
      intro h; exact hxa (by rw [← hk', h, hei0])
    rw [← hk']
    exact Finset.mem_erase.mpr ⟨hne_b k hk_ne, hmem_t k hk_ne⟩
  have hcard_s : ((s : Finset (Fin m)).erase a).card = d - 1 := by
    rw [Finset.card_erase_of_mem ha, Set.powersetCard.card_eq]
  have hcard_t : ((t : Finset (Fin m)).erase b).card = d - 1 := by
    rw [Finset.card_erase_of_mem hb, Set.powersetCard.card_eq]
  have hEq : (s : Finset (Fin m)).erase a = (t : Finset (Fin m)).erase b :=
    Finset.eq_of_subset_of_card_le hsub_erase (by rw [hcard_t, hcard_s])
  have hat : a ∉ (t : Finset (Fin m)) := by
    intro hat
    have hmem : a ∈ (t : Finset (Fin m)).erase b := Finset.mem_erase.mpr ⟨hab, hat⟩
    rw [← hEq] at hmem
    exact (Finset.notMem_erase a _) hmem
  refine ⟨hb, hat, ?_⟩
  rw [← hEq]
  exact (Finset.insert_erase ha).symm

omit [Fintype τ] in
theorem bWt_add_of_support (ε : τ → Finset (Fin n)) {r : τ} {a b : Fin n} (hab : a ≠ b)
    {j : Fin n} {s t : BIdx ε}
    (hagree : ∀ p : τ × Fin n, p ≠ (r, j) → s p = t p)
    (hb : b ∈ ((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)))
    (ha : a ∉ ((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)))
    (hs : ((s (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) =
      insert a (((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)).erase b)) :
    bWt ε s = bWt ε t + Pi.single r (Pi.single a 1 - Pi.single b 1) := by
  classical
  funext r' c
  by_cases hr : r' = r
  · subst r'
    by_cases hca : c = a
    · subst c
      have hfilter : (Finset.univ.filter fun j' : Fin n =>
          a ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))) =
          insert j (Finset.univ.filter fun j' : Fin n =>
            a ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))) := by
        ext j'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j' = j
        · subst j'
          simp [hs, ha]
        · rw [hagree (r, j') (by simp [hj])]
          simp [hj]
      unfold bWt
      rw [hfilter, Finset.card_insert_of_notMem]
      · push_cast
        simp [Pi.single_eq_same, Pi.single_eq_of_ne hab]
      · simp [ha]
    · by_cases hcb : c = b
      · subst c
        have hfilter : (Finset.univ.filter fun j' : Fin n =>
            b ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))) =
            (Finset.univ.filter fun j' : Fin n =>
              b ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).erase j := by
          ext j'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hj : j' = j
          · subst j'
            simp [hs, hab.symm]
          · rw [hagree (r, j') (by simp [hj])]
            simp [hj]
        have hcard : (Finset.univ.filter fun j' : Fin n =>
            b ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card + 1 =
            (Finset.univ.filter fun j' : Fin n =>
              b ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card := by
          rw [hfilter, Finset.card_erase_add_one]
          simp [hb]
        unfold bWt
        have hz : ((Finset.univ.filter fun j' : Fin n =>
            b ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card : ℤ) =
            ((Finset.univ.filter fun j' : Fin n =>
              b ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card : ℤ) - 1 := by
          have h := hcard
          have hz' : ((Finset.univ.filter fun j' : Fin n =>
              b ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card : ℤ) + 1 =
              ((Finset.univ.filter fun j' : Fin n =>
                b ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))).card : ℤ) := by
            exact_mod_cast h
          linarith
        rw [hz]
        have h1 : (Pi.single b (1 : ℤ) : Fin n → ℤ) b = 1 := by simp
        have h2 : (Pi.single a (1 : ℤ) : Fin n → ℤ) b = 0 := by simp [Ne.symm hab]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, h2]
        ring
      · have hfilter : (Finset.univ.filter fun j' : Fin n =>
            c ∈ ((s (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))) =
            (Finset.univ.filter fun j' : Fin n =>
              c ∈ ((t (r, j') : Set.powersetCard (Fin n) (bdeg ε (r, j'))) : Finset (Fin n))) := by
          ext j'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hj : j' = j
          · subst j'
            have hmem : c ∈ insert a (((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
                Finset (Fin n)).erase b) ↔
                c ∈ ((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) := by
              rw [Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro (rfl | ⟨-, hct⟩)
                · exact absurd rfl hca
                · exact hct
              · intro hct
                exact Or.inr ⟨hcb, hct⟩
            simp [hs, hmem]
          · rw [hagree (r, j') (by simp [hj])]
        unfold bWt
        rw [hfilter]
        simp [Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb]
  · have hfilter : (Finset.univ.filter fun j' : Fin n =>
        c ∈ ((s (r', j') : Set.powersetCard (Fin n) (bdeg ε (r', j'))) : Finset (Fin n))) =
        (Finset.univ.filter fun j' : Fin n =>
          c ∈ ((t (r', j') : Set.powersetCard (Fin n) (bdeg ε (r', j'))) : Finset (Fin n))) := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hagree (r', j')]
      intro h
      exact hr (congrArg Prod.fst h)
    unfold bWt
    rw [hfilter]
    simp [Pi.single_eq_of_ne hr]

theorem bWt_of_bDer_ne_zero (ε : τ → Finset (Fin n)) (x : τ × Fin n × Fin n) {s t : BIdx ε}
    (h : bDer (k := k) ε x s t ≠ 0) :
    bWt ε s = bWt ε t + Pi.single x.1 (Pi.single x.2.1 1 - Pi.single x.2.2 1) := by
  obtain ⟨r, a, b⟩ := x
  by_cases hab : a = b
  · subst b
    have hst : s = t := by
      by_contra hst
      apply h
      rw [bDer, kronDer_single_self_apply]
      simp [hst]
    subst hst
    simp
  · let P : τ × Fin n → Prop := fun p => p.1 = r
    let E : Matrix (Fin n) (Fin n) k := Matrix.single a b 1
    let G : τ × Fin n → Matrix (Fin n) (Fin n) (DualNumber k) := fun p =>
      if P p then 1 + (DualNumber.eps : DualNumber k) •
        E.map (TrivSqZeroExt.inl : k → DualNumber k) else 1
    have hder : bDer (k := k) ε (r, a, b) s t = (kronMinor G s t).snd := by
      rw [bDer]
      rfl
    have hprod : kronMinor G s t = ∏ p : τ × Fin n, minor (G p) (s p) (t p) :=
      kronMinor_apply G s t
    have hsum_ne : (∑ p : τ × Fin n, (minor (G p) (s p) (t p)).snd *
        ∏ q ∈ Finset.univ.erase p, (minor (G q) (s q) (t q)).fst) ≠ 0 := by
      intro hzero
      apply h
      rw [hder, hprod, snd_prod_eq_sum]
      exact hzero
    obtain ⟨p0, -, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
    have hsnd_p0 : (minor (G p0) (s p0) (t p0)).snd ≠ 0 := by
      intro hz
      exact hp0 (by rw [hz, zero_mul])
    have hfst_q : ∀ q, q ≠ p0 → (minor (G q) (s q) (t q)).fst ≠ 0 := by
      intro q hq hz
      exact hp0 (by
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hq, Finset.mem_univ q⟩) hz,
          mul_zero])
    have hGfst : ∀ q : τ × Fin n,
        (G q).map (TrivSqZeroExt.fst : DualNumber k → k) = 1 := by
      intro q
      ext i j
      by_cases hq : q.1 = r <;> by_cases hij : i = j <;>
        simp [G, P, hq, hij, Matrix.map_apply, Matrix.one_apply, TrivSqZeroExt.fst_add,
          TrivSqZeroExt.fst_one, DualNumber.fst_eps]
    have hfst_minor : ∀ q : τ × Fin n, (minor (G q) (s q) (t q)).fst =
        minor (1 : Matrix (Fin n) (Fin n) k) (s q) (t q) := by
      intro q
      have hmap : (G q).map (⇑(TrivSqZeroExt.fstHom k k k).toRingHom) =
          (G q).map (TrivSqZeroExt.fst : DualNumber k → k) := rfl
      have h := minor_map (n := bdeg ε q) (φ := (TrivSqZeroExt.fstHom k k k).toRingHom)
        (G q) (s q) (t q)
      rw [hmap, hGfst q] at h
      exact h.symm
    have hq_eq : ∀ q, q ≠ p0 → s q = t q := by
      intro q hq
      have hfq := hfst_q q hq
      rw [hfst_minor q, minor_one] at hfq
      by_contra hne
      simp [hne] at hfq
    have hp0_r : p0.1 = r := by
      by_contra hne
      apply hsnd_p0
      have hG1 : G p0 = 1 := by simp [G, P, hne]
      rw [hG1, minor_one]
      by_cases hst : s p0 = t p0 <;> simp [hst]
    obtain ⟨r', j⟩ := p0
    simp only at hp0_r
    subst r'
    have hG_eq : G (r, j) = 1 + (DualNumber.eps : DualNumber k) •
        E.map (TrivSqZeroExt.inl : k → DualNumber k) := by
      simp [G, P, E]
    rw [hG_eq] at hsnd_p0
    obtain ⟨hb, ha, hs⟩ := snd_minor_one_add_eps_single_ne_zero (R := k) hab hsnd_p0
    exact bWt_add_of_support ε hab (fun p hp => hq_eq p hp) hb ha hs

theorem homComp_bWt_mem_bCyc (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bCyc ε)
    (e : τ → Fin n → ℤ) : homComp (bWt ε) e w ∈ bCyc ε := by
  refine homComp_mem_cyclicSub (k := k) (deg := bWt ε) (D := bDer (k := k) ε)
    (v := bvec (k := k) ε) (e₀ := bWt ε (btop ε)) (δ := fun x =>
      Pi.single x.1 (Pi.single x.2.1 1 - Pi.single x.2.2 1)) ?_ ?_ hw e
  · intro x s t h
    exact bWt_of_bDer_ne_zero ε x h
  · intro s hs
    have hst : s = btop ε := by
      by_contra hne
      exact hs (by simp [bvec, hne])
    rw [hst]

theorem homComp_bWt_mem_bRad (ε : τ → Finset (Fin n)) {w : BIdx ε → k} (hw : w ∈ bRad ε)
    (e : τ → Fin n → ℤ) : homComp (bWt ε) e w ∈ bRad ε := by
  exact homComp_mem_dotRad (deg := bWt ε) (C := bCyc (k := k) ε)
    (fun e y hy => homComp_bWt_mem_bCyc ε hy e) hw e

theorem bMat_diagonal_mulVec_single (ε : τ → Finset (Fin n)) (d : τ → Fin n → k) (s : BIdx ε) :
    bMat ε (fun r => Matrix.diagonal (d r)) *ᵥ Pi.single s (1 : k) =
      (∏ p : τ × Fin n, ∏ a ∈
        ((s p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)), d p.1 a) •
        Pi.single s 1 := by
  rw [bMat, kronMinor_diagonal, Matrix.diagonal_mulVec_single, mul_one, ← Pi.single_smul']
  simp

theorem bMat_permMatrix_mulVec_single [CharP k 2] (ε : τ → Finset (Fin n))
    (π : τ → Equiv.Perm (Fin n)) (s : BIdx ε) :
    bMat ε (fun r => ((π r)⁻¹).permMatrix k) *ᵥ Pi.single s (1 : k) =
      Pi.single (bPerm ε π s) 1 := by
  have h2 : (2 : k) = 0 := by simpa using (CharP.cast_eq_zero k 2)
  rw [bMat, Matrix.mulVec_single_one]
  funext t
  rw [Matrix.col_apply, kronMinor_permMatrix (σ := fun p : τ × Fin n => (π p.1)⁻¹) h2]
  have hcond : (∀ i : τ × Fin n,
        ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).map
          ((π i.1)⁻¹).toEmbedding = ((s i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n))) ↔
      t = bPerm ε π s := by
    constructor
    · intro h
      funext i
      apply Subtype.ext
      have hi : (((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).map
          ((π i.1)⁻¹).toEmbedding) = ((s i : Set.powersetCard (Fin n) (bdeg ε i)) :
            Finset (Fin n)) := h i
      have hmap := congrArg (Finset.map (π i.1).toEmbedding) hi
      simpa [bPerm, Finset.map_map] using hmap
    · intro h i
      have hi : ((t i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)) =
          ((s i : Set.powersetCard (Fin n) (bdeg ε i)) : Finset (Fin n)).map
            (π i.1).toEmbedding := by
        simpa [bPerm] using congrArg Subtype.val (congrFun h i)
      rw [hi]
      simp [Finset.map_map]
  rw [if_congr hcond rfl rfl, Pi.single_apply]

theorem single_bPerm_btop_mem_bCyc [CharP k 2] (ε : τ → Finset (Fin n))
    (π : τ → Equiv.Perm (Fin n)) : Pi.single (bPerm ε π (btop ε)) (1 : k) ∈ bCyc ε := by
  have h := bMat_mulVec_mem_bCyc (k := k) ε (fun r => permSL ((π r)⁻¹))
    (bvec_mem_bCyc (k := k) ε)
  have hmat : (fun r => ((permSL ((π r)⁻¹) : Matrix.SpecialLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k)) = fun r => ((π r)⁻¹).permMatrix k := by
    funext r
    rfl
  rw [hmat] at h
  change bMat ε (fun r => ((π r)⁻¹).permMatrix k) *ᵥ Pi.single (btop ε) (1 : k) ∈ bCyc ε at h
  rw [bMat_permMatrix_mulVec_single ε π (btop ε)] at h
  exact h

theorem notMem_bRad_of_dotProduct_ne_zero (ε : τ → Finset (Fin n)) {x y : BIdx ε → k}
    (hy : y ∈ bCyc ε) (hxy : x ⬝ᵥ y ≠ 0) : x ∉ bRad ε := by
  intro hx
  exact hxy ((mem_dotRad.mp hx).2 y hy)

theorem single_notMem_bRad (ε : τ → Finset (Fin n)) {s : BIdx ε}
    (hs : Pi.single s (1 : k) ∈ bCyc ε) : Pi.single s (1 : k) ∉ bRad ε := by
  apply notMem_bRad_of_dotProduct_ne_zero ε hs
  rw [single_one_dotProduct, Pi.single_eq_same]
  exact one_ne_zero

theorem notMem_bRad_of_bDer_mulVec_notMem (ε : τ → Finset (Fin n))
    (b : τ × Fin n × Fin n) {x : BIdx ε → k} (hx : bDer ε b *ᵥ x ∉ bRad ε) :
    x ∉ bRad ε := by
  intro hxmem
  exact hx (bDer_mulVec_mem_bRad ε b hxmem)

theorem bMat_mulVec_notMem_bRad [CharP k 2] (ε : τ → Finset (Fin n))
    (h : τ → Matrix.SpecialLinearGroup (Fin n) k) {x : BIdx ε → k} (hx : x ∉ bRad ε) :
    bMat ε (fun r => (h r : Matrix (Fin n) (Fin n) k)) *ᵥ x ∉ bRad ε := by
  intro hy
  let hinv : τ → Matrix (Fin n) (Fin n) k := fun r => ((h r)⁻¹).val
  have hcoef : (fun r => hinv r * (h r).val) = fun _ => (1 : Matrix (Fin n) (Fin n) k) := by
    funext r
    change (((h r)⁻¹ * h r : Matrix.SpecialLinearGroup (Fin n) k)).val =
      (1 : Matrix (Fin n) (Fin n) k)
    rw [inv_mul_cancel]
    rfl
  have hx' : bMat ε hinv *ᵥ
      (bMat ε (fun r => (h r).val) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← bMat_mul, hcoef, bMat_one, Matrix.one_mulVec]
  have hmem : bMat ε hinv *ᵥ
      (bMat ε (fun r => (h r).val) *ᵥ x) ∈ bRad ε :=
    bMat_mulVec_mem_bRad ε (fun r => (h r)⁻¹) hy
  rw [hx'] at hmem
  exact hx hmem

theorem mk_eq_zero_iff (ε : τ → Finset (Fin n)) (w : bCyc (k := k) ε) :
    (Submodule.Quotient.mk w : BModel k ε) = 0 ↔ (w : BIdx ε → k) ∈ bRad ε := by
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem homComp_eq_self_of_forall_apply_ne_zero {Γ : Type*} [DecidableEq Γ] {I : Type*}
    {deg : I → Γ} {e : Γ} {w : I → k} (hw : ∀ i, w i ≠ 0 → deg i = e) :
    homComp deg e w = w := by
  funext i
  by_cases hi : w i = 0
  · simp [homComp, hi]
  · rw [homComp, if_pos (hw i hi)]

theorem homComp_eq_zero_of_forall_apply_ne_zero_ne {Γ : Type*} [DecidableEq Γ] {I : Type*}
    {deg : I → Γ} {e : Γ} {w : I → k} (hw : ∀ i, w i ≠ 0 → deg i ≠ e) :
    homComp deg e w = 0 := by
  funext i
  by_cases hi : w i = 0
  · simp [homComp, hi]
  · rw [homComp, if_neg (hw i hi)]
    rfl

theorem linearIndependent_mk_of_bWt (ε : τ → Finset (Fin n)) {ι : Type*} (v : ι → bCyc (k := k) ε)
    (wt : ι → (τ → Fin n → ℤ)) (hwt : Function.Injective wt)
    (hhom : ∀ i s, (v i : BIdx ε → k) s ≠ 0 → bWt ε s = wt i) (hv : ∀ i, (v i : BIdx ε → k) ∉ bRad ε) :
    LinearIndependent k (fun i => (Submodule.Quotient.mk (v i) : BModel k ε)) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  let p : Submodule k (bCyc (k := k) ε) := (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype
  have hq : p.mkQ (∑ j ∈ s, g j • v j) = 0 := by
    rw [map_sum]
    simp only [map_smul, Submodule.mkQ_apply]
    exact hsum
  have hmem_p : (∑ j ∈ s, g j • v j : bCyc (k := k) ε) ∈ p := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact hq
  have hmem : (↑(∑ j ∈ s, g j • v j : bCyc (k := k) ε) : BIdx ε → k) ∈ bRad ε :=
    hmem_p
  have hsum_coe : (↑(∑ j ∈ s, g j • v j : bCyc (k := k) ε) : BIdx ε → k) =
      ∑ j ∈ s, g j • (v j : BIdx ε → k) := by
    simp
  have hcomp_mem : homComp (bWt ε) (wt i)
      (∑ j ∈ s, g j • (v j : BIdx ε → k)) ∈ bRad ε := by
    rw [← hsum_coe]
    exact homComp_bWt_mem_bRad ε hmem (wt i)
  have hcomp_eq : homComp (bWt ε) (wt i)
      (∑ j ∈ s, g j • (v j : BIdx ε → k)) = g i • (v i : BIdx ε → k) := by
    rw [← homCompLin_apply]
    simp only [map_sum, map_smul, homCompLin_apply]
    rw [Finset.sum_eq_single i]
    · rw [homComp_eq_self_of_forall_apply_ne_zero (fun s hs => hhom i s hs)]
    · intro j hj hji
      have hne : wt j ≠ wt i := fun h => hji (hwt h)
      rw [homComp_eq_zero_of_forall_apply_ne_zero_ne (fun s hs => by
        rw [hhom j s hs]
        exact hne)]
      simp
    · intro hi_not
      exact absurd hi hi_not
  have hsmul_mem : g i • (v i : BIdx ε → k) ∈ bRad ε := by
    rw [← hcomp_eq]
    exact hcomp_mem
  by_contra hgi
  exact hv i ((Submodule.smul_mem_iff (p := bRad ε) hgi).mp hsmul_mem)

theorem exists_apply_mulVec_ne_zero {β : Type*} [Fintype β] {A : Matrix β β k}
    {v : β → k} {i : β} (h : (A *ᵥ v) i ≠ 0) : ∃ j, A i j ≠ 0 ∧ v j ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero fun j _ => by
    by_cases h0 : A i j = 0
    · rw [h0, zero_mul]
    · rw [hc j h0, mul_zero]

theorem bWt_of_bDer_mulVec_ne_zero (ε : τ → Finset (Fin n)) (x : τ × Fin n × Fin n)
    {v : BIdx ε → k} {w : τ → Fin n → ℤ} (hv : ∀ s, v s ≠ 0 → bWt ε s = w)
    {s : BIdx ε} (h : (bDer (k := k) ε x *ᵥ v) s ≠ 0) :
    bWt ε s = w + Pi.single x.1 (Pi.single x.2.1 1 - Pi.single x.2.2 1) := by
  have hsum : (bDer (k := k) ε x *ᵥ v) s = ∑ t, bDer (k := k) ε x s t * v t := rfl
  rw [hsum] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 : bDer (k := k) ε x s t ≠ 0 := fun hz => ht (by rw [hz, zero_mul])
  have h2 : v t ≠ 0 := fun hz => ht (by rw [hz, mul_zero])
  rw [bWt_of_bDer_ne_zero ε x h1, hv t h2]

omit [DecidableEq τ] in
theorem bWt_bvec_apply_ne_zero (ε : τ → Finset (Fin n)) {s : BIdx ε}
    (hs : bvec (k := k) ε s ≠ 0) : bWt ε s = bWt ε (btop ε) := by
  have hst : s = btop ε := by
    by_contra hne
    exact hs (by simp [bvec, hne])
  rw [hst]

omit [Fintype τ] [DecidableEq τ] in
theorem mem_btop_iff (ε : τ → Finset (Fin n)) (p : τ × Fin n) (a : Fin n) :
    a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) ↔
      (a : ℕ) < bdeg ε p := by
  simp [btop, ktop, mem_initSeg]

theorem bDer_mulVec_single_eq_single_update [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ)
    {a b j : Fin n} (hab : a ≠ b) (t : BIdx ε)
    (hb : b ∈ ((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)))
    (ha : a ∉ ((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)))
    (huniq : ∀ p : τ × Fin n, p.1 = r →
      b ∈ ((t p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      a ∉ ((t p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, j))
    (s0 : Set.powersetCard (Fin n) (bdeg ε (r, j)))
    (hs0 : (s0 : Finset (Fin n)) =
      insert a (((t (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)).erase b)) :
    bDer (k := k) ε (r, a, b) *ᵥ (Pi.single t (1 : k)) =
      (Pi.single (Function.update t (r, j) s0) (1 : k) : BIdx ε → k) := by
  have h2 : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  rw [Matrix.mulVec_single_one]
  funext s
  rw [Matrix.col_apply]
  change kronDer (d := bdeg ε) (fun p : τ × Fin n => p.1 = r)
    (Matrix.single a b (1 : k)) s t =
      ((Pi.single (Function.update t (r, j) s0) (1 : k) : BIdx ε → k) s)
  rw [kronDer_single_apply (R := k) h2 (P := fun p : τ × Fin n => p.1 = r) hab]
  by_cases hs : s = Function.update t (r, j) s0
  · rw [if_pos ?_]
    · rw [hs, Pi.single_eq_same]
    refine ⟨(r, j), rfl, ?_, hb, ha, ?_⟩
    · intro q hq
      rw [hs, Function.update_of_ne hq]
    · have hsj : s (r, j) = s0 := by rw [hs]; exact Function.update_self _ _ _
      exact (congrArg Subtype.val hsj).trans hs0
  · rw [if_neg ?_, Pi.single_apply, if_neg hs]
    intro hcond
    obtain ⟨i, hiP, hist, hbi, hai, hsi⟩ := hcond
    have hii : i = (r, j) := huniq i hiP hbi hai
    apply hs
    subst hii
    funext q
    by_cases hq : q = (r, j)
    · subst hq
      rw [Function.update_self]
      exact Subtype.ext (hsi.trans hs0.symm)
    · rw [Function.update_of_ne hq]
      exact hist q hq

def replaceSubset {n d : ℕ} (t : Set.powersetCard (Fin n) d) (a b : Fin n)
    (hb : b ∈ (t : Finset (Fin n))) (ha : a ∉ (t : Finset (Fin n))) :
    Set.powersetCard (Fin n) d :=
  ⟨insert a ((t : Finset (Fin n)).erase b), by
    rw [Set.powersetCard.mem_iff, Finset.card_insert_of_notMem, Finset.card_erase_of_mem hb]
    · have hpos : 0 < d := by
        rw [← t.2]
        exact Finset.card_pos.mpr ⟨b, hb⟩
      rw [t.2]
      omega
    · exact fun h => ha (Finset.mem_of_mem_erase h)⟩

theorem bDer_bDer_bvec_mem_bCyc (ε : τ → Finset (Fin n)) (r : τ) (hn : 3 ≤ n)
    (_h1 : (⟨1, by omega⟩ : Fin n) ∈ ε r) (_h2 : (⟨2, by omega⟩ : Fin n) ∈ ε r) :
    bDer (k := k) ε (r, ⟨2, by omega⟩, ⟨1, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨1, by omega⟩, ⟨0, by omega⟩) *ᵥ bvec (k := k) ε) ∈ bCyc (k := k) ε := by
  exact mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
    (r, ⟨2, by omega⟩, ⟨1, by omega⟩)
    (mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
      (r, ⟨1, by omega⟩, ⟨0, by omega⟩) (bvec_mem_bCyc (k := k) ε))

theorem bDer_bDer_bvec_notMem_bRad [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ) (hn : 3 ≤ n)
    (h1 : (⟨1, by omega⟩ : Fin n) ∈ ε r) (h2 : (⟨2, by omega⟩ : Fin n) ∈ ε r) :
    bDer (k := k) ε (r, ⟨2, by omega⟩, ⟨1, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨1, by omega⟩, ⟨0, by omega⟩) *ᵥ bvec (k := k) ε) ∉ bRad (k := k) ε := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let D10 := bDer (k := k) ε (r, i1, i0)
  let D21 := bDer (k := k) ε (r, i2, i1)
  let D01 := bDer (k := k) ε (r, i0, i1)
  let D00 := bDer (k := k) ε (r, i0, i0)
  let D11 := bDer (k := k) ε (r, i1, i1)
  have hb10 : i0 ∈ ((btop ε (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h1, i0, i1]
  have ha10 : i1 ∉ ((btop ε (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h1, i1]
  have huniq10 : ∀ p : τ × Fin n, p.1 = r →
      i0 ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      i1 ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, i1) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    have hb' : (i0 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) i0).mp hb
    have ha' : ¬ (i1 : ℕ) < bdeg ε (r, k) := fun hh =>
      ha ((mem_btop_iff ε (r, k) i1).mpr hh)
    by_cases hk : k ∈ ε r
    · have hb'' : (0 : ℕ) < (k : ℕ) := by simpa [bdeg, hk, i0] using hb'
      have ha'' : ¬ (1 : ℕ) < (k : ℕ) := by simpa [bdeg, hk, i1] using ha'
      have hk1 : (k : ℕ) = 1 := by omega
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [i1] using hk1
    · simp [bdeg, hk] at hb'
  have hb21 : i1 ∈ ((btop ε (r, i2) : Set.powersetCard (Fin n) (bdeg ε (r, i2))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h2, i1, i2]
  have ha21 : i2 ∉ ((btop ε (r, i2) : Set.powersetCard (Fin n) (bdeg ε (r, i2))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h2, i2]
  have huniq21 : ∀ p : τ × Fin n, p.1 = r →
      i1 ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      i2 ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, i2) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    have hb' : (i1 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) i1).mp hb
    have ha' : ¬ (i2 : ℕ) < bdeg ε (r, k) := fun hh =>
      ha ((mem_btop_iff ε (r, k) i2).mpr hh)
    by_cases hk : k ∈ ε r
    · have hb'' : (1 : ℕ) < (k : ℕ) := by simpa [bdeg, hk, i1] using hb'
      have ha'' : ¬ (2 : ℕ) < (k : ℕ) := by simpa [bdeg, hk, i2] using ha'
      have hk2 : (k : ℕ) = 2 := by omega
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [i2] using hk2
    · simp [bdeg, hk] at hb'
  have hbtop10 : ((btop ε (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) = {i0} := by
    ext a
    rw [mem_btop_iff, Finset.mem_singleton]
    constructor
    · intro ha
      have ha' : (a : ℕ) < 1 := by simpa [bdeg, h1, i1] using ha
      apply Fin.ext
      simp [i0]
      omega
    · intro ha
      rw [ha]
      simp [bdeg, h1, i0, i1]
  let s10 : Set.powersetCard (Fin n) (bdeg ε (r, i1)) := ⟨{i1}, by simp [bdeg, h1, i1]⟩
  have hs10 : (s10 : Finset (Fin n)) =
      insert i1 (((btop ε (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
        Finset (Fin n)).erase i0) := by
    dsimp [s10]
    rw [hbtop10]
    simp [i0, i1]
  let u : BIdx ε := Function.update (btop ε) (r, i1) s10
  have hu11 : u (r, i1) = s10 := by
    dsimp [u]
    exact Function.update_self _ _ _
  have hD10 : D10 *ᵥ bvec (k := k) ε = Pi.single u (1 : k) := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := i1) (b := i0) (j := i1)
      (by simp [i0, i1]) (btop ε) hb10 ha10 huniq10 s10 hs10
    simpa [bvec, u, D10] using h
  have hb01u : i1 ∈ ((u (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) := by
    simp [u, s10]
  have ha01u : i0 ∉ ((u (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) := by
    simp [u, s10, i0, i1]
  have huniq01 : ∀ p : τ × Fin n, p.1 = r →
      i1 ∈ ((u p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      i0 ∉ ((u p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, i1) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    by_cases hk : (r, k) = (r, i1)
    · exact hk
    · have hku : u (r, k) = btop ε (r, k) := by
        dsimp [u]
        rw [Function.update_of_ne hk]
      rw [hku] at hb ha
      have hb' : (i1 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) i1).mp hb
      have ha' : ¬ (i0 : ℕ) < bdeg ε (r, k) := fun hh =>
        ha ((mem_btop_iff ε (r, k) i0).mpr hh)
      by_cases hkε : k ∈ ε r
      · simp [bdeg, hkε, i0, i1] at hb' ha'
        omega
      · simp [bdeg, hkε] at hb'
  have hs01 : ((btop ε (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
      Finset (Fin n)) =
      insert i0 (((u (r, i1) : Set.powersetCard (Fin n) (bdeg ε (r, i1))) :
        Finset (Fin n)).erase i1) := by
    rw [hbtop10, hu11]
    dsimp [s10]
    simp [i0, i1]
  have hD01u : D01 *ᵥ (Pi.single u (1 : k)) = bvec (k := k) ε := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := i0) (b := i1) (j := i1)
      (by simp [i0, i1]) u hb01u ha01u huniq01 (btop ε (r, i1)) hs01
    have hupd : Function.update u (r, i1) (btop ε (r, i1)) = btop ε := by
      funext p
      by_cases hp : p = (r, i1)
      · subst hp
        rw [Function.update_self]
      · rw [Function.update_of_ne hp]
        dsimp [u]
        rw [Function.update_of_ne hp]
    simpa [bvec, D01, hupd] using h
  have hbtop21 : ((btop ε (r, i2) : Set.powersetCard (Fin n) (bdeg ε (r, i2))) :
      Finset (Fin n)) = {i0, i1} := by
    ext a
    rw [mem_btop_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ha
      have ha' : (a : ℕ) < 2 := by simpa [bdeg, h2, i2] using ha
      have : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
      rcases this with h | h
      · left
        apply Fin.ext
        simpa [i0] using h
      · right
        apply Fin.ext
        simpa [i1] using h
    · rintro (ha | ha)
      · rw [ha]
        simp [bdeg, h2, i0, i2]
      · rw [ha]
        simp [bdeg, h2, i1, i2]
  let s21 : Set.powersetCard (Fin n) (bdeg ε (r, i2)) := ⟨{i0, i2}, by
    rw [show bdeg ε (r, i2) = 2 by simp [bdeg, h2, i2]]
    exact Finset.card_pair (by intro h; have := congrArg Fin.val h; simp [i0, i2] at this)⟩
  have hs21 : (s21 : Finset (Fin n)) =
      insert i2 (((btop ε (r, i2) : Set.powersetCard (Fin n) (bdeg ε (r, i2))) :
        Finset (Fin n)).erase i1) := by
    dsimp [s21]
    rw [hbtop21]
    have h01 : i0 ≠ i1 := by simp [i0, i1]
    have h12 : i1 ≠ i2 := by simp [i1, i2]
    ext a
    simp [i0, i1, i2]
    constructor
    · rintro (h | h)
      · right
        refine ⟨?_, Or.inl h⟩
        intro ha
        exact h01 (h.symm.trans ha)
      · left
        exact h
    · rintro (h | ⟨hne, h | h⟩)
      · right
        exact h
      · left
        exact h
      · exact absurd h hne
  let c : BIdx ε := Function.update (btop ε) (r, i2) s21
  have hD21 : D21 *ᵥ bvec (k := k) ε = Pi.single c (1 : k) := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := i2) (b := i1) (j := i2)
      (by simp [i1, i2]) (btop ε) hb21 ha21 huniq21 s21 hs21
    simpa [bvec, c, D21] using h
  have hmat0 : Matrix.single i0 i1 (1 : k) * Matrix.single i2 i1 1 -
      Matrix.single i2 i1 1 * Matrix.single i0 i1 1 = 0 := by
    simp [i0, i1, i2]
  have hcomm2 : D01 * D21 = D21 * D01 := by
    have h := kronDer_mul_sub_mul (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single i0 i1 (1 : k)) (Matrix.single i2 i1 1)
    rw [hmat0, kronDer_zero, sub_eq_zero] at h
    simpa [bDer, D01, D21] using h
  have hmat1 : Matrix.single i0 i1 (1 : k) * Matrix.single i1 i0 1 -
      Matrix.single i1 i0 1 * Matrix.single i0 i1 1 =
      Matrix.single i0 i0 1 - Matrix.single i1 i1 1 := by
    simp [i0, i1]
  have hsub : kronDer (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single i0 i0 1 - Matrix.single i1 i1 1) = D00 - D11 := by
    have hlin := (kronDerLin (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)).map_sub
      (Matrix.single i0 i0 (1 : k)) (Matrix.single i1 i1 1)
    simpa [kronDerLin, bDer, D00, D11] using hlin
  have hcomm : D01 * D10 - D10 * D01 = D00 - D11 := by
    have h := kronDer_mul_sub_mul (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single i0 i1 (1 : k)) (Matrix.single i1 i0 1)
    rw [hmat1, hsub] at h
    simpa [bDer, D01, D10, D00, D11] using h
  have hD01bvec : D01 *ᵥ bvec (k := k) ε = 0 := by
    simpa [D01] using bDer_mulVec_bvec_of_lt (k := k) ε r (a := i0) (b := i1)
      (by simp [i0, i1])
  have hD01D10 : (D01 * D10) *ᵥ bvec (k := k) ε = bvec (k := k) ε := by
    rw [← Matrix.mulVec_mulVec, hD10]
    exact hD01u
  have hcomm' : D01 * D10 = D10 * D01 + (D00 - D11) := by
    rw [← hcomm]
    abel_nf
  have hcartan : (D00 - D11) *ᵥ bvec (k := k) ε = bvec (k := k) ε := by
    have h := congrArg (fun M : Matrix (BIdx ε) (BIdx ε) k => M *ᵥ bvec (k := k) ε) hcomm'
    rw [hD01D10] at h
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hD01bvec, Matrix.mulVec_zero] at h
    simpa using h.symm
  let x := D21 *ᵥ (D10 *ᵥ bvec (k := k) ε)
  change x ∉ bRad (k := k) ε
  have hD01x : D01 *ᵥ x = D21 *ᵥ bvec (k := k) ε := by
    calc D01 *ᵥ x
        = D01 *ᵥ (D21 *ᵥ (D10 *ᵥ bvec (k := k) ε)) := rfl
      _ = (D01 * D21) *ᵥ (D10 *ᵥ bvec (k := k) ε) := by rw [Matrix.mulVec_mulVec]
      _ = (D21 * D01) *ᵥ (D10 *ᵥ bvec (k := k) ε) := by rw [hcomm2]
      _ = D21 *ᵥ ((D01 * D10) *ᵥ bvec (k := k) ε) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = D21 *ᵥ bvec (k := k) ε := by rw [hD01D10]
  have hc_mem : Pi.single c (1 : k) ∈ bCyc (k := k) ε := by
    rw [← hD21]
    exact mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
      (r, i2, i1) (bvec_mem_bCyc (k := k) ε)
  intro hxmem
  have hD01x_mem : D01 *ᵥ x ∈ bRad (k := k) ε :=
    bDer_mulVec_mem_bRad ε (r, i0, i1) hxmem
  rw [hD01x, hD21] at hD01x_mem
  exact single_notMem_bRad ε hc_mem hD01x_mem

theorem bWt_of_bDer_bDer_bvec_ne_zero [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ) (hn : 3 ≤ n)
    (_h1 : (⟨1, by omega⟩ : Fin n) ∈ ε r) (_h2 : (⟨2, by omega⟩ : Fin n) ∈ ε r)
    {s : BIdx ε}
    (h : (bDer (k := k) ε (r, ⟨2, by omega⟩, ⟨1, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨1, by omega⟩, ⟨0, by omega⟩) *ᵥ bvec (k := k) ε)) s ≠ 0) :
    bWt ε s = bWt ε (btop ε) +
      Pi.single r (Pi.single ⟨2, by omega⟩ (1 : ℤ) - Pi.single ⟨0, by omega⟩ 1) := by
  have hbvec : ∀ u : BIdx ε, bvec (k := k) ε u ≠ 0 → bWt ε u = bWt ε (btop ε) :=
    fun u hu => bWt_bvec_apply_ne_zero ε hu
  have hwt1 : ∀ u : BIdx ε,
      (bDer (k := k) ε (r, ⟨1, by omega⟩, ⟨0, by omega⟩) *ᵥ bvec (k := k) ε) u ≠ 0 →
      bWt ε u = bWt ε (btop ε) +
        Pi.single r (Pi.single ⟨1, by omega⟩ 1 - Pi.single ⟨0, by omega⟩ 1) :=
    fun u hu => bWt_of_bDer_mulVec_ne_zero ε (r, ⟨1, by omega⟩, ⟨0, by omega⟩) hbvec hu
  rw [bWt_of_bDer_mulVec_ne_zero ε (r, ⟨2, by omega⟩, ⟨1, by omega⟩) hwt1 h,
    add_assoc, ← Pi.single_add]
  congr 1
  abel_nf

theorem bDer_bDer_bvec_mem_bCyc_last (ε : τ → Finset (Fin n)) (r : τ) (hn : 3 ≤ n)
    (_h1 : (⟨n - 2, by omega⟩ : Fin n) ∈ ε r) (_h2 : (⟨n - 1, by omega⟩ : Fin n) ∈ ε r) :
    bDer (k := k) ε (r, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) *ᵥ bvec (k := k) ε) ∈ bCyc (k := k) ε := by
  exact mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
    (r, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩)
    (mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
      (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) (bvec_mem_bCyc (k := k) ε))

theorem bDer_bDer_bvec_notMem_bRad_last [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ) (hn : 3 ≤ n)
    (h1 : (⟨n - 2, by omega⟩ : Fin n) ∈ ε r) (h2 : (⟨n - 1, by omega⟩ : Fin n) ∈ ε r) :
    bDer (k := k) ε (r, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) *ᵥ bvec (k := k) ε) ∉ bRad (k := k) ε := by
  let j0 : Fin n := ⟨n - 3, by omega⟩
  let j1 : Fin n := ⟨n - 2, by omega⟩
  let j2 : Fin n := ⟨n - 1, by omega⟩
  let D10 := bDer (k := k) ε (r, j1, j0)
  let D21 := bDer (k := k) ε (r, j2, j1)
  let D01 := bDer (k := k) ε (r, j0, j1)
  let D00 := bDer (k := k) ε (r, j0, j0)
  let D11 := bDer (k := k) ε (r, j1, j1)
  have hj01 : (j0 : ℕ) + 1 = (j1 : ℕ) := by simp [j0, j1]; omega
  have hj12 : (j1 : ℕ) + 1 = (j2 : ℕ) := by simp [j1, j2]; omega
  have hj01lt : j0 < j1 := by rw [Fin.lt_def]; omega
  have hj12lt : j1 < j2 := by rw [Fin.lt_def]; omega
  have hj01ne : j0 ≠ j1 := ne_of_lt hj01lt
  have hj12ne : j1 ≠ j2 := ne_of_lt hj12lt
  have hb10 : j0 ∈ ((btop ε (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h1, j0, j1]
    omega
  have ha10 : j1 ∉ ((btop ε (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h1, j1]
  have huniq10 : ∀ p : τ × Fin n, p.1 = r →
      j0 ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      j1 ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, j1) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    have hb' : (j0 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) j0).mp hb
    have ha' : ¬ (j1 : ℕ) < bdeg ε (r, k) := fun hh =>
      ha ((mem_btop_iff ε (r, k) j1).mpr hh)
    by_cases hk : k ∈ ε r
    · have hb'' : (j0 : ℕ) < (k : ℕ) := by simpa [bdeg, hk] using hb'
      have ha'' : ¬ (j1 : ℕ) < (k : ℕ) := by simpa [bdeg, hk] using ha'
      have hk1 : (k : ℕ) = (j1 : ℕ) := by omega
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [j1] using hk1
    · simp [bdeg, hk] at hb'
  have hb21 : j1 ∈ ((btop ε (r, j2) : Set.powersetCard (Fin n) (bdeg ε (r, j2))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h2, j1, j2]
    omega
  have ha21 : j2 ∉ ((btop ε (r, j2) : Set.powersetCard (Fin n) (bdeg ε (r, j2))) :
      Finset (Fin n)) := by
    rw [mem_btop_iff]
    simp [bdeg, h2, j2]
  have huniq21 : ∀ p : τ × Fin n, p.1 = r →
      j1 ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      j2 ∉ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, j2) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    have hb' : (j1 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) j1).mp hb
    have ha' : ¬ (j2 : ℕ) < bdeg ε (r, k) := fun hh =>
      ha ((mem_btop_iff ε (r, k) j2).mpr hh)
    by_cases hk : k ∈ ε r
    · have hb'' : (j1 : ℕ) < (k : ℕ) := by simpa [bdeg, hk] using hb'
      have ha'' : ¬ (j2 : ℕ) < (k : ℕ) := by simpa [bdeg, hk] using ha'
      have hk2 : (k : ℕ) = (j2 : ℕ) := by omega
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [j2] using hk2
    · simp [bdeg, hk] at hb'
  let s10 : Set.powersetCard (Fin n) (bdeg ε (r, j1)) :=
    replaceSubset (btop ε (r, j1)) j1 j0 hb10 ha10
  have hs10 : (s10 : Finset (Fin n)) =
      insert j1 (((btop ε (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
        Finset (Fin n)).erase j0) := rfl
  let u : BIdx ε := Function.update (btop ε) (r, j1) s10
  have hu11 : u (r, j1) = s10 := by
    dsimp [u]
    exact Function.update_self _ _ _
  have hD10 : D10 *ᵥ bvec (k := k) ε = Pi.single u (1 : k) := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := j1) (b := j0) (j := j1)
      hj01ne.symm (btop ε) hb10 ha10 huniq10 s10 hs10
    simpa [bvec, u, D10] using h
  have hb01u : j1 ∈ ((u (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
      Finset (Fin n)) := by
    simp [u, s10, replaceSubset]
  have ha01u : j0 ∉ ((u (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
      Finset (Fin n)) := by
    simp [u, s10, replaceSubset, j0, j1]
    omega
  have huniq01 : ∀ p : τ × Fin n, p.1 = r →
      j1 ∈ ((u p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) →
      j0 ∉ ((u p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) → p = (r, j1) := by
    rintro ⟨r', k⟩ hr' hb ha
    simp only at hr'
    subst r'
    by_cases hk : (r, k) = (r, j1)
    · exact hk
    · have hku : u (r, k) = btop ε (r, k) := by
        dsimp [u]
        rw [Function.update_of_ne hk]
      rw [hku] at hb ha
      have hb' : (j1 : ℕ) < bdeg ε (r, k) := (mem_btop_iff ε (r, k) j1).mp hb
      have ha' : ¬ (j0 : ℕ) < bdeg ε (r, k) := fun hh =>
        ha ((mem_btop_iff ε (r, k) j0).mpr hh)
      by_cases hkε : k ∈ ε r
      · simp [bdeg, hkε, j0, j1] at hb' ha'
        omega
      · simp [bdeg, hkε] at hb'
  have hs01 : ((btop ε (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
      Finset (Fin n)) =
      insert j0 (((u (r, j1) : Set.powersetCard (Fin n) (bdeg ε (r, j1))) :
        Finset (Fin n)).erase j1) := by
    rw [hu11]
    dsimp [s10, replaceSubset]
    rw [Finset.erase_insert]
    · exact (Finset.insert_erase hb10).symm
    · exact fun h => ha10 (Finset.mem_of_mem_erase h)
  have hD01u : D01 *ᵥ (Pi.single u (1 : k)) = bvec (k := k) ε := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := j0) (b := j1) (j := j1)
      hj01ne u hb01u ha01u huniq01 (btop ε (r, j1)) hs01
    have hupd : Function.update u (r, j1) (btop ε (r, j1)) = btop ε := by
      funext p
      by_cases hp : p = (r, j1)
      · subst hp
        rw [Function.update_self]
      · rw [Function.update_of_ne hp]
        dsimp [u]
        rw [Function.update_of_ne hp]
    simpa [bvec, D01, hupd] using h
  let s21 : Set.powersetCard (Fin n) (bdeg ε (r, j2)) :=
    replaceSubset (btop ε (r, j2)) j2 j1 hb21 ha21
  have hs21 : (s21 : Finset (Fin n)) =
      insert j2 (((btop ε (r, j2) : Set.powersetCard (Fin n) (bdeg ε (r, j2))) :
        Finset (Fin n)).erase j1) := rfl
  let c : BIdx ε := Function.update (btop ε) (r, j2) s21
  have hD21 : D21 *ᵥ bvec (k := k) ε = Pi.single c (1 : k) := by
    have h := bDer_mulVec_single_eq_single_update (k := k) ε r (a := j2) (b := j1) (j := j2)
      hj12ne.symm (btop ε) hb21 ha21 huniq21 s21 hs21
    simpa [bvec, c, D21] using h
  have hmat0 : Matrix.single j0 j1 (1 : k) * Matrix.single j2 j1 1 -
      Matrix.single j2 j1 1 * Matrix.single j0 j1 1 = 0 := by
    rw [Matrix.single_mul_single_of_ne (i := j0) (j := j1) (k := j2) (h := hj12ne),
      Matrix.single_mul_single_of_ne (i := j2) (j := j1) (k := j0) (h := hj01ne.symm)]
    simp
  have hcomm2 : D01 * D21 = D21 * D01 := by
    have h := kronDer_mul_sub_mul (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single j0 j1 (1 : k)) (Matrix.single j2 j1 1)
    rw [hmat0, kronDer_zero, sub_eq_zero] at h
    simpa [bDer, D01, D21] using h
  have hmat1 : Matrix.single j0 j1 (1 : k) * Matrix.single j1 j0 1 -
      Matrix.single j1 j0 1 * Matrix.single j0 j1 1 =
      Matrix.single j0 j0 1 - Matrix.single j1 j1 1 := by
    simp [j0, j1]
  have hsub : kronDer (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single j0 j0 1 - Matrix.single j1 j1 1) = D00 - D11 := by
    have hlin := (kronDerLin (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)).map_sub
      (Matrix.single j0 j0 (1 : k)) (Matrix.single j1 j1 1)
    simpa [kronDerLin, bDer, D00, D11] using hlin
  have hcomm : D01 * D10 - D10 * D01 = D00 - D11 := by
    have h := kronDer_mul_sub_mul (d := bdeg ε) (P := fun p : τ × Fin n => p.1 = r)
      (Matrix.single j0 j1 (1 : k)) (Matrix.single j1 j0 1)
    rw [hmat1, hsub] at h
    simpa [bDer, D01, D10, D00, D11] using h
  have hD01bvec : D01 *ᵥ bvec (k := k) ε = 0 := by
    simpa [D01] using bDer_mulVec_bvec_of_lt (k := k) ε r (a := j0) (b := j1) hj01lt
  have hD01D10 : (D01 * D10) *ᵥ bvec (k := k) ε = bvec (k := k) ε := by
    rw [← Matrix.mulVec_mulVec, hD10]
    exact hD01u
  have hcomm' : D01 * D10 = D10 * D01 + (D00 - D11) := by
    rw [← hcomm]
    abel_nf
  have hcartan : (D00 - D11) *ᵥ bvec (k := k) ε = bvec (k := k) ε := by
    have h := congrArg (fun M : Matrix (BIdx ε) (BIdx ε) k => M *ᵥ bvec (k := k) ε) hcomm'
    rw [hD01D10] at h
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hD01bvec, Matrix.mulVec_zero] at h
    simpa using h.symm
  let x := D21 *ᵥ (D10 *ᵥ bvec (k := k) ε)
  change x ∉ bRad (k := k) ε
  have hD01x : D01 *ᵥ x = D21 *ᵥ bvec (k := k) ε := by
    calc D01 *ᵥ x
        = D01 *ᵥ (D21 *ᵥ (D10 *ᵥ bvec (k := k) ε)) := rfl
      _ = (D01 * D21) *ᵥ (D10 *ᵥ bvec (k := k) ε) := by rw [Matrix.mulVec_mulVec]
      _ = (D21 * D01) *ᵥ (D10 *ᵥ bvec (k := k) ε) := by rw [hcomm2]
      _ = D21 *ᵥ ((D01 * D10) *ᵥ bvec (k := k) ε) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = D21 *ᵥ bvec (k := k) ε := by rw [hD01D10]
  have hc_mem : Pi.single c (1 : k) ∈ bCyc (k := k) ε := by
    rw [← hD21]
    exact mulVec_mem_cyclicSub (D := bDer (k := k) ε) (v := bvec (k := k) ε)
      (r, j2, j1) (bvec_mem_bCyc (k := k) ε)
  intro hxmem
  have hD01x_mem : D01 *ᵥ x ∈ bRad (k := k) ε :=
    bDer_mulVec_mem_bRad ε (r, j0, j1) hxmem
  rw [hD01x, hD21] at hD01x_mem
  exact single_notMem_bRad ε hc_mem hD01x_mem

theorem bWt_of_bDer_bDer_bvec_ne_zero_last [CharP k 2] (ε : τ → Finset (Fin n)) (r : τ)
    (hn : 3 ≤ n) (_h1 : (⟨n - 2, by omega⟩ : Fin n) ∈ ε r)
    (_h2 : (⟨n - 1, by omega⟩ : Fin n) ∈ ε r) {s : BIdx ε}
    (h : (bDer (k := k) ε (r, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) *ᵥ
      (bDer (k := k) ε (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) *ᵥ bvec (k := k) ε)) s ≠ 0) :
    bWt ε s = bWt ε (btop ε) +
      Pi.single r (Pi.single ⟨n - 1, by omega⟩ (1 : ℤ) - Pi.single ⟨n - 3, by omega⟩ 1) := by
  have hbvec : ∀ u : BIdx ε, bvec (k := k) ε u ≠ 0 → bWt ε u = bWt ε (btop ε) :=
    fun u hu => bWt_bvec_apply_ne_zero ε hu
  have hwt1 : ∀ u : BIdx ε,
      (bDer (k := k) ε (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) *ᵥ
        bvec (k := k) ε) u ≠ 0 →
      bWt ε u = bWt ε (btop ε) +
        Pi.single r (Pi.single ⟨n - 2, by omega⟩ 1 - Pi.single ⟨n - 3, by omega⟩ 1) :=
    fun u hu => bWt_of_bDer_mulVec_ne_zero ε (r, ⟨n - 2, by omega⟩, ⟨n - 3, by omega⟩) hbvec hu
  rw [bWt_of_bDer_mulVec_ne_zero ε (r, ⟨n - 1, by omega⟩, ⟨n - 2, by omega⟩) hwt1 h,
    add_assoc, ← Pi.single_add]
  congr 1
  abel_nf

end CFSG.LieType.SpecialLinear.ExteriorModel