module

public import CFSG.Quasithin.Vol2.Ch12Sec1H9FourFacts

public section

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.H9Four CFSG.Open CFSG.Quasithin.E3

namespace CFSG.Certificates.Kernel.H9Four

section Rep

variable {gs : List Elt} (hg : Good gs) (hnd : (elems gs).Nodup)
include hg hnd

theorem card_sub_eq : Nat.card (sub gs) = 2 ^ gs.length := by
  rw [card_sub hg.1 hg.2.1 hg.2.2 hnd, length_elems]

theorem card_le_two_of_length (hl : gs.length ≤ 1) : Nat.card (sub gs) ≤ 2 := by
  rw [card_sub_eq hg hnd]
  exact (Nat.pow_le_pow_right (by norm_num) hl).trans (by norm_num)

theorem ff_of_rep (h : gs = [] ∨ Nat.card (sub gs) * Nat.card (fixV (sub gs)) < Nat.card Pt ∨
      (gs.length = 4 ∧ ∀ g ∈ gs, g.b = false)) :
    sub gs ≠ ⊥ → Nat.card Pt ≤ Nat.card (sub gs) * Nat.card (fixV (sub gs)) →
      sub gs ≤ modelL4 ∧ Nat.card (sub gs) = 2 ^ 4 := by
  intro hne hf
  rcases h with rfl | h | ⟨hl, hb⟩
  · exact absurd sub_nil hne
  · exact absurd hf (not_le.mpr h)
  · refine ⟨(Subgroup.closure_le _).mpr ?_, by rw [card_sub_eq hg hnd, hl]⟩
    rintro _ ⟨g, hg', rfl⟩
    exact (Elt.sem_mem_modelL4_iff (hg.1 g hg')).mpr (hb g hg')

theorem comm_of_rep (h : gs.length ≤ 1 ∨ 2 ^ 2 < Nat.card (commV (sub gs))) :
    Nat.card (commV (sub gs)) ≤ 2 ^ 2 → Nat.card (sub gs) ≤ 2 := by
  intro hc
  rcases h with h | h
  · exact card_le_two_of_length hg hnd h
  · exact absurd hc (not_le.mpr h)

theorem cent_of_rep (h : gs.length ≤ 1 ∨ 2 ^ 2 * Nat.card (fixV (sub gs)) < Nat.card Pt) :
    Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV (sub gs)) → Nat.card (sub gs) ≤ 2 := by
  intro hc
  rcases h with h | h
  · exact card_le_two_of_length hg hnd h
  · exact absurd hc (not_le.mpr h)

end Rep

theorem sub_append_eq {gs : List Elt} {y y' : Elt} (h : y'.sem = y.sem) :
    sub (gs ++ [y']) = sub (gs ++ [y]) := by
  have hs : semSet (gs ++ [y']) = semSet (gs ++ [y]) := by
    ext x
    simp only [semSet, Set.mem_setOf_eq, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨g, hg | rfl, rfl⟩
      · exact ⟨g, Or.inl hg, rfl⟩
      · exact ⟨y, Or.inr rfl, h.symm⟩
    · rintro ⟨g, hg | rfl, rfl⟩
      · exact ⟨g, Or.inl hg, rfl⟩
      · exact ⟨y', Or.inr rfl, h⟩
  rw [sub, sub, hs]

theorem repClosed_of_list {R : List (List Elt)} (L : List Elt)
    (hL : ∀ y : Elt, y.valid = true → y.sem * y.sem = 1 → y.sem ≠ 1 →
      ∃ y' ∈ L, y'.valid = true ∧ y'.sem = y.sem)
    (hcl : ∀ gs ∈ R, ∀ y ∈ L, y.valid = true → (∀ g ∈ gs, y.sem * g.sem = g.sem * y.sem) →
      y.sem ∉ sub gs → ∃ gs' ∈ R, ∃ c ∈ modelM4, conjAut (sub (gs ++ [y])) c = sub gs') :
    RepClosed R := by
  intro gs hgs y hyv hy2 hyc hyn
  have hy1 : y.sem ≠ 1 := fun h => hyn (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨y', hy'L, hy'v, hy'⟩ := hL y hyv hy2 hy1
  obtain ⟨gs', hgs', c, hc, hconj⟩ := hcl gs hgs y' hy'L hy'v (by rw [hy']; exact hyc)
    (by rw [hy']; exact hyn)
  exact ⟨gs', hgs', c, hc, by rw [← sub_append_eq hy']; exact hconj⟩

open scoped Matrix in
theorem exists_invAll_of
    (hL : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.of A * Matrix.of A = 1 → Matrix.of A ≠ 1 →
      ∃ k ∈ invLCodes, (Mat.ofCode k).toMatrix = Matrix.of A)
    (hS : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.transpose (Matrix.of A) = Matrix.of A →
      (Matrix.of A).det ≠ 0 → ∃ p ∈ invSCodes, (Mat.ofCode p.1).toMatrix = Matrix.of A)
    (hval : ∀ x ∈ invAll, x.valid = true) (e : Elt) (he : e.valid = true)
    (hx2 : e.sem * e.sem = 1) (hx1 : e.sem ≠ 1) :
    ∃ y ∈ invAll, y.valid = true ∧ y.sem = e.sem := by
  have hee : e.mul e = Elt.one := Elt.sem_injective (Elt.valid_mul he he) Elt.valid_one
    (by rw [Elt.sem_mul he he, hx2, Elt.sem_one])
  have he' := (Elt.valid_iff e).mp he
  cases hb : e.b
  ·
    have hA2 : e.a.toMatrix * e.a.toMatrix = 1 := by
      have h1 := congrArg (fun f : Elt => f.a.toMatrix) hee
      simpa [Elt.mul, hb, Mat.toMatrix_mul, Elt.one, Mat.toMatrix_one] using h1
    have hA1 : e.a.toMatrix ≠ 1 := by
      intro h
      apply hx1
      have h1 : e = Elt.one := Elt.eq_of_a he Elt.valid_one
        (by rw [h]; exact Mat.toMatrix_one.symm) (by rw [hb]; rfl)
      rw [h1, Elt.sem_one]
    obtain ⟨k, hk, hkA⟩ := hL e.a.toMatrix hA2 hA1
    have hmem : (⟨Mat.ofCode k, Mat.ofCode k, false⟩ : Elt) ∈ invAll :=
      List.mem_append_left _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
    exact ⟨_, hmem, hval _ hmem, by rw [Elt.eq_of_a (hval _ hmem) he hkA hb.symm]⟩
  ·
    have hAt : e.a.toMatrix * e.ai.toMatrixᵀ = 1 := by
      have h1 := congrArg (fun f : Elt => f.a.toMatrix) hee
      simpa [Elt.mul, hb, Mat.toMatrix_mul, Mat.toMatrix_tr, Elt.one, Mat.toMatrix_one] using h1
    have hsym' : e.ai.toMatrixᵀ = e.ai.toMatrix := by
      calc e.ai.toMatrixᵀ = (e.ai.toMatrix * e.a.toMatrix) * e.ai.toMatrixᵀ := by
            rw [he'.2, Matrix.one_mul]
        _ = e.ai.toMatrix := by rw [Matrix.mul_assoc, hAt, Matrix.mul_one]
    have hsym : e.a.toMatrixᵀ = e.a.toMatrix := by
      have h1 : e.a.toMatrixᵀ * e.ai.toMatrix = 1 := by
        rw [← hsym', ← Matrix.transpose_mul, he'.2, Matrix.transpose_one]
      calc e.a.toMatrixᵀ = e.a.toMatrixᵀ * (e.ai.toMatrix * e.a.toMatrix) := by
            rw [he'.2, Matrix.mul_one]
        _ = e.a.toMatrix := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hdet : e.a.toMatrix.det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det he'.1
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    obtain ⟨p, hp, hpA⟩ := hS e.a.toMatrix hsym hdet
    have hmem : (⟨Mat.ofCode p.1, Mat.ofCode p.2, true⟩ : Elt) ∈ invAll :=
      List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact ⟨_, hmem, hval _ hmem, by rw [Elt.eq_of_a (hval _ hmem) he hpA hb.symm]⟩

theorem reps_length_four :
    ∀ i < reps.length, (reps.getD i []).length = 4 → i = 26 ∨ i = 27 ∨ i = 28 := by
  decide

theorem reps_card16 (hc : ∀ gs ∈ reps, Nat.card (sub gs) = 2 ^ gs.length) :
    ∀ gs ∈ reps, Nat.card (sub gs) = 2 ^ 4 → sub gs = sub (reps.getD 28 []) ∨
      sub gs = sub (reps.getD 26 []) ∨ sub gs = sub (reps.getD 27 []) := by
  intro gs hgs hcard
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgs
  rw [hc _ hgs] at hcard
  have h4 : reps[i].length = 4 := Nat.pow_right_injective (le_refl 2) hcard
  have hgi : reps.getD i [] = reps[i] := List.getD_eq_getElem _ _ hi
  rcases reps_length_four i hi (by rw [hgi]; exact h4) with rfl | rfl | rfl
  · exact Or.inr (Or.inl (by rw [hgi]))
  · exact Or.inr (Or.inr (by rw [hgi]))
  · exact Or.inl (by rw [hgi])

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.H9Four CFSG.Open CFSG.Quasithin.E3 in
theorem certificate7104_of {R : List (List Elt)} (hnil : [] ∈ R) (hgood : ∀ gs ∈ R, Good gs)
    (hcl : RepClosed R) (hcard : ∀ gs ∈ R, Nat.card (sub gs) ≤ 2 ^ 4)
    (hff : ∀ gs ∈ R, sub gs ≠ ⊥ → Nat.card Pt ≤ Nat.card (sub gs) * Nat.card (fixV (sub gs)) →
      sub gs ≤ modelL4 ∧ Nat.card (sub gs) = 2 ^ 4)
    (hcomm : ∀ gs ∈ R, Nat.card (commV (sub gs)) ≤ 2 ^ 2 → Nat.card (sub gs) ≤ 2)
    (hcent : ∀ gs ∈ R, Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV (sub gs)) → Nat.card (sub gs) ≤ 2)
    (haxes : ∀ gs ∈ R, ConstFixL (sub gs) → 2 ^ 2 ≤ Nat.card (sub gs) →
      Nat.card (sub gs) = 2 ^ 2 ∧ ∀ b ∈ sub gs, b ≠ 1 →
        Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2 ∧
          Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₂) = 2 ^ 2)
    {A₀ A₁ A₂ : Subgroup (MulAut Pt)}
    (hmem : ∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
      A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4)
    (h16 : ∀ gs ∈ R, Nat.card (sub gs) = 2 ^ 4 → sub gs = A₀ ∨ sub gs = A₁ ∨ sub gs = A₂)
    (h0 : Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤)
    (h1 : Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6)
    (h2 : Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
      ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1)
    (h7 : ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
      (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
        (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
        2 ^ 7 ≤ Nat.card (gammaCheck 3 A)) :

    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A ≤ 2 ^ 4) ∧
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card Pt ≤ Nat.card A * Nat.card (fixV A) → A ≤ modelL4 ∧ Nat.card A = 2 ^ 4) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card (commV X) ≤ 2 ^ 2 → Nat.card X ≤ 2) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV X) → Nat.card X ≤ 2) ∧
    (∀ B : Subgroup (MulAut Pt), B ≤ modelL4 → IsElemAbelian2 B → 2 ^ 2 ≤ Nat.card B →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
        fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
          fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂) →
      Nat.card B = 2 ^ 2 ∧
        ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2) ∧
    ∃ A₀ A₁ A₂ : Subgroup (MulAut Pt),
      (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
        A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
      (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
        ∃ m ∈ modelM4, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
      (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
      (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
      (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
        ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
      ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
        (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
          (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A) := by
  have hR := classifies_of hnil hgood hcl
  exact ⟨fun _ hAM hA => card_le_of_classifies hR hcard hAM hA,
    fun _ hAM hA hA1 hf => le_L_of_classifies hR hff hAM hA hA1 hf,
    fun _ hXM hX hc => card_le_two_of_commV_of_classifies hR hcomm hXM hX hc,
    fun _ hXM hX hc => card_le_two_of_fixV_of_classifies hR hcent hXM hX hc,
    fun _ hBL hB hc hfix => axes_of_classifies hR haxes hBL hB hc hfix,
    lemH93_of_classifies hR hmem h16 h0 h1 h2 h7⟩

theorem invAll_valid_of (h : checkInv = true) {x : Elt} (hx : x ∈ invAll) : x.valid = true := by
  rw [checkInv, List.all_eq_true] at h
  have h1 := h x hx
  simp only [Bool.and_eq_true] at h1
  exact h1.1.1

theorem reps_spec_of (h : repCheck = true) {gs : List Elt} (hgs : gs ∈ reps) :
    (∀ g ∈ gs, g.valid = true ∧ g.mul g = Elt.one ∧ g ≠ Elt.one) ∧
      (∀ g ∈ gs, ∀ h ∈ gs, g.mul h = h.mul g) ∧ (elems gs).Nodup := by
  rw [repCheck, List.all_eq_true] at h
  have h1 := h gs hgs
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, commutes] at h1
  exact ⟨fun g hg => ⟨(h1.1.1 g hg).1.1, (h1.1.1 g hg).1.2, (h1.1.1 g hg).2⟩, h1.1.2, h1.2⟩

theorem good_of_reps (h : repCheck = true) {gs : List Elt} (hgs : gs ∈ reps) : Good gs := by
  obtain ⟨h1, h2, -⟩ := reps_spec_of h hgs
  refine ⟨fun g hg => (h1 g hg).1, fun g hg => ?_, fun g hg h hh => ?_⟩
  · rw [← Elt.sem_mul (h1 g hg).1 (h1 g hg).1, (h1 g hg).2.1, Elt.sem_one]
  · rw [← Elt.sem_mul (h1 g hg).1 (h1 h hh).1, ← Elt.sem_mul (h1 h hh).1 (h1 g hg).1, h2 g hg h hh]

theorem conjAut_sub_le {gs gs' : List Elt} (hg' : Good gs') {c : Elt} (hcv : c.valid = true)
    (hv : ∀ g ∈ gs, g.valid = true) (h : ∀ g ∈ gs, (c.mul g).mul c.inv ∈ elems gs') :
    conjAut (sub gs) c.sem ≤ sub gs' := by
  rw [H13.conjAut, sub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  have h1 := mem_sub_of_mem_elems hg' (h g hg)
  rw [Elt.sem_mul (Elt.valid_mul hcv (hv g hg)) (Elt.valid_inv hcv), Elt.sem_mul hcv (hv g hg),
    Elt.sem_inv hcv] at h1
  simpa only [SetLike.mem_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1

theorem repClosed_reps
    (hL : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.of A * Matrix.of A = 1 → Matrix.of A ≠ 1 →
      ∃ k ∈ invLCodes, (Mat.ofCode k).toMatrix = Matrix.of A)
    (hS : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.transpose (Matrix.of A) = Matrix.of A →
      (Matrix.of A).det ≠ 0 → ∃ p ∈ invSCodes, (Mat.ofCode p.1).toMatrix = Matrix.of A)
    (hinv : checkInv = true) (hrep : repCheck = true)
    (hclos : ∀ {i : ℕ}, i < reps.length → ∀ {y : Elt}, y ∈ invAll →
      (reps.getD i []).all (commutes y) = true → (elems (reps.getD i [])).contains y = false →
      ∃ j < reps.length, ∃ c : Elt, c.valid = true ∧
        (reps.getD j []).length = (reps.getD i []).length + 1 ∧
        ∀ g ∈ reps.getD i [] ++ [y], (c.mul g).mul c.inv ∈ elems (reps.getD j [])) :
    RepClosed reps := by
  refine repClosed_of_list invAll (fun y hyv hy2 hy1 =>
    exists_invAll_of hL hS (fun x hx => invAll_valid_of hinv hx) y hyv hy2 hy1) ?_
  intro gs hgs y hyI hyv hyc hyn
  have hgood := good_of_reps hrep hgs
  obtain ⟨i, hi, hig⟩ := List.getElem_of_mem hgs
  have hgetR : reps.getD i [] = gs := by rw [List.getD_eq_getElem _ _ hi, hig]
  have hc : (reps.getD i []).all (commutes y) = true := by
    rw [hgetR, List.all_eq_true]
    intro g hg
    simp only [commutes, beq_iff_eq]
    apply Elt.sem_injective (Elt.valid_mul hyv (hgood.1 g hg)) (Elt.valid_mul (hgood.1 g hg) hyv)
    rw [Elt.sem_mul hyv (hgood.1 g hg), Elt.sem_mul (hgood.1 g hg) hyv]
    exact hyc g hg
  have hn : (elems (reps.getD i [])).contains y = false := by
    rw [hgetR]
    by_contra h
    simp only [Bool.not_eq_false, List.contains_iff_mem] at h
    exact hyn ((mem_sub_iff hgood.1 hgood.2.1 hgood.2.2 _).mpr ⟨y, h, rfl⟩)
  obtain ⟨j, hj, c, hcv, hlen, hmem⟩ := hclos hi hyI hc hn
  rw [hgetR] at hlen hmem
  have hgs' : reps.getD j [] ∈ reps := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hgood' := good_of_reps hrep hgs'
  refine ⟨_, hgs', c.sem, Elt.sem_mem hcv, ?_⟩
  have hv : ∀ g ∈ gs ++ [y], g.valid = true := fun g hg => by
    rcases List.mem_append.mp hg with hg | hg
    · exact hgood.1 g hg
    · rw [List.mem_singleton.mp hg]
      exact hyv
  refine Subgroup.eq_of_le_of_card_ge (conjAut_sub_le hgood' hcv hv hmem) ?_
  rw [H9Conj.card_conjAut, card_sub_eq hgood' (reps_spec_of hrep hgs').2.2, hlen, pow_succ,
    ← card_sub_eq hgood (reps_spec_of hrep hgs).2.2]
  have hlt : sub gs < sub (gs ++ [y]) := by
    refine lt_of_le_of_ne (Subgroup.closure_mono fun _ ⟨g, hg, h⟩ =>
      ⟨g, List.mem_append_left _ hg, h⟩) fun h => hyn ?_
    rw [h]
    exact Subgroup.subset_closure ⟨y, List.mem_append_right _ (List.mem_singleton_self y), rfl⟩
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hlt.le
  have h1 := Subgroup.card_lt_of_lt hlt
  have hq1 : 2 ≤ q := by
    by_contra hq2
    push Not at hq2
    interval_cases q <;> omega
  rw [hq]
  exact Nat.mul_le_mul_left _ hq1

theorem two_pow_lt_four {n : ℕ} (h : 2 ^ n < 4) : n ≤ 1 := by
  by_contra h2
  have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem length_reps : reps.length = 29 := by decide

theorem length_rep16 : (reps.getD 26 []).length = 4 ∧ (reps.getD 27 []).length = 4 ∧
    (reps.getD 28 []).length = 4 := by
  decide

theorem rep16_of (hrep : repCheck = true) {i : ℕ} (hi : i = 26 ∨ i = 27 ∨ i = 28) :
    reps.getD i [] ∈ reps ∧ Good (reps.getD i []) ∧ Nat.card (sub (reps.getD i [])) = 2 ^ 4 := by
  have hlt : i < reps.length := by rw [length_reps]; omega
  have hmem : reps.getD i [] ∈ reps := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  refine ⟨hmem, good_of_reps hrep hmem, ?_⟩
  rw [card_sub_eq (good_of_reps hrep hmem) (reps_spec_of hrep hmem).2.2]
  rcases hi with rfl | rfl | rfl
  · rw [length_rep16.1]
  · rw [length_rep16.2.1]
  · rw [length_rep16.2.2]

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.H9Four CFSG.Open CFSG.Quasithin.E3 in
theorem certificate7104_of_checks
    (hL : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.of A * Matrix.of A = 1 → Matrix.of A ≠ 1 →
      ∃ k ∈ invLCodes, (Mat.ofCode k).toMatrix = Matrix.of A)
    (hS : ∀ A : Fin 4 → Fin 4 → ZMod 2, Matrix.transpose (Matrix.of A) = Matrix.of A →
      (Matrix.of A).det ≠ 0 → ∃ p ∈ invSCodes, (Mat.ofCode p.1).toMatrix = Matrix.of A)
    (hinv : checkInv = true) (hrep : repCheck = true)
    (hclos : ∀ {i : ℕ}, i < reps.length → ∀ {y : Elt}, y ∈ invAll →
      (reps.getD i []).all (commutes y) = true → (elems (reps.getD i [])).contains y = false →
      ∃ j < reps.length, ∃ c : Elt, c.valid = true ∧
        (reps.getD j []).length = (reps.getD i []).length + 1 ∧
        ∀ g ∈ reps.getD i [] ++ [y], (c.mul g).mul c.inv ∈ elems (reps.getD j []))
    (hrank : rankCheck = true)
    (hff : ∀ gs ∈ reps, gs = [] ∨ (elems gs).length * (fixPts gs).length < 256 ∨
      (inL gs = true ∧ (elems gs).length = 16))
    (hcomm : commCheck = true) (hcent : centCheck = true) (haxes : axesCheck = true)
    (he16 : e16Check = true) :
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A ≤ 2 ^ 4) ∧
    (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → A ≠ ⊥ →
      Nat.card Pt ≤ Nat.card A * Nat.card (fixV A) → A ≤ modelL4 ∧ Nat.card A = 2 ^ 4) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card (commV X) ≤ 2 ^ 2 → Nat.card X ≤ 2) ∧
    (∀ X : Subgroup (MulAut Pt), X ≤ modelM4 → IsElemAbelian2 X →
      Nat.card Pt ≤ 2 ^ 2 * Nat.card (fixV X) → Nat.card X ≤ 2) ∧
    (∀ B : Subgroup (MulAut Pt), B ≤ modelL4 → IsElemAbelian2 B → 2 ^ 2 ≤ Nat.card B →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ 1 → c ≠ 1 →
        fixV (Subgroup.zpowers b) ⊓ ptW₁ = fixV (Subgroup.zpowers c) ⊓ ptW₁ ∧
          fixV (Subgroup.zpowers b) ⊓ ptW₂ = fixV (Subgroup.zpowers c) ⊓ ptW₂) →
      Nat.card B = 2 ^ 2 ∧
        ∀ b ∈ B, b ≠ 1 → Nat.card ↥(fixV (Subgroup.zpowers b) ⊓ ptW₁) = 2 ^ 2) ∧
    ∃ A₀ A₁ A₂ : Subgroup (MulAut Pt),
      (∀ A ∈ ({A₀, A₁, A₂} : Set (Subgroup (MulAut Pt))),
        A ≤ modelM4 ∧ IsElemAbelian2 A ∧ Nat.card A = 2 ^ 4) ∧
      (∀ A : Subgroup (MulAut Pt), A ≤ modelM4 → IsElemAbelian2 A → Nat.card A = 2 ^ 4 →
        ∃ m ∈ modelM4, A = conjAut A₀ m ∨ A = conjAut A₁ m ∨ A = conjAut A₂ m) ∧
      (Nat.card (fixV A₀) = 2 ^ 4 ∧ gammaCheck 2 A₀ = ⊤) ∧
      (Nat.card (fixV A₁) = 2 ∧ Nat.card (gammaCheck 2 A₁) = 2 ^ 6) ∧
      (Nat.card (fixV A₂) = 2 ^ 2 ∧ Nat.card (gammaCheck 2 A₂) = 2 ^ 6 ∧
        ∀ a ∈ A₂, (∀ w ∈ gammaCheck 2 A₂, a w = w) → a = 1) ∧
      ∀ A ∈ ({A₁, A₂} : Set (Subgroup (MulAut Pt))),
        (∃ b ∈ A ⊓ modelL4, IsTransvOn b ptW₁) ∧
          (∃ b ∈ A ⊓ modelL4, b ≠ 1 ∧ ¬ IsTransvOn b ptW₁) ∧
          2 ^ 7 ≤ Nat.card (gammaCheck 3 A) := by
  have hnd : ∀ gs ∈ reps, (elems gs).Nodup := fun gs hgs => (reps_spec_of hrep hgs).2.2
  have hgood : ∀ gs ∈ reps, Good gs := fun gs hgs => good_of_reps hrep hgs
  have hc : ∀ gs ∈ reps, Nat.card (sub gs) = 2 ^ gs.length := fun gs hgs =>
    card_sub_eq (hgood gs hgs) (hnd gs hgs)
  have hce : ∀ gs ∈ reps, Nat.card (sub gs) = (elems gs).length := fun gs hgs => by
    rw [hc gs hgs, length_elems]
  have hpt : Nat.card Pt = 256 := by rw [card_pt]; norm_num
  obtain ⟨-, h28g, h28c⟩ := rep16_of hrep (i := 28) (by norm_num)
  obtain ⟨-, h26g, h26c⟩ := rep16_of hrep (i := 26) (by norm_num)
  obtain ⟨-, h27g, h27c⟩ := rep16_of hrep (i := 27) (by norm_num)
  have he := he16
  simp only [e16Check, Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true, List.any_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨h0f, h0g⟩, h1f⟩, h1g⟩, h2f⟩, h2g⟩, h2faith⟩, ⟨⟨h1t, h1n⟩, h1g3⟩, ⟨h2t, h2n⟩,
    h2g3⟩ := he
  refine certificate7104_of nil_mem_reps hgood (repClosed_reps hL hS hinv hrep hclos)
    (fun gs hgs => ?_) (fun gs hgs => ?_) (fun gs hgs => ?_) (fun gs hgs => ?_)
    (fun gs hgs => ?_) (A₀ := sub (reps.getD 28 [])) (A₁ := sub (reps.getD 26 []))
    (A₂ := sub (reps.getD 27 [])) ?_ (reps_card16 hc) ⟨?_, ?_⟩ ⟨?_, ?_⟩ ⟨?_, ?_, ?_⟩ ?_
  ·
    have h := hrank
    rw [rankCheck, List.all_eq_true] at h
    rw [hce gs hgs]
    simpa using h gs hgs
  ·
    refine ff_of_rep (hgood gs hgs) (hnd gs hgs) ?_
    rcases hff gs hgs with h | h | ⟨hL0, h16'⟩
    · exact Or.inl h
    · right
      left
      rw [hce gs hgs, card_fixV_sub (hgood gs hgs).1, hpt]
      exact h
    · right
      right
      refine ⟨?_, ?_⟩
      · rw [length_elems] at h16'
        exact Nat.pow_right_injective (le_refl 2) (h16'.trans (by norm_num))
      · intro g hg
        rw [inL, List.all_eq_true] at hL0
        simpa using hL0 g hg
  ·
    refine comm_of_rep (hgood gs hgs) (hnd gs hgs) ?_
    have h := hcomm
    rw [commCheck, List.all_eq_true] at h
    have h1 := h gs hgs
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · rw [length_elems] at h1
      exact Or.inl (two_pow_lt_four h1)
    · right
      have h2 := Subgroup.card_le_of_le (closure_commPts_le (hgood gs hgs))
      rw [card_closure_eq_spanList] at h2
      omega
  ·
    refine cent_of_rep (hgood gs hgs) (hnd gs hgs) ?_
    have h := hcent
    rw [centCheck, List.all_eq_true] at h
    have h1 := h gs hgs
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    rcases h1 with h1 | h1
    · rw [length_elems] at h1
      exact Or.inl (two_pow_lt_four h1)
    · right
      rw [card_fixV_sub (hgood gs hgs).1, hpt]
      omega
  ·
    intro hC h4
    have hg := hgood gs hgs
    have hval := valid_of_mem_elems hg.1
    have hinL : inL gs = true := by
      rw [inL, List.all_eq_true]
      intro g hg'
      have h1 := hC.1 (Subgroup.subset_closure ⟨g, hg', rfl⟩)
      rw [Elt.sem_mem_modelL4_iff (hg.1 g hg')] at h1
      simp [h1]
    have hlen : 4 ≤ (elems gs).length := by
      rw [hce gs hgs] at h4
      simpa using h4
    have hcf : constFix (elems gs) = true := by
      rw [constFix, List.all_eq_true]
      intro e he
      rw [List.all_eq_true]
      intro f hf
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
      by_cases he1 : e = Elt.one
      · exact Or.inl (Or.inl he1)
      by_cases hf1 : f = Elt.one
      · exact Or.inl (Or.inr hf1)
      obtain ⟨h1, h2⟩ := hC.2 _ (mem_sub_of_mem_elems hg he) _ (mem_sub_of_mem_elems hg hf)
        (Elt.sem_ne_one (hval e he) he1) (Elt.sem_ne_one (hval f hf) hf1)
      exact Or.inr ⟨fixPts₁_eq (hval e he) (hval f hf) h1, fixPts₂_eq (hval e he) (hval f hf) h2⟩
    have h := haxes
    rw [axesCheck, List.all_eq_true] at h
    have h1 := h gs hgs
    simp only [hinL, hcf, Bool.not_true, Bool.false_or, Bool.or_false, Bool.or_eq_true,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
    rcases h1 with h1 | ⟨hl4, hall⟩
    · omega
    refine ⟨by rw [hce gs hgs, hl4]; norm_num, fun b hb hb1 => ?_⟩
    obtain ⟨e, he, rfl⟩ := (mem_sub_iff hg.1 hg.2.1 hg.2.2 _).mp hb
    have he1 : e ≠ Elt.one := fun h => hb1 (by rw [h, Elt.sem_one])
    obtain ⟨h₁, h₂⟩ := (hall e he).resolve_left he1
    rw [card_fixPts₁ (hval e he), card_fixPts₂ (hval e he), h₁, h₂]
    norm_num
  ·
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl
    · exact ⟨sub_le_modelM4 h28g.1, isElemAbelian2_sub h28g, h28c⟩
    · exact ⟨sub_le_modelM4 h26g.1, isElemAbelian2_sub h26g, h26c⟩
    · exact ⟨sub_le_modelM4 h27g.1, isElemAbelian2_sub h27g, h27c⟩
  · rw [card_fixV_sub h28g.1, h0f]
    norm_num
  · have htop : Subgroup.closure {w | w ∈ gam2Pts (elems (reps.getD 28 []))} = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [card_closure_eq_spanList, h0g, hpt]
    rw [eq_top_iff, ← htop]
    exact closure_gam2_le h28g h28c
  · rw [card_fixV_sub h26g.1, h1f]
  · rw [gammaCheck_two_eq h26g h26c, card_closure_eq_spanList, h1g]
    norm_num
  · rw [card_fixV_sub h27g.1, h2f]
    norm_num
  · rw [gammaCheck_two_eq h27g h27c, card_closure_eq_spanList, h2g]
    norm_num
  · intro a ha hfa
    obtain ⟨e, he, rfl⟩ := (mem_sub_iff h27g.1 h27g.2.1 h27g.2.2 _).mp ha
    rcases h2faith e he with he1 | ⟨w, hw, hne⟩
    · rw [he1, Elt.sem_one]
    · exfalso
      apply hne
      have hw' : w ∈ gammaCheck 2 (sub (reps.getD 27 [])) := by
        rw [gammaCheck_two_eq h27g h27c]
        exact ((mem_spanList _).1 w).mp hw
      rw [← Elt.sem_apply (valid_of_mem_elems h27g.1 e he)]
      exact hfa w hw'
  · intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact seven_of h26g h26c h1t h1n h1g3
    · exact seven_of h27g h27c h2t h2n h2g3

end CFSG.Certificates.Kernel.H9Four
