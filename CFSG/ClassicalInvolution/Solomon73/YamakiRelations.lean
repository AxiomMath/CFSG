module

public import CFSG.ClassicalInvolution.Solomon73.YamakiModel
public import Certificates.Certificate550751

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open Matrix

section Bicommutant

theorem bicomExpand_holds : BicomExpand :=
  Certificates.certificate550751.1

theorem bicomCommute_holds : BicomCommute :=
  Certificates.certificate550751.2

variable {X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}

private theorem mulVec_bicomWordVec :
    ∀ w : List (Fin 12), (∀ i ∈ w, Commute X (yamakiMat i)) → ∀ v : Fin 3 ⊕ Fin 3 → ZMod 2,
      X *ᵥ bicomWordVec w v = bicomWordVec w (X *ᵥ v)
  | [], _, _ => rfl
  | i :: w, hw, v => by
    have ih := mulVec_bicomWordVec w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) v
    show X *ᵥ (yamakiMat i *ᵥ bicomWordVec w v) = yamakiMat i *ᵥ bicomWordVec w (X *ᵥ v)
    rw [Matrix.mulVec_mulVec, (hw i List.mem_cons_self).eq, ← Matrix.mulVec_mulVec, ih]

private theorem mulVec_bicomTermsVec (hX : ∀ i ∈ bicomLetters, Commute X (yamakiMat i))
    (y : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) :
    ∀ l : List (Fin 2 × List (Fin 12)), (∀ t ∈ l, ∀ i ∈ t.2, i ∈ bicomLetters) →
      X *ᵥ bicomTermsVec y l = bicomTermsVec (fun k => X *ᵥ y k) l
  | [], _ => by simp [bicomTermsVec]
  | t :: l, hl => by
    have ih := mulVec_bicomTermsVec hX y l fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')
    have ht := mulVec_bicomWordVec t.2 (fun i hi => hX i (hl t List.mem_cons_self i hi)) (y t.1)
    simp only [bicomTermsVec, List.map_cons, List.sum_cons] at ih ⊢
    rw [Matrix.mulVec_add, ih, ht]

theorem eq_bicomMat
    (hX : ∀ i ∈ bicomLetters, Commute X (yamakiMat i)) :
    X = bicomMat fun k => X *ᵥ bicomGen k := by
  obtain ⟨hlet, hexp⟩ := bicomExpand_holds
  ext r j
  have hl : ∀ t ∈ bicomTerms (finSumFinEquiv j), ∀ i ∈ t.2, i ∈ bicomLetters :=
    hlet (finSumFinEquiv j)
  rw [bicomMat, Matrix.of_apply, ← mulVec_bicomTermsVec hX bicomGen _ hl, hexp j,
    Matrix.mulVec_single_one, Matrix.col_apply]

theorem commute_yamakiMat_eight
    (hX : ∀ i ∈ bicomLetters, Commute X (yamakiMat i)) : Commute X (yamakiMat 8) := by
  have h : BicomCommute := bicomCommute_holds
  have hy : (fun k => X *ᵥ bicomGen k) = ![X *ᵥ bicomGen 0, X *ᵥ bicomGen 1] := by
    funext k
    fin_cases k <;> rfl
  have hXe : X = bicomMat ![X *ᵥ bicomGen 0, X *ᵥ bicomGen 1] :=
    (eq_bicomMat hX).trans (congrArg bicomMat hy)
  have h8 := h (X *ᵥ bicomGen 0) (X *ᵥ bicomGen 1) fun i hi => by
    rw [← hXe]
    exact hX i hi
  rw [← hXe] at h8
  exact h8

private theorem spMat_yamakiSp (i : Fin 12) :
    spMat (yamakiSp i) = yamakiMat i :=
  rfl

theorem commute_yamakiSp_eight
    {g : StatedSp 3 (ZMod 2)}
    (hg : ∀ i : Fin 12, 1 ≤ i.val → i.val ≤ 7 → Commute g (yamakiSp i)) :
    Commute g (yamakiSp 8) := by
  have h := commute_yamakiMat_eight (X := spMat g) fun i hi => by
    have hi' := (by decide : ∀ j ∈ bicomLetters, 1 ≤ j.val ∧ j.val ≤ 7) i hi
    simpa only [spMat_yamakiSp] using (hg i hi'.1 hi'.2).map spMat
  show g * yamakiSp 8 = yamakiSp 8 * g
  apply spMat_injective
  rw [map_mul, map_mul, spMat_yamakiSp]
  exact h

end Bicommutant

section Transport

variable {α K : Type*} [Group K]

private theorem lift_mk_congr {f g : α → K} {r : List (α × Bool)} (h : ∀ l ∈ r, f l.1 = g l.1) :
    FreeGroup.lift f (FreeGroup.mk r) = FreeGroup.lift g (FreeGroup.mk r) := by
  rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
  congr 1
  exact List.map_congr_left fun l hl => by rw [h l hl]

private theorem map_lift_apply {L : Type*} [Group L] (φ : L →* K) (f : α → L) (w : FreeGroup α) :
    φ (FreeGroup.lift f w) = FreeGroup.lift (φ ∘ f) w :=
  FreeGroup.lift_unique (φ.comp (FreeGroup.lift f)) fun a => by simp

theorem lift_mk_eq_one_of_letters
    {L : Subgroup (StatedSp 3 (ZMod 2))} (φ : ↥L →* K) {p : Fin 12 → Prop}
    (hp : ∀ i, p i → yamakiSp i ∈ L) {y : Fin 12 → K}
    (hy : ∀ i (hi : p i), y i = φ ⟨yamakiSp i, hp i hi⟩) {r : List (Fin 12 × Bool)}
    (hr : ∀ l ∈ r, p l.1) (h1 : FreeGroup.lift yamakiSp (FreeGroup.mk r) = 1) :
    FreeGroup.lift y (FreeGroup.mk r) = 1 := by
  classical
  let y' : Fin 12 → ↥L := fun i => if hi : p i then ⟨yamakiSp i, hp i hi⟩ else 1
  have hy' : ∀ l (hl : l ∈ r), y' l.1 = ⟨yamakiSp l.1, hp _ (hr l hl)⟩ :=
    fun l hl => dif_pos (hr l hl)
  have h3 : (L.subtype (FreeGroup.lift y' (FreeGroup.mk r)) : StatedSp 3 (ZMod 2)) = 1 := by
    rw [map_lift_apply]
    have hl : ∀ l ∈ r, (L.subtype ∘ y') l.1 = yamakiSp l.1 := fun l hl =>
      congrArg L.subtype (hy' l hl)
    exact (lift_mk_congr hl).trans h1
  have h2 : FreeGroup.lift y' (FreeGroup.mk r) = 1 := Subtype.ext h3
  have hl : ∀ l ∈ r, y l.1 = (φ ∘ y') l.1 := fun l hl =>
    (hy l.1 (hr l hl)).trans (congrArg φ (hy' l hl)).symm
  calc FreeGroup.lift y (FreeGroup.mk r) = FreeGroup.lift (φ ∘ y') (FreeGroup.mk r) :=
        lift_mk_congr hl
    _ = φ (FreeGroup.lift y' (FreeGroup.mk r)) := (map_lift_apply φ y' _).symm
    _ = 1 := by rw [h2, map_one]

end Transport

section GroupLemmas

variable {G : Type*} [Group G]

theorem commute_sq_of_semiconjBy {w₁ w₃ a b c d : G} (h1 : SemiconjBy w₃ a b)
    (h2 : SemiconjBy w₁ b c) (h3 : SemiconjBy w₃ c d) (h4 : SemiconjBy w₁ d a) :
    Commute (w₁ * w₃ * (w₁ * w₃)) a :=
  (h4.mul_left h3).mul_left (h2.mul_left h1)

theorem commute_of_yamaki_lemma10 {w₁ w₃ a : G} (h3 : w₃ * w₃ = 1) (hw₁a : Commute w₁ a)
    (hc : Commute (w₁ * w₃ * (w₁ * w₃)) a) (h33 : w₃ * a * (w₃ * a) * (w₃ * a) = 1) :
    Commute w₁ w₃ := by
  have e3 : w₃⁻¹ = w₃ := inv_eq_of_mul_eq_one_right h3
  have ht : Commute (w₃ * w₁ * w₃⁻¹) a := by
    have h : w₃ * w₁ * w₃⁻¹ = w₁⁻¹ * (w₁ * w₃ * (w₁ * w₃)) := by
      rw [e3]
      group
    rw [h]
    exact hw₁a.inv_left.mul_left hc
  have hb : Commute w₁ (w₃⁻¹ * a * w₃) := by
    calc w₁ * (w₃⁻¹ * a * w₃) = w₃⁻¹ * (w₃ * w₁ * w₃⁻¹ * a) * w₃ := by group
      _ = w₃⁻¹ * (a * (w₃ * w₁ * w₃⁻¹)) * w₃ := by rw [ht.eq]
      _ = w₃⁻¹ * a * w₃ * w₁ := by group
  have h33' : a * w₃ * a * w₃ * a = w₃⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc a * w₃ * a * w₃ * a * w₃ = w₃⁻¹ * (w₃ * a * (w₃ * a) * (w₃ * a)) * w₃ := by group
      _ = 1 := by rw [h33]; group
  have hw3 : w₃ = a * (w₃⁻¹ * a * w₃) * a := by
    calc w₃ = w₃⁻¹ := e3.symm
      _ = a * w₃ * a * w₃ * a := h33'.symm
      _ = a * (w₃⁻¹ * a * w₃) * a := by rw [e3]; group
  have h := (hw₁a.mul_right hb).mul_right hw₁a
  rwa [← hw3] at h

theorem yamakiRels_letters :
    ∀ r ∈ yamakiRels, r ≠ posW [9, 11, 9, 11] → (∀ l ∈ r, l.1 ≠ 11) ∨ (∀ l ∈ r, l.1 ≠ 9) := by
  decide

theorem lift_w13_of {x : Fin 12 → G} (hinv : ∀ i, x i * x i = 1)
    (sc : ∀ w a b : Fin 12, relW (posW [w, a, w]) (posW [b]) ∈ yamakiRels →
      SemiconjBy (x w) (x a) (x b))
    (h33 : FreeGroup.lift x (FreeGroup.mk (posW [11, 8, 11, 8, 11, 8])) = 1)
    (hcent : (∀ i : Fin 12, 1 ≤ i.val → i.val ≤ 7 → Commute (x 9 * x 11 * (x 9 * x 11)) (x i)) →
      Commute (x 9 * x 11 * (x 9 * x 11)) (x 8)) :
    FreeGroup.lift x (FreeGroup.mk (posW [9, 11, 9, 11])) = 1 := by
  have hc : ∀ i : Fin 12, 1 ≤ i.val → i.val ≤ 7 → Commute (x 9 * x 11 * (x 9 * x 11)) (x i) := by
    intro i h1 h7
    rcases (by decide : ∀ j : Fin 12, 1 ≤ j.val → j.val ≤ 7 →
      j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) i h1 h7 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact commute_sq_of_semiconjBy (sc 11 1 3 (by decide)) (sc 9 3 6 (by decide))
        (sc 11 6 2 (by decide)) (sc 9 2 1 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 2 6 (by decide)) (sc 9 6 3 (by decide))
        (sc 11 3 1 (by decide)) (sc 9 1 2 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 3 1 (by decide)) (sc 9 1 2 (by decide))
        (sc 11 2 6 (by decide)) (sc 9 6 3 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 4 4 (by decide)) (sc 9 4 4 (by decide))
        (sc 11 4 4 (by decide)) (sc 9 4 4 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 5 5 (by decide)) (sc 9 5 7 (by decide))
        (sc 11 7 7 (by decide)) (sc 9 7 5 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 6 2 (by decide)) (sc 9 2 1 (by decide))
        (sc 11 1 3 (by decide)) (sc 9 3 6 (by decide))
    · exact commute_sq_of_semiconjBy (sc 11 7 7 (by decide)) (sc 9 7 5 (by decide))
        (sc 11 5 5 (by decide)) (sc 9 5 7 (by decide))
  have h33' : x 11 * x 8 * (x 11 * x 8) * (x 11 * x 8) = 1 := by
    rw [lift_mk_eq_prod hinv] at h33
    simpa only [posW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_assoc] using h33
  have h13 : Commute (x 9) (x 11) :=
    commute_of_yamaki_lemma10 (hinv 11) (sc 9 8 8 (by decide)) (hcent hc) h33'
  rw [lift_mk_eq_prod hinv]
  simp only [posW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  calc x 9 * (x 11 * (x 9 * x 11)) = x 9 * (x 9 * x 11 * x 11) := by
        rw [← mul_assoc (x 11), ← h13.eq]
    _ = x 9 * x 9 * (x 11 * x 11) := by simp only [mul_assoc]
    _ = 1 := by rw [hinv, hinv, one_mul]

private theorem mul_self_eq_one_of_hom {A B : Type*} [Group A] [Group B] (f : A →* B) {g : A}
    (hg : g * g = 1) : f g * f g = 1 := by
  rw [← map_mul, hg, map_one]

end GroupLemmas

section Generators

variable {G : Type*} [Group G] {N H : Subgroup G}

theorem yamakiSp_mem_N0_of_ne {i : Fin 12} (hi : i ≠ 11) : yamakiSp i ∈ N0 :=
  yamakiSp_mem_N0 ((by decide : ∀ j : Fin 12, j ≠ 11 → j.val ≤ 8 ∨ j = 9 ∨ j = 10) i hi)

theorem yamakiSp_mem_Hhat_of_ne {i : Fin 12} (hi : i ≠ 9) : yamakiSp i ∈ Hhat :=
  yamakiSp_mem_Hhat ((by decide : ∀ j : Fin 12, j ≠ 9 → j.val ≤ 8 ∨ j = 10 ∨ j = 11) i hi)

theorem yamakiSp_mem_X0_of_ne {i : Fin 12} (h9 : i ≠ 9) (h11 : i ≠ 11) : yamakiSp i ∈ X0 :=
  yamakiSp_mem_X0 ((by decide : ∀ j : Fin 12, j ≠ 9 → j ≠ 11 → j.val ≤ 8 ∨ j = 10) i h9 h11)

@[expose] def yamakiPre (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat) (i : Fin 12) : G :=
  if h : i = 11 then (θ.symm ⟨yamakiSp 11, yamakiSp_mem_Hhat (Or.inr (Or.inr rfl))⟩ : G)
  else (ν.symm ⟨yamakiSp i, yamakiSp_mem_N0_of_ne h⟩ : G)

variable (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat)

theorem yamakiPre_eleven :
    yamakiPre ν θ 11 = θ.symm ⟨yamakiSp 11, yamakiSp_mem_Hhat (Or.inr (Or.inr rfl))⟩ :=
  dif_pos rfl

theorem yamakiPre_of_ne {i : Fin 12} (hi : i ≠ 11) :
    yamakiPre ν θ i = ν.symm ⟨yamakiSp i, yamakiSp_mem_N0_of_ne hi⟩ :=
  dif_neg hi

theorem yamakiPre_mem_N {i : Fin 12} (hi : i ≠ 11) : yamakiPre ν θ i ∈ N := by
  rw [yamakiPre_of_ne ν θ hi]
  exact (ν.symm _).2

theorem apply_yamakiPre {i : Fin 12} (hi : i ≠ 11) (h : yamakiPre ν θ i ∈ N) :
    ν ⟨yamakiPre ν θ i, h⟩ = ⟨yamakiSp i, yamakiSp_mem_N0_of_ne hi⟩ := by
  rw [show (⟨yamakiPre ν θ i, h⟩ : ↥N) = ν.symm ⟨yamakiSp i, yamakiSp_mem_N0_of_ne hi⟩ from
    Subtype.ext (yamakiPre_of_ne ν θ hi), MulEquiv.apply_symm_apply]

theorem yamakiPre_mul_self (i : Fin 12) : yamakiPre ν θ i * yamakiPre ν θ i = 1 := by
  by_cases h : i = 11
  · subst h
    rw [yamakiPre_eleven]
    exact mul_self_eq_one_of_hom (H.subtype.comp θ.symm.toMonoidHom)
      (g := ⟨yamakiSp 11, yamakiSp_mem_Hhat (Or.inr (Or.inr rfl))⟩)
      (Subtype.ext (yamakiSp_mul_self 11))
  · rw [yamakiPre_of_ne ν θ h]
    exact mul_self_eq_one_of_hom (N.subtype.comp ν.symm.toMonoidHom)
      (g := ⟨yamakiSp i, yamakiSp_mem_N0_of_ne h⟩) (Subtype.ext (yamakiSp_mul_self i))

variable {ν θ}

theorem yamakiPre_mem_H_of_ne
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {i : Fin 12} (h9 : i ≠ 9) (h11 : i ≠ 11) : yamakiPre ν θ i ∈ H :=
  hνX _ (yamakiPre_mem_N ν θ h11) (by
    rw [apply_yamakiPre ν θ h11]
    exact yamakiSp_mem_X0_of_ne h9 h11)

theorem yamakiPre_eq_symm_theta
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {i : Fin 12} (h9 : i ≠ 9) :
    yamakiPre ν θ i = θ.symm ⟨yamakiSp i, yamakiSp_mem_Hhat_of_ne h9⟩ := by
  by_cases h11 : i = 11
  · subst h11
    exact yamakiPre_eleven ν θ
  · have hH := yamakiPre_mem_H_of_ne (θ := θ) hνX h9 h11
    have hθ : θ ⟨yamakiPre ν θ i, hH⟩ = ⟨yamakiSp i, yamakiSp_mem_Hhat_of_ne h9⟩ := by
      apply Subtype.ext
      rw [← hagree _ (yamakiPre_mem_N ν θ h11) hH, apply_yamakiPre ν θ h11]
    exact congrArg Subtype.val ((MulEquiv.eq_symm_apply θ).mpr hθ)

theorem yamakiPre_mem_H
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {i : Fin 12} (h9 : i ≠ 9) : yamakiPre ν θ i ∈ H := by
  rw [yamakiPre_eq_symm_theta hagree hνX h9]
  exact (θ.symm _).2

theorem apply_yamakiPre_theta
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {i : Fin 12} (h9 : i ≠ 9) (h : yamakiPre ν θ i ∈ H) :
    θ ⟨yamakiPre ν θ i, h⟩ = ⟨yamakiSp i, yamakiSp_mem_Hhat_of_ne h9⟩ := by
  rw [show (⟨yamakiPre ν θ i, h⟩ : ↥H) = θ.symm ⟨yamakiSp i, yamakiSp_mem_Hhat_of_ne h9⟩ from
    Subtype.ext (yamakiPre_eq_symm_theta hagree hνX h9), MulEquiv.apply_symm_apply]

end Generators

section Relations

variable {G : Type*} [Group G] {N H : Subgroup G}
  {ν : ↥N ≃* ↥N0} {θ : ↥H ≃* ↥Hhat}

theorem lift_yamakiPre_rel_of_ne
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {r : List (Fin 12 × Bool)} (hr : r ∈ yamakiRels) (hne : r ≠ posW [9, 11, 9, 11]) :
    FreeGroup.lift (yamakiPre ν θ) (FreeGroup.mk r) = 1 := by
  rcases yamakiRels_letters r hr hne with h | h
  · exact lift_mk_eq_one_of_letters (N.subtype.comp ν.symm.toMonoidHom) (p := fun i => i ≠ 11)
      (fun _ hi => yamakiSp_mem_N0_of_ne hi) (fun _ hi => yamakiPre_of_ne ν θ hi) h
      (lift_yamakiSp_rel hr)
  · exact lift_mk_eq_one_of_letters (H.subtype.comp θ.symm.toMonoidHom) (p := fun i => i ≠ 9)
      (fun _ hi => yamakiSp_mem_Hhat_of_ne hi) (fun _ hi => yamakiPre_eq_symm_theta hagree hνX hi)
      h (lift_yamakiSp_rel hr)

theorem semiconjBy_yamakiPre
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    {w a b : Fin 12} (hr : relW (posW [w, a, w]) (posW [b]) ∈ yamakiRels) :
    SemiconjBy (yamakiPre ν θ w) (yamakiPre ν θ a) (yamakiPre ν θ b) := by
  have h := lift_yamakiPre_rel_of_ne hagree hνX hr (by simp [relW, posW, invW])
  rw [lift_mk_eq_prod (yamakiPre_mul_self ν θ)] at h
  simp only [relW, posW, invW, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one] at h
  have h' : yamakiPre ν θ w * yamakiPre ν θ a * (yamakiPre ν θ w * yamakiPre ν θ b) = 1 := by
    simpa only [mul_assoc] using h
  show yamakiPre ν θ w * yamakiPre ν θ a = yamakiPre ν θ b * yamakiPre ν θ w
  rw [eq_inv_of_mul_eq_one_left h', _root_.mul_inv_rev,
    inv_eq_of_mul_eq_one_right (yamakiPre_mul_self ν θ b),
    inv_eq_of_mul_eq_one_right (yamakiPre_mul_self ν θ w)]

theorem lift_yamakiPre_w13
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    (hC : Subgroup.centralizer {(θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : G)} ≤ H) :
    FreeGroup.lift (yamakiPre ν θ) (FreeGroup.mk (posW [9, 11, 9, 11])) = 1 := by
  refine lift_w13_of (yamakiPre_mul_self ν θ) (fun _ _ _ hr => semiconjBy_yamakiPre hagree hνX hr)
    (lift_yamakiPre_rel_of_ne hagree hνX (by decide) (by decide)) fun hc => ?_
  have he : (θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : G) = yamakiPre ν θ 5 :=
    (yamakiPre_eq_symm_theta hagree hνX (by decide)).symm
  have hcH : yamakiPre ν θ 9 * yamakiPre ν θ 11 * (yamakiPre ν θ 9 * yamakiPre ν θ 11) ∈ H :=
    hC (Subgroup.mem_centralizer_iff.mpr fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      rw [hg, he]
      exact (hc 5 (by decide) (by decide)).symm.eq)
  have hθ : ∀ i : Fin 12, 1 ≤ i.val → i.val ≤ 7 →
      Commute (θ ⟨_, hcH⟩ : StatedSp 3 (ZMod 2)) (yamakiSp i) := by
    intro i h1 h7
    have h9 : i ≠ 9 := by
      rintro rfl
      revert h7
      decide
    have hH := yamakiPre_mem_H hagree hνX h9
    have h := ((show Commute (⟨_, hcH⟩ : ↥H) ⟨yamakiPre ν θ i, hH⟩ from
      Subtype.ext (hc i h1 h7)).map θ).map Hhat.subtype
    rwa [apply_yamakiPre_theta hagree hνX h9 hH] at h
  have h8 := commute_yamakiSp_eight hθ
  have hH8 := yamakiPre_mem_H hagree hνX (i := 8) (by decide)
  have h' : Commute (θ ⟨_, hcH⟩) (θ ⟨yamakiPre ν θ 8, hH8⟩) := by
    rw [apply_yamakiPre_theta hagree hνX (by decide) hH8]
    exact Subtype.ext h8
  have h'' := (h'.map θ.symm).map H.subtype
  simpa only [MulEquiv.symm_apply_apply, Subgroup.coe_subtype] using h''

theorem lift_yamakiPre_rel
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    (hC : Subgroup.centralizer {(θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : G)} ≤ H)
    {r : List (Fin 12 × Bool)} (hr : r ∈ yamakiRels) :
    FreeGroup.lift (yamakiPre ν θ) (FreeGroup.mk r) = 1 := by
  by_cases hne : r = posW [9, 11, 9, 11]
  · rw [hne]
    exact lift_yamakiPre_w13 hagree hνX hC
  · exact lift_yamakiPre_rel_of_ne hagree hνX hr hne

end Relations

section Recognition

variable {G : Type*} [Group G] {N H : Subgroup G}
  {ν : ↥N ≃* ↥N0} {θ : ↥H ≃* ↥Hhat}

theorem le_closure_range_yamakiPre_left :
    N ≤ Subgroup.closure (Set.range (yamakiPre ν θ)) := by
  intro n hn
  have htop : Subgroup.closure (((↑) : ↥N0 → StatedSp 3 (ZMod 2)) ⁻¹'
      (yamakiSp '' {i | i.val ≤ 8 ∨ i = 9 ∨ i = 10})) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : (⊤ : Subgroup ↥N0) ≤ (Subgroup.closure (Set.range (yamakiPre ν θ))).comap
      (N.subtype.comp ν.symm.toMonoidHom) := by
    rw [← htop, Subgroup.closure_le]
    rintro ⟨g, hg⟩ ⟨i, hi, hgi⟩
    change yamakiSp i = g at hgi
    subst hgi
    have h11 : i ≠ 11 := by
      rintro rfl
      simp only [Set.mem_setOf_eq] at hi
      revert hi
      decide
    exact Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨i, yamakiPre_of_ne ν θ h11⟩)
  have h := Subgroup.mem_comap.mp (hle (Subgroup.mem_top (ν ⟨n, hn⟩)))
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
  exact h

theorem le_closure_range_yamakiPre_right
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H) :
    H ≤ Subgroup.closure (Set.range (yamakiPre ν θ)) := by
  intro n hn
  have htop : Subgroup.closure (((↑) : ↥Hhat → StatedSp 3 (ZMod 2)) ⁻¹'
      (yamakiSp '' {i | i.val ≤ 8 ∨ i = 10 ∨ i = 11})) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : (⊤ : Subgroup ↥Hhat) ≤ (Subgroup.closure (Set.range (yamakiPre ν θ))).comap
      (H.subtype.comp θ.symm.toMonoidHom) := by
    rw [← htop, Subgroup.closure_le]
    rintro ⟨g, hg⟩ ⟨i, hi, hgi⟩
    change yamakiSp i = g at hgi
    subst hgi
    have h9 : i ≠ 9 := by
      rintro rfl
      simp only [Set.mem_setOf_eq] at hi
      revert hi
      decide
    exact Subgroup.mem_comap.mpr
      (Subgroup.subset_closure ⟨i, yamakiPre_eq_symm_theta hagree hνX h9⟩)
  have h := Subgroup.mem_comap.mp (hle (Subgroup.mem_top (θ ⟨n, hn⟩)))
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h
  exact h

theorem sup_eq_closure_range_yamakiPre
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H) :
    N ⊔ H = Subgroup.closure (Set.range (yamakiPre ν θ)) := by
  apply le_antisymm (sup_le le_closure_range_yamakiPre_left
    (le_closure_range_yamakiPre_right hagree hνX))
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  by_cases h : i = 11
  · subst h
    exact Subgroup.mem_sup_right (yamakiPre_mem_H hagree hνX (by decide))
  · exact Subgroup.mem_sup_left (yamakiPre_mem_N ν θ h)

private theorem yamakiSp_zero_ne_one : yamakiSp 0 ≠ 1 := by
  intro h
  have h' := congrArg (fun g => spMat g (Sum.inl 1) (Sum.inl 1)) h
  simp only [spMat_yamakiSp, map_one] at h'
  revert h'
  decide

private theorem hom_ext_closure_yamakiSp {P : Type*} [Group P] {S : Set (Fin 12)}
    {ψ₁ ψ₂ : ↥(Subgroup.closure (yamakiSp '' S)) →* P}
    (h : ∀ i (hi : i ∈ S), ψ₁ ⟨yamakiSp i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩ =
      ψ₂ ⟨yamakiSp i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩) :
    ψ₁ = ψ₂ := by
  apply MonoidHom.eq_of_eqOn_dense Subgroup.closure_closure_coe_preimage
  rintro ⟨g, hg⟩ ⟨i, hi, hgi⟩
  change yamakiSp i = g at hgi
  subst hgi
  exact h i hi

theorem exists_mulEquiv_sup
    (hagree : ∀ x (hN : x ∈ N) (hH : x ∈ H), (ν ⟨x, hN⟩ : StatedSp 3 (ZMod 2)) = θ ⟨x, hH⟩)
    (hνX : ∀ x (hx : x ∈ N), (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 → x ∈ H)
    (hC : Subgroup.centralizer {(θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : G)} ≤ H) :
    ∃ f : ↥(N ⊔ H) ≃* StatedSp 3 (ZMod 2),
      (∀ i (h : yamakiPre ν θ i ∈ N ⊔ H), f ⟨yamakiPre ν θ i, h⟩ = yamakiSp i) ∧
      (∀ x (hx : x ∈ N), f ⟨x, Subgroup.mem_sup_left hx⟩ = ν ⟨x, hx⟩) ∧
      (∀ x (hx : x ∈ H), f ⟨x, Subgroup.mem_sup_right hx⟩ = θ ⟨x, hx⟩) := by
  have hsup := sup_eq_closure_range_yamakiPre hagree hνX
  rcases closure_eq_bot_or_exists_mulEquiv (yamakiPre ν θ)
      (fun r hr => lift_yamakiPre_rel hagree hνX hC hr) with hbot | ⟨f₀, hf₀⟩
  · exfalso
    have h0 : yamakiPre ν θ 0 = 1 := by
      rw [← Subgroup.mem_bot, ← hbot]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    have h1 : (⟨yamakiPre ν θ 0, yamakiPre_mem_N ν θ (by decide)⟩ : ↥N) = 1 := Subtype.ext h0
    have h2 := apply_yamakiPre ν θ (i := 0) (by decide) (yamakiPre_mem_N ν θ (by decide))
    rw [h1, map_one] at h2
    exact yamakiSp_zero_ne_one (congrArg Subtype.val h2).symm
  obtain ⟨f, hfdef⟩ : ∃ f : ↥(N ⊔ H) ≃* StatedSp 3 (ZMod 2),
      f = (MulEquiv.subgroupCongr hsup).trans f₀ := ⟨_, rfl⟩
  have hgen : ∀ (z : ↥(N ⊔ H)) (i : Fin 12), (z : G) = yamakiPre ν θ i → f z = yamakiSp i := by
    intro z i hz
    rw [hfdef, MulEquiv.trans_apply, ← hf₀ i]
    congr 1
    exact Subtype.ext hz
  refine ⟨f, fun i h => hgen _ i rfl, fun n hn => ?_, fun n hn => ?_⟩
  · have key : (f.toMonoidHom.comp (Subgroup.inclusion le_sup_left)).comp ν.symm.toMonoidHom =
        N0.subtype := by
      apply hom_ext_closure_yamakiSp
      intro i hi
      have h11 : i ≠ 11 := by
        rintro rfl
        simp only [Set.mem_setOf_eq] at hi
        revert hi
        decide
      exact hgen (Subgroup.inclusion le_sup_left (ν.symm ⟨yamakiSp i, yamakiSp_mem_N0_of_ne h11⟩))
        i (yamakiPre_of_ne ν θ h11).symm
    have h := congrArg (fun ψ => ψ (ν ⟨n, hn⟩)) key
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h
  · have key : (f.toMonoidHom.comp (Subgroup.inclusion le_sup_right)).comp θ.symm.toMonoidHom =
        Hhat.subtype := by
      apply hom_ext_closure_yamakiSp
      intro i hi
      have h9 : i ≠ 9 := by
        rintro rfl
        simp only [Set.mem_setOf_eq] at hi
        revert hi
        decide
      exact hgen
        (Subgroup.inclusion le_sup_right (θ.symm ⟨yamakiSp i, yamakiSp_mem_Hhat_of_ne h9⟩))
        i (yamakiPre_eq_symm_theta hagree hνX h9).symm
    have h := congrArg (fun ψ => ψ (θ ⟨n, hn⟩)) key
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h
    exact h

end Recognition

end CFSG.ClassicalInvolution.Solomon73.Yamaki
