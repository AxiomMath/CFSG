module

public import CFSG.Certificates.Kernel.U62PairMat
public import CFSG.LargeExtraspecial.SMod20AutPlane

public section

namespace CFSG.KC.U62P.Snd

open CFSG.Fischer Matrix CFSG.KC.F4M CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.F4M.Aux
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LargeExtraspecial.SMod20.Aut (frob4 fieldPerm semiPerm fvec glAut_mem_GU0 ptOf ptOf_val
  ptOf_eq_ptOf_iff fvec_uVec_ne_zero fvec_uVec_iso)

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem unitary_of_isom {g : Matrix (Fin 6) (Fin 6) F4} (h : IsIsom g) :
    gᵀ * g.map (fun a => a ^ 2) = 1 := by
  ext a b
  have := h (e a) (e b)
  rw [mulVec_e, mulVec_e, herm_eq, herm_e_left] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply] at this ⊢
  rw [this]
  by_cases hab : a = b
  · subst hab
    simp [e]
  · simp [e, hab]

theorem isom_of_mem {g : GL (Fin 6) F4} (h : g ∈ GU0) : IsIsom (g : Matrix (Fin 6) (Fin 6) F4) := h

@[expose] def RepSU (M : ℕ) (g : SU0) : Prop :=
  ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = decM M

theorem RepSU_ONE : RepSU ONE 1 := by
  unfold RepSU
  rw [decM_ONE]
  rfl

theorem RepSU_mul {A B : ℕ} {g h : SU0} (hg : RepSU A g) (hh : RepSU B h) :
    RepSU (mulK A B) (g * h) := by
  unfold RepSU at *
  rw [decM_mulK, ← hg, ← hh]
  rfl

theorem RepSU_inv {A : ℕ} {g : SU0} (hg : RepSU A g) : RepSU (invK A) g⁻¹ := by
  unfold RepSU at *
  rw [decM_invK, ← hg]
  have hu := unitary_of_isom (isom_of_mem (SU0_le_GU0 g.2))
  have h2 : (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).map (fun a => a ^ 2))ᵀ *
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
    have := congrArg Matrix.transpose hu
    simpa [Matrix.transpose_mul] using this
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv h2

theorem frSU_mem (g : SU0) : glAut frob4 (g : GL (Fin 6) F4) ∈ SU0 := by
  rw [mem_SU0]
  obtain ⟨hdet, -⟩ := mem_SU0.1 g.2
  refine ⟨?_, glAut_mem_GU0 frob4 (SU0_le_GU0 g.2)⟩
  have h1 : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).det = 1 := by
    have := congrArg Units.val hdet
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_glAut, Units.val_one]
  have h2 := RingEquiv.map_det frob4 ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  rw [h1, map_one] at h2
  exact h2.symm

@[expose] noncomputable def frSU : SU0 →* SU0 :=
  MonoidHom.mk' (fun g => ⟨glAut frob4 (g : GL (Fin 6) F4), frSU_mem g⟩) (fun g h => by
    apply Subtype.ext
    exact map_mul (glAut frob4) _ _)

theorem frSU_val (g : SU0) : ((frSU g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).map (fun a => a ^ 2) := by
  change ((glAut frob4 (g : GL (Fin 6) F4) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = _
  rw [coe_glAut]
  rfl

theorem RepSU_barK {A : ℕ} {g : SU0} (hg : RepSU A g) : RepSU (barK A) (frSU g) := by
  unfold RepSU at *
  rw [decM_barK, ← hg, frSU_val]

section Perm

theorem fieldPerm_inv : (fieldPerm frob4)⁻¹ = fieldPerm frob4 := by
  have e : (fieldPerm frob4)⁻¹ = fieldPerm frob4.symm := by
    ext p
    rfl
  have e2 : frob4.symm = frob4 := RingEquiv.ext fun x => rfl
  rw [e, e2]

theorem conj_frSU (g : SU0) :
    fieldPerm frob4 * piSU g * (fieldPerm frob4)⁻¹ = piSU (frSU g) := by
  have h := CFSG.LargeExtraspecial.SMod20.Aut.conj_semiPerm 1 frob4 ⟨g, SU0_le_GU0 g.2⟩
  rw [semiPerm, map_one, one_mul] at h
  have e : CFSG.LargeExtraspecial.SMod20.Aut.semiConj 1 frob4 ⟨g, SU0_le_GU0 g.2⟩ =
      ⟨glAut frob4 (g : GL (Fin 6) F4), glAut_mem_GU0 frob4 (SU0_le_GU0 g.2)⟩ := by
    apply Subtype.ext
    rw [CFSG.LargeExtraspecial.SMod20.Aut.coe_semiConj]
    simp
  rw [e] at h
  exact h

theorem piSU_scalar {c : F4} (hc : c ≠ 0) {g : SU0}
    (h : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • 1) : piSU g = 1 := by
  have hg : g = ⟨scalarGL (Units.mk0 c hc), scalarGL_mem _⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [scalarGL_val]
    exact h
  have hz : g ∈ Subgroup.center SU0 := by
    rw [hg, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact (scalarGL_central _ _).symm
  exact MonoidHom.mem_ker.1 (center_le_ker hz)

theorem card_ker_le : Nat.card piSU.ker ≤ 3 := by
  have h1 := card_SU0_eq
  rw [range_piSU, card_T46] at h1
  have h2 := card_SU0_mul_three_le
  have h3 := card_GU0_le
  omega

theorem ker_scalar {g : SU0} (h : piSU g = 1) :
    ∃ c : F4, c ≠ 0 ∧ ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • 1 := by
  let f : F4ˣ → piSU.ker := fun c => ⟨⟨scalarGL c, scalarGL_mem c⟩,
    MonoidHom.mem_ker.2 (piSU_scalar c.ne_zero (by
      change ((scalarGL c : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = (c : F4) • 1
      exact scalarGL_val c))⟩
  have hinj : Function.Injective f := by
    intro c d hcd
    apply scalarGL_injective
    exact congrArg (fun x : piSU.ker => ((x : SU0) : GL (Fin 6) F4)) hcd
  have hcard : Nat.card piSU.ker ≤ Nat.card F4ˣ := by
    have h4 : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
    rw [Nat.card_units, h4]
    have := card_ker_le
    omega
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨g, MonoidHom.mem_ker.2 h⟩
  refine ⟨c, c.ne_zero, ?_⟩
  have := congrArg (fun x : piSU.ker => ((x : SU0) : GL (Fin 6) F4)) hc
  change scalarGL c = (g : GL (Fin 6) F4) at this
  rw [← this]
  exact scalarGL_val c

theorem piSU_eq_iff {A B : ℕ} {g h : SU0} (hg : RepSU A g)
    (hh : RepSU B h) : piSU g = piSU h ↔ ProjEq A B := by
  unfold RepSU at hg hh
  constructor
  · intro e
    have e1 : piSU (g * h⁻¹) = 1 := by rw [map_mul, map_inv, e, mul_inv_cancel]
    obtain ⟨c, hc, hmat⟩ := ker_scalar e1
    refine ⟨c, hc, ?_⟩
    have e2 : g = (g * h⁻¹) * h := (inv_mul_cancel_right g h).symm
    have e3 : ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
        (((g * h⁻¹ * h : SU0)) : GL (Fin 6) F4) :=
      congrArg (fun x : SU0 => ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) e2
    rw [Subgroup.coe_mul, Units.val_mul] at e3
    rw [← hg, e3, hmat, ← hh, Matrix.smul_mul, Matrix.one_mul]
  · rintro ⟨c, hc, hmat⟩
    have key : (((g * h⁻¹ : SU0) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • 1 := by
      rw [Subgroup.coe_mul, Units.val_mul, hg, hmat, ← hh, Matrix.smul_mul, Subgroup.coe_inv,
        Units.mul_inv]
    have e1 := piSU_scalar hc key
    rw [map_mul, map_inv, mul_inv_eq_one] at e1
    exact e1

theorem piSU_eq_of_eqP {A B : ℕ} {g h : SU0} (hg : RepSU A g)
    (hh : RepSU B h) (e : eqP A B = true) : piSU g = piSU h :=
  (piSU_eq_iff hg hh).2 (eqP_sound e)

theorem eqP_of_piSU_eq {A B : ℕ} {g h : SU0} (hg : RepSU A g)
    (hh : RepSU B h) (hA : A < 2 ^ 72) (hB : B < 2 ^ 72) (e : piSU g = piSU h) :
    eqP A B = true :=
  eqP_complete hA hB ((piSU_eq_iff hg hh).1 e)

theorem isScal_iff {M : ℕ} {g : SU0} (hg : RepSU M g)
    (hM : M < 2 ^ 72) : isScal M = true ↔ piSU g = 1 := by
  constructor
  · intro h
    have := piSU_eq_of_eqP hg RepSU_ONE h
    rwa [map_one] at this
  · intro h
    exact eqP_of_piSU_eq hg RepSU_ONE hM ONE_lt (by rw [h, map_one])

theorem piSU_val (g : SU0) (p : Fin 693) :
    (piSU g p).val = ptIdx (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) :=
  piSU_apply g p

theorem fieldPerm_val (p : Fin 693) :
    (fieldPerm frob4 p).val = ptIdx (fvec frob4 (uVec p)) := rfl

theorem piSU_fix_iff (g : SU0) (p : Fin 693) :
    piSU g p = p ↔ ∃ c : F4, c ≠ 0 ∧
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p = c • uVec p := by
  have hw := mulVec_ne_zero (g : GL (Fin 6) F4) (uVec_ne_zero ptsFacts p.2)
  have hiso : hermStd (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) = 0 := by
    rw [hermStd_mulVec ⟨g, SU0_le_GU0 g.2⟩]
    exact uVec_iso ptsFacts p.2
  have h0 := uVec_ne_zero ptsFacts p.2
  have hi0 := uVec_iso ptsFacts p.2
  constructor
  · intro h
    have h1 : ptOf _ hw hiso = ptOf (uVec p) h0 hi0 := by
      apply Fin.ext
      rw [ptOf_val, ptOf_val, ptIdx_uVec ptsFacts p.2, ← piSU_val, h]
    obtain ⟨c, hc, hcv⟩ := (ptOf_eq_ptOf_iff hw hiso h0 hi0).1 h1
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    calc ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p
        = c⁻¹ • (c • ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • uVec p := by rw [← hcv]
  · rintro ⟨c, hc, h⟩
    apply Fin.ext
    rw [piSU_val, h, ptIdx_smul hc, ptIdx_uVec ptsFacts p.2]

theorem piSU_eq_phi_iff (g : SU0) (p : Fin 693) :
    piSU g p = fieldPerm frob4 p ↔ ∃ c : F4, c ≠ 0 ∧
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p = c • fvec frob4 (uVec p) := by
  have hw := mulVec_ne_zero (g : GL (Fin 6) F4) (uVec_ne_zero ptsFacts p.2)
  have hiso : hermStd (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) = 0 := by
    rw [hermStd_mulVec ⟨g, SU0_le_GU0 g.2⟩]
    exact uVec_iso ptsFacts p.2
  have h0 := fvec_uVec_ne_zero frob4 p
  have hi0 := fvec_uVec_iso frob4 p
  constructor
  · intro h
    have h1 : ptOf _ hw hiso = ptOf (fvec frob4 (uVec p)) h0 hi0 := by
      apply Fin.ext
      rw [ptOf_val, ptOf_val, ← piSU_val, ← fieldPerm_val, h]
    obtain ⟨c, hc, hcv⟩ := (ptOf_eq_ptOf_iff hw hiso h0 hi0).1 h1
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    calc ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p
        = c⁻¹ • (c • ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec p) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • fvec frob4 (uVec p) := by rw [← hcv]
  · rintro ⟨c, hc, h⟩
    apply Fin.ext
    rw [piSU_val, h, ptIdx_smul hc, fieldPerm_val]

end Perm

theorem f72_lt (T k : ℕ) : f72 T k < 2 ^ 72 :=
  Nat.and_lt_two_pow _ (by norm_num)

theorem RepSU_wordK {F : ℕ → ℕ} {g : ℕ → SU0} (w : List ℕ) (hF : ∀ z ∈ w, RepSU (F z) (g z)) :
    RepSU (wordK F w) (w.map g).prod := by
  induction w with
  | nil => exact RepSU_ONE
  | cons z w ih =>
    exact RepSU_mul (hF z (List.mem_cons_self ..)) (ih fun y hy => hF y (List.mem_cons_of_mem _ hy))

theorem RepSU_powK {A : ℕ} {g : SU0} (hg : RepSU A g) (m : ℕ) : RepSU (powK A m) (g ^ m) := by
  induction m with
  | zero => exact RepSU_ONE
  | succ m ih =>
    change RepSU (strictN (powK A m) fun a => mulK a A) _
    rw [strictN_eq, pow_succ]
    exact RepSU_mul ih hg

theorem RepSU_prodK (b : ℕ) {F : ℕ → ℕ} (Q : SU0 → Prop) (hQm : ∀ x y, Q x → Q y → Q (x * y))
    (hQ1 : Q 1) : ∀ len : ℕ, (∀ l < len, ∃ g : SU0, RepSU (F (b + l)) g ∧ Q g) →
      ∃ γ : SU0, Q γ ∧ RepSU (prodK b F len) γ
  | 0, _ => ⟨1, hQ1, RepSU_ONE⟩
  | len + 1, hF => by
    obtain ⟨γ, hQγ, hγ⟩ := RepSU_prodK b Q hQm hQ1 len fun l hl => hF l (Nat.lt_succ_of_lt hl)
    obtain ⟨g, hg, hQg⟩ := hF len (Nat.lt_succ_self len)
    refine ⟨γ * g, hQm _ _ hQγ hQg, ?_⟩
    change RepSU (strictN (prodK b F len) fun a => mulK a (F (Nat.add b len))) _
    rw [strictN_eq]
    exact RepSU_mul hγ hg

theorem RepSU_prodK_prodRK (b : ℕ) {F : ℕ → ℕ} (Q : SU0 → Prop)
    (hQm : ∀ x y, Q x → Q y → Q (x * y)) (hQi : ∀ x, Q x → Q x⁻¹) (hQ1 : Q 1) :
    ∀ len : ℕ, (∀ l < len, ∃ g : SU0, RepSU (F (b + l)) g ∧ Q g) →
      ∃ γ : SU0, Q γ ∧ RepSU (prodK b F len) γ ∧
        RepSU (prodRK b (fun u => invK (F u)) len) γ⁻¹
  | 0, _ => ⟨1, hQ1, RepSU_ONE, by rw [inv_one]; exact RepSU_ONE⟩
  | len + 1, hF => by
    obtain ⟨γ, hQγ, hγ, hγi⟩ := RepSU_prodK_prodRK b Q hQm hQi hQ1 len
      fun l hl => hF l (Nat.lt_succ_of_lt hl)
    obtain ⟨g, hg, hQg⟩ := hF len (Nat.lt_succ_self len)
    refine ⟨γ * g, hQm _ _ hQγ hQg, ?_, ?_⟩
    · change RepSU (strictN (prodK b F len) fun a => mulK a (F (Nat.add b len))) _
      rw [strictN_eq]
      exact RepSU_mul hγ hg
    · change RepSU (strictN (prodRK b (fun u => invK (F u)) len)
        fun a => mulK (invK (F (Nat.add b len))) a) _
      rw [strictN_eq, _root_.mul_inv_rev]
      exact RepSU_mul (RepSU_inv hg) hγi

end CFSG.KC.U62P.Snd

end
