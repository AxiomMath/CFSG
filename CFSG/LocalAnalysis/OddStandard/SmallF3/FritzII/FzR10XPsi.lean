module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XInd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XBas

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t tau lam rho : G} {Z E W Q R T : Subgroup G}

private lemma fzrAux_zmod2_eq_one (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  have key : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases key a with h0 | h1
  · exact absurd h0 h
  · exact h1

private lemma fzrAux_zmod4_two (a : ZMod 4) (h : a + a = 0) : a = 0 ∨ a = 2 := by
  have key : ∀ a : ZMod 4, a + a = 0 → a = 0 ∨ a = 2 := by decide
  exact key a h

private lemma fzrAux_x1_notin_Z (h : FzStr t tau lam rho Z E W Q R T) {x1 : G}
    (hx1Z : x1⁻¹ * (lam * x1 * lam⁻¹) ∉ Z) : x1 ∉ Z := by
  intro hx1
  apply hx1Z
  have hx2Z : lam * x1 * lam⁻¹ ∈ Z := h.nrm_Z lam h.lam_T x1 hx1
  exact Z.mul_mem (Z.inv_mem hx1) hx2Z

private lemma fzrAux_x2_notin_Z (h : FzStr t tau lam rho Z E W Q R T) {x1 : G}
    (hx1Z : x1 ∉ Z) : lam * x1 * lam⁻¹ ∉ Z := by
  intro hx2Z
  apply hx1Z
  have h1 : lam⁻¹ * (lam * x1 * lam⁻¹) * (lam⁻¹)⁻¹ = x1 := by group
  rw [← h1]
  exact h.nrm_Z lam⁻¹ (T.inv_mem h.lam_T) _ hx2Z

private lemma fzrAux_surj [Finite G] {t x1 x2 : G} {W : Subgroup G} (hW : Nat.card W = 32)
    (hmem : ∀ v, fzxElt t x1 x2 v ∈ W) (hinj : Function.Injective (fzxElt t x1 x2)) :
    ∀ w ∈ W, ∃ v, fzxElt t x1 x2 v = w := by
  intro w hw
  let f : FzXW → W := fun v => ⟨fzxElt t x1 x2 v, hmem v⟩
  have hfinj : Function.Injective f := fun v v' hv => hinj (Subtype.ext_iff.mp hv)
  have hcard : Nat.card W ≤ Nat.card FzXW := by
    rw [hW]
    simp only [Nat.card_prod, Nat.card_zmod]
    norm_num
  have hbij : Function.Bijective f := hfinj.bijective_of_nat_card_le hcard
  obtain ⟨v, hv⟩ := hbij.2 ⟨w, hw⟩
  exact ⟨v, congrArg Subtype.val hv⟩

private lemma fzrAux_E_iff (h : FzStr t tau lam rho Z E W Q R T) {x1 x2 : G}
    (hx1 : x1 ∈ E) (hx2 : x2 ∈ E) :
    ∀ v, fzxElt t x1 x2 v ∈ E ↔ v.1 = 0 := by
  intro v
  constructor
  · intro hv
    by_contra hne
    have h1 : v.1 = 1 := fzrAux_zmod2_eq_one v.1 hne
    have hv1 : v.1.val = 1 := by rw [h1]; rfl
    have he : x1 ^ v.2.1.val * x2 ^ v.2.2.val ∈ E :=
      E.mul_mem (E.pow_mem hx1 _) (E.pow_mem hx2 _)
    have hte : t * (x1 ^ v.2.1.val * x2 ^ v.2.2.val) ∈ E := by
      have h' : t ^ v.1.val * x1 ^ v.2.1.val * x2 ^ v.2.2.val ∈ E := hv
      rw [hv1, pow_one, mul_assoc] at h'
      exact h'
    have h2 : t * (x1 ^ v.2.1.val * x2 ^ v.2.2.val) *
        (x1 ^ v.2.1.val * x2 ^ v.2.2.val)⁻¹ ∈ E := E.mul_mem hte (E.inv_mem he)
    rw [mul_inv_cancel_right] at h2
    exact h.t_notin_E h2
  · intro hv0
    have hv0' : v.1.val = 0 := by rw [hv0]; exact ZMod.val_zero
    simp only [fzxElt, hv0', pow_zero, one_mul]
    exact E.mul_mem (E.pow_mem hx1 _) (E.pow_mem hx2 _)

private lemma fzrAux_Z_fzXZ (h : FzStr t tau lam rho Z E W Q R T) {x1 x2 : G}
    (hb : FzXBasis t x1 x2 W) (hE : ∀ v, fzxElt t x1 x2 v ∈ E ↔ v.1 = 0) :
    ∀ v, fzxElt t x1 x2 v ∈ Z → fzXZ v := by
  intro v hv
  have hv1 : v.1 = 0 := (hE v).1 (h.ZE hv)
  have hvv : v + v = 0 := by
    apply hb.inj
    calc fzxElt t x1 x2 (v + v) = fzxElt t x1 x2 v * fzxElt t x1 x2 v := hb.add v v
      _ = 1 := by simpa [pow_two] using h.Z_sq (fzxElt t x1 x2 v) hv
      _ = fzxElt t x1 x2 0 := fzxElt_zero.symm
  have h21 : v.2.1 = 0 ∨ v.2.1 = 2 := by
    have h : v.2.1 + v.2.1 = 0 := by
      simpa using congrArg (fun w : FzXW => w.2.1) hvv
    exact fzrAux_zmod4_two v.2.1 h
  have h22 : v.2.2 = 0 ∨ v.2.2 = 2 := by
    have h : v.2.2 + v.2.2 = 0 := by
      simpa using congrArg (fun w : FzXW => w.2.2) hvv
    exact fzrAux_zmod4_two v.2.2 h
  exact ⟨hv1, h21, h22⟩

theorem fzr_x_basis [Finite G] (h : FzStr t tau lam rho Z E W Q R T) :
    ∃ x1 x2 : G, x1 ∈ E ∧ x2 ∈ E ∧ lam * x1 * lam⁻¹ = x2 ∧ FzXBasis t x1 x2 W ∧
      (∀ v, fzxElt t x1 x2 v ∈ E ↔ v.1 = 0) ∧ (∀ v, fzxElt t x1 x2 v ∈ Z → fzXZ v) := by
  obtain ⟨x1, hx1E, hx1Z⟩ := fzr_x_exists_x1 h
  obtain ⟨x2, hx2⟩ : ∃ x2 : G, x2 = lam * x1 * lam⁻¹ := ⟨_, rfl⟩
  have hx2E : x2 ∈ E := by rw [hx2]; exact h.lam_E.1 x1 hx1E
  have h12Z : x1⁻¹ * x2 ∉ Z := by rw [hx2]; exact hx1Z
  have hx1Z' : x1 ∉ Z := fzrAux_x1_notin_Z h hx1Z
  have hx2Z' : x2 ∉ Z := by rw [hx2]; exact fzrAux_x2_notin_Z h hx1Z'
  have htx1 : t * x1 = x1 * t := h.W_comm t h.t_mem x1 (h.EW hx1E)
  have htx2 : t * x2 = x2 * t := h.W_comm t h.t_mem x2 (h.EW hx2E)
  have h12 : x1 * x2 = x2 * x1 := h.W_comm x1 (h.EW hx1E) x2 (h.EW hx2E)
  have hmem : ∀ v, fzxElt t x1 x2 v ∈ W := by
    intro v
    have hv : t ^ v.1.val * x1 ^ v.2.1.val * x2 ^ v.2.2.val ∈ W :=
      W.mul_mem (W.mul_mem (W.pow_mem h.t_mem v.1.val) (W.pow_mem (h.EW hx1E) v.2.1.val))
        (W.pow_mem (h.EW hx2E) v.2.2.val)
    exact hv
  have hinj : Function.Injective (fzxElt t x1 x2) :=
    fzxElt_inj h hx1E hx2E hx1Z' hx2Z' h12Z
  have hadd : ∀ v v', fzxElt t x1 x2 (v + v') = fzxElt t x1 x2 v * fzxElt t x1 x2 v' :=
    fzxElt_add h.t_sq (h.E_exp x1 hx1E) (h.E_exp x2 hx2E) htx1 htx2 h12
  have hsurj : ∀ w ∈ W, ∃ v, fzxElt t x1 x2 v = w :=
    fzrAux_surj h.card_W hmem hinj
  have hbasis : FzXBasis t x1 x2 W := ⟨hmem, hsurj, hinj, hadd⟩
  have hE : ∀ v, fzxElt t x1 x2 v ∈ E ↔ v.1 = 0 := fzrAux_E_iff h hx1E hx2E
  have hZ : ∀ v, fzxElt t x1 x2 v ∈ Z → fzXZ v := fzrAux_Z_fzXZ h hbasis hE
  exact ⟨x1, x2, hx1E, hx2E, hx2.symm, hbasis, hE, hZ⟩

end CFSG.OddStandard.SmallF3.FritzII
