module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptFrame

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan Module

section General

variable {E : Type*} [Field E] {σ : E ≃+* E} {n : ℕ}

structure IsoSquare (σ : E ≃+* E) (g : Matrix (Fin n) (Fin n) E) (lam : E) : Prop where
  iso : ∀ u v, herm σ (g *ᵥ u) (g *ᵥ v) = herm σ u v
  sq : g * g = (lam * lam) • (1 : Matrix (Fin n) (Fin n) E)
  ne_zero : lam ≠ 0

structure IsotropicData (σ : E ≃+* E) (g : Matrix (Fin n) (Fin n) E) (lam : E) : Prop
    extends IsoSquare σ g lam where
  norm : σ lam * lam = -1

variable {g : Matrix (Fin n) (Fin n) E} {lam : E}

@[expose] def MulVecStable (g : Matrix (Fin n) (Fin n) E) (H : Submodule E (Fin n → E)) : Prop :=
  ∀ x ∈ H, g *ᵥ x ∈ H

theorem IsoSquare.mulVec_mulVec (h : IsoSquare σ g lam) (u : Fin n → E) :
    g *ᵥ (g *ᵥ u) = (lam * lam) • u := by
  rw [Matrix.mulVec_mulVec, h.sq, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem IsoSquare.mulVecStable_perp (h : IsoSquare σ g lam) {H : Submodule E (Fin n → E)}
    (hH : MulVecStable g H) : MulVecStable g (perp σ H) := by
  intro u hu s hs
  have hl : lam * lam ≠ 0 := mul_ne_zero h.ne_zero h.ne_zero
  have hs' : (lam * lam)⁻¹ • (g *ᵥ s) ∈ H := H.smul_mem _ (hH s hs)
  have e : g *ᵥ ((lam * lam)⁻¹ • (g *ᵥ s)) = s := by
    rw [Matrix.mulVec_smul, h.mulVec_mulVec, smul_smul, inv_mul_cancel₀ hl, one_smul]
  calc herm σ (g *ᵥ u) s = herm σ (g *ᵥ u) (g *ᵥ ((lam * lam)⁻¹ • (g *ᵥ s))) := by rw [e]
    _ = herm σ u ((lam * lam)⁻¹ • (g *ᵥ s)) := h.iso u _
    _ = 0 := hu _ hs'

theorem IsoSquare.herm_eq_zero_of_eig (h : IsoSquare σ g lam) (h2 : (2 : E) ≠ 0)
    {u v : Fin n → E} {a b : E} (hu : g *ᵥ u = a • u) (hv : g *ᵥ v = b • v)
    (hab : σ a * b = -1) : herm σ u v = 0 := by
  have h1 := h.iso u v
  rw [hu, hv, herm_smul_left, herm_smul_right, ← mul_assoc, hab] at h1
  have h3 : (2 : E) * herm σ u v = 0 := by linear_combination (-1 : E) * h1
  exact (mul_eq_zero.mp h3).resolve_left h2

theorem IsoSquare.exists_decomp (h : IsoSquare σ g lam) (h2 : (2 : E) ≠ 0) (u : Fin n → E) :
    ∃ a b : Fin n → E, g *ᵥ a = lam • a ∧ g *ᵥ b = -lam • b ∧ a + b = u ∧
      ∀ H : Submodule E (Fin n → E), MulVecStable g H → u ∈ H → a ∈ H ∧ b ∈ H := by
  have hl := h.ne_zero
  set t : E := (2 * lam)⁻¹ with ht
  have ht1 : t * (2 * lam) = 1 := inv_mul_cancel₀ (mul_ne_zero h2 hl)
  have hgu : g *ᵥ (g *ᵥ u) = (lam * lam) • u := h.mulVec_mulVec u
  refine ⟨t • (g *ᵥ u + lam • u), t • (lam • u - g *ᵥ u), ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, hgu]
    module
  · rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hgu]
    module
  · rw [← smul_add]
    have : g *ᵥ u + lam • u + (lam • u - g *ᵥ u) = (2 * lam) • u := by module
    rw [this, smul_smul, ht1, one_smul]
  · intro H hH huH
    exact ⟨H.smul_mem _ (H.add_mem (hH u huH) (H.smul_mem _ huH)),
      H.smul_mem _ (H.sub_mem (H.smul_mem _ huH) (hH u huH))⟩

variable (h : IsotropicData σ g lam)

include h

theorem IsotropicData.herm_eq_zero_pos (h2 : (2 : E) ≠ 0) {u v : Fin n → E}
    (hu : g *ᵥ u = lam • u) (hv : g *ᵥ v = lam • v) : herm σ u v = 0 :=
  h.toIsoSquare.herm_eq_zero_of_eig h2 hu hv h.norm

theorem IsotropicData.herm_eq_zero_neg (h2 : (2 : E) ≠ 0) {u v : Fin n → E}
    (hu : g *ᵥ u = -lam • u) (hv : g *ᵥ v = -lam • v) : herm σ u v = 0 :=
  h.toIsoSquare.herm_eq_zero_of_eig h2 hu hv (by rw [map_neg, neg_mul_neg, h.norm])

theorem IsotropicData.exists_hyperbolic_pair (hσ : IsUnitaryInvolution σ) (h2 : (2 : E) ≠ 0)
    {H : Submodule E (Fin n → E)} (hH : Nondeg σ H) (hne : H ≠ ⊥) (hst : MulVecStable g H) :
    ∃ a ∈ H, ∃ b ∈ H, g *ᵥ a = lam • a ∧ g *ᵥ b = -lam • b ∧ herm σ a b = 1 := by
  obtain ⟨x, hxH, hx⟩ := exists_aniso_of_nondeg hσ hH hne
  obtain ⟨a, b, haX, hbY, hab, hmem⟩ := h.toIsoSquare.exists_decomp h2 x
  obtain ⟨haH, hbH⟩ := hmem H hst hxH
  have haa : herm σ a a = 0 := h.herm_eq_zero_pos h2 haX haX
  have hbb : herm σ b b = 0 := h.herm_eq_zero_neg h2 hbY hbY
  have hab0 : herm σ a b ≠ 0 := by
    intro h0
    have h0' : herm σ b a = 0 := herm_eq_zero_comm σ hσ.invol h0
    apply hx
    rw [← hab, herm_add_left, herm_add_right, herm_add_right, haa, hbb, h0, h0']
    ring
  refine ⟨a, haH, (herm σ a b)⁻¹ • b, H.smul_mem _ hbH, haX, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hbY, smul_comm]
  · rw [herm_smul_right, inv_mul_cancel₀ hab0]

end General

section Plane

variable {E : Type*} [Field E] {σ : E ≃+* E} {n : ℕ}

theorem nondeg_span_hyperbolic (hσ : IsUnitaryInvolution σ) {a b : Fin n → E}
    (haa : herm σ a a = 0) (hbb : herm σ b b = 0) (hab : herm σ a b = 1) :
    Nondeg σ (Submodule.span E {a, b}) := by
  intro v hv hvt
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
  have hba : herm σ b a = 1 := by rw [herm_conj σ hσ.invol, hab, map_one]
  have hb : b ∈ Submodule.span E {a, b} := Submodule.subset_span (by simp)
  have ha : a ∈ Submodule.span E {a, b} := Submodule.subset_span (by simp)
  have h1 := hvt b hb
  have h2 := hvt a ha
  rw [herm_add_left, herm_smul_left, herm_smul_left, hab, hbb] at h1
  rw [herm_add_left, herm_smul_left, herm_smul_left, haa, hba] at h2
  have hc : c = 0 := by
    have : σ c = 0 := by simpa using h1
    exact (map_eq_zero_iff σ σ.injective).mp this
  have hd : d = 0 := by
    have : σ d = 0 := by simpa using h2
    exact (map_eq_zero_iff σ σ.injective).mp this
  rw [hc, hd]
  simp

theorem finrank_span_pair_le_two (a b : Fin n → E) : finrank E (Submodule.span E {a, b}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := E) ({a, b} : Finset (Fin n → E))
  rw [Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans Finset.card_le_two

variable {g : Matrix (Fin n) (Fin n) E}

theorem mulVecStable_span_pair {a b : Fin n → E} {c d : E} (ha : g *ᵥ a = c • a)
    (hb : g *ᵥ b = d • b) :
    MulVecStable g (Submodule.span E {a, b}) := by
  intro v hv
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb]
  have ha' : a ∈ Submodule.span E {a, b} := Submodule.subset_span (by simp)
  have hb' : b ∈ Submodule.span E {a, b} := Submodule.subset_span (by simp)
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ha'))
    (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hb'))

theorem MulVecStable.inf {H H' : Submodule E (Fin n → E)} (h : MulVecStable g H)
    (h' : MulVecStable g H') :
    MulVecStable g (H ⊓ H') := fun x hx => ⟨h x hx.1, h' x hx.2⟩

end Plane

section Basis

open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem mulVecStable_te6Minus {g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))}
    (hW : g * suMat (te6Inv p f) = suMat (te6Inv p f) * g) : MulVecStable g (te6Minus p f) := by
  intro u hu
  have hu' : suMat (te6Inv p f) *ᵥ u = -u := mem_minusSpaceSU.mp hu
  show g *ᵥ u ∈ minusSpaceSU (te6Inv p f)
  rw [mem_minusSpaceSU, Matrix.mulVec_mulVec, ← hW, ← Matrix.mulVec_mulVec, hu',
    Matrix.mulVec_neg]

theorem IsoSquare.mulVecStable_te6Plus {g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))}
    {lam : GaloisField p (2 * f)}
    (h : IsoSquare (unitaryInvolution (GaloisField p (2 * f)) p f) g lam)
    (hW : g * suMat (te6Inv p f) = suMat (te6Inv p f) * g) : MulVecStable g (te6Plus p f) :=
  h.mulVecStable_perp (mulVecStable_te6Minus hW)

theorem exists_adaptedBasis (hf : 1 ≤ f) (hp2 : p ≠ 2)
    {g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))} {lam : GaloisField p (2 * f)}
    (h : IsotropicData (unitaryInvolution (GaloisField p (2 * f)) p f) g lam)
    (hW : g * suMat (te6Inv p f) = suMat (te6Inv p f) * g) :
    ∃ P : GL (Fin 6) (GaloisField p (2 * f)), AdaptedBasis p f g P lam (-lam) := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_te6 hp2
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  have hW₀nd : Nondeg σ (te6Minus p f) := te6Minus_nondeg hp2
  have hW₀ne : te6Minus p f ≠ ⊥ := fun h0 => by
    have := finrank_te6Minus (p := p) (f := f) hp2
    rw [h0, finrank_bot] at this
    omega
  have hstW₀ : MulVecStable g (te6Minus p f) := mulVecStable_te6Minus hW
  have hEnd : Nondeg σ (te6Plus p f) := te6Plus_nondeg hp2 hf
  have hEne : te6Plus p f ≠ ⊥ := fun h0 => by
    have := finrank_te6Plus (p := p) (f := f) hp2 hf
    rw [h0, finrank_bot] at this
    omega
  have hstE : MulVecStable g (te6Plus p f) := h.toIsoSquare.mulVecStable_te6Plus hW
  obtain ⟨a₁, ha₁W, b₁, hb₁W, ha₁g, hb₁g, hab₁⟩ := h.exists_hyperbolic_pair hσ h2 hW₀nd hW₀ne hstW₀
  obtain ⟨a₂, ha₂E, b₂, hb₂E, ha₂g, hb₂g, hab₂⟩ := h.exists_hyperbolic_pair hσ h2 hEnd hEne hstE
  have ha₂a₂ : herm σ a₂ a₂ = 0 := h.herm_eq_zero_pos h2 ha₂g ha₂g
  have hb₂b₂ : herm σ b₂ b₂ = 0 := h.herm_eq_zero_neg h2 hb₂g hb₂g
  have hP2nd := nondeg_span_hyperbolic hσ ha₂a₂ hb₂b₂ hab₂
  have hP2E : Submodule.span (GaloisField p (2 * f)) {a₂, b₂} ≤ te6Plus p f := by
    refine Submodule.span_le.mpr ?_
    rintro _ (rfl | rfl)
    · exact ha₂E
    · exact hb₂E
  have hH2nd : Nondeg σ (te6Plus p f ⊓ perp σ (Submodule.span (GaloisField p (2 * f)) {a₂, b₂})) :=
    Nondeg.inf_perp hσ hEnd hP2nd hP2E
  have hH2ne : te6Plus p f ⊓ perp σ (Submodule.span (GaloisField p (2 * f)) {a₂, b₂}) ≠ ⊥ := by
    intro h0
    have h1 := finrank_eq_add_finrank_inf_perp hσ hP2nd hP2E
    rw [h0, finrank_bot, finrank_te6Plus hp2 hf] at h1
    have := finrank_span_pair_le_two (E := GaloisField p (2 * f)) a₂ b₂
    omega
  have hstH2 :
      MulVecStable g (te6Plus p f ⊓ perp σ (Submodule.span (GaloisField p (2 * f)) {a₂, b₂})) :=
    hstE.inf (h.toIsoSquare.mulVecStable_perp (mulVecStable_span_pair ha₂g hb₂g))
  obtain ⟨a₃, ha₃H, b₃, hb₃H, ha₃g, hb₃g, hab₃⟩ :=
    h.exists_hyperbolic_pair hσ h2 hH2nd hH2ne hstH2
  have hWE : ∀ v ∈ te6Plus p f, ∀ w ∈ te6Minus p f, herm σ v w = 0 ∧ herm σ w v = 0 :=
    fun v hv w hw => ⟨mem_perp.mp hv w hw, herm_eq_zero_comm σ hσ.invol (mem_perp.mp hv w hw)⟩
  have hPH : ∀ v ∈ perp σ (Submodule.span (GaloisField p (2 * f)) {a₂, b₂}),
      herm σ v a₂ = 0 ∧ herm σ v b₂ = 0 ∧ herm σ a₂ v = 0 ∧ herm σ b₂ v = 0 := by
    intro v hv
    have h1 : herm σ v a₂ = 0 := mem_perp.mp hv a₂ (Submodule.subset_span (by simp))
    have h2' : herm σ v b₂ = 0 := mem_perp.mp hv b₂ (Submodule.subset_span (by simp))
    exact ⟨h1, h2', herm_eq_zero_comm σ hσ.invol h1, herm_eq_zero_comm σ hσ.invol h2'⟩
  have ha₃E : a₃ ∈ te6Plus p f := ha₃H.1
  have hb₃E : b₃ ∈ te6Plus p f := hb₃H.1
  let A : Fin 3 → (Fin 6 → GaloisField p (2 * f)) := ![a₁, a₂, a₃]
  let B : Fin 3 → (Fin 6 → GaloisField p (2 * f)) := ![b₁, b₂, b₃]
  have hAg : ∀ k, g *ᵥ A k = lam • A k := by
    intro k; fin_cases k
    · exact ha₁g
    · exact ha₂g
    · exact ha₃g
  have hBg : ∀ k, g *ᵥ B k = -lam • B k := by
    intro k; fin_cases k
    · exact hb₁g
    · exact hb₂g
    · exact hb₃g
  have hAA : ∀ k l, herm σ (A k) (A l) = 0 := fun k l => h.herm_eq_zero_pos h2 (hAg k) (hAg l)
  have hBB : ∀ k l, herm σ (B k) (B l) = 0 := fun k l => h.herm_eq_zero_neg h2 (hBg k) (hBg l)
  have hAB : ∀ k l, herm σ (A k) (B l) = if k = l then 1 else 0 := by
    intro k l
    fin_cases k <;> fin_cases l
    · simpa [A, B] using hab₁
    · simpa [A, B] using (hWE b₂ hb₂E a₁ ha₁W).2
    · simpa [A, B] using (hWE b₃ hb₃E a₁ ha₁W).2
    · simpa [A, B] using (hWE a₂ ha₂E b₁ hb₁W).1
    · simpa [A, B] using hab₂
    · simpa [A, B] using (hPH b₃ hb₃H.2).2.2.1
    · simpa [A, B] using (hWE a₃ ha₃E b₁ hb₁W).1
    · simpa [A, B] using (hPH a₃ ha₃H.2).2.1
    · simpa [A, B] using hab₃
  have hBA : ∀ k l, herm σ (B l) (A k) = if k = l then 1 else 0 := by
    intro k l
    rw [herm_conj σ hσ.invol, hAB k l]
    split_ifs <;> simp
  let col : Fin 6 → (Fin 6 → GaloisField p (2 * f)) := fun c =>
    if hc : c.val < 3 then A ⟨2 - c.val, by omega⟩ else B ⟨c.val - 3, by omega⟩
  let M : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) := Matrix.of fun r c => col c r
  have hgram : conjTr σ M * M = antidiag 6 := by
    ext i j
    have e : (conjTr σ M * M) i j = herm σ (col i) (col j) := by
      simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, M,
        Matrix.of_apply]
      rfl
    rw [e]
    simp only [antidiag, Matrix.of_apply]
    by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
    · simp only [col, dite_eq_left hi, dite_eq_left hj, hAA]
      rw [ite_eq_right]
      intro hji
      have := congrArg Fin.val hji
      simp only [Fin.val_rev] at this
      omega
    · simp only [col, dite_eq_left hi, dite_eq_right hj, hAB]
      refine if_congr ?_ rfl rfl
      simp only [Fin.ext_iff, Fin.val_rev]
      omega
    · simp only [col, dite_eq_right hi, dite_eq_left hj, hBA]
      refine if_congr ?_ rfl rfl
      simp only [Fin.ext_iff, Fin.val_rev]
      omega
    · simp only [col, dite_eq_right hi, dite_eq_right hj, hBB]
      rw [ite_eq_right]
      intro hji
      have := congrArg Fin.val hji
      simp only [Fin.val_rev] at this
      omega
  have heig : g * M =
      M * Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then lam else -lam) := by
    ext r c
    rw [Matrix.mul_diagonal]
    have e : (g * M) r c = (g *ᵥ col c) r := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [e]
    by_cases hc : c.val < 3
    · have hg' : g *ᵥ col c = lam • col c := by
        simp only [col, dite_eq_left hc]
        exact hAg _
      rw [hg']
      simp only [M, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ite_eq_left hc, mul_comm]
    · have hg' : g *ᵥ col c = -lam • col c := by
        simp only [col, dite_eq_right hc]
        exact hBg _
      rw [hg']
      simp only [M, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ite_eq_right hc, mul_comm]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hgram
    rw [Matrix.det_mul, h0, mul_zero] at this
    exact det_antidiag_ne_zero 6 this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hgram, heig, ?_⟩
  intro r hr
  refine ⟨?_, ?_⟩
  · show col 2 r = 0
    simp only [col]
    exact (mem_te6Minus_iff hp2 a₁).mp ha₁W r hr
  · show col 3 r = 0
    simp only [col]
    exact (mem_te6Minus_iff hp2 b₁).mp hb₁W r hr

end Basis

end CFSG.ClassicalInvolution.RouteD.NonClassical
