module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDown

public section

open CFSG.LocalAnalysis.GLTheoremA.AltDown

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Inner

variable {Y : Type} [Group Y]

@[expose] def conjKequiv (K : Subgroup Y) (hK : K.Normal) (y : Y) : K ≃* K where
  toFun k := ⟨y * k * y⁻¹, hK.conj_mem k.1 k.2 y⟩
  invFun k := ⟨y⁻¹ * k * y, by simpa using hK.conj_mem k.1 k.2 y⁻¹⟩
  left_inv k := by ext; simp [mul_assoc]
  right_inv k := by ext; simp [mul_assoc]
  map_mul' k l := by ext; simp [mul_assoc]

theorem conjKequiv_apply (K : Subgroup Y) (hK : K.Normal) (y : Y) (k : K) :
    ((conjKequiv K hK y k : K) : Y) = y * k * y⁻¹ := rfl

variable {n : ℕ} (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n))

@[expose] def alphaEquiv (y : Y) : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
  e.symm.trans ((conjKequiv K hK y).trans e)

@[expose] def alphaHom : Y →* MulAut (alternatingGroup (Fin n)) where
  toFun y := alphaEquiv K hK e y
  map_one' := by
    ext x
    simp [alphaEquiv, conjKequiv]
  map_mul' y z := by
    ext x
    simp [alphaEquiv, conjKequiv, mul_assoc]

theorem alphaHom_apply_coe (y : Y) (k : K) :
    alphaHom K hK e y (e k) = e (conjKequiv K hK y k) := by
  simp [alphaHom, alphaEquiv]

theorem center_alt_eq_bot (hn : 5 ≤ n) : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
  alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)

theorem conj_injective_alt (hn : 5 ≤ n) {x x' : alternatingGroup (Fin n)}
    (h : MulAut.conj x = MulAut.conj x') : x = x' := by
  have hc : x'⁻¹ * x ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg' : x * g * x⁻¹ = x' * g * x'⁻¹ := by
      have := DFunLike.congr_fun h g
      simpa only [MulAut.conj_apply] using this
    have : x'⁻¹ * x * g = g * (x'⁻¹ * x) := by
      calc x'⁻¹ * x * g = x'⁻¹ * (x * g * x⁻¹) * x := by group
        _ = x'⁻¹ * (x' * g * x'⁻¹) * x := by rw [hg']
        _ = g * (x'⁻¹ * x) := by group
    exact this.symm
  rw [center_alt_eq_bot hn, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

theorem exists_unique_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    {α : MulAut (alternatingGroup (Fin n))} (hα : α ^ p = 1) :
    ∃ x : alternatingGroup (Fin n), α = MulAut.conj x := by
  by_cases h1 : α = 1
  · exact ⟨1, by rw [h1, map_one]⟩
  · obtain ⟨x, -, -, hx⟩ := exists_conj_of_alt hn hp hp2 hα h1
    exact ⟨x, hx⟩

theorem alphaHom_pow_eq_one (p : ℕ) {b : Y} (hb : b ^ p = 1) :
    (alphaHom K hK e b) ^ p = 1 := by
  rw [← map_pow, hb, map_one]

@[expose] noncomputable def psiFun {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) : alternatingGroup (Fin n) :=
  Classical.choose (exists_unique_inner (n := n) hp hp2 hn
    (alphaHom_pow_eq_one K hK e p (hB b b.2)))

theorem psiFun_spec {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    MulAut.conj (psiFun K hK e hp hp2 hn B hB b) = alphaHom K hK e (b : Y) :=
  (Classical.choose_spec (exists_unique_inner (n := n) hp hp2 hn
    (alphaHom_pow_eq_one K hK e p (hB b b.2)))).symm

@[expose] noncomputable def psiHom {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) : B →* alternatingGroup (Fin n) :=
  MonoidHom.mk' (psiFun K hK e hp hp2 hn B hB) (fun b c => by
    apply conj_injective_alt hn
    simp only [map_mul (MulAut.conj), psiFun_spec, Subgroup.coe_mul, map_mul (alphaHom K hK e)])

theorem psiHom_apply {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    psiHom K hK e hp hp2 hn B hB b = psiFun K hK e hp hp2 hn B hB b := by
  simp only [psiHom, MonoidHom.mk'_apply]

theorem alpha_apply_eq_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) (x : alternatingGroup (Fin n)) :
    alphaEquiv K hK e (b : Y) x = psiFun K hK e hp hp2 hn B hB b * x *
      (psiFun K hK e hp hp2 hn B hB b)⁻¹ := by
  have h := DFunLike.congr_fun (psiFun_spec K hK e hp hp2 hn B hB b) x
  simp only [MulAut.conj_apply] at h
  exact h.symm

theorem psiHom_conj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) (k : K) :
    (b : Y) * (k : Y) * (b : Y)⁻¹ =
      ((e.symm (psiHom K hK e hp hp2 hn B hB b) : K) : Y) * (k : Y) *
        ((e.symm (psiHom K hK e hp hp2 hn B hB b) : K) : Y)⁻¹ := by
  have h1 : e (conjKequiv K hK (b : Y) k) =
      psiHom K hK e hp hp2 hn B hB b * e k * (psiHom K hK e hp hp2 hn B hB b)⁻¹ := by
    rw [psiHom_apply K hK e hp hp2 hn B hB b, ← alphaHom_apply_coe K hK e (b : Y) k]
    exact alpha_apply_eq_conj K hK e hp hp2 hn B hB b (e k)
  have h2 : conjKequiv K hK (b : Y) k =
      e.symm (psiHom K hK e hp hp2 hn B hB b) * k * (e.symm (psiHom K hK e hp hp2 hn B hB b))⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg (fun z : K => (z : Y)) h2
  simpa only [conjKequiv_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h3

theorem psiHom_eq_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (b : B) :
    psiHom K hK e hp hp2 hn B hB b = 1 ↔ (b : Y) ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have hc := psiHom_conj K hK e hp hp2 hn B hB b ⟨k, hk⟩
    rw [h, map_one] at hc
    simp only [Subgroup.coe_one, one_mul, inv_one, mul_one] at hc
    calc (k : Y) * (b : Y) = ((b : Y) * k * (b : Y)⁻¹) * (b : Y) := by rw [hc]
      _ = (b : Y) * k := by group
  · intro h
    apply conj_injective_alt hn
    have hal : alphaHom K hK e (b : Y) = 1 := by
      ext x
      obtain ⟨k, rfl⟩ := e.surjective x
      rw [alphaHom_apply_coe K hK e (b : Y) k, MulAut.one_apply]
      have hk := h k k.2
      have hbk : (b : Y) * k * (b : Y)⁻¹ = k := by
        rw [← hk]; group
      have hcoe : ((conjKequiv K hK (b : Y) k : K) : Y) = (k : Y) := by
        rw [conjKequiv_apply, hbk]
      rw [Subtype.ext hcoe]
    rw [map_one, psiHom_apply K hK e hp hp2 hn B hB b, psiFun_spec K hK e hp hp2 hn B hB b, hal]

end CFSG.LocalAnalysis.GLTheoremA.KD264Inner
