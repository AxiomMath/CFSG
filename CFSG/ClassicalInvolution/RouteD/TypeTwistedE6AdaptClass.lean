module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptBasis

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic Module
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem exists_sqrt_of_norm_one (hp2 : p ≠ 2) (hf : 1 ≤ f) {a : GaloisField p (2 * f)}
    (ha : unitaryInvolution (GaloisField p (2 * f)) p f a * a = 1) :
    ∃ lam : GaloisField p (2 * f), lam * lam = a := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  let _ : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  rw [unitaryInvolution_apply] at ha
  obtain ⟨s, hs⟩ : Odd (p ^ f) := ((Fact.out (p := p.Prime)).odd_of_ne_two hp2).pow
  have hcard : Fintype.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hring : ringChar (GaloisField p (2 * f)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (2 * f)) p]
    exact hp2
  have hsq : IsSquare a := by
    rw [FiniteField.isSquare_iff hring ha0, hcard]
    have h1 : a ^ (p ^ f + 1) = 1 := by rw [pow_succ]; exact ha
    have h2 : (p ^ f) ^ 2 / 2 = (p ^ f + 1) * s := by
      have e : (p ^ f) ^ 2 = 2 * ((p ^ f + 1) * s) + 1 := by rw [hs]; ring
      rw [e]
      generalize (p ^ f + 1) * s = X
      omega
    rw [h2, pow_mul, h1, one_pow]
  obtain ⟨lam, hlam⟩ := hsq
  exact ⟨lam, hlam.symm⟩

section Involutory

variable {g : GL (Fin 6) (GaloisField p (2 * f))}
  {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}

theorem sq_scalar_of_involutory (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hα2 : α.comp α = MonoidHom.id _) :
    ∃ a : GaloisField p (2 * f), (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := by
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul_eq hq
  refine eq_smul_one_of_commute (unitaryFieldData_te6 hf) hp2 (by norm_num : 3 ≤ 6) _ ?_
  intro y hy
  set x : Su (GaloisField p (2 * f)) p f 6 :=
    (suEquivUnitarySU (GaloisField p (2 * f)) p f hK 6).symm ⟨y, hy⟩ with hx
  have hxy : ((x : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6)
      (GaloisField p (2 * f))) = (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := rfl
  have e0 : α (α x) = x := DFunLike.congr_fun hα2 x
  have e := congrArg (fun z : Su (GaloisField p (2 * f)) p f 6 =>
    ((z : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) e0
  simp only [hα] at e
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  set Gi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
      Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) with hGi
  have hGiG : Gi * Gm = 1 := by rw [hGi, hGm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [hxy] at e
  calc Gm * Gm * (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
      = (Gm * (Gm * (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * Gi) * Gi) *
          (Gm * Gm) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Gi Gm Gm, hGiG, Matrix.one_mul, hGiG, Matrix.mul_one]
    _ = (y : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * (Gm * Gm) := by rw [e]

theorem exists_lam (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    (hα2 : α.comp α = MonoidHom.id _)
    (hiso : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = 1) :
    ∃ lam : GaloisField p (2 * f),
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
          (lam * lam) • (1 : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) ∧
      (unitaryInvolution (GaloisField p (2 * f)) p f lam * lam = 1 ∨
        unitaryInvolution (GaloisField p (2 * f)) p f lam * lam = -1) := by
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσ
  obtain ⟨a, ha⟩ := sq_scalar_of_involutory hf hp2 hq hα hα2
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  have h1 : conjTr σ (Gm * Gm) * (Gm * Gm) = 1 := by
    rw [conjTr_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjTr σ Gm) Gm Gm, hiso,
      Matrix.one_mul, hiso]
  rw [ha] at h1
  have h2 : conjTr σ (a • (1 : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) = σ a • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [conjTr]
    · simp [conjTr, hij, Ne.symm hij]
  rw [h2, Matrix.smul_mul, Matrix.one_mul] at h1
  have hN : σ a * a = 1 := by
    have := congrFun (congrFun h1 0) 0
    simpa [Matrix.smul_apply, Matrix.one_apply] using this
  obtain ⟨lam, hlam⟩ := exists_sqrt_of_norm_one hp2 hf hN
  refine ⟨lam, by rw [hlam, ha], ?_⟩
  have h3 : (σ lam * lam) * (σ lam * lam) = 1 := by
    calc (σ lam * lam) * (σ lam * lam) = σ (lam * lam) * (lam * lam) := by rw [map_mul]; ring
      _ = 1 := by rw [hlam, hN]
  exact mul_self_eq_one_iff.mp h3

end Involutory

section ClassA

theorem exists_fixed_plane (hf : 1 ≤ f) (hp2 : p ≠ 2)
    {g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))} {lam : GaloisField p (2 * f)}
    (h : IsoSquare (unitaryInvolution (GaloisField p (2 * f)) p f) g lam)
    (hν : unitaryInvolution (GaloisField p (2 * f)) p f lam * lam = 1)
    (hW : g * suMat (te6Inv p f) = suMat (te6Inv p f) * g) :
    ∃ W : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f)),
      Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) W ∧
        finrank (GaloisField p (2 * f)) W = 2 ∧ W ≤ te6Plus p f ∧
        ∃ c : GaloisField p (2 * f), ∀ u ∈ W, g *ᵥ u = c • u := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_te6 hp2
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  have hstE : MulVecStable g (te6Plus p f) := h.mulVecStable_te6Plus hW
  have hEnd : Nondeg σ (te6Plus p f) := te6Plus_nondeg hp2 hf
  let U : GaloisField p (2 * f) →
      Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f)) :=
    fun c => te6Plus p f ⊓ eigSpace g c
  have hperp : ∀ c d : GaloisField p (2 * f), σ c * d = -1 → ∀ u ∈ eigSpace g c,
      ∀ v ∈ eigSpace g d, herm σ u v = 0 := fun c d hcd u hu v hv =>
    h.herm_eq_zero_of_eig h2 (mem_eigSpace.mp hu) (mem_eigSpace.mp hv) hcd
  have hn1 : σ lam * -lam = -1 := by rw [mul_neg, hν]
  have hn2 : σ (-lam) * lam = -1 := by rw [map_neg, neg_mul, hν]
  have hsup : U lam ⊔ U (-lam) = te6Plus p f := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun u hu => ?_
    obtain ⟨a, b, haX, hbY, hab, hmem⟩ := h.exists_decomp h2 u
    obtain ⟨haH, hbH⟩ := hmem _ hstE hu
    rw [← hab]
    exact Submodule.add_mem_sup ⟨haH, mem_eigSpace.mpr haX⟩ ⟨hbH, mem_eigSpace.mpr hbY⟩
  have hinf : U lam ⊓ U (-lam) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have h1 := mem_eigSpace.mp hu.1.2
    have h3 := mem_eigSpace.mp hu.2.2
    rw [h1] at h3
    have h4 : (2 * lam) • u = 0 := by
      calc (2 * lam) • u = lam • u - -lam • u := by module
        _ = 0 := by rw [h3]; module
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (mul_ne_zero h2 h.ne_zero)
    · simpa using h5
  have hdim : finrank (GaloisField p (2 * f)) (U lam) + finrank (GaloisField p (2 * f)) (U (-lam)) =
      4 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (U lam) (U (-lam))
    rw [hsup, hinf, finrank_bot, finrank_te6Plus hp2 hf] at this
    omega
  have hnd : ∀ c : GaloisField p (2 * f), (c = lam ∨ c = -lam) → Nondeg σ (U c) := by
    intro c hc s hs hs'
    refine hEnd s hs.1 fun t ht => ?_
    rcases hc with rfl | rfl
    · rw [← hsup] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp ht
      rw [herm_add_right, hs' t₁ ht₁, hperp _ _ hn1 s hs.2 t₂ ht₂.2, add_zero]
    · rw [← hsup, sup_comm] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp ht
      rw [herm_add_right, hs' t₁ ht₁, hperp _ _ hn2 s hs.2 t₂ ht₂.2, add_zero]
  have hpick : ∃ c : GaloisField p (2 * f), (c = lam ∨ c = -lam) ∧
      2 ≤ finrank (GaloisField p (2 * f)) (U c) := by
    by_cases h1 : 2 ≤ finrank (GaloisField p (2 * f)) (U lam)
    · exact ⟨lam, Or.inl rfl, h1⟩
    · exact ⟨-lam, Or.inr rfl, by omega⟩
  obtain ⟨c, hc, hdc⟩ := hpick
  obtain ⟨W, hWU, hW2, hWnd⟩ := exists_nondeg_plane_le hσ (hnd c hc) hdc
  exact ⟨W, hWnd, hW2, hWU.trans inf_le_left,
    c, fun u hu => mem_eigSpace.mp (hWU hu).2⟩

theorem perp_perp_eq_of_nondeg (hf : 1 ≤ f)
    {W : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f))}
    (hW : Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) W) :
    perp (unitaryInvolution (GaloisField p (2 * f)) p f)
      (perp (unitaryInvolution (GaloisField p (2 * f)) p f) W) = W := by
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  have h1 := finrank_add_finrank_herm_perp hσ hW
  have h2 := finrank_add_finrank_herm_perp hσ (nondeg_herm_perp hσ hW)
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by omega)
  intro w hw t ht
  exact herm_eq_zero_comm _ hσ.invol (ht w hw)

theorem alpha_fixes_planeGroupU (hf : 1 ≤ f)
    {g : GL (Fin 6) (GaloisField p (2 * f))}
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    {lam : GaloisField p (2 * f)}
    (h : IsoSquare (unitaryInvolution (GaloisField p (2 * f)) p f)
      (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) lam)
    {W : Submodule (GaloisField p (2 * f)) (Fin 6 → GaloisField p (2 * f))}
    (hW : Nondeg (unitaryInvolution (GaloisField p (2 * f)) p f) W)
    {c : GaloisField p (2 * f)}
    (hc : ∀ u ∈ W, (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *ᵥ u = c • u) :
    ∀ x ∈ planeGroupU (GaloisField p (2 * f)) p f W, α x = x := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := isUnitaryInvolution_unitaryInvolution (p := p) (f := f) hK
  set σ := unitaryInvolution (GaloisField p (2 * f)) p f with hσdef
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  intro x hx
  have hxfix : ∀ y ∈ perp σ W, suMat x *ᵥ y = y := fun y hy =>
    (mem_fixingSubgroup_iff (Su (GaloisField p (2 * f)) p f 6)).mp hx y hy
  have hstW : MulVecStable Gm W := fun u hu => by
    rw [hc u hu]
    exact W.smul_mem _ hu
  have hstP : MulVecStable Gm (perp σ W) := h.mulVecStable_perp hstW
  have hxW : ∀ w ∈ W, suMat x *ᵥ w ∈ W := by
    intro w hw
    rw [← perp_perp_eq_of_nondeg hf hW]
    intro t ht
    have h1 : herm σ (x • w) (x • t) = herm σ w t := herm_smul_smul σ x w t
    have h2 : x • t = t := hxfix t ht
    rw [h2] at h1
    exact h1.trans (herm_eq_zero_comm σ hσ.invol (ht w hw))
  refine alpha_eq_of_commutes hα ?_
  rw [Matrix.ext_iff_mulVec]
  intro u
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  show Gm *ᵥ (suMat x *ᵥ u) = suMat x *ᵥ (Gm *ᵥ u)
  have hdec : u ∈ W ⊔ (⊤ ⊓ perp σ W) := by
    rw [sup_inf_perp_of_nondeg hσ _ rfl hW le_top]
    exact Submodule.mem_top
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hdec
  have e1 : Gm *ᵥ (suMat x *ᵥ u₁) = c • (suMat x *ᵥ u₁) := hc _ (hxW u₁ hu₁)
  have e2 : suMat x *ᵥ (Gm *ᵥ u₁) = c • (suMat x *ᵥ u₁) := by
    rw [hc u₁ hu₁, Matrix.mulVec_smul]
  have e3 : suMat x *ᵥ (Gm *ᵥ u₂) = Gm *ᵥ u₂ := hxfix _ (hstP u₂ hu₂.2)
  calc Gm *ᵥ (suMat x *ᵥ (u₁ + u₂)) = Gm *ᵥ (suMat x *ᵥ u₁) + Gm *ᵥ u₂ := by
        rw [Matrix.mulVec_add, hxfix u₂ hu₂.2, Matrix.mulVec_add]
    _ = suMat x *ᵥ (Gm *ᵥ (u₁ + u₂)) := by
        rw [e1, Matrix.mulVec_add, Matrix.mulVec_add, e2, e3]

end ClassA

section Node

variable {G : Type} [Group G]

theorem trace_te6Inv : Matrix.trace (suMat (te6Inv p f)) = (2 : GaloisField p (2 * f)) := by
  show Matrix.trace (zMat (GaloisField p (2 * f)) (5 + 1) (nodePair 5 0 (by norm_num)).1) = 2
  have hmem : ∀ r : Fin (5 + 1), r ∈ (nodePair 5 0 (by norm_num)).1 ↔ r.val < 2 := by
    intro r
    simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [zMat, Matrix.trace_diagonal]
  simp only [hmem, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num

end Node

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

omit [Finite G] in
theorem map_zEltU_eq {c : UCtx p f 5 Ω K z} {nd : UNodes c}
    {Θ : Su (GaloisField p (2 * f)) p f 6 →* G} (hΘ : TE6Chart c nd Θ) {a : ℕ} (ha : a < 5) :
    Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)) = nd.w a := by
  have hnode : zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha) ∈
      (blockEmb2 (GaloisField p (2 * f)) p f 5 ⟨a, ha⟩).range := by
    rw [range_blockEmb2_eq_LcU_nodePair c.h2 ha]
    exact (isLongRootSU2_LcU c.h2 c.hn (nodePair 5 a ha)).mem
  have hmem : Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)) ∈ nd.j a := by
    rw [← hΘ.block ⟨a, ha⟩]
    exact Subgroup.mem_map_of_mem Θ hnode
  have hsq : Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)) *
      Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)) = 1 := by
    rw [← map_mul, zEltU_mul_self, map_one]
  have hne : Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)) ≠ 1 := fun h1 =>
    zEltU_not_mem_center c.card_eq c.h2 (by norm_num : 3 ≤ 5 + 1) (nodePair 5 a ha)
      (hΘ.ker_le (MonoidHom.mem_ker.mpr h1))
  have hord : orderOf (Θ (zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha))) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hne
  exact eq_of_mem_of_orderOf_eq_two (two_ne_zero_of_charP_ne_two c.hp2)
    (c.hex (nd.j a) (nd.mem a ha).1) (nd.isCl a ha) hmem hord

omit [Finite G] in
theorem map_te6Inv_eq {c : UCtx p f 5 Ω K z} {nd : UNodes c}
    {Θ : Su (GaloisField p (2 * f)) p f 6 →* G} (hΘ : TE6Chart c nd Θ) :
    Θ (te6Inv p f) = nd.w 0 :=
  map_zEltU_eq hΘ (by norm_num : 0 < 5)

@[expose] def TE6PartnerIsolated (c : UCtx p f 5 Ω K z) (nd : UNodes c) : Prop :=
  ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N (nd.j 0)) →
    ∀ L ∈ centralizingMembers Ω {z * nd.w 0, z}, L ≠ K → ¬ Commutes N L

end Group

end CFSG.ClassicalInvolution.RouteD.NonClassical
