module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreAltSwap
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSym
public import CFSG.HardMathSupport.Cooperstein.StructureLie.TypeScriptLSp

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section Six

theorem bilinIsometryGroup_heartForm_six :
    bilinIsometryGroup (heartForm 6) = (heartRep 6).range := by
  have hcard := natCard_bilinIsometryGroup_symplectic_four (heartForm_nondegenerate 6)
    (heartForm_isAlt 6) finrank_heart_six
  have : Finite ↥(bilinIsometryGroup (heartForm 6)) := Nat.finite_of_card_ne_zero (by omega)
  symm
  apply Subgroup.eq_of_le_of_card_ge (range_heartRep_le_bilinIsometryGroup 6)
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective (heartRep_injective (by norm_num))).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem heartEquivAltHeart_heartRep (m : ℕ) (σ : Equiv.Perm (Fin m))
    (y : sumZero m ⧸ onesLine m) :
    heartEquivAltHeart m (((heartRep m σ : LinearMap.GeneralLinearGroup (ZMod 2)
      (sumZero m ⧸ onesLine m)) : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m ⧸ onesLine m)) y) =
      altAct σ (heartEquivAltHeart m y) := by
  induction y using Submodule.Quotient.induction_on with
  | H u =>
    rw [heartRep_apply_mk, heartEquivAltHeart_mk, heartEquivAltHeart_mk,
      sumZeroEquivEvenWeight_sumZeroEquiv, altAct_mk]

theorem mem_range_heartRep_six
    (T : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6))
    (hT : ∀ h ∈ alternatingGroup (Fin 6), ∃ h' ∈ alternatingGroup (Fin 6), ∀ y,
      ((T : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
        (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6))
          (((heartRep 6 h : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
            (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) y) =
        ((heartRep 6 h' : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
          (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6))
            (((T : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
              (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) y)) :
    T ∈ (heartRep 6).range := by
  have hB := heartForm_nondegenerate 6
  let B := heartForm 6
  let Tl : (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6) := (T : _)
  let ρ : Equiv.Perm (Fin 6) → (sumZero 6 ⧸ onesLine 6) → (sumZero 6 ⧸ onesLine 6) :=
    fun σ y => ((heartRep 6 σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) y
  have hρmul : ∀ σ τ y, ρ (σ * τ) y = ρ σ (ρ τ y) := fun σ τ y => by
    show (((heartRep 6 (σ * τ) : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6))) y = _
    rw [map_mul]; rfl
  have hρone : ∀ y, ρ 1 y = y := fun y => by
    show (((heartRep 6 1 : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6))) y = y
    rw [map_one]; rfl
  have hBρ : ∀ σ x y, B (ρ σ x) (ρ σ y) = B x y := fun σ x y => heartForm_heartRep σ x y
  let B' : LinearMap.BilinForm (ZMod 2) (sumZero 6 ⧸ onesLine 6) := B.compl₁₂ Tl Tl
  let E : (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6) :=
    LinearMap.BilinForm.symmCompOfNondegenerate B' B hB
  have hE : ∀ x y, B (E x) y = B (Tl x) (Tl y) := fun x y =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' hB y x
  have hEcomm : ∀ h ∈ alternatingGroup (Fin 6), ∀ x, E (ρ h x) = ρ h (E x) := by
    intro h hh x
    obtain ⟨h', hh', hTh⟩ := hT h hh
    have hsep : E (ρ h x) - ρ h (E x) = 0 := by
      apply hB.1
      intro y
      have hy : y = ρ h (ρ h⁻¹ y) := by rw [← hρmul, mul_inv_cancel, hρone]
      have h1 : Tl y = ρ h' (Tl (ρ h⁻¹ y)) :=
        calc Tl y = Tl (ρ h (ρ h⁻¹ y)) := by rw [← hy]
          _ = ρ h' (Tl (ρ h⁻¹ y)) := hTh (ρ h⁻¹ y)
      rw [LinearMap.map_sub₂, hE, hTh x, h1, hBρ, show B (ρ h (E x)) y =
        B (ρ h (E x)) (ρ h (ρ h⁻¹ y)) by rw [← hy], hBρ, hE, sub_self]
    exact sub_eq_zero.1 hsep
  let q := heartEquivAltHeart 6
  let g : CFSG.RankThree.PartTwo.altHeart 6 →+ CFSG.RankThree.PartTwo.altHeart 6 :=
    q.toAddMonoidHom.comp (E.toAddMonoidHom.comp q.symm.toAddMonoidHom)
  have hqρ : ∀ σ y, q (ρ σ y) = altAct σ (q y) := heartEquivAltHeart_heartRep 6
  have hqρ' : ∀ σ v, q.symm (altAct σ v) = ρ σ (q.symm v) := by
    intro σ v
    apply q.injective
    rw [q.apply_symm_apply, hqρ, q.apply_symm_apply]
  have hg : ∀ σ ∈ alternatingGroup (Fin 6), ∀ v, g (altAct σ v) = altAct σ (g v) := by
    intro σ hσ v
    show q (E (q.symm (altAct σ v))) = altAct σ (q (E (q.symm v)))
    rw [hqρ', hEcomm σ hσ, hqρ]
  haveI : Nontrivial (sumZero 6 ⧸ onesLine 6) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [finrank_heart_six]; norm_num)
  have hTsurj : ∀ x, ∃ x', Tl x' = x := fun x => ⟨((T⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2)
    (sumZero 6 ⧸ onesLine 6)) : (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) x, by
      show ((T * T⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
        (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) x = x
      rw [mul_inv_cancel]; rfl⟩
  rcases altHeart_endo_eq_zero_or_id (by norm_num : 5 ≤ 6) g hg with h0 | hid
  · exfalso
    have hE0 : ∀ y, E y = 0 := by
      intro y
      have h1 := congrArg (fun f : CFSG.RankThree.PartTwo.altHeart 6 →+ _ => f (q y)) h0
      have h2 : q (E y) = 0 := by
        simpa [g] using h1
      exact q.injective (h2.trans q.map_zero.symm)
    obtain ⟨x, hx⟩ := exists_ne (0 : sumZero 6 ⧸ onesLine 6)
    apply hx
    apply hB.1
    intro y
    obtain ⟨x', rfl⟩ := hTsurj x
    obtain ⟨y', rfl⟩ := hTsurj y
    rw [← hE, hE0]
    simp
  · have hEid : ∀ y, E y = y := by
      intro y
      have h1 := congrArg (fun f : CFSG.RankThree.PartTwo.altHeart 6 →+ _ => f (q y)) hid
      have h2 : q (E y) = q y := by
        simpa [g] using h1
      exact q.injective h2
    rw [← bilinIsometryGroup_heartForm_six, mem_bilinIsometryGroup]
    intro x y
    have := hE x y
    rw [hEid] at this
    exact this.symm

theorem exists_perm_act_six {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)}
    (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart 6) (θ : ↥L ≃* ↥(alternatingGroup (Fin 6)))
    (hA : ∀ (g : ↥L) (w : P) (x : CFSG.QuasithinUnique.evenWeight 6),
      φ w = (x : CFSG.RankThree.PartTwo.altHeart 6) →
        φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
          (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin 6)) x :
            CFSG.RankThree.PartTwo.altHeart 6))
    {τ : LinearMap.GeneralLinearGroup (ZMod 2) P}
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ w : P, φ ((τ : P →ₗ[ZMod 2] P) w) = altAct σ (φ w) := by
  have hL := act_of_isAlt φ θ hA
  let q := heartEquivAltHeart 6
  let ξ : P ≃+ (sumZero 6 ⧸ onesLine 6) := φ.trans q.symm
  let ρ : Equiv.Perm (Fin 6) → (sumZero 6 ⧸ onesLine 6) → (sumZero 6 ⧸ onesLine 6) :=
    fun σ y => ((heartRep 6 σ : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) y
  have hqρ : ∀ σ y, q (ρ σ y) = altAct σ (q y) := heartEquivAltHeart_heartRep 6
  have hqξ : ∀ w, q (ξ w) = φ w := fun w => q.apply_symm_apply (φ w)
  have hξact : ∀ (g : ↥L) (w : P), ξ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) :
      P →ₗ[ZMod 2] P) w) = ρ (θ g : Equiv.Perm (Fin 6)) (ξ w) := by
    intro g w
    apply q.injective
    rw [hqξ, hqρ, hqξ, hL g w]
  let nτ : MulAut ↥L := L.normalizerMonoidHom ⟨τ, hτn⟩
  have hcoe : ∀ g : ↥L, ((nτ g : ↥L) : LinearMap.GeneralLinearGroup (ZMod 2) P) = τ * g * τ⁻¹ :=
    fun g => Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨τ, hτn⟩ g
  have hτinv : ∀ w : P, ((τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
      ((τ : P →ₗ[ZMod 2] P) w) = w := fun w => by
    show ((τ⁻¹ * τ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w = w
    rw [inv_mul_cancel]; rfl
  have hnτ : ∀ (g : ↥L) (w : P), (((nτ g : ↥L) : LinearMap.GeneralLinearGroup (ZMod 2) P) :
      P →ₗ[ZMod 2] P) ((τ : P →ₗ[ZMod 2] P) w) =
        (τ : P →ₗ[ZMod 2] P) (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) :
          P →ₗ[ZMod 2] P) w) := by
    intro g w
    rw [hcoe]
    show ((τ * g * τ⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P)
      ((τ : P →ₗ[ZMod 2] P) w) = _
    simp [mul_assoc, hτinv]
  let tE : P ≃+ P := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) P τ).toAddEquiv
  let Tc : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6) :=
    addEquivToGL ((ξ.symm.trans tE).trans ξ)
  have hTc : ∀ w : P, ((Tc : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) (ξ w) =
        ξ ((τ : P →ₗ[ZMod 2] P) w) := fun w => by
    show ξ (tE (ξ.symm (ξ w))) = _
    rw [ξ.symm_apply_apply]; rfl
  have hmem : Tc ∈ (heartRep 6).range := by
    apply mem_range_heartRep_six
    intro h hh
    set g : ↥L := θ.symm ⟨h, hh⟩ with hg
    have hθg : (θ g : Equiv.Perm (Fin 6)) = h := by rw [hg, MulEquiv.apply_symm_apply]
    refine ⟨(θ (nτ g) : Equiv.Perm (Fin 6)), (θ (nτ g)).2, fun y => ?_⟩
    obtain ⟨w, rfl⟩ := ξ.surjective y
    have h1 : ρ h (ξ w) = ξ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) := by
      rw [hξact g w, hθg]
    have h2 : ((Tc : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
        (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) (ρ h (ξ w)) =
        ρ (θ (nτ g) : Equiv.Perm (Fin 6)) (((Tc : LinearMap.GeneralLinearGroup (ZMod 2)
          (sumZero 6 ⧸ onesLine 6)) : (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2]
            (sumZero 6 ⧸ onesLine 6)) (ξ w)) := by
      rw [h1, hTc, hTc, ← hξact (nτ g), hnτ]
    exact h2
  obtain ⟨σ, hσ⟩ := hmem
  refine ⟨σ, fun w => ?_⟩
  have h1 : ((Tc : LinearMap.GeneralLinearGroup (ZMod 2) (sumZero 6 ⧸ onesLine 6)) :
      (sumZero 6 ⧸ onesLine 6) →ₗ[ZMod 2] (sumZero 6 ⧸ onesLine 6)) (ξ w) = ρ σ (ξ w) := by
    rw [← hσ]
  rw [hTc] at h1
  rw [← hqξ, h1, hqρ, hqξ]

theorem isAlt_transv_swap_six_proof {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    {L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)} (hA : IsAltModel L 6)
    {τ : LinearMap.GeneralLinearGroup (ZMod 2) P} (hτ : IsF2Transvection τ)
    (hτn : τ ∈ Subgroup.normalizer (L : Set (LinearMap.GeneralLinearGroup (ZMod 2) P))) :
    AltSwapConcl L 6 τ := by
  obtain ⟨φ, θ, hA'⟩ := hA
  obtain ⟨σ, hσ⟩ := exists_perm_act_six φ θ hA' hτn
  exact swapConcl_of_act (by norm_num) φ θ hA' hτ hσ

end Six

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
