module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGeom

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam hypComb hypComb_injective map_hypComb
  exists_isometry_of_isHypFam)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Family

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem isHypFam_of_pairs {m : ℕ} (P : Fin m → HypPair Q) (h : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    IsHypFam Q (fun i s => if s then (P i).e else (P i).f) := by
  refine ⟨fun i s => ?_, fun i j hij s t => ?_, fun i s => ?_⟩
  · cases s
    · exact (P i).Q_f
    · exact (P i).Q_e
  · have := h i j hij
    cases s <;> cases t
    · exact this.ff
    · exact this.fe
    · exact this.ef
    · exact this.ee
  · cases s
    · exact (P i).polar_fe
    · exact (P i).polar_ef

theorem orth_pairs_of_span_le_perp {F₀ F₁ : OFrame Q} (h : F₁.span ≤ F₀.perp) :
    F₀.P.Orth F₁.P ∧ F₀.P.Orth F₁.P' ∧ F₀.P'.Orth F₁.P ∧ F₀.P'.Orth F₁.P' := by
  obtain ⟨a11, a12, a13, a14⟩ := (mem_perp_iff_four F₀).mp (h F₁.e₁_mem_span)
  obtain ⟨a21, a22, a23, a24⟩ := (mem_perp_iff_four F₀).mp (h F₁.f₁_mem_span)
  obtain ⟨a31, a32, a33, a34⟩ := (mem_perp_iff_four F₀).mp (h F₁.e₂_mem_span)
  obtain ⟨a41, a42, a43, a44⟩ := (mem_perp_iff_four F₀).mp (h F₁.f₂_mem_span)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    rw [polar_comm] <;> assumption

end Family

section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_frame_in_perp_of_isHypFam {m : ℕ} (hm : 4 ≤ m) (w : Fin m → Bool → V)
    (hw : IsHypFam Q w) (F₁ : OFrame Q) : ∃ G : OFrame Q, G.span ≤ F₁.perp := by
  let T2 : Fin 2 → HypPair Q := ![F₁.P, F₁.P']
  have hT2 : ∀ i j, i ≠ j → (T2 i).Orth (T2 j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [T2] <;>
      first
      | exact absurd rfl hij
      | exact F₁.orth | exact F₁.orth.symm
  let v : Fin 2 → Bool → V := fun i s => if s then (T2 i).e else (T2 i).f
  have hv : IsHypFam Q v := isHypFam_of_pairs T2 hT2
  let c : Fin 2 → Fin m := Fin.castLE (by omega)
  let v' : Fin 2 → Bool → V := fun i s => w (c i) s
  have hv' : IsHypFam Q v' :=
    ⟨fun i s => hw.1 _ s,
      fun i j hij s t => hw.2.1 _ _ (fun h => hij (Fin.castLE_injective _ h)) s t,
      fun i s => hw.2.2 _ s⟩
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hωs : ω.symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hω
  have hvi : ∀ i s, ω.symm (w (c i) s) = v i s := fun i s =>
    (ω.symm_apply_eq).mpr (hωv i s).symm
  let j2 : Fin m := ⟨2, by omega⟩
  let j3 : Fin m := ⟨3, by omega⟩
  let W : Fin m → HypPair Q := fun j =>
    ⟨ω.symm (w j true), ω.symm (w j false), by rw [map_of_mem hωs]; exact hw.1 j true,
      by rw [map_of_mem hωs]; exact hw.1 j false,
      by rw [polar_map_of_mem hωs]; simpa using hw.2.2 j true⟩
  have hG : (W j2).Orth (W j3) := by
    have hne : j2 ≠ j3 := by simp [j2, j3, Fin.ext_iff]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> show polar Q (ω.symm _) (ω.symm _) = 0 <;>
      rw [polar_map_of_mem hωs]
    · exact hw.2.1 j2 j3 hne true true
    · exact hw.2.1 j2 j3 hne true false
    · exact hw.2.1 j2 j3 hne false true
    · exact hw.2.1 j2 j3 hne false false
  have hperp : ∀ (j : Fin m), 2 ≤ j.val → ∀ (s t : Bool) (i : Fin 2),
      polar Q (ω.symm (w j s)) (v i t) = 0 := by
    intro j hj s t i
    rw [← hvi i t, polar_map_of_mem hωs]
    refine hw.2.1 j (c i) ?_ s t
    intro h
    have := congrArg Fin.val h
    have hi : i.val < 2 := i.2
    simp [c] at this
    omega
  refine ⟨⟨W j2, W j3, hG⟩, ?_⟩
  refine span_le_of_gens ?_ ?_ ?_ ?_ <;> rw [mem_perp_iff_four]
  · exact ⟨hperp j2 le_rfl true true 0, hperp j2 le_rfl true false 0,
      hperp j2 le_rfl true true 1, hperp j2 le_rfl true false 1⟩
  · exact ⟨hperp j2 le_rfl false true 0, hperp j2 le_rfl false false 0,
      hperp j2 le_rfl false true 1, hperp j2 le_rfl false false 1⟩
  · exact ⟨hperp j3 (by simp [j3]) true true 0, hperp j3 (by simp [j3]) true false 0,
      hperp j3 (by simp [j3]) true true 1, hperp j3 (by simp [j3]) true false 1⟩
  · exact ⟨hperp j3 (by simp [j3]) false true 0, hperp j3 (by simp [j3]) false false 0,
      hperp j3 (by simp [j3]) false true 1, hperp j3 (by simp [j3]) false false 1⟩

end Frames

section Count

variable {F : Type} [Field F] [Finite F]

theorem false_of_isHypFam_quadMinus (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F) {m : ℕ}
    (v : Fin (m + 1) → Bool → (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F))
    (hv : IsHypFam (quadMinus (m + 1) F b c) v) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  let e' : Fin (m + 1) × Bool ≃ Fin (m + 1) ⊕ Fin (m + 1) :=
    (Equiv.prodComm (Fin (m + 1)) Bool).trans (Equiv.boolProdEquivSum (Fin (m + 1)))
  let ψ₀ : (Fin (m + 1) ⊕ Fin (m + 1) → F) →ₗ[F]
      (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) :=
    (hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus (m + 1) F b c (ψ₀ w) = quadPlus (m + 1) F w := by
    intro w
    show quadMinus (m + 1) F b c (hypComb v (w ∘ e')) = _
    rw [map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (hypComb_injective hv).comp (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin (m + 1) ⊕ Fin (m + 1) → F) =
      Module.finrank F (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
    omega
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin (m + 1) ⊕ Fin (m + 1) → F // quadPlus (m + 1) F w = 0} =
      Nat.card {x : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) //
        quadMinus (m + 1) F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin (m + 1) ⊕ Fin (m + 1) → F // quadPlus (m + 1) F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus m
  have e2 : (Nat.card {x : (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → F) //
      quadMinus (m + 1) F b c x = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ (m + 1) + 1) * ((Nat.card F : ℤ) ^ m - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr m
  rw [hcard] at e1
  have hq : (4 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ (m + 1) - 1) * ((Nat.card F : ℤ) ^ m + 1) -
      ((Nat.card F : ℤ) ^ (m + 1) + 1) * ((Nat.card F : ℤ) ^ m - 1) =
      2 * ((Nat.card F : ℤ) ^ m * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ m * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) m) (by linarith)
  linarith

theorem false_of_three_orth_quadMinus_six (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F)
    (F₀ F₁ F₂ : OFrame (quadMinus 6 F b c)) (h01 : F₁.span ≤ F₀.perp) (h02 : F₂.span ≤ F₀.perp)
    (h12 : F₂.span ≤ F₁.perp) : False := by
  obtain ⟨o01, o02, o03, o04⟩ := orth_pairs_of_span_le_perp h01
  obtain ⟨p01, p02, p03, p04⟩ := orth_pairs_of_span_le_perp h02
  obtain ⟨q01, q02, q03, q04⟩ := orth_pairs_of_span_le_perp h12
  let P : Fin 6 → HypPair (quadMinus 6 F b c) := ![F₀.P, F₀.P', F₁.P, F₁.P', F₂.P, F₂.P']
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [P] <;>
      first
      | exact absurd rfl hij
      | exact F₀.orth | exact F₀.orth.symm | exact F₁.orth | exact F₁.orth.symm
      | exact F₂.orth | exact F₂.orth.symm
      | exact o01 | exact o01.symm | exact o02 | exact o02.symm
      | exact o03 | exact o03.symm | exact o04 | exact o04.symm
      | exact p01 | exact p01.symm | exact p02 | exact p02.symm
      | exact p03 | exact p03.symm | exact p04 | exact p04.symm
      | exact q01 | exact q01.symm | exact q02 | exact q02.symm
      | exact q03 | exact q03.symm | exact q04 | exact q04.symm
  exact false_of_isHypFam_quadMinus (m := 5) h2 hirr h4 _ (isHypFam_of_pairs P hP)

theorem minus_twinWithinCentralizer_six (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin (quadMinus 6 F b c)).Nondegenerate) :
    TwinWithinCentralizer (fundSet (quadMinus 6 F b c)) := by
  have hdim : Module.finrank F (Fin (6 - 1) ⊕ Fin (6 - 1) ⊕ Fin 2 → F) = 12 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  exact fundSet_twinWithinCentralizer_of hodd (fundSet_hubUnique hodd hQ (Or.inl (by omega)))
    fun F₀ F₁ F₂ h01 h02 h12 =>
      (false_of_three_orth_quadMinus_six h2 hirr h4 F₀ F₁ F₂ h01 h02 h12).elim

end Count

end CFSG.ClassicalInvolution.RouteD.Exotic
