module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptMain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6SU6
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpLayerCount

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive
  exists_unitaryInvolution_eq_neg)
open CFSG.LieType.Steinberg.Exceptional (frobQ frobQ_apply frobQ_frobQ)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem exists_su6Frame_of_witt (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (P : GL (Fin 6) (GaloisField p (2 * f)))
    (hP : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = antidiag 6) :
    ∃ F : SU6Frame p f hf,
      F.R₁ = (nodeSU (unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f)
        (CFSG.LieType.Universal.card_galoisField_two_mul p f hf)) 2).map
          (conjEquiv P hP).toMonoidHom ∧
      F.S₂ = (nodeSU (unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f)
        (CFSG.LieType.Universal.card_galoisField_two_mul p f hf)) 1).map
          (conjEquiv P hP).toMonoidHom ∧
      F.S₃ = (nodeSU (unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f)
        (CFSG.LieType.Universal.card_galoisField_two_mul p f hf)) 0).map
          (conjEquiv P hP).toMonoidHom := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f) hF
  obtain ⟨μ, hμ0, hμ⟩ := exists_unitaryInvolution_eq_neg (K := GaloisField p (2 * f)) (p := p)
    (f := f) hF
  have hσθ : ∀ c, unitaryInvolution (GaloisField p (2 * f)) p f c = frobQ p f c := fun c => by
    rw [unitaryInvolution_apply, frobQ_apply]
  have hθ := frobQ_frobQ p f hf
  let φ := conjEquiv P hP
  obtain ⟨i₀, hi₀⟩ : ∃ i, IsLongRootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 6)
      ((nodeSU hσ 2).map φ.toMonoidHom) i :=
    CFSG.ClassicalInvolution.ModelFacts.exists_isLongRootSU2_map_rankOne hF hp2 (by norm_num)
      (k := ⟨2, by norm_num⟩) (γ := Pi.single 2 1) (by decide +kernel) (by decide +kernel) P hP
  have hB23 : nodeSU hσ 1 = (WeakCT.B23 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B23_ge hσ) (iota3_B23_le hσ)
  have hB12 : nodeSU hσ 0 = (WeakCT.B12 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B12_ge hσ) (iota3_B12_le hσ)
  have hlb : nodeSU hσ 2 = ((ulb (frobQ p f) hθ).range).map (iota4 hθ hμ0 hμ hσθ) :=
    le_antisymm (iota4_ulb_ge hσ hθ hμ0 hμ hσθ) (iota4_ulb_le hσ hθ hμ0 hμ hσθ)
  have hker : (QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * f)) p f 6))).ker ≤
      Subgroup.center (Su (GaloisField p (2 * f)) p f 6) := by
    rw [QuotientGroup.ker_mk']
  refine ⟨{
    R₁ := (nodeSU hσ 2).map φ.toMonoidHom
    S₂ := (nodeSU hσ 1).map φ.toMonoidHom
    S₃ := (nodeSU hσ 0).map φ.toMonoidHom
    R₁_mem := ⟨i₀, hi₀⟩
    commutes_R₁_S₃ := ?_
    gen := ?_
    ι₄ := φ.toMonoidHom.comp (iota4 hθ hμ0 hμ hσθ)
    ι₄_injective := φ.injective.comp (iota4_injective hθ hμ0 hμ hσθ)
    ι₄_long := ?_
    ι₄_short := ?_
    ι₃ := φ.toMonoidHom.comp (iota3 hσ)
    ι₃_injective := φ.injective.comp (iota3_injective hσ)
    ι₃_B23 := ?_
    ι₃_B12 := ?_
    R₁_center := ?_
    S₂_center := ?_ }, rfl, rfl, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul, commutes_node2_node0 hσ hθ hμ0 hμ hσθ x hx y hy]
  · rw [← Subgroup.map_sup, ← Subgroup.map_sup, nodes_generate hF]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom) hlb.symm
  · rw [← Subgroup.map_map]
    exact congrArg (Subgroup.map φ.toMonoidHom)
      ((iota4_usb_range hσ hθ hμ0 hμ hσθ).trans hB23.symm)
  · rw [← Subgroup.map_map, ← hB23]
  · rw [← Subgroup.map_map, ← hB12]
  · exact fun r hr hc => CFSG.ClassicalInvolution.Models.Transfer.eq_one_of_mem_ker_of_isLongRootSU2
      hF hp2 hq (by norm_num) hi₀ hker r hr (by rw [QuotientGroup.ker_mk']; exact hc)
  · rintro _ ⟨x, hx, rfl⟩ hc
    rw [hB23] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hcx : ∀ y : SU (unitaryInvolution (GaloisField p (2 * f)) p f) 6,
        iota3 hσ b * y = y * iota3 hσ b := fun y =>
      φ.injective (by rw [map_mul, map_mul]; exact ((Subgroup.mem_center_iff.mp hc) (φ y)).symm)
    have hb1 : b = 1 := by
      refine eq_one_of_mem_B23_commute_B12 hb (fun c => ?_) (fun c => ?_)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
      · exact iota3_injective hσ (by rw [map_mul, map_mul]; exact hcx _)
    rw [hb1, map_one, map_one]


theorem mem_te6Minus_iff (hp2 : p ≠ 2) (v : Fin (5 + 1) → GaloisField p (2 * f)) :
    v ∈ te6Minus p f ↔ ∀ r : Fin (5 + 1), 2 ≤ r.val → v r = 0 := by
  have h2 : (2 : GaloisField p (2 * f)) ≠ 0 := two_ne_zero_te6 hp2
  unfold te6Minus
  rw [mem_minusSpaceSU]
  have hrw : ∀ r : Fin (5 + 1), (suMat (te6Inv p f) *ᵥ v) r =
      (if r.val < 2 then (-1 : GaloisField p (2 * f)) else 1) * v r := by
    intro r
    show (zMat (GaloisField p (2 * f)) (5 + 1) (nodePair 5 0 (by norm_num)).1 *ᵥ v) r = _
    rw [zMat, Matrix.mulVec_diagonal]
    have : r ∈ (nodePair 5 0 (by norm_num)).1 ↔ r.val < 2 := by
      simp only [nodePair, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    simp only [this]
  constructor
  · intro h r hr
    have := congrFun h r
    rw [hrw r, Pi.neg_apply, ite_eq_right (by omega)] at this
    have h3 : (2 : GaloisField p (2 * f)) * v r = 0 := by
      calc (2 : GaloisField p (2 * f)) * v r = v r - -v r := by ring
        _ = 0 := by rw [← this]; ring
    exact (mul_eq_zero.mp h3).resolve_left h2
  · intro h
    funext r
    rw [hrw r, Pi.neg_apply]
    by_cases hr : r.val < 2
    · simp [hr]
    · rw [h r (by omega)]
      simp

structure AdaptedBasis (p f : ℕ) [Fact p.Prime]
    (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    (P : GL (Fin 6) (GaloisField p (2 * f))) (d₀ d₁ : GaloisField p (2 * f)) : Prop where
  gram : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
    (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = antidiag 6
  eigen : g * (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
    (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁)
  plane : ∀ r : Fin 6, 2 ≤ r.val →
    (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) r 2 = 0 ∧
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) r 3 = 0

section Frame

variable {E : Type*} [Field E]

theorem diagonal_mul_blockMat {m i k : ℕ} (d : Fin m → E)
    (hd : ∀ a b : Fin m, (i ≤ a.val ∧ a.val < i + k) → (i ≤ b.val ∧ b.val < i + k) → d a = d b)
    (A : Matrix (Fin k) (Fin k) E) :
    Matrix.diagonal d * blockMat m i A = blockMat m i A * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, blockMat_apply]
  by_cases h : (i ≤ a.val ∧ a.val < i + k) ∧ (i ≤ b.val ∧ b.val < i + k)
  · rw [dite_eq_left h, hd a b h.1 h.2, mul_comm]
  · rw [dite_eq_right h]
    by_cases hab : a = b
    · subst hab
      simp [mul_comm]
    · simp [hab]

end Frame

section Matrices

variable {E : Type} [Field E] {σ : E ≃+* E} (hσ : ∀ c, σ (σ c) = c)

include hσ in
theorem coe_iota3_blocks (b : SL(3, E)) :
    (((iota3 hσ b : SU σ 6) : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) =
      blockMat 6 0 (b : Matrix (Fin 3) (Fin 3) E) *
        blockMat 6 3 ((tau3 σ b : SL(3, E)) : Matrix (Fin 3) (Fin 3) E) := by
  show ((iota3SL σ b : SL(6, E)) : Matrix (Fin 6) (Fin 6) E) = _
  rw [iota3SL_apply, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_blockSL]

include hσ in
theorem diagonal_mul_iota3 (d₀ d₁ : E) (b : SL(3, E)) :
    Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁) *
        (((iota3 hσ b : SU σ 6) : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) =
      (((iota3 hσ b : SU σ 6) : GL (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) *
        Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁) := by
  rw [coe_iota3_blocks hσ, ← Matrix.mul_assoc,
    diagonal_mul_blockMat (k := 3) (i := 0) _ (fun a b ha hb => by
      simp only [show a.val < 3 by omega, show b.val < 3 by omega, ite_true]),
    Matrix.mul_assoc,
    diagonal_mul_blockMat (k := 3) (i := 3) _ (fun a b ha hb => by
      simp only [show ¬ a.val < 3 by omega, show ¬ b.val < 3 by omega, ite_false]),
    ← Matrix.mul_assoc]

end Matrices

section Main

variable {g : GL (Fin 6) (GaloisField p (2 * f))} {P : GL (Fin 6) (GaloisField p (2 * f))}
  {d₀ d₁ : GaloisField p (2 * f)}

theorem commutes_of_conj_diagonal
    (hg : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁))
    {M : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))}
    (hM : Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁) * M =
      M * Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁)) :
    (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        ((P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * M *
          ((P⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6)
            (GaloisField p (2 * f)))) =
      ((P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) * M *
          ((P⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6)
            (GaloisField p (2 * f)))) *
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) := by
  set D := Matrix.diagonal (fun i : Fin 6 => if i.val < 3 then d₀ else d₁) with hD
  set Pm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((P : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hPm
  set Pi : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((P⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hPi'
  set Gm : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)) :=
    ((g : GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
    with hGm
  have hPi : Pi * Pm = 1 := by
    rw [hPi', hPm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP : Pm * Pi = 1 := by
    rw [hPi', hPm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1 : Pi * Gm = D * Pi := by
    have h := congrArg (fun X => Pi * X * Pi) hg
    simp only [Matrix.mul_assoc] at h
    rw [hPP, Matrix.mul_one, ← Matrix.mul_assoc Pi Pm, hPi, Matrix.one_mul] at h
    exact h
  calc Gm * (Pm * M * Pi) = (Gm * Pm) * M * Pi := by simp only [Matrix.mul_assoc]
    _ = Pm * (D * M) * Pi := by rw [hg]; simp only [Matrix.mul_assoc]
    _ = Pm * (M * D) * Pi := by rw [hM]
    _ = Pm * M * (D * Pi) := by simp only [Matrix.mul_assoc]
    _ = Pm * M * (Pi * Gm) := by rw [e1]
    _ = (Pm * M * Pi) * Gm := by simp only [Matrix.mul_assoc]

theorem map_node_two_eq (hf : 1 ≤ f) (hp2 : p ≠ 2)
    (hP : conjTr (unitaryInvolution (GaloisField p (2 * f)) p f)
      (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = antidiag 6)
    (hcol : colPlane (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
      (lowIdx (⟨2, by norm_num⟩ : Fin (6 / 2))) = te6Minus p f) :
    (nodeSU (unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f)
        (CFSG.LieType.Universal.card_galoisField_two_mul p f hf)) 2).map
          (conjEquiv P hP).toMonoidHom =
      LcU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num)) := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hfix : nodeSU (unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f)
      hF) 2 = fixCols (unitaryInvolution (GaloisField p (2 * f)) p f) 6
        (lastIdxEven (⟨2, by norm_num⟩ : Fin (6 / 2))) :=
    rankOne_eq_fixCols hF (k := ⟨2, by norm_num⟩) (γ := Pi.single 2 1) (by decide +kernel)
      (by decide +kernel)
  ext y
  have h1 := mem_map_fixCols_iff (p := p) (f := f) (k := (⟨2, by norm_num⟩ : Fin (6 / 2))) P hP y
  have h2 : y ∈ te6Node p f ↔ ∀ w ∈ perp (unitaryInvolution (GaloisField p (2 * f)) p f)
      (te6Minus p f), y • w = w := by
    rw [te6Node_eq hp2 hf]
    exact mem_fixingSubgroup_iff _
  change y ∈ Subgroup.map _ (nodeSU _ 2) ↔ y ∈ te6Node p f
  rw [hfix, h1, hcol, h2]

variable {g : GL (Fin 6) (GaloisField p (2 * f))}

theorem alpha_eq_of_commutes
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    {y : Su (GaloisField p (2 * f)) p f 6}
    (h : (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
        ((y : GL (Fin 6) (GaloisField p (2 * f))) :
          Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
      ((y : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))) : α y = y := by
  apply Subtype.ext
  apply Units.ext
  rw [hα y, h, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem adaptedFrame_of_adaptedBasis (hf : 1 ≤ f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hα : ∀ x : Su (GaloisField p (2 * f)) p f 6,
      ((α x : GL (Fin 6) (GaloisField p (2 * f))) :
        Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) =
        (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((x : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
          ((g⁻¹ : GL (Fin 6) (GaloisField p (2 * f))) :
            Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))))
    {d₀ d₁ : GaloisField p (2 * f)}
    (hAB : AdaptedBasis p f (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) P d₀ d₁) :
    AdaptedFrame p f hf α := by
  classical
  have : NeZero (2 * f) := ⟨by omega⟩
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hσ := unitaryInvolution_involutive (K := GaloisField p (2 * f)) (p := p) (f := f) hF
  obtain ⟨F, hR, hS2, hS3⟩ := exists_su6Frame_of_witt hf hp2 hq P hAB.gram
  have hB23 : nodeSU hσ 1 = (WeakCT.B23 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B23_ge hσ) (iota3_B23_le hσ)
  have hB12 : nodeSU hσ 0 = (WeakCT.B12 (GaloisField p (2 * f))).map (iota3 hσ) :=
    le_antisymm (iota3_B12_ge hσ) (iota3_B12_le hσ)
  have hfixι : ∀ b : SL(3, GaloisField p (2 * f)),
      α (conjEquiv P hAB.gram (iota3 hσ b)) = conjEquiv P hAB.gram (iota3 hσ b) := by
    intro b
    refine alpha_eq_of_commutes hα ?_
    show (g : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) *
      ((P * ((iota3 hσ b : SU _ 6) : GL (Fin 6) (GaloisField p (2 * f))) * P⁻¹ :
        GL (Fin 6) (GaloisField p (2 * f))) : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f))) = _
    rw [Units.val_mul, Units.val_mul]
    exact commutes_of_conj_diagonal hAB.eigen (diagonal_mul_iota3 hσ d₀ d₁ b)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hR]
    refine map_node_two_eq hf hp2 hAB.gram ?_
    have hle : colPlane (P : Matrix (Fin 6) (Fin 6) (GaloisField p (2 * f)))
        (lowIdx (⟨2, by norm_num⟩ : Fin (6 / 2))) ≤ te6Minus p f := by
      refine Submodule.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [SetLike.mem_coe, mem_te6Minus_iff hp2]
        intro r hr
        rw [Matrix.mulVec_single_one]
        exact (hAB.plane r hr).1
      · rw [SetLike.mem_coe, mem_te6Minus_iff hp2]
        intro r hr
        rw [Matrix.mulVec_single_one]
        exact (hAB.plane r hr).2
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_colPlane hAB.gram (lowIdx_ne_rev _ _), finrank_te6Minus hp2])
  · intro x hx
    rw [hS2] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hB23] at ha
    obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := ha
    exact hfixι _
  · intro x hx
    rw [hS3] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hB12] at ha
    obtain ⟨_, ⟨b, -, rfl⟩, rfl⟩ := ha
    exact hfixι _

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
