module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Th

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Certificates CFSG.Sporadic.Th.Max3.AltQuot

@[expose] def thSing (v : Fin 8 → ZMod 2) : Prop := v ≠ 0 ∧ ExtraspecialNF.qf c v = 0

instance (v : Fin 8 → ZMod 2) : Decidable (thSing v) := by unfold thSing; infer_instance

@[expose] def applyWord (A B : Matrix (Fin 8) (Fin 8) (ZMod 2)) :
    List Bool → (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2)
  | [], v => v
  | b :: l, v => applyWord A B l (Matrix.mulVec (if b then B else A) v)

@[expose] def thWords : List ((Fin 8 → ZMod 2) × List Bool) := [
  (![0, 0, 0, 0, 0, 0, 0, 1], []),
  (![0, 0, 0, 0, 0, 0, 1, 0], [false, true, false, true, false, true, true, true, false]),
  (![0, 0, 0, 0, 0, 0, 1, 1], [true, false, true, false, true, false, true, true, true, false]),
  (![0, 0, 0, 0, 0, 1, 0, 0], [false]),
  (![0, 0, 0, 0, 0, 1, 1, 1], [false, true, true, true, true, false, true]),
  (![0, 0, 0, 0, 1, 0, 0, 0], [false, true, false, true, false, true, true, true]),
  (![0, 0, 0, 0, 1, 0, 1, 0], [true, false, true, true, true, false, true, true, true, true, true]),
  (![0, 0, 0, 0, 1, 1, 0, 0], [true, false, true, false, true, false, true, true, true]),
  (![0, 0, 0, 0, 1, 1, 0, 1], [true, false, true, true, true, true, true]),
  (![0, 0, 0, 1, 0, 0, 0, 0], [false, true]),
  (![0, 0, 0, 1, 0, 0, 0, 1], [false, true, true, true, false, true, true, false, true, false, true, true, true]),
  (![0, 0, 0, 1, 0, 1, 0, 1], [true, false, true, true, true, false, true, true]),
  (![0, 0, 0, 1, 0, 1, 1, 1], [true, false, true, true, false, true, false]),
  (![0, 0, 0, 1, 1, 0, 0, 1], [false, true, true, false, true, true, true, true, false, true, true]),
  (![0, 0, 0, 1, 1, 0, 1, 0], [false, true, true, true, false, true, true, false, true, false, true, true]),
  (![0, 0, 0, 1, 1, 1, 0, 0], [true, false, true, false, true, true, true, true, true, false]),
  (![0, 0, 0, 1, 1, 1, 0, 1], [true, false, true, true, false, true, true, true, false, true]),
  (![0, 0, 0, 1, 1, 1, 1, 0], [true, true]),
  (![0, 0, 0, 1, 1, 1, 1, 1], [true]),
  (![0, 0, 1, 0, 0, 0, 0, 0], [false, true, false]),
  (![0, 0, 1, 0, 0, 0, 1, 1], [true, false, true, false, true, true, true, true, true]),
  (![0, 0, 1, 0, 0, 1, 0, 0], [true, false, true, true, false, true, false, true, false, true, true, true, true]),
  (![0, 0, 1, 0, 0, 1, 0, 1], [true, false, true, true, true, false, true, true, false]),
  (![0, 0, 1, 0, 0, 1, 1, 0], [false, true, true, false, true, true, true, true, false, true, true, false]),
  (![0, 0, 1, 0, 0, 1, 1, 1], [false, true, true, true, true, true, false, true, true, false, true]),
  (![0, 0, 1, 0, 1, 0, 1, 0], [false, true, false, true, false, true, true, true, false, true, false, true]),
  (![0, 0, 1, 0, 1, 0, 1, 1], [true, true, false]),
  (![0, 0, 1, 0, 1, 1, 0, 1], [true, false, true, true, false, true]),
  (![0, 0, 1, 0, 1, 1, 1, 1], [true, false]),
  (![0, 0, 1, 1, 0, 0, 0, 0], [true, false, true, false, true, false, true, true, true, true]),
  (![0, 0, 1, 1, 0, 0, 1, 0], [true, false, true, true, true, true, false, true, true, true, true]),
  (![0, 0, 1, 1, 0, 1, 1, 0], [false, true, true, false, true, true]),
  (![0, 0, 1, 1, 0, 1, 1, 1], [true, false, true, false, true, true, false]),
  (![0, 0, 1, 1, 1, 0, 0, 0], [true, false, true, true, true, true, false, true, true, true, true, false]),
  (![0, 0, 1, 1, 1, 0, 0, 1], [false, true, true, false, true, false, true]),
  (![0, 0, 1, 1, 1, 0, 1, 0], [true, false, true, true, false, true, false, true, false, true, true]),
  (![0, 0, 1, 1, 1, 0, 1, 1], [true, false, true, true, false, true, false, true, false]),
  (![0, 0, 1, 1, 1, 1, 0, 1], [true, false, true, false, true, true]),
  (![0, 0, 1, 1, 1, 1, 1, 0], [true, false, true, true, false, true, false, true]),
  (![0, 1, 0, 0, 0, 0, 0, 0], [false, true, false, true, false]),
  (![0, 1, 0, 0, 0, 0, 1, 0], [true, false, true, false, true, true, true, true]),
  (![0, 1, 0, 0, 0, 1, 0, 0], [true, false, true, true, false, true, false, true, true, false]),
  (![0, 1, 0, 0, 0, 1, 0, 1], [false, true, true, true, true, false, true, true]),
  (![0, 1, 0, 0, 1, 0, 0, 0], [true, false, true, true, true, false, true, true, true, true, false]),
  (![0, 1, 0, 0, 1, 0, 0, 1], [false, true, true, true, false, true, true, false, true, false, true, false]),
  (![0, 1, 0, 0, 1, 0, 1, 0], [false, true, false, true, false, true, true, true, false, true]),
  (![0, 1, 0, 0, 1, 0, 1, 1], [true, false, true, false, true, true, true, true, true, false, true]),
  (![0, 1, 0, 0, 1, 1, 0, 0], [true, false, true, true, true, false, true, false]),
  (![0, 1, 0, 0, 1, 1, 1, 1], [true, false, true, false, true, false, true, true]),
  (![0, 1, 0, 1, 0, 0, 0, 1], [true, false, true, true, true, true]),
  (![0, 1, 0, 1, 0, 0, 1, 0], [true, false, true, true, true, true, false, true, true]),
  (![0, 1, 0, 1, 0, 1, 0, 0], [false, true, true, false, true, true, true, false]),
  (![0, 1, 0, 1, 0, 1, 0, 1], [true, false, true, true, false, true, true, true, false]),
  (![0, 1, 0, 1, 0, 1, 1, 0], [true, false, true, true, true, true, false, true, false, true, false]),
  (![0, 1, 0, 1, 0, 1, 1, 1], [true, false, true, false, true, true, true, false, true, false, true, false]),
  (![0, 1, 0, 1, 1, 0, 0, 0], [true, false, true, true, true, true, false, true, true, true]),
  (![0, 1, 0, 1, 1, 0, 0, 1], [true, false, true, true, false]),
  (![0, 1, 0, 1, 1, 1, 0, 1], [true, false, true, false, true]),
  (![0, 1, 0, 1, 1, 1, 1, 1], [true, false, true, true, false, true, true, false]),
  (![0, 1, 1, 0, 0, 0, 0, 0], [true, false, true, false, true, true, true, true, false, true]),
  (![0, 1, 1, 0, 0, 0, 0, 1], [false, true, false, true, false, true, false, true]),
  (![0, 1, 1, 0, 0, 1, 0, 0], [true, false, true, true, false, true, false, true, false, true, true, true, false]),
  (![0, 1, 1, 0, 0, 1, 1, 0], [false, true, true, true, true, true, false]),
  (![0, 1, 1, 0, 1, 0, 0, 1], [false, true, false, true, false, true]),
  (![0, 1, 1, 0, 1, 0, 1, 0], [true, false, true, true, true, false]),
  (![0, 1, 1, 1, 0, 1, 0, 0], [true, false, true, true, true, false, true, true, true]),
  (![0, 1, 1, 1, 0, 1, 1, 1], [false, true, true, true, false, true, true, false]),
  (![0, 1, 1, 1, 1, 0, 0, 1], [true, false, true, false, true, true, true, false, true, false]),
  (![0, 1, 1, 1, 1, 0, 1, 1], [false, true, true]),
  (![0, 1, 1, 1, 1, 1, 0, 0], [false, true, true, true, true, true, false, true, false]),
  (![0, 1, 1, 1, 1, 1, 0, 1], [false, true, true, true, false, true]),
  (![1, 0, 0, 0, 0, 0, 0, 0], [false, true, false, true]),
  (![1, 0, 0, 0, 0, 0, 0, 1], [true, false, true, true, false, true, false, true, true]),
  (![1, 0, 0, 0, 0, 0, 1, 0], [true, false, true, true, true, false, true, true, true, true]),
  (![1, 0, 0, 0, 0, 0, 1, 1], [true, false, true, true, true, false, true]),
  (![1, 0, 0, 0, 0, 1, 0, 1], [true, false, true, false, true, false, true]),
  (![1, 0, 0, 0, 0, 1, 1, 0], [false, true, true, true, false, true, true, false, true, false, true]),
  (![1, 0, 0, 0, 1, 0, 0, 0], [true, false, true, false, true, true, true, true, false]),
  (![1, 0, 0, 0, 1, 0, 1, 0], [false, true, false, true, false, true, true, true, false, true, false]),
  (![1, 0, 0, 0, 1, 1, 1, 0], [true, false, true, true, false, true, false, true, false, true]),
  (![1, 0, 0, 0, 1, 1, 1, 1], [true, false, true, false, true, false, true, true, false]),
  (![1, 0, 0, 1, 0, 0, 0, 0], [true, false, true, false, true, true, true, true, false, true, false]),
  (![1, 0, 0, 1, 0, 0, 0, 1], [true, false, true, true, false, true, false, true, false, true, true, true]),
  (![1, 0, 0, 1, 0, 1, 0, 0], [false, true, true, true, false, true, true, true]),
  (![1, 0, 0, 1, 0, 1, 1, 0], [false, true, false, true, false, true, false]),
  (![1, 0, 0, 1, 1, 0, 0, 1], [false, true, true, true, true, true]),
  (![1, 0, 0, 1, 1, 0, 1, 0], [true, false, true, true, true]),
  (![1, 0, 1, 0, 0, 0, 0, 1], [false, true, true, false, true, true, true]),
  (![1, 0, 1, 0, 0, 0, 1, 0], [false, true, true, true, true, true, false, true, false, true]),
  (![1, 0, 1, 0, 0, 1, 0, 0], [true, false, true, true, true, true, false]),
  (![1, 0, 1, 0, 0, 1, 0, 1], [true, false, true, true, false, true, true, true]),
  (![1, 0, 1, 0, 0, 1, 1, 0], [true, false, true, true]),
  (![1, 0, 1, 0, 0, 1, 1, 1], [true, false, true, false, true, false]),
  (![1, 0, 1, 0, 1, 0, 0, 0], [false, true, true, true, false, true, false, true, true]),
  (![1, 0, 1, 0, 1, 0, 0, 1], [true, false, true, true, true, true, false, true, false, true]),
  (![1, 0, 1, 0, 1, 1, 0, 1], [true, false, true, false, true, true, true, false, true, false, true]),
  (![1, 0, 1, 0, 1, 1, 1, 1], [true, false, true, true, false, true, true]),
  (![1, 0, 1, 1, 0, 0, 0, 1], [true, false, true, true, true, false, true, true, true, false]),
  (![1, 0, 1, 1, 0, 0, 1, 1], [false, true, true, true, true, true, false, true]),
  (![1, 0, 1, 1, 0, 1, 1, 0], [true, false, true, false, true, true, true, false, true]),
  (![1, 0, 1, 1, 0, 1, 1, 1], [false, true, true, true, false, true, false]),
  (![1, 0, 1, 1, 1, 1, 0, 1], [false, true, true, true, false, true, true]),
  (![1, 0, 1, 1, 1, 1, 1, 0], [false, true, true, false]),
  (![1, 1, 0, 0, 0, 0, 0, 1], [false, true, true, false, true]),
  (![1, 1, 0, 0, 0, 0, 1, 1], [false, true, true, false, true, true, true, true, false, true, false]),
  (![1, 1, 0, 0, 0, 1, 0, 0], [false, true, true, false, true, false]),
  (![1, 1, 0, 0, 0, 1, 0, 1], [false, true, true, true, true, true, false, true, true, false, true, true]),
  (![1, 1, 0, 0, 1, 1, 0, 0], [false, true, true, false, true, true, true, true, false, true]),
  (![1, 1, 0, 0, 1, 1, 1, 1], [true, false, true, true, false, true, true, true, true]),
  (![1, 1, 0, 1, 0, 0, 0, 0], [true, false, true, true, true, true, false, true]),
  (![1, 1, 0, 1, 0, 0, 1, 1], [false, true, true, true, true, false]),
  (![1, 1, 0, 1, 0, 1, 0, 0], [true, false, true, false, true, true, true]),
  (![1, 1, 0, 1, 0, 1, 0, 1], [true, false, true, false]),
  (![1, 1, 0, 1, 0, 1, 1, 0], [false, true, false, true, false, true, true]),
  (![1, 1, 0, 1, 0, 1, 1, 1], [false, true, true, true, false, true, true, false, true]),
  (![1, 1, 0, 1, 1, 0, 1, 0], [false, true, true, false, true, true, true, true, false, true, true, false, true]),
  (![1, 1, 0, 1, 1, 0, 1, 1], [false, true, true, true, true, true, false, true, true, false]),
  (![1, 1, 0, 1, 1, 1, 0, 1], [false, true, true, true, false]),
  (![1, 1, 0, 1, 1, 1, 1, 1], [false, true, true, false, true, true, true, true]),
  (![1, 1, 1, 0, 0, 0, 0, 0], [true, false, true, true, true, true, false, true, false]),
  (![1, 1, 1, 0, 0, 0, 0, 1], [true, false, true, false, true, true, true, false]),
  (![1, 1, 1, 0, 0, 1, 0, 1], [true, false, true]),
  (![1, 1, 1, 0, 0, 1, 1, 1], [false, true, true, true]),
  (![1, 1, 1, 0, 1, 0, 0, 1], [false, true, false, true, false, true, true, false]),
  (![1, 1, 1, 0, 1, 0, 1, 0], [false, true, false, true, false, true, true, true, false, true, false, true, true]),
  (![1, 1, 1, 0, 1, 1, 0, 0], [false, true, true, true, true]),
  (![1, 1, 1, 0, 1, 1, 0, 1], [false, true, true, true, false, true, true, false, true, false]),
  (![1, 1, 1, 0, 1, 1, 1, 0], [false, true, true, true, true, true, false, true, true]),
  (![1, 1, 1, 0, 1, 1, 1, 1], [false, true, true, false, true, true, true, true, false]),
  (![1, 1, 1, 1, 0, 1, 0, 1], [true, true, false, true]),
  (![1, 1, 1, 1, 0, 1, 1, 0], [false, true, false, true, false, true, false, true, true]),
  (![1, 1, 1, 1, 1, 0, 0, 1], [false, true, false, true, false, true, false, true, true, false]),
  (![1, 1, 1, 1, 1, 0, 1, 1], [false, true, true, true, false, true, false, true, false]),
  (![1, 1, 1, 1, 1, 1, 1, 0], [false, true, true, true, false, true, false, true]),
  (![1, 1, 1, 1, 1, 1, 1, 1], [true, false, true, true, true, true, false, true, false, true, true])]

@[expose] def thV0 : Fin 8 → ZMod 2 := ![0, 0, 0, 0, 0, 0, 0, 1]

theorem thWords_check : ∀ p ∈ thWords, applyWord B1 B2 p.2 thV0 = p.1 := by decide +kernel

theorem thWords_cover : ∀ v : Fin 8 → ZMod 2, thSing v → v ∈ thWords.map Prod.fst := by
  decide +kernel

theorem thSing_B1 : ∀ v : Fin 8 → ZMod 2, thSing v ↔ thSing (Matrix.mulVec B1 v) := by
  decide +kernel

theorem thSing_B2 : ∀ v : Fin 8 → ZMod 2, thSing v ↔ thSing (Matrix.mulVec B2 v) := by
  decide +kernel

theorem card_thSing : Nat.card {v : Fin 8 → ZMod 2 // thSing v} = 135 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

section Generic

variable {X : Type} [Group X] (M Q : Subgroup X) (hc : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)

@[expose] def conjOn : ↥M →* MulAut ↥Q where
  toFun g :=
    { toFun := fun q => ⟨g * q * (g : X)⁻¹, hc g g.2 q q.2⟩
      invFun := fun q => ⟨(g : X)⁻¹ * q * g, by simpa using hc _ (M.inv_mem g.2) q q.2⟩
      left_inv := fun q => Subtype.ext (by simp [mul_assoc])
      right_inv := fun q => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun p q => Subtype.ext (by
        show (g : X) * (p * q) * (g : X)⁻¹ = (g * p * (g : X)⁻¹) * (g * q * (g : X)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun q => Subtype.ext (by
    show ((1 : ↥M) : X) * q * ((1 : ↥M) : X)⁻¹ = q
    simp)
  map_mul' g h := MulEquiv.ext fun q => Subtype.ext (by
    show ((g * h : ↥M) : X) * q * ((g * h : ↥M) : X)⁻¹ = (g : X) * (h * q * (h : X)⁻¹) * (g : X)⁻¹
    simp only [Subgroup.coe_mul]
    group)

variable {V : Type} [Group V] (θ : V ≃* Q ⧸ Subgroup.center Q)

@[expose] noncomputable def rhoGen : ↥M →* MulAut V :=
  (MulAut.congr θ.symm).toMonoidHom.comp
    ((CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥Q).comp (conjOn M Q hc))

theorem rhoGen_mk (g : ↥M) (q : ↥Q) :
    rhoGen M Q hc θ g (θ.symm (QuotientGroup.mk q)) =
      θ.symm (QuotientGroup.mk ⟨g * q * (g : X)⁻¹, hc g g.2 q q.2⟩) := by
  show θ.symm (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot ↥Q (conjOn M Q hc g)
    (θ (θ.symm (QuotientGroup.mk q)))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

@[expose] def wordElt (a b : ↥M) : List Bool → ↥M
  | [] => 1
  | t :: l => wordElt a b l * (if t then b else a)

variable {M} in
theorem rho_word (ρ : ↥M →* MulAut (Multiplicative (Fin 8 → ZMod 2))) (a b : ↥M)
    (A B : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (ha : ∀ v, ρ a (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec A v))
    (hb : ∀ v, ρ b (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec B v))
    (l : List Bool) (v : Fin 8 → ZMod 2) :
    ρ (wordElt M a b l) (Multiplicative.ofAdd v) = Multiplicative.ofAdd (applyWord A B l v) := by
  induction l generalizing v with
  | nil => simp [wordElt, applyWord]
  | cons t l ih =>
    rw [wordElt, map_mul, MulAut.mul_apply]
    cases t
    · simp only [Bool.false_eq_true, if_false]
      rw [ha, ih]
      rfl
    · simp only [if_true]
      rw [hb, ih]
      rfl

variable {M} in
theorem pred_invariant (ρ : ↥M →* MulAut (Multiplicative (Fin 8 → ZMod 2)))
    (P : (Fin 8 → ZMod 2) → Prop) {x y : X} (hM : M = Subgroup.closure {x, y}) (hx : x ∈ M)
    (hy : y ∈ M) (A B : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (ha : ∀ v, ρ ⟨x, hx⟩ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec A v))
    (hb : ∀ v, ρ ⟨y, hy⟩ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec B v))
    (hA : ∀ v, P v ↔ P (Matrix.mulVec A v)) (hB : ∀ v, P v ↔ P (Matrix.mulVec B v))
    (g : ↥M) (w : Multiplicative (Fin 8 → ZMod 2)) :
    P (Multiplicative.toAdd w) ↔ P (Multiplicative.toAdd (ρ g w)) := by
  obtain ⟨g, hg⟩ := g
  have hgc : g ∈ Subgroup.closure {x, y} := hM ▸ hg
  revert w
  revert hg
  induction hgc using Subgroup.closure_induction with
  | mem g hg =>
    intro hg' w
    rcases hg with rfl | hg
    · rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from rfl, ha]
      exact hA _
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from rfl, hb]
      exact hB _
  | one =>
    intro h1 w
    have e : (⟨1, h1⟩ : ↥M) = 1 := rfl
    rw [e, map_one, MulAut.one_apply]
  | mul g h hgc hhc ihg ihh =>
    intro hgh w
    have hg : g ∈ M := by rw [hM]; exact hgc
    have hh : h ∈ M := by rw [hM]; exact hhc
    have e : (⟨g * h, hgh⟩ : ↥M) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
    rw [e, map_mul, MulAut.mul_apply]
    exact (ihh hh w).trans (ihg hg _)
  | inv g hgc ihg =>
    intro hgi w
    have hg : g ∈ M := by rw [hM]; exact hgc
    have e : (⟨g⁻¹, hgi⟩ : ↥M) = (⟨g, hg⟩ : ↥M)⁻¹ := rfl
    rw [e]
    have h1 := ihg hg (ρ (⟨g, hg⟩ : ↥M)⁻¹ w)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
    exact h1.symm

variable {M} in
theorem trans_of_words (ρ : ↥M →* MulAut (Multiplicative (Fin 8 → ZMod 2))) (a b : ↥M)
    (A B : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (ha : ∀ v, ρ a (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec A v))
    (hb : ∀ v, ρ b (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec B v))
    (L : List ((Fin 8 → ZMod 2) × List Bool)) (v0 : Fin 8 → ZMod 2)
    (hL : ∀ p ∈ L, applyWord A B p.2 v0 = p.1) {v v' : Fin 8 → ZMod 2}
    (hv : v ∈ L.map Prod.fst) (hv' : v' ∈ L.map Prod.fst) :
    ∃ g : ↥M, ρ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v' := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hv'
  refine ⟨wordElt M a b p'.2 * (wordElt M a b p.2)⁻¹, ?_⟩
  rw [← hL p hp, ← rho_word ρ a b A B ha hb, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel_right,
    rho_word ρ a b A B ha hb, hL p' hp']

theorem card_centralizer_mul_dvd [Finite X] (P : (Fin 8 → ZMod 2) → Prop)
    (θ' : Multiplicative (Fin 8 → ZMod 2) ≃* Q ⧸ Subgroup.center Q)
    (hinv : ∀ (g : ↥M) w, P (Multiplicative.toAdd w) ↔
      P (Multiplicative.toAdd (rhoGen M Q hc θ' g w)))
    (htr : ∀ v v', P v → P v' →
      ∃ g : ↥M, rhoGen M Q hc θ' g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v')
    {u : X} (huQ : u ∈ Q) {v : Fin 8 → ZMod 2}
    (hθ : θ'.symm (QuotientGroup.mk ⟨u, huQ⟩) = Multiplicative.ofAdd v) (hPv : P v) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set X) ⊓ M) * Nat.card {v' // P v'} ∣ Nat.card ↥M := by
  letI : MulAction ↥M (Multiplicative (Fin 8 → ZMod 2)) := MulAction.compHom _ (rhoGen M Q hc θ')
  have horb : MulAction.orbit ↥M (Multiplicative.ofAdd v) = {w' | P (Multiplicative.toAdd w')} := by
    ext w'
    constructor
    · rintro ⟨g, rfl⟩
      exact (hinv g _).1 hPv
    · intro hw'
      exact htr v _ hPv hw'
  have hidx := MulAction.index_stabilizer ↥M (Multiplicative.ofAdd v)
  rw [← Nat.card_coe_set_eq, horb] at hidx
  have hcP : Nat.card ↥{w' : Multiplicative (Fin 8 → ZMod 2) | P (Multiplicative.toAdd w')} =
      Nat.card {v' // P v'} :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun _ => Iff.rfl))
  rw [hcP] at hidx
  have hstab := (MulAction.stabilizer ↥M (Multiplicative.ofAdd v)).card_mul_index
  rw [hidx] at hstab
  have hle : (Subgroup.centralizer ({u} : Set X) ⊓ M).subgroupOf M ≤
      MulAction.stabilizer ↥M (Multiplicative.ofAdd v) := by
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    rw [MulAction.mem_stabilizer_iff]
    show rhoGen M Q hc θ' g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v
    have hcm := Subgroup.mem_centralizer_singleton_iff.1 hg.1
    rw [← hθ, rhoGen_mk]
    congr 2
    apply Subtype.ext
    show (g : X) * u * (g : X)⁻¹ = u
    rw [hcm, mul_inv_cancel_right]
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
  rw [← hstab]
  exact Nat.mul_dvd_mul_right h1 _

end Generic

theorem conj_mem_Q_th : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q :=
  fun _ hg _ hq => conj_mem_Q_of_mem_M hg hq

@[expose] noncomputable def rhoTh : ↥M →* MulAut (Multiplicative (Fin 8 → ZMod 2)) :=
  rhoGen M Q conj_mem_Q_th theta

set_option maxRecDepth 100000 in
theorem rhoTh_x (v : Fin 8 → ZMod 2) :
    rhoTh ⟨x, x_mem_M⟩ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec B1 v) := by
  rw [← MulEquiv.symm_apply_apply theta (Multiplicative.ofAdd v), theta_apply_nf 0 v]
  unfold rhoTh
  rw [rhoGen_mk, MulEquiv.symm_apply_eq]
  exact (theta_B1 v).symm

set_option maxRecDepth 100000 in
theorem rhoTh_y (v : Fin 8 → ZMod 2) :
    rhoTh ⟨y, y_mem_M⟩ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (Matrix.mulVec B2 v) := by
  rw [← MulEquiv.symm_apply_apply theta (Multiplicative.ofAdd v), theta_apply_nf 0 v]
  unfold rhoTh
  rw [rhoGen_mk, MulEquiv.symm_apply_eq]
  exact (theta_B2 v).symm

set_option maxRecDepth 100000 in
theorem thQCentFact_holds : ThQCentFact := by
  intro u huQ hu2 huz
  haveI : Finite ↥J := Finite.of_equiv _ thEquivJ.toEquiv
  obtain ⟨s, v, rfl⟩ := mem_Q_iff.1 huQ
  have hsing : thSing v := by
    refine ⟨fun hv0 => ?_, ?_⟩
    · subst hv0
      have h0 : nf s 0 = z ^ s.val := by simp [nf]
      rcases ExtraspecialNF.zmod_two_cases s with rfl | rfl
      · rw [h0] at hu2
        simp at hu2
      · rw [h0] at huz
        exact huz (by simp [ExtraspecialNF.val_one_two])
    · have h2 := nf_sq s v
      have h1 : nf s v ^ 2 = 1 := by
        have := pow_orderOf_eq_one (nf s v)
        rwa [hu2] at this
      rw [h1] at h2
      rcases ExtraspecialNF.zmod_two_cases (ExtraspecialNF.qf c v) with h | h
      · exact h
      · rw [h, ExtraspecialNF.val_one_two, pow_one] at h2
        exact absurd h2.symm z_ne_one
  have hinv : ∀ (g : ↥M) w, thSing (Multiplicative.toAdd w) ↔
      thSing (Multiplicative.toAdd (rhoTh g w)) :=
    pred_invariant rhoTh thSing rfl x_mem_M y_mem_M B1 B2 rhoTh_x rhoTh_y thSing_B1 thSing_B2
  have htr : ∀ v v', thSing v → thSing v' →
      ∃ g : ↥M, rhoTh g (Multiplicative.ofAdd v) = Multiplicative.ofAdd v' :=
    fun v v' hv hv' => trans_of_words rhoTh ⟨x, x_mem_M⟩ ⟨y, y_mem_M⟩ B1 B2 rhoTh_x rhoTh_y
      thWords thV0 thWords_check (thWords_cover v hv) (thWords_cover v' hv')
  have hθ : theta.symm (QuotientGroup.mk ⟨nf s v, huQ⟩) = Multiplicative.ofAdd v := by
    rw [MulEquiv.symm_apply_eq]
    exact (theta_apply_nf s v).symm
  have hd := card_centralizer_mul_dvd M Q conj_mem_Q_th thSing theta hinv htr huQ hθ hsing
  rw [card_thSing, card_M] at hd
  intro h27
  have := (Nat.mul_dvd_mul_right h27 135).trans hd
  norm_num at this

theorem i1016ThFact_holds : I1016ThFact := i1016ThFact_of_qCent thQCentFact_holds

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
