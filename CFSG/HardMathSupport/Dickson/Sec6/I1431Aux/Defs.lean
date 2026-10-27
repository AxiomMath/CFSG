module

public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.ComponentClassification.OuterAutomorphisms

section Induced

variable {Y : Type*} [Group Y]

@[expose] def stabAut (J : Subgroup Y) : Subgroup (MulAut Y) where
  carrier := {η | ∀ y, η y ∈ J ↔ y ∈ J}
  mul_mem' := fun {a b} ha hb y => by
    show a (b y) ∈ J ↔ y ∈ J
    exact (ha (b y)).trans (hb y)
  one_mem' := fun y => Iff.rfl
  inv_mem' := fun {a} ha y => by
    show a⁻¹ y ∈ J ↔ y ∈ J
    rw [← ha (a⁻¹ y)]
    simp

theorem mem_stabAut {J : Subgroup Y} {η : MulAut Y} : η ∈ stabAut J ↔ ∀ y, η y ∈ J ↔ y ∈ J :=
  Iff.rfl

@[expose] def restrictAut {J : Subgroup Y} (η : MulAut Y) (h : η ∈ stabAut J) : MulAut ↥J where
  toFun j := ⟨η (j : Y), (h (j : Y)).2 j.2⟩
  invFun j := ⟨η⁻¹ (j : Y), by
    refine (h (η⁻¹ (j : Y))).1 ?_
    simpa using j.2⟩
  left_inv j := Subtype.ext (by simp)
  right_inv j := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (map_mul η (a : Y) (b : Y))

theorem restrictAut_coe {J : Subgroup Y} {η : MulAut Y} (h : η ∈ stabAut J) (j : ↥J) :
    ((restrictAut η h j : ↥J) : Y) = η (j : Y) :=
  rfl

@[expose] def restrictHom (J : Subgroup Y) : ↥(stabAut J) →* MulAut ↥J where
  toFun η := restrictAut η.1 η.2
  map_one' := by
    ext j
    rfl
  map_mul' a b := by
    ext j
    rfl

@[expose] noncomputable def inducedBarHom (J : Subgroup Y) :
    ↥(stabAut J) →* MulAut (barOf 3 J) :=
  quotAutHom (GLAPPrimeCore 3 ↥J) (restrictHom J)
    (fun γ => map_gLAPPrimeCore 3 (restrictHom J γ))

theorem inducedBarHom_mk (J : Subgroup Y) (γ : ↥(stabAut J)) (j : ↥J) :
    inducedBarHom J γ (QuotientGroup.mk j) = QuotientGroup.mk (restrictAut γ.1 γ.2 j) :=
  quotAutHom_mk _ _ _ γ j

@[expose] def TrivBar (J : Subgroup Y) (η : MulAut Y) : Prop :=
  ∃ h : η ∈ stabAut J, inducedBarHom J ⟨η, h⟩ = 1

@[expose] def FieldBar (n : ℕ) (J : Subgroup Y) (η : MulAut Y) : Prop :=
  ∃ h : η ∈ stabAut J, IsFieldAutPSLn n (inducedBarHom J ⟨η, h⟩)

end Induced

@[expose] def RkY (Y : Type*) [Group Y] : Prop :=
  ∀ U : Subgroup Y, U ≠ ⊥ → IsPGroup 2 ↥U → ∀ E : Subgroup Y,
    E ≤ Subgroup.normalizer (U : Set Y) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 4 ∧ (E ⊓ Subgroup.center Y = ⊥ → Nat.card E ≤ 3 ^ 3)

@[expose] def IsD4Type (Y : Type) [Group Y] : Prop :=
  ∃ p f : ℕ, StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 p f

open Classical in
@[expose] noncomputable def d4Vocab : InndiagVocab where
  innDiag Y _ := if IsD4Type Y then innerAut Y else innAutDerived Y

structure Y1431Cfg (V : InndiagVocab) (Y : Type) [Group Y] [Finite Y]
    (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y) (q : ℕ) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple Y
  kgroup : CFSG.IsKGroup Y
  core : GLAPPrimeCore 3 Y = ⊥
  rank : RkY Y
  elemAbelian : IsElemAbelian 3 Â
  card : Nat.card Â = 9
  mem : ξ ∈ Â
  ne_one : ξ ≠ 1
  comp : GLAPComponent 3 (fixSub ξ) J
  typeL2 : IsTypeL2 q (barOf 3 J)
  not_dvd : ¬ 3 ∣ q
  ne_eight : q ≠ 8
  inn : ∀ e ∈ Â, e ∈ V.innDiag Y
  field : ∀ η ∈ Â, η ∉ Subgroup.zpowers ξ → FieldBar 2 J η ∧ ¬ TrivBar J η

structure Y1431Concl (Y : Type) [Group Y] [Finite Y]
    (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y) (q : ℕ) : Prop where
  psu : ∃ r0 : ℕ, r0 ^ 3 = q ∧ IsPSUn 6 r0 (Y ⧸ Subgroup.center Y)
  layer : ∀ J' : Subgroup Y, GLAPComponent 3 (fixSub ξ) J' → J' = J
  triple : ∃ η ∈ Â, η ≠ 1 ∧ ∃ r0 : ℕ, r0 ^ 3 = q ∧ ∃ H₁ H₂ H₃ : Subgroup Y,
    (∀ H : Subgroup Y, GLAPComponent 3 (fixSub η) H ↔ (H = H₁ ∨ H = H₂ ∨ H = H₃)) ∧
    H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
    (∀ H : Subgroup Y, (H = H₁ ∨ H = H₂ ∨ H = H₃) → IsTypeL2 r0 (barOf 3 H)) ∧
    ∀ H H' : Subgroup Y, (H = H₁ ∨ H = H₂ ∨ H = H₃) → (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) →
      ∃ e ∈ Â, H.map e.toMonoidHom = H'

@[expose] def Y1431 (V : InndiagVocab) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Â : Subgroup (MulAut Y)) (ξ : MulAut Y) (J : Subgroup Y)
    (q : ℕ), Y1431Cfg V Y Â ξ J q → Y1431Concl Y Â ξ J q

end CFSG.HardMathSupport.Dickson.Sec6.I1431
