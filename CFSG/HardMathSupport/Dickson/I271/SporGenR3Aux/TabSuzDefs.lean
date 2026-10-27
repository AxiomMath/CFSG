module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalBridge
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.CoverA6

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

section Entry

variable {Q Q' : Type} [Group Q] [Group Q']

@[expose] def SplitShapeAt (p : ℕ) (k : Q) : Prop :=
  PConstrainedShape p (Subgroup.centralizer ({k} : Set Q)) ∨
    ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) J ∧
      (∀ I : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({k} : Set Q)) I → I = J) ∧
      SplitGoodAt p J

theorem SplitShapeAt.of_centralizer_eq {p : ℕ} {k k' : Q}
    (h : Subgroup.centralizer ({k} : Set Q) = Subgroup.centralizer ({k'} : Set Q))
    (hk : SplitShapeAt p k) : SplitShapeAt p k' := by
  unfold SplitShapeAt at hk ⊢
  rw [← h]
  exact hk

theorem SplitShapeAt.pow {c : Q} (hc : c ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2)
    (h : SplitShapeAt 3 c) : SplitShapeAt 3 (c ^ e) :=
  SplitShapeAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc he).symm h

variable [Finite Q] [Finite Q']

theorem SplitShapeAt.of_equiv {p : ℕ} (hp : p.Prime) (e : Q ≃* Q') {k : Q}
    (h : SplitShapeAt p k) : SplitShapeAt p (e k) := by
  have hmap : (Subgroup.centralizer ({k} : Set Q)).map e.toMonoidHom =
      Subgroup.centralizer ({e k} : Set Q') := map_centralizer_singleton e k
  rcases h with hc | ⟨J, hJ, hu, hG⟩
  · left
    rw [← hmap]
    exact pConstrainedShape_map e hc
  · right
    refine ⟨J.map e.toMonoidHom, ?_, ?_, hG.of_equiv e⟩
    · rw [← hmap]
      exact glaPComponent_map_equiv hp e hJ
    · intro I' hI'
      have h1 := glaPComponent_map_equiv hp e.symm hI'
      have hmap' : (Subgroup.centralizer ({e k} : Set Q')).map e.symm.toMonoidHom =
          Subgroup.centralizer ({k} : Set Q) := by
        rw [map_centralizer_singleton e.symm (e k)]
        simp
      rw [hmap'] at h1
      have h2 := hu _ h1
      rw [← h2, Subgroup.map_map]
      have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext; simp
      rw [this, Subgroup.map_id]

theorem SplitShapeAt.conj {p : ℕ} (hp : p.Prime) (g : Q) {k : Q} (h : SplitShapeAt p k) :
    SplitShapeAt p (g * k * g⁻¹) := by
  have := SplitShapeAt.of_equiv hp (MulAut.conj g) h
  simpa [MulAut.conj_apply] using this

end Entry

end CFSG.HardMathSupport.Dickson.I271
