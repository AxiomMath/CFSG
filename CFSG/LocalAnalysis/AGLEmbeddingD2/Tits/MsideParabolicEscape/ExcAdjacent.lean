module

public import CFSG.Timmesfeld.RankTwo.SimplyLaced
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.Timmesfeld Matrix CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped commutatorElement

variable {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem range_le_of_sl3 (hL : SimplyLacedLevis D F adj x) {i j : Fin D.rank} (hij : adj i j)
    {l : SpecialLinearGroup (Fin 3) F →* K}
    (hl : ∀ c, l (tv 0 1 c) = x (sroot i) c ∧ l (tv 1 0 c) = x (-sroot i) c ∧
      l (tv 1 2 c) = x (sroot j) c ∧ l (tv 2 1 c) = x (-sroot j) c ∧
      l (tv 0 2 c) = x (sroot i + sroot j) c ∧ l (tv 2 0 c) = x (-(sroot i + sroot j)) c)
    (g : SpecialLinearGroup (Fin 3) F) : l g ∈ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j := by
  have hi := hL.ne i j hij
  have hroot : ∀ k, (sroot k : Fin D.rank → ℤ) ∈ D.roots ∧ (-sroot k : Fin D.rank → ℤ) ∈ D.roots :=
    fun k => ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k,
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)⟩
  set J := rankOne D.rootGroup i ⊔ rankOne D.rootGroup j with hJ
  have h01 : ∀ c, l (tv 0 1 c) ∈ J := fun c => by
    rw [(hl c).1]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hL.mem _ (hroot i).1 c))
  have h10 : ∀ c, l (tv 1 0 c) ∈ J := fun c => by
    rw [(hl c).2.1]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hL.mem _ (hroot i).2 c))
  have h12 : ∀ c, l (tv 1 2 c) ∈ J := fun c => by
    rw [(hl c).2.2.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (hL.mem _ (hroot j).1 c))
  have h21 : ∀ c, l (tv 2 1 c) ∈ J := fun c => by
    rw [(hl c).2.2.2.1]
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (hL.mem _ (hroot j).2 c))
  have hS : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) F → SpecialLinearGroup (Fin 3) F)) = ⊤ :=
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) F → SpecialLinearGroup (Fin 3) F)) ≤
      J.comap l := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
    show l (Matrix.SpecialLinearGroup.transvection hab c) ∈ J
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · rw [← tv_of_ne hab]; exact h01 c
    · have h01' : (0 : Fin 3) ≠ 1 := by decide
      have h12' : (1 : Fin 3) ≠ 2 := by decide
      have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection (A := F) h01' h12' hab
        (1 : F) c
      rw [one_mul] at hc
      rw [← hc, map_commutatorElement, commutatorElement_def]
      have ha : l (Matrix.SpecialLinearGroup.transvection h01' (1 : F)) ∈ J := by
        rw [← tv_of_ne h01']; exact h01 1
      have hb : l (Matrix.SpecialLinearGroup.transvection h12' c) ∈ J := by
        rw [← tv_of_ne h12']; exact h12 c
      exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
    · rw [← tv_of_ne hab]; exact h10 c
    · exact absurd rfl hab
    · rw [← tv_of_ne hab]; exact h12 c
    · have h21' : (2 : Fin 3) ≠ 1 := by decide
      have h10' : (1 : Fin 3) ≠ 0 := by decide
      have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection (A := F) h21' h10' hab
        c (1 : F)
      rw [mul_one] at hc
      rw [← hc, map_commutatorElement, commutatorElement_def]
      have ha : l (Matrix.SpecialLinearGroup.transvection h21' c) ∈ J := by
        rw [← tv_of_ne h21']; exact h21 c
      have hb : l (Matrix.SpecialLinearGroup.transvection h10' (1 : F)) ∈ J := by
        rw [← tv_of_ne h10']; exact h10 1
      exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)
    · rw [← tv_of_ne hab]; exact h21 c
    · exact absurd rfl hab
  have : g ∈ Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) F → SpecialLinearGroup (Fin 3) F)) := by
    rw [hS]; trivial
  exact hle this

@[expose] def adjE (i j : ℕ) : Prop := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (2 ≤ i ∧ j = i + 1)

instance (i j : ℕ) : Decidable (adjE i j) := by unfold adjE; infer_instance

section E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley

theorem cartan_E6_iff (i j : Fin (Tag.rank .E6)) (hij : i ≠ j) :
    Tag.cartan .E6 i j = 0 ↔ ¬ (adjE i.val j.val ∨ adjE j.val i.val) := by
  revert hij
  fin_cases i <;> fin_cases j <;> decide

end E6

section E7

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley

theorem cartan_E7_iff (i j : Fin (Tag.rank .E7)) (hij : i ≠ j) :
    Tag.cartan .E7 i j = 0 ↔ ¬ (adjE i.val j.val ∨ adjE j.val i.val) := by
  revert hij
  fin_cases i <;> fin_cases j <;> decide

end E7

section E8

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley

theorem cartan_E8_iff (i j : Fin (Tag.rank .E8)) (hij : i ≠ j) :
    Tag.cartan .E8 i j = 0 ↔ ¬ (adjE i.val j.val ∨ adjE j.val i.val) := by
  revert hij
  fin_cases i <;> fin_cases j <;> decide

end E8

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
