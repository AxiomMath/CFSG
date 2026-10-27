module

public import Certificates.Data.Kernel.L34FW
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.L34W.OuterSound

public section

namespace CFSG.KC.L34FW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34W
open CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four

variable {T PAR DEP G W : ℕ → ℕ} {f : ℕ → Equiv.Perm (Fin 42)}

theorem tree_sound (hc : ∀ j < 315, canonK 42 6 (mask 6) (42 * 6) (T j) = true)
    (hf : ∀ j < 315, TabRep (unpack 42 6 (T j)) (f j)) (h : treeK T PAR DEP = true) :
    ∀ j < 315, Relation.ReflTransGen
      (fun x y => ∃ a < 315, ∃ b < 315, x = f a ∧ y = f b ∧ x * y = y * x) (f 0) (f j) := by
  unfold treeK at h
  rw [bAnd_iff] at h
  obtain ⟨h0, hall⟩ := h
  have key : ∀ d j, DEP j = d → j < 315 → Relation.ReflTransGen
      (fun x y => ∃ a < 315, ∃ b < 315, x = f a ∧ y = f b ∧ x * y = y * x) (f 0) (f j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hd hj
      have hj' := allN_spec hall j hj
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact Relation.ReflTransGen.refl
      have hne : Nat.beq j 0 = false := by
        cases hb : Nat.beq j 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
      rw [hne, strictB_eq] at hj'
      simp only [bAnd_iff] at hj'
      obtain ⟨⟨hp, hdp⟩, hcm⟩ := hj'
      have hp' := Nat.blt_eq.mp hp
      have hdp' := Nat.blt_eq.mp hdp
      rw [CFSG.KC.L34KSnd.commPt_iff (hc j hj) (hc _ hp')] at hcm
      have e : f j * f (PAR j) = f (PAR j) * f j :=
        (((hf j hj).comp (hf _ hp')).eq_iff ((hf _ hp').comp (hf j hj))).1 hcm
      exact (ih _ (hd ▸ hdp') _ rfl hp').tail ⟨_, hp', j, hj, rfl, rfl, e.symm⟩
  exact fun j hj => key _ j rfl hj

theorem gen_sound (h : genK T G W = true) :
    W 0 < 315 ∧ W 1 < 315 ∧ W 2 < 315 ∧ W 3 < 315 ∧
      pcomp 42 6 (mask 6) (T (W 0)) (T (W 1)) = G 0 ∧ T (W 2) = G 1 ∧ T (W 3) = G 2 := by
  unfold genK at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨⟨h0, h1⟩, h2, h3⟩, h4, h5, h6⟩ := h
  exact ⟨Nat.blt_eq.mp h0, Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

end CFSG.KC.L34FW

end
