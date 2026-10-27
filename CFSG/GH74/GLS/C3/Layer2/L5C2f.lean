module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2fInputs
public import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputs
public import Certificates.Certificate5045
public import Certificates.Certificate5051
public import Certificates.Certificate5056
public import Certificates.Certificate5142

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem chk0_true :
    chk0 = true :=
  Certificates.certificate5142

end Fus

open Fus

theorem engine0
    {E : ↥Sh0 → ↥Sh0 → Prop} (h : FusionHyp ↥Sh0 embHom0 E) :
    ∀ a b : ↥Sh0, (a : Perm (Fin 16)) ∈ R1L → a * a = 1 → b * b = 1 → E a b →
      (b : Perm (Fin 16)) ∈ R1L := by
  intro a b haR ha2 hb2 hab
  by_cases ha1 : a = 1
  · subst ha1
    have hb : b = 1 := h.eq_one_of_E_one hb2 hab
    subst hb
    exact one_mem_R1L
  · by_cases hb1 : b = 1
    · subst hb1
      exact absurd (h.eq_one_of_E_one ha2 (h.equiv.symm hab)) ha1
    · let _ := sh0D.grp
      have hc := chk0_true
      simp only [chk0, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
      obtain ⟨⟨hok, hsurv⟩, hpost⟩ := hc
      obtain ⟨ld, hld, hblk⟩ := fusion_blocks h sh0D hok
      have hld' : ld = [0, 1, 1, 0, 0, 1] := by
        have := hld
        rw [show survivors (engOf sh0D embHom0) = [[0, 1, 1, 0, 0, 1]] from hsurv] at this
        simpa using this
      subst hld'
      have hbl := (hblk a b ha2 ha1 hb2 hb1).1 hab
      have hia : isInv (sh0D.idx a) = true := (isInv_idx sh0D a).2 ⟨ha2, ha1⟩
      have hib : isInv (sh0D.idx b) = true := (isInv_idx sh0D b).2 ⟨hb2, hb1⟩
      have hp := hpost (sh0D.idx a) ((mem_engOf_invs sh0D embHom0 _).2 hia) (sh0D.idx b)
        ((mem_engOf_invs sh0D embHom0 _).2 hib)
      have h1 : isR1 (sh0D.idx a) = true := by
        simp only [isR1, sh0D.e_idx]
        exact List.contains_iff_mem.2 haR
      have h2 : isR1 (sh0D.idx b) = true := by
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hp
        rcases hp with (hp | hp) | hp
        · rw [h1] at hp; exact absurd hp (by simp)
        · exact absurd hbl hp
        · exact hp
      simp only [isR1, sh0D.e_idx] at h2
      exact List.contains_iff_mem.1 h2

end CFSG.GH74.GLS.C3.Layer2.L5
