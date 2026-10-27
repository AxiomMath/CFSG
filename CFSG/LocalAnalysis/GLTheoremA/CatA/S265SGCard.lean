module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF1
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF6
import CFSG.LocalAnalysis.GLTheoremA.CatB.U48LayerY
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SG

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem card_le_of_nl_unitary_three {m : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData 2 m F)
    (h3 : 3 ∣ 2 ^ m + 1) (h2 : 2 ^ m ≠ 2)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))}
    (hX : IsElemAbelian 3 X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer 3 (fixSubgroup α) = ⊥) :
    Nat.card X ≤ 27 ∧ (2 ^ m ≠ 8 → Nat.card X ≤ 9) := by
  have hq : ¬(3 = 3 ∧ 2 ^ m = 2) := fun h' => h2 h'.2
  refine ⟨(CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_le_pow_unitary hF le_rfl hq
    Nat.prime_three (by norm_num) h3 X hX).trans (by norm_num), fun h8 => ?_⟩
  have h4 : 3 < 2 ^ m := by
    have hm : m ≠ 1 := by
      rintro rfl
      exact h2 (pow_one 2)
    have : 4 ≤ 2 ^ m := calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by have := hF.one_le; omega)
    omega
  have hXD := SF.le_primeFormD_of_nl_of_ne (p := 3) hF le_rfl hq
    (fun h' => h8 (h'.2.trans (by norm_num))) Nat.prime_three (by norm_num) h3 hX hnl
  exact (SF.card_le_of_nl_primeFormD hF le_rfl Nat.prime_three h4 h3 hXD hX hnl).trans
    (by norm_num)

private theorem nontrivial_of_tyFUni {Ω : Type} [Group Ω] {K : Subgroup Ω}
    (h : catalogIs (PSimple 3 K) (tyFUni 3)) : Nontrivial (PSimple 3 K) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases i with _ | _ | ⟨⟨l, hv⟩⟩ | _
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases l
    case twistedA r q =>
      exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ _ _ _
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)).1
    all_goals exact (hi : False).elim
  · exact (hi : False).elim

theorem card_eq_of_tyF {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) (hty : catalogIs (PSimple 3 K) (tyF 3)) :
    Nat.card B = 3 ^ 4 ∨ (catalogIs (PSimple 3 K) S9.isU3eight ∧ Nat.card B = 3 ^ 5) := by
  obtain ⟨-, -, hDcard, -, -, hKcomp, -⟩ := h.cfg.std
  have hbig : 3 ^ 4 ≤ Nat.card B := h.cfg.big
  rcases catalogIs_tyF hty with hL | hU
  · obtain ⟨F, _, _, _, hpF, ⟨θ⟩⟩ := SF.exists_psl_model hKcomp.2.2 hL
    obtain ⟨X, hX, hBX, hnl⟩ := SF.exists_aut_nl h θ
    have hX9 := SF.card_le_of_nl_linear le_rfl Nat.prime_three (by norm_num) hpF hX hnl
    rw [hDcard] at hBX
    norm_num at hX9 hBX hbig ⊢
    omega
  · obtain ⟨m, F, _, hFd, hpm, -, hq, ⟨θ⟩⟩ := SF.exists_psu_model hKcomp.2.2 hU
    obtain ⟨X, hX, hBX, hnl⟩ := SF.exists_aut_nl h θ
    obtain ⟨h27, h9⟩ := card_le_of_nl_unitary_three hFd hpm (fun h' => hq (by rw [h'])) hX hnl
    by_cases h8 : 2 ^ m = 8
    · have hm : m = 3 := Nat.pow_right_injective le_rfl (h8.trans (by norm_num) : 2 ^ m = 2 ^ 3)
      subst hm
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.cfg.elem.isPGroup
      have hle : Nat.card B ≤ 3 ^ 5 := by
        rw [hBX, hDcard]
        norm_num
        omega
      rw [hk] at hbig hle
      have h4k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hbig
      have hk5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
      rcases (by omega : k = 4 ∨ k = 5) with rfl | rfl
      · exact Or.inl hk
      refine Or.inr ⟨?_, hk⟩
      haveI := hFd.finite
      haveI := nontrivial_of_tyFUni hU
      obtain ⟨ψ⟩ := SF.nonempty_centerQuot_equiv_pSimple (p := 3) hKcomp.2.2
      have hF : Nat.card F = 64 := hFd.card.trans (by norm_num)
      exact CFSG.LocalAnalysis.GLTheoremA.CatB.U48.catalogIs_u3eight_of_statedProj hF
        (ψ.symm.trans (θ.trans (CFSG.StandardType.InndiagSU.projEquiv hFd (d := 3)
          (by norm_num)).symm))
    · left
      have hX9 := h9 h8
      rw [hDcard] at hBX
      norm_num at hBX hbig ⊢
      omega

end CFSG.LocalAnalysis.GLTheoremA.S265.SG

end
