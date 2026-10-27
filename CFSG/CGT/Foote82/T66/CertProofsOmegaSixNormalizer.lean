module

public import CFSG.CGT.Foote82.T66.CitedBB
public import CFSG.CGT.Foote82.T66.OmegaSixModel
public import Certificates.Certificate919003
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem transCheck_holds : transCheck () = true :=
  Certificates.certificate919003.1

theorem countCheck_holds : countCheck () = true :=
  Certificates.certificate919003.2

theorem exists_mem_mulVec_eq
    {v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2} (hv : q6 v = 1) :
    ∃ x ∈ omegaMinusTwo 2,
      (x : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ cvec v0 = v := by
  have h := transCheck_holds
  unfold transCheck at h
  have h' := List.all_eq_true.mp h (vcode v) (List.mem_range.mpr (vcode_lt v))
  rw [cvec_vcode, hv] at h'
  simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Array.any_eq_true, beq_iff_eq] at h'
  obtain ⟨i, hi, hti⟩ := h'
  obtain ⟨x, hx⟩ := exists_glArr_eq hi
  refine ⟨x, x.2, ?_⟩
  have h1 : (marr ((x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)))[v0]! = vcode v := by
    rw [show marr ((x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = glArr x from rfl, hx,
      getElem!_pos _ i hi]
    exact hti
  rw [mulVec_cvec _ (by decide : v0 < 64), h1, cvec_vcode]

end CFSG.CGT.Foote82.OmegaSix

namespace CFSG.CGT.Foote82

open Matrix OmegaSix

theorem omegaMinusSixNormalizer_holds :
    OmegaMinusSixNormalizer := by
  intro T hT hnorm
  have hTT : ∀ v, (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) = v := by
    intro v
    rw [mulVec_mulVec, ← Units.val_mul, hT, Units.val_one, one_mulVec]
  have hinj : Set.InjOn (fun v => (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (ZMod 2)) *ᵥ v) Set.univ := fun v _ w _ h => by
    have := congrArg (fun u => (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (ZMod 2)) *ᵥ u) h
    simpa only [hTT] using this
  have hNT : ∀ v, q6 v = 1 →
      q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
          cvec v0) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := exists_mem_mulVec_eq hv
    rw [← conj_mulVec,
      q6_mulVec_of_mem (omegaMinusTwo_le_orthogonalMinus (hnorm x hx))]
  have hcount := countCheck_holds
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq] at hcount
  obtain ⟨hN, hZ⟩ := hcount
  have hz2 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  have hTv0 : q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      cvec v0) = 1 := by
    by_contra hne
    have h0 := hz2 _ hne
    have hle := Finset.card_le_card_of_injOn
      (s := Finset.univ.filter fun v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 => q6 v = 1)
      (t := Finset.univ.filter fun v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 => v ≠ 0 ∧ q6 v = 0)
      (fun v => (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v)
      (fun v hv => by
        have hv' : q6 v = 1 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · show (T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v ≠ 0
          intro h
          have h1 := hTT v
          rw [h, mulVec_zero] at h1
          rw [← h1] at hv'
          exact absurd hv' (by decide)
        · show q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v) = 0
          rw [hNT v hv', h0])
      (fun v _ w _ h => hinj (Set.mem_univ v) (Set.mem_univ w) h)
    rw [hN, hZ] at hle
    omega
  have hQ : ∀ v, q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
      v) = q6 v := by
    intro v
    by_cases hv : q6 v = 1
    · rw [hNT v hv, hTv0, hv]
    · rw [hz2 _ hv]
      by_contra hne
      have hTv : q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ
          v) = 1 := by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (q6 ((T : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
          (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v)) with h | h
        · exact absurd h hne
        · exact h
      have h1 := hNT _ hTv
      rw [hTT, hTv0] at h1
      exact hv h1
  apply Subgroup.subset_closure
  intro v
  rw [← q6_eq, ← q6_eq]
  exact hQ v

end CFSG.CGT.Foote82
