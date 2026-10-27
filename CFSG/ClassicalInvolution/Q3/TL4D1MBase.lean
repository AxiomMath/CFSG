module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Wr

variable {n : ℕ}

noncomputable def permBar (n : ℕ) : AEQ n →* Equiv.Perm (Fin n) :=
  QuotientGroup.lift (piSub n) (permHom n) (by
    rintro a (rfl | rfl)
    · rfl
    · rfl)

theorem permBar_mkQ (a : Wr n) : permBar n (mkQ n a) = a.perm :=
  QuotientGroup.lift_mk _ _ a

theorem ofVec_mul_ofVec (u v : Fin n → ZMod 2) : ofVec u * ofVec v = ofVec (u + v) :=
  Wr.ext (funext fun _ => rfl) (mul_one _)

theorem eq_ofVec_mul_ofPerm (a : Wr n) : a = ofVec a.vec * ofPerm a.perm :=
  Wr.ext (funext fun i => by show a.vec i = a.vec i + 0; rw [add_zero]) (one_mul _).symm

theorem conj_ofVec (a : Wr n) (u : Fin n → ZMod 2) :
    a * ofVec u * a⁻¹ = ofVec (fun i => u (a.perm.symm i)) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, inv_vec]
    show a.vec i + u (a.perm.symm i) + a.vec (a.perm ((a.perm * 1).symm i)) = u (a.perm.symm i)
    rw [mul_one, Equiv.apply_symm_apply, add_comm (a.vec i), add_assoc, zmod_two_add_self,
      add_zero]
  · show a.perm * 1 * a.perm⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem wsum_ofVec (u : Fin n → ZMod 2) : wsum (ofVec u) = ∑ i, u i := rfl

theorem ofVec_mem_aeSubOver {P : Subgroup (Equiv.Perm (Fin n))} {u : Fin n → ZMod 2}
    (hu : ∑ i, u i = 0) : ofVec u ∈ aeSubOver P :=
  ⟨⟨hu, by rw [show (ofVec u).perm = 1 from rfl, Equiv.Perm.sign_one]⟩, P.one_mem⟩

@[expose] def pairVec (j k : Fin n) : Fin n → ZMod 2 := Pi.single j 1 + Pi.single k 1

theorem mem_of_pairVec {H : Subgroup (AEQ n)}
    (hH : ∀ j k : Fin n, j ≠ k → mkQ n (ofVec (pairVec j k)) ∈ H) {u : Fin n → ZMod 2}
    (hu : ∑ i, u i = 0) : mkQ n (ofVec u) ∈ H := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : u = 0 := funext fun i => i.elim0
    rw [this, show ofVec (0 : Fin 0 → ZMod 2) = 1 from rfl, map_one]
    exact H.one_mem
  set o : Fin n := ⟨0, hn⟩
  have hterm : ∀ i : Fin n, mkQ n (ofVec (u i • pairVec i o)) ∈ H := by
    intro i
    by_cases hio : i = o
    · have : u i • pairVec i o = 0 := by
        rw [hio, pairVec]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul, zmod_two_add_self,
          mul_zero]
      rw [this, show ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]
      exact H.one_mem
    · have hu2 : u i = 0 ∨ u i = 1 := by
        generalize u i = x
        revert x
        decide
      rcases hu2 with h0 | h1
      · rw [h0, zero_smul, show ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]
        exact H.one_mem
      · rw [h1, one_smul]
        exact hH i o hio
  have hfin : ∀ s : Finset (Fin n), mkQ n (ofVec (∑ i ∈ s, u i • pairVec i o)) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, show ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one]
      exact H.one_mem
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, ← ofVec_mul_ofVec, map_mul]
      exact H.mul_mem (hterm i) ih
  have hsum : ∑ i, u i • pairVec i o = u := by
    funext x
    have h1 : ∑ i, u i * (Pi.single i 1 : Fin n → ZMod 2) x = u x := by
      rw [Finset.sum_eq_single x (fun b _ hb => by rw [Pi.single_eq_of_ne hb.symm, mul_zero])
        (fun h => absurd (Finset.mem_univ x) h), Pi.single_eq_same, mul_one]
    have h2 : ∑ i, u i * (Pi.single o 1 : Fin n → ZMod 2) x = 0 := by
      rw [← Finset.sum_mul, hu, zero_mul]
    simp only [Finset.sum_apply, Pi.smul_apply, pairVec, Pi.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, h1, h2, add_zero]
  have := hfin Finset.univ
  rwa [hsum] at this

end CFSG.ClassicalInvolution.Q3.TL4
