module

public import CFSG.ClassicalInvolution.Q3.TL3T32

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr

theorem mem_closure_threeCycle_fix {α : Type} [Fintype α] [DecidableEq α] (a : α)
    {σ : Equiv.Perm α} (hσ : σ ∈ alternatingGroup α) (ha : σ a = a) :
    σ ∈ Subgroup.closure {τ : Equiv.Perm α | τ.IsThreeCycle ∧ τ a = a} := by
  have h₁ : ∀ x, (σ x ≠ a) ↔ (x ≠ a) := fun x => by
    constructor
    · intro h hx
      exact h (by rw [hx, ha])
    · intro h hx
      exact h (σ.injective (hx.trans ha.symm))
  have h₂ : ∀ x, σ x ≠ x → x ≠ a := fun x hx h => hx (by rw [h, ha])
  set τ := σ.subtypePerm (p := fun x => x ≠ a) h₁ with hτ
  have hτσ : Equiv.Perm.ofSubtype τ = σ := Equiv.Perm.ofSubtype_subtypePerm h₁ h₂
  have hτA : τ ∈ alternatingGroup {x // x ≠ a} := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hτσ]
    exact Equiv.Perm.mem_alternatingGroup.mp hσ
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hτA
  rw [← hτσ]
  have hle : (Subgroup.closure {τ : Equiv.Perm {x // x ≠ a} | τ.IsThreeCycle}).map
      Equiv.Perm.ofSubtype ≤ Subgroup.closure {τ : Equiv.Perm α | τ.IsThreeCycle ∧ τ a = a} := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨ρ, hρ, rfl⟩
    refine Subgroup.subset_closure ⟨?_, Equiv.Perm.ofSubtype_apply_of_not_mem ρ (by simp)⟩
    rw [← _root_.card_support_eq_three_iff, Equiv.Perm.support_ofSubtype, Finset.card_map]
    exact hρ.card_support
  exact hle ⟨τ, hτA, rfl⟩

variable {n : ℕ}

theorem ofVec_add (v w : Fin n → ZMod 2) : ofVec (v + w) = ofVec v * ofVec w :=
  Wr.ext rfl (mul_one 1).symm

theorem ofVec_zero : ofVec (0 : Fin n → ZMod 2) = 1 := rfl

theorem ofVec_pow (v : Fin n → ZMod 2) (m : ℕ) : ofVec v ^ m = ofVec (m • v) := by
  induction m with
  | zero => rw [pow_zero, zero_smul, ofVec_zero]
  | succ m ih => rw [pow_succ, ih, ← ofVec_add, succ_nsmul]

theorem mkQ_ofVec_pow (v : Fin n → ZMod 2) (m : ℕ) :
    mkQ n (ofVec v) ^ m = mkQ n (ofVec (m • v)) := by
  rw [← map_pow, ofVec_pow]

theorem conj_ofVec_wr (w : Wr n) (v : Fin n → ZMod 2) :
    w * ofVec v * w⁻¹ = ofVec fun i => v (w.perm.symm i) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (w.vec i + v (w.perm.symm i)) + w.vec (w.perm ((w.perm * 1).symm i)) =
      v (w.perm.symm i)
    rw [mul_one, Equiv.apply_symm_apply, add_comm (w.vec i), add_assoc, zmod_two_add_self,
      add_zero]
  · show w.perm * 1 * w.perm⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

@[expose] noncomputable def ePt (n : ℕ) (p : Fin n) : AEQ n := mkQ n (ofVec (Pi.single p 1))

theorem ePt_mem_aeModel (hn : Odd n) (p : Fin n) : ePt n p ∈ TL4.aeModel n := by
  have e : ePt n p = mkQ n (ofVec (Pi.single p 1) * allOnes n) := by
    rw [map_mul, show mkQ n (allOnes n) = 1 from (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl),
      mul_one]
    rfl
  rw [e]
  refine ⟨_, ⟨?_, ?_⟩, rfl⟩
  · show ∑ i, ((Pi.single p 1 : Fin n → ZMod 2) i +
      (allOnes n).vec ((1 : Equiv.Perm (Fin n)).symm i)) = 0
    simp only [allOnes, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    obtain ⟨j, rfl⟩ := hn
    push_cast
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring
  · show Equiv.Perm.sign ((1 : Equiv.Perm (Fin n)) * 1) = 1
    rw [mul_one, Equiv.Perm.sign_one]

theorem conj_ePt (g : AEQ n) (p : Fin n) : g * ePt n p * g⁻¹ = ePt n (permQ n g p) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
  show mkQ n w * mkQ n (ofVec (Pi.single p 1)) * (mkQ n w)⁻¹ = ePt n (permQ n (mkQ n w) p)
  rw [← map_inv, ← map_mul, ← map_mul, conj_ofVec_wr, permQ_mkQ, ePt]
  congr 2
  funext i
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

theorem eq_zero_of_mkQ_ofVec_eq_one (hn : Odd n) {v : Fin n → ZMod 2} (hv : ∑ i, v i = 0)
    (h : mkQ n (ofVec v) = 1) : v = 0 := by
  have h' : ofVec v ∈ piSub n := (QuotientGroup.eq_one_iff (N := piSub n) (ofVec v)).mp h
  rcases mem_piSub.mp h' with h1 | h1
  · exact congrArg Wr.vec h1
  · exfalso
    have hv1 : v = fun _ => 1 := congrArg Wr.vec h1
    rw [hv1, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hv
    obtain ⟨j, rfl⟩ := hn
    simp only [nsmul_eq_mul, mul_one] at hv
    push_cast at hv
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add] at hv
    exact one_ne_zero hv

end CFSG.ClassicalInvolution.Q3.TL4.AECov
