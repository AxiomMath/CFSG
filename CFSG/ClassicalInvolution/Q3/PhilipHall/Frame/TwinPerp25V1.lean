module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25AE5Sq
public import Certificates.Certificate397701

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open Certificates.AE117 Certificates.AE5Sq Certificates.AE5X
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5Sq (finAll_iff mem_alphas card_of_mem_alphas ord4Pi_iff)

@[expose] def permHom : Wr 5 →* Equiv.Perm (Fin 5) where
  toFun x := x.perm
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def permQ : AEQ 5 →* Equiv.Perm (Fin 5) :=
  QuotientGroup.lift (piSub 5) permHom (by
    intro x hx
    rcases hx with rfl | rfl
    · exact permHom.map_one
    · rfl)

@[expose] def InV (x : AEQ 5) : Prop := permQ x = 1

theorem InV.conj {x : AEQ 5} (hx : InV x) (g : AEQ 5) : InV (g * x * g⁻¹) := by
  unfold InV at hx ⊢
  rw [map_mul, map_mul, map_inv, hx, mul_one, mul_inv_cancel]

theorem InV.comm {x y : AEQ 5} (hx : InV x) (hy : InV y) : x * y = y * x := by
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  have hx' : x'.perm = 1 := hx
  have hy' : y'.perm = 1 := hy
  show mkQ 5 x' * mkQ 5 y' = mkQ 5 y' * mkQ 5 x'
  rw [← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, hx', hy']
    exact add_comm _ _
  · simp only [mul_perm, hx', hy', mul_one]

theorem check_parts :
    chkCent () = true ∧ chkOdd () = true ∧ chkInv () = true ∧ chkZV () = true ∧
      ∀ p ∈ labs, ∀ q ∈ labs, twin p q = true → chkTwin p q = true := by
  have h := Certificates.certificate397701
  simp only [checkX, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun p hp q hq ht => ?_⟩
  rcases h5 p hp q hq with h | h
  · rw [ht] at h
    exact absurd h (by simp)
  · exact h

theorem mem_labs {α : Finset (Fin 5)} (h : α.card = 4) (b : Bool) : (α, b) ∈ labs := by
  have := mem_alphas α h
  cases b <;> simp [labs, List.mem_flatMap, this]

theorem spec_cent (x : AEQ 5) (h1 : x * mkQ 5 (a0 ()) = mkQ 5 (a0 ()) * x)
    (h2 : x * mkQ 5 (b0 ()) = mkQ 5 (b0 ()) * x) : x = 1 := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  have h := finAll_iff.1 check_parts.1 c (Finset.mem_univ c)
  have e1 : eqPi (c * a0 ()) (a0 () * c) = true := by
    rw [TL4.Mdl117.eqPi_iff, map_mul, map_mul]; exact h1
  have e2 : eqPi (c * b0 ()) (b0 () * c) = true := by
    rw [TL4.Mdl117.eqPi_iff, map_mul, map_mul]; exact h2
  rw [e1, e2] at h
  simpa [TL4.Mdl117.inPi_iff] using h

theorem spec_odd {α : Finset (Fin 5)} (hα : α.card = 4) (b : Bool) (c : AEQ 5)
    (hc : ∀ x ∈ memBar α hα b, c * x = x * c) (h15 : c ^ 15 = 1) : c = 1 := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  have h := finAll_iff.1 ((List.all_eq_true.1 check_parts.2.1) (α, b) (mem_labs hα b)) c (Finset.mem_univ c)
  have e1 : ((memL (α, b)).all fun m => eqPi (c * m) (m * c)) = true := by
    rw [List.all_eq_true]
    intro m hm
    rw [TL4.Mdl117.eqPi_iff, map_mul, map_mul]
    exact hc _ ((TL4.Mdl117.mem_memBar_iff α hα b _).2 ⟨m, hm, rfl⟩)
  have e2 : inPi (c ^ 15) = true := by
    rw [TL4.Mdl117.inPi_iff, map_pow]; exact h15
  rw [e1, e2] at h
  simpa [TL4.Mdl117.inPi_iff] using h

theorem spec_inv {α : Finset (Fin 5)} (hα : α.card = 4) (b : Bool) {x : AEQ 5}
    (hx : x ∈ memBar α hα b) (hx1 : x ≠ 1) (hx2 : x * x = 1) : x = mkQ 5 (zW (α, b)) := by
  obtain ⟨m, hm, rfl⟩ := (TL4.Mdl117.mem_memBar_iff α hα b x).1 hx
  have h := List.all_eq_true.1 ((List.all_eq_true.1 check_parts.2.2.1) (α, b) (mem_labs hα b)) m hm
  have e1 : inPi m = false := by
    rw [Bool.eq_false_iff, Ne, TL4.Mdl117.inPi_iff]; exact hx1
  have e2 : inPi (m * m) = true := by
    rw [TL4.Mdl117.inPi_iff, map_mul]; exact hx2
  rw [e1, e2] at h
  simpa [TL4.Mdl117.eqPi_iff] using h

theorem spec_zV {α : Finset (Fin 5)} (hα : α.card = 4) (b : Bool) : InV (mkQ 5 (zW (α, b))) := by
  have h := List.all_eq_true.1 check_parts.2.2.2.1 (α, b) (mem_labs hα b)
  have h' : (zW (α, b)).perm = 1 := by simpa [inV] using h
  exact h'

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
