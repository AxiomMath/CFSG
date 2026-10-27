module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRootTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm epsAct)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (rootVec posRoots negRoots
  mem_negRoots simpleRefl simpleRefl_mem simpleRefl_mul_self simpleSnd inl_ne_simpleSnd
  simpleRootVec simpleRootVec_mem_posRoots rootVec_simpleSnd neg_rootVec epsAct_neg
  epsAct_epsAct_inv IsSpReducedWord signed_descents)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

variable (ε) in
@[expose] noncomputable def uWeylRep (h : UnitaryFieldData p f K) (k : Fin r) (c : K)
    (hc : c ∈ h.traceZero) : hypSU h r ε :=
  if hk : (k : ℕ) + 1 < r then uWeylRepShort ε h k hk else uWeylRepLong ε h k c hc

theorem weylPerm_mul (σ τ : Equiv.Perm (Fin r ⊕ Fin r)) :
    weylPerm (ε := ε) (σ * τ) = weylPerm σ * weylPerm τ := by
  ext x
  rcases x with i | l | i
  · simp only [Equiv.Perm.mul_apply, weylPerm_inl, weylPerm_lineCoord]
  · rfl
  · simp only [Equiv.Perm.mul_apply, weylPerm_inr_inr, weylPerm_lineCoord]

variable {h : UnitaryFieldData p f K}

theorem isLinePerm_uWeylRep {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (k : Fin r) :
    IsLinePerm (weylPerm (ε := ε) (simpleRefl r k))
      (((uWeylRep ε h k c hc : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  unfold uWeylRep
  split_ifs with hk
  · exact isLinePerm_uWeylRepShort h k hk
  · rw [uWeylRepLong_eq_weylElt h hc hc0 k hk, coe_weylElt]
    exact isLinePerm_weylMat h hc0 _

theorem uWeylRep_mem_of_le {A : Subgroup (hypSU h r ε)} (k : Fin r) {c : K}
    (hc : c ∈ h.traceZero) (hpos : uRootSubgroup ε h (simpleRootVec r k) ≤ A)
    (hneg : uRootSubgroup ε h (-simpleRootVec r k) ≤ A) : uWeylRep ε h k c hc ∈ A := by
  have hmem : ∀ {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (t : uRootDom h a b),
      uRootElt (ε := ε) h hab t ∈ uRootSubgroup ε h (rootVec a b) := fun hab t => by
    rw [uRootSubgroup_eq_range h hab]
    exact ⟨Multiplicative.ofAdd t, rfl⟩
  unfold uWeylRep
  split_ifs with hk
  · unfold uWeylRepShort
    refine mul_mem (mul_mem (hpos ?_) (hneg ?_)) (hpos ?_)
    · rw [← rootVec_simpleSnd]
      exact hmem _ _
    · rw [← rootVec_simpleSnd, neg_rootVec]
      exact hmem _ _
    · rw [← rootVec_simpleSnd]
      exact hmem _ _
  · have hsnd : simpleSnd k = .inr k := by
      unfold simpleSnd
      rw [dite_eq_right hk]
    have hα : rootVec (Sum.inl k) (Sum.inr k) = simpleRootVec r k := by
      rw [← hsnd]
      exact rootVec_simpleSnd k
    unfold uWeylRepLong
    refine mul_mem (mul_mem (hpos ?_) (hneg ?_)) (hpos ?_)
    · rw [← hα]
      exact hmem _ _
    · rw [← hα, neg_rootVec]
      exact hmem _ _
    · rw [← hα]
      exact hmem _ _

theorem uWeylRep_mem_and_map_le {A : Subgroup (hypSU h r ε)} {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) {w : Equiv.Perm (Fin r ⊕ Fin r)} (hw : w ∈ hypWeyl r)
    (hB : hypBorel h r ε ≤ A)
    (hwA : (hypBorel h r ε).map (MulAut.conj (weylElt h hc hc0 hw)).toMonoidHom ≤ A)
    {k : Fin r} (hk : epsAct w⁻¹ (simpleRootVec r k) ∈ negRoots r) :
    uWeylRep ε h k c hc ∈ A ∧
      (hypBorel h r ε).map (MulAut.conj (weylElt h hc hc0
        (mul_mem (simpleRefl_mem k) hw))).toMonoidHom ≤ A := by
  have hdot : IsLinePerm (weylPerm (ε := ε) w)
      (((weylElt (ε := ε) h hc hc0 hw : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_weylElt]
    exact isLinePerm_weylMat h hc0 w
  have hβ : -epsAct w⁻¹ (simpleRootVec r k) ∈ posRoots r := mem_negRoots.mp hk
  have hneg : uRootSubgroup ε h (-simpleRootVec r k) ≤ A := by
    have h1 := map_conj_uRootSubgroup hw _ hdot (-epsAct w⁻¹ (simpleRootVec r k))
    rw [epsAct_neg, epsAct_epsAct_inv hw] at h1
    rw [← h1]
    exact (Subgroup.map_mono (uRootSubgroup_le_hypBorel h hβ)).trans hwA
  have hpos : uRootSubgroup ε h (simpleRootVec r k) ≤ A :=
    (uRootSubgroup_le_hypBorel h (simpleRootVec_mem_posRoots k)).trans hB
  have hnk : uWeylRep ε h k c hc ∈ A := uWeylRep_mem_of_le k hc hpos hneg
  refine ⟨hnk, ?_⟩
  have hsinv : (weylPerm (ε := ε) (simpleRefl r k))⁻¹ = weylPerm (simpleRefl r k) :=
    inv_eq_of_mul_eq_one_left (by rw [← weylPerm_mul, simpleRefl_mul_self, weylPerm_one])
  have hmono : IsLinePerm (weylPerm (ε := ε) (simpleRefl r k * w))
      ((((uWeylRep ε h k c hc)⁻¹ * weylElt h hc hc0 hw : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    have := (isLinePerm_uWeylRep hc hc0 k).inv.mul hdot
    rw [hsinv, ← weylPerm_mul] at this
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    exact this
  obtain ⟨t, ht, hteq⟩ := exists_torus_of_isLinePerm hc hc0 (mul_mem (simpleRefl_mem k) hw) hmono
  have htB : t ∈ hypBorel h r ε := hypTorus_le_hypBorel h ht
  rintro _ ⟨b, hb, rfl⟩
  have hv : weylElt h hc hc0 (mul_mem (simpleRefl_mem k) hw) =
      (uWeylRep ε h k c hc)⁻¹ * weylElt h hc hc0 hw * t⁻¹ := by
    rw [hteq, mul_inv_cancel_right]
  change weylElt h hc hc0 (mul_mem (simpleRefl_mem k) hw) * b *
    (weylElt h hc hc0 (mul_mem (simpleRefl_mem k) hw))⁻¹ ∈ A
  have hmid : weylElt h hc hc0 hw * (t⁻¹ * b * t) * (weylElt h hc hc0 hw)⁻¹ ∈ A :=
    hwA ⟨t⁻¹ * b * t, mul_mem (mul_mem (inv_mem htB) hb) htB, rfl⟩
  have : weylElt h hc hc0 (mul_mem (simpleRefl_mem k) hw) * b *
      (weylElt h hc hc0 (mul_mem (simpleRefl_mem k) hw))⁻¹ =
      (uWeylRep ε h k c hc)⁻¹ * (weylElt h hc hc0 hw * (t⁻¹ * b * t) *
        (weylElt h hc hc0 hw)⁻¹) * uWeylRep ε h k c hc := by
    rw [hv]
    group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hnk) hmid) hnk

theorem unitary_reduced_word_extraction (h : UnitaryFieldData p f K) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε))
    (hB : hypBorel h r ε ≤ A) :
    ∀ (l : List (Fin r)) (w : Equiv.Perm (Fin r ⊕ Fin r)) (hw : w ∈ hypWeyl r),
      (hypBorel h r ε).map (MulAut.conj (weylElt h hc hc0 hw)).toMonoidHom ≤ A →
      IsSpReducedWord w l → ∀ k ∈ l, uWeylRep ε h k c hc ∈ A := by
  intro l
  induction l with
  | nil => intro _ _ _ _ k hk; exact absurd hk List.not_mem_nil
  | cons k l ih =>
    intro w hw hwA hl k' hk'
    obtain ⟨hdesc, hred⟩ := (signed_descents hw).2.2 k l hl
    obtain ⟨hnk, hv⟩ := uWeylRep_mem_and_map_le hc hc0 hw hB hwA hdesc
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hnk
    · exact ih _ (mul_mem (simpleRefl_mem k) hw) hv hred k' hk'

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
