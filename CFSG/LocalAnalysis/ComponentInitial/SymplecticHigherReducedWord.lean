module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherRootTransport

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

theorem weylRep_mem_and_map_le {A : Subgroup (StatedSp r K)} {w : signedPermGroup r}
    (hB : borelSubgroup r K ≤ A)
    (hw : (borelSubgroup r K).map (MulAut.conj (dotW K w)).toMonoidHom ≤ A) {k : Fin r}
    (hk : epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹ (simpleRootVec r k) ∈ negRoots r) :
    weylRep K k ∈ A ∧
      (borelSubgroup r K).map (MulAut.conj (dotW K
        ⟨simpleRefl r k * (w : Equiv.Perm (Fin r ⊕ Fin r)),
          mul_mem (simpleRefl_mem k) w.2⟩)).toMonoidHom ≤ A := by
  have hw2 := w.2
  have hβ : -epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹ (simpleRootVec r k) ∈ posRoots r :=
    mem_negRoots.mp hk
  have hneg : rootSubgroup K (-simpleRootVec r k) ≤ A := by
    have h1 := (root_transport (K := K)).1 w (-epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹
      (simpleRootVec r k))
    rw [epsAct_neg, epsAct_epsAct_inv hw2] at h1
    rw [← h1]
    exact (Subgroup.map_mono (rootSubgroup_le_borelSubgroup hβ)).trans hw
  have hpos : rootSubgroup K (simpleRootVec r k) ≤ A :=
    (rootSubgroup_le_borelSubgroup (simpleRootVec_mem_posRoots k)).trans hB
  have hnk : weylRep K k ∈ A := weylRep_mem_of_rootSubgroup_le k hpos hneg
  refine ⟨hnk, ?_⟩
  set v : signedPermGroup r :=
    ⟨simpleRefl r k * (w : Equiv.Perm (Fin r ⊕ Fin r)), mul_mem (simpleRefl_mem k) w.2⟩
  have hmono : IsLinePerm (v : Equiv.Perm (Fin r ⊕ Fin r))
      ((((weylRep K k)⁻¹ * dotW K w : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have := (isLinePerm_weylRep (K := K) k).inv.mul (isLinePerm_dotW (K := K) w)
    rw [simpleRefl_inv] at this
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    exact this
  obtain ⟨t, ht, hteq⟩ := exists_torus_of_isLinePerm hmono
  have htB : t ∈ borelSubgroup r K := torus_le_borelSubgroup ht
  rintro _ ⟨b, hb, rfl⟩
  have hv : dotW K v = (weylRep K k)⁻¹ * dotW K w * t⁻¹ := by
    rw [hteq, mul_inv_cancel_right]
  change dotW K v * b * (dotW K v)⁻¹ ∈ A
  have hmid : dotW K w * (t⁻¹ * b * t) * (dotW K w)⁻¹ ∈ A :=
    hw ⟨t⁻¹ * b * t, mul_mem (mul_mem (inv_mem htB) hb) htB, rfl⟩
  have : dotW K v * b * (dotW K v)⁻¹ =
      (weylRep K k)⁻¹ * (dotW K w * (t⁻¹ * b * t) * (dotW K w)⁻¹) * weylRep K k := by
    rw [hv]
    group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hnk) hmid) hnk

theorem reduced_word_extraction (A : Subgroup (StatedSp r K)) (hB : borelSubgroup r K ≤ A) :
    ∀ (l : List (Fin r)) (w : signedPermGroup r),
      (borelSubgroup r K).map (MulAut.conj (dotW K w)).toMonoidHom ≤ A →
      IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l → ∀ k ∈ l, weylRep K k ∈ A := by
  intro l
  induction l with
  | nil => intro _ _ _ k hk; exact absurd hk (List.not_mem_nil)
  | cons k l ih =>
    intro w hw hl k' hk'
    obtain ⟨hdesc, hred⟩ := (signed_descents w.2).2.2 k l hl
    obtain ⟨hnk, hv⟩ := weylRep_mem_and_map_le hB hw hdesc
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hnk
    · exact ih ⟨simpleRefl r k * (w : Equiv.Perm (Fin r ⊕ Fin r)),
        mul_mem (simpleRefl_mem k) w.2⟩ hv hred k' hk'

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
