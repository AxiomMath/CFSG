module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eComb
public import CFSG.ClassicalInvolution.Q3.TL3T32

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open Finset

theorem ind_symmDiff (S T : Finset (Fin 8)) (z : Fin 8) :
    ind (symmDiff S T) z = ind S z + ind T z := by
  unfold ind
  by_cases hS : z ∈ S <;> by_cases hT : z ∈ T <;> simp [hS, hT, Finset.mem_symmDiff] <;> decide

theorem ind_univ (z : Fin 8) : ind Finset.univ z = 1 := by
  simp [ind]

theorem ind_empty (z : Fin 8) : ind (∅ : Finset (Fin 8)) z = 0 := by
  simp [ind]

theorem ofVec_mul' (v w : Fin 8 → ZMod 2) : ofVec v * ofVec w = ofVec (v + w) :=
  Wr.ext (funext fun _ => rfl) rfl

theorem ofVec_mul_self (v : Fin 8 → ZMod 2) : ofVec v * ofVec v = 1 := by
  rw [ofVec_mul']
  refine Wr.ext (funext fun z => ?_) rfl
  exact zmod_two_add_self (v z)

@[expose] def vq (S : Finset (Fin 8)) : AEQ 8 := mkQ 8 (ofVec (ind S))

theorem vq_mul (S T : Finset (Fin 8)) : vq S * vq T = vq (symmDiff S T) := by
  unfold vq
  rw [← map_mul, ofVec_mul']
  congr 2
  funext z
  exact (ind_symmDiff S T z).symm

theorem vq_mul_self (S : Finset (Fin 8)) : vq S * vq S = 1 := by
  unfold vq
  rw [← map_mul, ofVec_mul_self, map_one]

theorem vq_inv (S : Finset (Fin 8)) : (vq S)⁻¹ = vq S :=
  inv_eq_of_mul_eq_one_right (vq_mul_self S)

theorem vq_empty : vq (∅ : Finset (Fin 8)) = 1 := by
  unfold vq
  have : (ofVec (ind (∅ : Finset (Fin 8))) : Wr 8) = 1 :=
    Wr.ext (funext fun z => ind_empty z) rfl
  rw [this, map_one]

theorem vq_univ : vq (Finset.univ : Finset (Fin 8)) = 1 := by
  unfold vq
  have : (ofVec (ind (Finset.univ : Finset (Fin 8))) : Wr 8) = allOnes 8 :=
    Wr.ext (funext fun z => ind_univ z) rfl
  rw [this]
  exact (QuotientGroup.eq_one_iff _).2 (Or.inr rfl)

theorem vq_compl (S : Finset (Fin 8)) : vq Sᶜ = vq S := by
  have h : Sᶜ = symmDiff S Finset.univ := by
    rw [symmDiff_comm]
    ext z
    simp [Finset.mem_symmDiff]
  rw [h, ← vq_mul, vq_univ, mul_one]

theorem permQ_vq (S : Finset (Fin 8)) : permQ 8 (vq S) = 1 := rfl

theorem vq_eq_iff {S T : Finset (Fin 8)} : vq S = vq T ↔ T = S ∨ T = Sᶜ := by
  constructor
  · intro h
    unfold vq at h
    have hinv : (ofVec (ind S))⁻¹ = ofVec (ind S) :=
      inv_eq_of_mul_eq_one_right (ofVec_mul_self _)
    rcases mkQ_eq_iff.mp h with h1 | h1
    · left
      rw [hinv, ofVec_mul'] at h1
      have h2 : ∀ z, ind S z + ind T z = 0 := fun z => by
        have := congrFun (congrArg Wr.vec h1) z
        exact this
      ext z
      have := h2 z
      unfold ind at this
      by_cases hS : z ∈ S <;> by_cases hT : z ∈ T <;> simp_all <;> revert this <;> decide
    · right
      rw [hinv, ofVec_mul'] at h1
      have h2 : ∀ z, ind S z + ind T z = 1 := fun z => by
        have := congrFun (congrArg Wr.vec h1) z
        exact this
      ext z
      have := h2 z
      unfold ind at this
      by_cases hS : z ∈ S <;> by_cases hT : z ∈ T <;> simp_all <;> revert this <;> decide
  · rintro (rfl | rfl)
    · rfl
    · exact (vq_compl S).symm

theorem conj_vq (g : AEQ 8) (S : Finset (Fin 8)) :
    g * vq S * g⁻¹ = vq (S.map (permQ 8 g).toEmbedding) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  have e : (QuotientGroup.mk a : AEQ 8) = mkQ 8 a := rfl
  rw [e]
  unfold vq
  rw [← map_inv, ← map_mul, ← map_mul, conj_ofVec]
  congr 2
  funext z
  show ind S (a.perm.symm z) = ind (S.map (permQ 8 (mkQ 8 a)).toEmbedding) z
  unfold ind
  rw [permQ_mkQ]
  simp [Finset.mem_map_equiv]

@[expose] def aeBar8 : Subgroup (AEQ 8) := (aeSub 8).map (mkQ 8)

theorem vq_mem_aeBar8 {S : Finset (Fin 8)} (hS : Even S.card) : vq S ∈ aeBar8 := by
  refine ⟨ofVec (ind S), ⟨?_, ?_⟩, rfl⟩
  · show wsum (ofVec (ind S)) = 0
    unfold wsum ofVec ind
    simp only
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    obtain ⟨m, hm⟩ := hS
    rw [hm]
    push_cast
    exact zmod_two_add_self _
  · show Equiv.Perm.sign (1 : Equiv.Perm (Fin 8)) = 1
    exact Equiv.Perm.sign_one

theorem exists_vq_of_ker {x : AEQ 8} (hx : x ∈ aeBar8) (hp : permQ 8 x = 1) :
    ∃ S : Finset (Fin 8), Even S.card ∧ x = vq S := by
  obtain ⟨a, ha, rfl⟩ := hx
  have hperm : a.perm = 1 := hp
  have ha1 : a = ofVec a.vec := Wr.ext rfl hperm
  have hvec : ∀ z, a.vec z = 0 ∨ a.vec z = 1 := by
    intro z
    generalize a.vec z = c
    revert c
    decide
  refine ⟨Finset.univ.filter (fun z => a.vec z = 1), ?_, ?_⟩
  · have hw : wsum a = 0 := ha.1
    unfold wsum at hw
    have : ∑ z, a.vec z = ((Finset.univ.filter (fun z => a.vec z = 1)).card : ZMod 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z => a.vec z = 1)]
      have h0 : ∑ z ∈ Finset.univ.filter (fun z => ¬ a.vec z = 1), a.vec z = 0 := by
        refine Finset.sum_eq_zero fun z hz => ?_
        have := (Finset.mem_filter.mp hz).2
        exact (hvec z).resolve_right this
      rw [h0, add_zero, Finset.sum_congr rfl (fun z hz => (Finset.mem_filter.mp hz).2)]
      simp
    rw [this] at hw
    exact (ZMod.natCast_eq_zero_iff_even).mp hw
  · have hm : mkQ 8 a = mkQ 8 (ofVec a.vec) := by rw [← ha1]
    rw [hm]
    unfold vq
    congr 2
    funext z
    unfold ind
    show a.vec z = _
    rcases hvec z with h | h <;> simp [h]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
