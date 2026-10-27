module

public import Certificates.Data.Kernel.E64FactsK
public import CFSG.Certificates.Kernel.E64AutKSound

public section

namespace CFSG.KC.E64FactsK

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117 Certificates.E64Facts

variable {e pp : Nat}

theorem sort_eq_ptsIn (s : Finset (Fin 7)) : s.sort (· ≤ ·) = ptsIn s := by
  have hn : (ptsIn s).Nodup := (List.nodup_finRange 7).filter _
  have hp : (ptsIn s).Pairwise (· ≤ ·) := (List.pairwise_le_finRange 7).filter _
  have hs : (ptsIn s).toFinset = s := by
    ext i
    simp [ptsIn]
  conv_lhs => rw [← hs]
  exact (List.toFinset_sort (· ≤ ·) hn).2 hp

theorem memAtL_eq (α : Finset (Fin 7)) (b : Bool) : memAtL α b = memAtK α b := by
  unfold memAtL memAtK
  rw [sort_eq_ptsIn]
  rcases ptsIn α with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> rfl

theorem memS_eq (ℓ : Finset (Fin 7)) : memS ℓ = memSK ℓ := by
  unfold memS memSK
  rw [memAtL_eq, memAtL_eq]

theorem centAt_eq (ℓ : Finset (Fin 7)) : centAt ℓ = centK ℓ := by
  unfold centAt centK
  rw [sort_eq_ptsIn, sort_eq_ptsIn]
  rcases ptsIn ℓ with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

theorem beq_enc (x y : Wr 7) : Nat.beq (enc x) (enc y) = decide (x = y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
  exact ⟨enc_inj, congrArg enc⟩

theorem any_eqPi_eq (hp : enc (allOnes 7) = pp) (x : Wr 7) (B : List (Wr 7)) :
    inModPi pp (enc x) (B.map enc) = B.any (eqPi x) := by
  rw [Bool.eq_iff_iff, inModPi_iff hp, List.any_eq_true]

theorem eqPi_eq (hp : enc (allOnes 7) = pp) (x y : Wr 7) :
    inModPi pp (enc x) [enc y] = eqPi x y := by
  have := any_eqPi_eq hp x [y]
  rw [List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at this
  exact this

theorem commP_eq (hp : enc (allOnes 7) = pp) (S : List (Wr 7)) (x : Wr 7) :
    commP pp (enc x) (S.map enc) = commAll S x := by
  unfold commP commAll
  rw [List.all_map]
  refine congrArg S.all (funext fun s => ?_)
  rw [Function.comp_apply, pm_enc, pm_enc, eqPi_eq hp]

theorem distinctPi_eq (hp : enc (allOnes 7) = pp) (C : List (Wr 7)) :
    distinctPi C = decide ((C.map enc).Pairwise fun c d => inModPi pp c [d] = false) := by
  unfold distinctPi
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, List.pairwise_map]
  simp only [eqPi_eq hp]

theorem all_sq_eq (he : enc (1 : Wr 7) = e) (C : List (Wr 7)) :
    (C.all fun c => decide (c * c = 1)) = (C.map enc).all fun c => Nat.beq (pm c c) e := by
  rw [List.all_map]
  refine congrArg C.all (funext fun c => ?_)
  rw [Function.comp_apply, pm_enc, ← he, beq_enc]

theorem all_comm_eq (C : List (Wr 7)) :
    (C.all fun c => C.all fun d => decide (c * d = d * c)) =
      (C.map enc).all fun c => (C.map enc).all fun d => Nat.beq (pm c d) (pm d c) := by
  rw [List.all_map]
  refine congrArg C.all (funext fun c => ?_)
  rw [Function.comp_apply, List.all_map]
  refine congrArg C.all (funext fun d => ?_)
  rw [Function.comp_apply, pm_enc, pm_enc, beq_enc]

theorem centCOK_sound (hp : enc (allOnes 7) = pp) {P : List (Nat × Nat)} {V : List Nat}
    {S C : List (Wr 7)} (h : centCOK pp P V (S.map enc) (C.map enc) = true) (a : Wr 7)
    (hP : lvl a.perm ∈ P) (hV : enc (ofVec a.vec) ∈ V)
    (hc : ∀ s ∈ S, eqPi (a * s) (s * a) = true) : ∃ c ∈ C, eqPi a c = true := by
  have h1 := List.all_eq_true.1 h _ hP
  beta_reduce at h1
  have hA : ((S.map enc).all fun s => samePerm (pm (lvl a.perm).1 s) (pm s (lvl a.perm).1)) =
      true := by
    rw [List.all_eq_true]
    intro s0 hs0
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hs0
    rw [lvl_fst, pm_enc, pm_enc, samePerm_iff, mul_perm, mul_perm]
    have h3 : (a * s).perm = (s * a).perm := eqPi_perm' (hc s hs)
    rw [mul_perm, mul_perm] at h3
    change a.perm * s.perm = s.perm * a.perm
    exact h3
  rw [hA, Bool.not_true, Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  beta_reduce at h2
  have hB : commP pp (pm (enc (ofVec a.vec)) (lvl a.perm).1) (S.map enc) = true := by
    rw [pm_lvl, commP_eq hp]
    exact List.all_eq_true.2 hc
  rw [hB, Bool.not_true, Bool.false_or, pm_lvl, any_eqPi_eq hp, List.any_eq_true] at h2
  exact h2

end CFSG.KC.E64FactsK

end
