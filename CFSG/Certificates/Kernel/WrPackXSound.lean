module

public import Certificates.Data.Kernel.WrPackX
public import CFSG.Certificates.Kernel.WrPackSound

public section

namespace CFSG.KC.WrPackX

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n e pp : Nat}

theorem ofVec_inv (v : Fin n → ZMod 2) : (ofVec v : Wr n)⁻¹ = ofVec v := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rfl
  · change (1 : Equiv.Perm (Fin n))⁻¹ = 1
    exact inv_one

theorem enc_inv_lvl (hn : n ≤ 8) (a : Wr n) :
    pm n (lvl a.perm).2 (enc (ofVec a.vec)) = enc a⁻¹ := by
  rw [lvl_snd, pm_enc hn]
  congr 1
  conv_rhs => rw [← ofVec_mul_ofPerm a]
  rw [mul_inv_rev, ofVec_inv]

theorem allPF_sound (hn : n ≤ 8) {P : List (Nat × Nat)} {V : List Nat} {g : Nat → Bool}
    {f : Nat → Nat → Bool} (h : allPF n P V g f = true) (a : Wr n) (hP : lvl a.perm ∈ P)
    (hV : enc (ofVec a.vec) ∈ V) (hg : g (enc (ofPerm a.perm)) = false) :
    f (enc a) (enc a⁻¹) = true := by
  have h1 := List.all_eq_true.1 h _ hP
  have hg' : g (lvl a.perm).1 = false := hg
  rw [hg', Bool.false_or] at h1
  have h2 := List.all_eq_true.1 h1 _ hV
  simp only [strictB_eq] at h2
  rw [enc_inv_lvl hn] at h2
  have h3 : pm n (enc (ofVec a.vec)) (lvl a.perm).1 = enc a := pm_lvl hn a
  rw [h3] at h2
  exact h2

theorem okW_sound (hn : n ≤ 8) {P : List (Nat × Nat)} {V : List Nat} {w : (Nat × Nat) × Nat}
    {Q : Equiv.Perm (Fin n) → Prop} {R : (Fin n → ZMod 2) → Prop}
    (hP : ∀ t ∈ P, ∃ σ, Q σ ∧ t = lvl σ) (hV : ∀ v ∈ V, ∃ x, R x ∧ v = enc (ofVec x))
    (h : okW P V w = true) :
    ∃ σ x, Q σ ∧ R x ∧ wx n w = enc (ofVec x * ofPerm σ) ∧
      wxi n w = enc (ofVec x * ofPerm σ)⁻¹ := by
  simp only [okW, Bool.and_eq_true, List.any_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨t, ht, h1, h2⟩, ⟨v, hv, h3⟩⟩ := h
  obtain ⟨σ, hσ, rfl⟩ := hP t ht
  obtain ⟨x, hx, rfl⟩ := hV v hv
  refine ⟨σ, x, hσ, hx, ?_, ?_⟩
  · rw [wx, ← h1, h3, lvl_fst, pm_enc hn]
  · rw [wxi, ← h2, h3, lvl_snd, pm_enc hn, mul_inv_rev, ofVec_inv]

theorem any_beq_or (B : List Nat) (p q : Nat → Bool) :
    B.any (fun y => p y || q y) = (B.any p || B.any q) := by
  induction B with
  | nil => rfl
  | cons y B ih =>
    simp only [List.any_cons, ih]
    cases p y <;> cases q y <;> cases B.any p <;> cases B.any q <;> rfl

theorem any_dbl (B : List Nat) (x : Nat) :
    (dbl n pp B).any (Nat.beq x) = B.any (eqPiP n pp x) := by
  unfold dbl eqPiP
  rw [List.any_append, List.any_map, any_beq_or]
  rfl

theorem pw_enc (hn : n ≤ 8) (he : enc (1 : Wr n) = e) (x : Wr n) :
    ∀ k : Nat, pw n e k (enc x) = enc (x ^ k)
  | 0 => by rw [pow_zero, ← he]; rfl
  | k + 1 => by
    change pm n (pw n e k (enc x)) (enc x) = _
    rw [pw_enc hn he x k, pm_enc hn, pow_succ]

theorem inv_of_perm_one (x : Wr n) (h : x.perm = 1) : x⁻¹ = x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [inv_vec, h]
    rfl
  · rw [inv_perm, h, inv_one]

theorem comm_of_perm_one (x y : Wr n) (hx : x.perm = 1) (hy : y.perm = 1) : x * y = y * x := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [mul_vec, mul_vec, hx, hy]
    exact add_comm _ _
  · rw [mul_perm, mul_perm, hx, hy]

theorem conj_perm_only (c z : Wr n) (hz : z.perm = 1) :
    c * z * c⁻¹ = ofPerm c.perm * z * (ofPerm c.perm)⁻¹ := by
  have hy : (ofPerm c.perm * z * (ofPerm c.perm)⁻¹).perm = 1 := by
    rw [mul_perm, mul_perm, inv_perm, hz, mul_one]
    exact mul_inv_cancel _
  have hv : (ofVec c.vec : Wr n).perm = 1 := rfl
  conv_lhs => rw [← ofVec_mul_ofPerm c]
  calc ofVec c.vec * ofPerm c.perm * z * (ofVec c.vec * ofPerm c.perm)⁻¹ =
        ofVec c.vec * (ofPerm c.perm * z * (ofPerm c.perm)⁻¹) * (ofVec c.vec)⁻¹ := by group
    _ = ofPerm c.perm * z * (ofPerm c.perm)⁻¹ := by
        rw [comm_of_perm_one _ _ hv hy, mul_inv_cancel_right]

theorem eqPi_symm (x y : Wr n) : eqPi x y = eqPi y x := by
  refine Bool.eq_iff_iff.2 ?_
  rw [eqPi_iff', eqPi_iff']
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h, mul_assoc, allOnes_mul_self n, mul_one])
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h, mul_assoc, allOnes_mul_self n, mul_one])

theorem inPi_of_eqPi_one {x : Wr n} (h : eqPi x 1 = true) : inPi x = true := by
  unfold eqPi at h
  unfold inPi
  rw [one_mul] at h
  exact h

theorem mem_dbl_of_eqPi {B : List (Wr n)} {x y : Wr n}
    (hy : y ∈ B ++ B.map (· * allOnes n)) (h : eqPi x y = true) :
    x ∈ B ++ B.map (· * allOnes n) := by
  rcases eqPi_iff'.1 h with rfl | h
  · exact hy
  · have hx : x = y * allOnes n := by rw [← h, mul_assoc, allOnes_mul_self n, mul_one]
    rw [hx]
    rcases List.mem_append.1 hy with hy | hy
    · exact List.mem_append.2 (Or.inr (List.mem_map_of_mem hy))
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      rw [mul_assoc, allOnes_mul_self n, mul_one]
      exact List.mem_append.2 (Or.inl hb)

theorem dbl_enc (hn : n ≤ 8) (hp : enc (allOnes n) = pp) (B : List (Wr n)) :
    dbl n pp (B.map enc) = (B ++ B.map (· * allOnes n)).map enc := by
  unfold dbl
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, ← hp, pm_enc hn]

end CFSG.KC.WrPackX

end
