module

public import Certificates.Data.Kernel.Co1Seven.Forest
public import CFSG.Certificates.Kernel.Co1Three.TermSound

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B

theorem cedgeK_sound {TS E : Nat → Nat} {GN : List Nat} {c pc q : Nat}
    (h : cedgeK TS E GN c pc q = true) :
    ∃ g < GN.length, mulWK (TS (GN.getD g 0)) (E c) = mulWK (E pc) (TS (GN.getD g 0)) ∨
      mulWK (E c) (TS (GN.getD g 0)) = mulWK (TS (GN.getD g 0)) (E pc) := by
  have h' : strictB (Nat.shiftRight q 1) (fun g =>
      Bool.rec (motive := fun _ => Bool) false
        (strictB (TS (getL 0 GN g)) fun X =>
          Bool.rec (motive := fun _ => Bool)
            (Nat.beq (mulWK (E c) X) (mulWK X (E pc)))
            (Nat.beq (mulWK X (E c)) (mulWK (E pc) X))
            (Nat.beq (Nat.land q 1) 0))
        (Nat.blt g (lenL GN))) = true := h
  simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
  obtain ⟨hg, h2⟩ := h'
  rw [Nat.blt_eq, lenL_eq] at hg
  rw [getL_eq] at h2
  refine ⟨_, hg, ?_⟩
  rcases h2 with ⟨-, h3⟩ | ⟨-, h3⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h3)
  · exact Or.inr (Nat.eq_of_beq_eq_true h3)

theorem cforFromK_sound {TS E : Nat → Nat} {GN : List Nat} {N : Nat} {RT : List Nat} {DP : Nat} :
    ∀ {FT : List Nat} {c : Nat}, cforFromK TS E GN N RT DP FT c = true → ∀ c', c ≤ c' → c' < N →
      (depK DP c' = 0 ∧ c' ∈ RT) ∨
      (∃ pc < N, 0 < pc ∧ depK DP pc + 1 = depK DP c' ∧ ∃ g < GN.length,
        mulWK (TS (GN.getD g 0)) (E c') = mulWK (E pc) (TS (GN.getD g 0)) ∨
          mulWK (E c') (TS (GN.getD g 0)) = mulWK (TS (GN.getD g 0)) (E pc))
  | [], c, h, c', h1, h2 => by
    have : c = N := Nat.eq_of_beq_eq_true h
    omega
  | e :: FT, c, h, c', h1, h2 => by
    have h' : strictB c (fun c => strictB (depK DP c) fun d =>
        Bool.rec (motive := fun _ => Bool) false (cforFromK TS E GN N RT DP FT (Nat.succ c))
          (Bool.rec (motive := fun _ => Bool)
            (strictB (Nat.mod e N) fun pc =>
              Bool.rec (motive := fun _ => Bool) false
                (Bool.rec (motive := fun _ => Bool) false (cedgeK TS E GN c pc (Nat.div e N))
                  (Nat.beq (Nat.succ (depK DP pc)) d))
                (Nat.blt 0 pc))
            (memK c RT) (Nat.beq d 0))) = true := h
    simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
    obtain ⟨h3, h4⟩ := h'
    by_cases hc : c' = c
    · subst hc
      rcases h3 with ⟨h5, h6⟩ | ⟨-, h5, h6, h7⟩
      · exact Or.inl ⟨Nat.eq_of_beq_eq_true h5, memK_sound h6⟩
      · rw [Nat.blt_eq] at h5
        exact Or.inr ⟨e % N, Nat.mod_lt _ (by omega), h5, Nat.eq_of_beq_eq_true h6, cedgeK_sound h7⟩
    · exact cforFromK_sound h4 c' (by omega) h2

theorem cforK_sound {G : Type*} [Group G] (φ : G →* Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hφ : Function.Injective φ) {TS E : Nat → Nat} {GN : List Nat} {N : Nat} {RT : List Nat}
    {DP : Nat} {FT : List Nat} (h : cforK TS E GN N RT DP FT = true) (e : Nat → G)
    (he : ∀ c < N, matK (E c) = φ (e c)) (x : Nat → G)
    (hx : ∀ g < GN.length, matK (TS (GN.getD g 0)) = φ (x g)) :
    ∀ c, 1 ≤ c → c < N → ∃ r ∈ RT, r < N ∧ IsConj (e r) (e c) := by
  have h' : cforFromK TS E GN N RT DP FT 1 = true := h
  have key : ∀ d c, depK DP c = d → 1 ≤ c → c < N → ∃ r ∈ RT, r < N ∧ IsConj (e r) (e c) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro c hd h1 h2
      rcases cforFromK_sound h' c h1 h2 with ⟨-, hr⟩ | ⟨pc, hpc, hpc0, hdp, g, hg, hed⟩
      · exact ⟨c, hr, h2, IsConj.refl _⟩
      · obtain ⟨r, hr, hrN, hrc⟩ := ih (depK DP pc) (by omega) pc rfl hpc0 hpc
        refine ⟨r, hr, hrN, hrc.trans ?_⟩
        rcases hed with hed | hed
        · have hm := congrArg matK hed
          rw [matK_mulWK, matK_mulWK, he c h2, he pc hpc, hx g hg, ← map_mul, ← map_mul] at hm
          have hm' := hφ hm
          exact isConj_iff.2 ⟨(x g)⁻¹, by rw [inv_inv, mul_assoc, ← hm', inv_mul_cancel_left]⟩
        · have hm := congrArg matK hed
          rw [matK_mulWK, matK_mulWK, he c h2, he pc hpc, hx g hg, ← map_mul, ← map_mul] at hm
          have hm' := hφ hm
          exact isConj_iff.2 ⟨x g, by rw [← hm', mul_inv_cancel_right]⟩
  exact fun c => key _ c rfl

end CFSG.KC.Co1Cl

end
