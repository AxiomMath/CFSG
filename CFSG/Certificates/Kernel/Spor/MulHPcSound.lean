module

public import Certificates.Data.Kernel.Spor.MulHPc
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.MulHQISound

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.PEnum

variable {n w : Nat}

theorem pcomp_assoc_p {p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem pcomp_id_p {p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p ∧ pcomp n w (mask w) (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hpr⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine ⟨PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_,
    PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) hp0 fun i hi => ?_⟩
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]
  · rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hpr i hi)]

theorem shl_one (r : Nat) : Nat.shiftLeft 1 r = 2 ^ r := by
  have h := Nat.shiftLeft_eq 1 r
  rw [Nat.one_mul] at h
  exact h

theorem pc_closed {m : Nat} {N : Nat → Nat} (h0 : N 0 = pidn n w)
    (hc0 : canonK n w (mask w) (n * w) (N 0) = true)
    (hc : ∀ r < m, canonK n w (mask w) (n * w) (N (2 ^ r)) = true)
    (ht : ∀ r < m, ∀ i < 2 ^ r, N (2 ^ r + i) = pcomp n w (mask w) (N i) (N (2 ^ r)))
    (hsq : ∀ r < m, ∃ a < 2 ^ r, pcomp n w (mask w) (N (2 ^ r)) (N (2 ^ r)) = N a)
    (hcj : ∀ r < m, ∀ s < r, ∃ b < 2 ^ r,
      pcomp n w (mask w) (N (2 ^ r)) (N (2 ^ s)) = pcomp n w (mask w) (N b) (N (2 ^ r))) :
    ∀ t ≤ m, (∀ i < 2 ^ t, canonK n w (mask w) (n * w) (N i) = true) ∧
      ∀ i < 2 ^ t, ∀ i' < 2 ^ t, ∃ k < 2 ^ t, pcomp n w (mask w) (N i) (N i') = N k := by
  have cid : canonK n w (mask w) (n * w) (pidn n w) = true := h0 ▸ hc0
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i hi => ?_, fun i hi i' hi' => ⟨0, by simp, ?_⟩⟩
    · have e : i = 0 := by simpa using hi
      rw [e]
      exact hc0
    · have e : i = 0 := by simpa using hi
      have e' : i' = 0 := by simpa using hi'
      rw [e, e', h0, (pcomp_id_p cid).1]
  | succ t ih =>
    intro ht1
    have htm : t < m := by omega
    obtain ⟨IC, IM⟩ := ih (by omega)
    have cy := hc t htm
    have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by rw [Nat.pow_succ]; omega
    have Q : ∀ r ≤ t, ∀ i < 2 ^ r, ∃ i' < 2 ^ t,
        pcomp n w (mask w) (N (2 ^ t)) (N i) = pcomp n w (mask w) (N i') (N (2 ^ t)) := by
      intro r
      induction r with
      | zero =>
        intro _ i hi
        have e : i = 0 := by simpa using hi
        refine ⟨0, Nat.two_pow_pos t, ?_⟩
        rw [e, h0, (pcomp_id_p cy).1, (pcomp_id_p cy).2]
      | succ r ihr =>
        intro hr i hi
        by_cases hlt : i < 2 ^ r
        · exact ihr (by omega) i hlt
        · have hp2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
          obtain ⟨i0, rfl⟩ : ∃ i0, i = 2 ^ r + i0 := ⟨i - 2 ^ r, by omega⟩
          have hi0 : i0 < 2 ^ r := by omega
          have hrm : r < m := by omega
          have hrt : r < t := by omega
          obtain ⟨i1, hi1, e1⟩ := ihr (by omega) i0 hi0
          obtain ⟨b, hb, eb⟩ := hcj t htm r hrt
          have cz := hc r hrm
          have ci1 := IC i1 hi1
          obtain ⟨k, hk, ek⟩ := IM i1 hi1 b hb
          refine ⟨k, hk, ?_⟩
          rw [ht r hrm i0 hi0, ← pcomp_assoc_p cy cz, e1, pcomp_assoc_p ci1 cz, eb,
            ← pcomp_assoc_p ci1 cy, ek]
    have split : ∀ x < 2 ^ (t + 1), x < 2 ^ t ∨ ∃ x0 < 2 ^ t, x = 2 ^ t + x0 := by
      intro x hx
      by_cases h : x < 2 ^ t
      · exact Or.inl h
      · exact Or.inr ⟨x - 2 ^ t, by omega, by omega⟩
    refine ⟨fun i hi => ?_, fun a ha b hb => ?_⟩
    · rcases split i hi with h | ⟨i0, hi0, rfl⟩
      · exact IC i h
      · rw [ht t htm i0 hi0]
        exact CFSG.KC.BfsPin.canonK_pcomp (IC i0 hi0) cy
    · rcases split a ha with ha' | ⟨a0, ha0, rfl⟩ <;> rcases split b hb with hb' | ⟨b0, hb0, rfl⟩
      · obtain ⟨k, hk, e⟩ := IM a ha' b hb'
        exact ⟨k, by omega, e⟩
      · rw [ht t htm b0 hb0, ← pcomp_assoc_p (IC a ha') cy]
        obtain ⟨k, hk, ek⟩ := IM a ha' b0 hb0
        rw [ek]
        exact ⟨2 ^ t + k, by omega, (ht t htm k hk).symm⟩
      · rw [ht t htm a0 ha0, pcomp_assoc_p (IC a0 ha0) (IC b hb')]
        obtain ⟨b1, hb1, e1⟩ := Q t (Nat.le_refl _) b hb'
        rw [e1, ← pcomp_assoc_p (IC a0 ha0) cy]
        obtain ⟨k, hk, ek⟩ := IM a0 ha0 b1 hb1
        rw [ek]
        exact ⟨2 ^ t + k, by omega, (ht t htm k hk).symm⟩
      · rw [ht t htm a0 ha0, ht t htm b0 hb0,
          pcomp_assoc_p (IC a0 ha0) (CFSG.KC.BfsPin.canonK_pcomp (IC b0 hb0) cy),
          ← pcomp_assoc_p cy cy]
        obtain ⟨b1, hb1, e1⟩ := Q t (Nat.le_refl _) b0 hb0
        rw [e1, pcomp_assoc_p (IC b1 hb1) cy]
        obtain ⟨a', ha'', ea⟩ := hsq t htm
        rw [ea]
        obtain ⟨k1, hk1, ek1⟩ := IM b1 hb1 a' ha''
        rw [ek1]
        obtain ⟨k2, hk2, ek2⟩ := IM a0 ha0 k1 hk1
        exact ⟨k2, by omega, ek2⟩

theorem pcT_spec {m : Nat} {T P : Nat → Nat} {r i : Nat}
    (h : pcTK n w m T P r i = true) :
    pcNK T P (2 ^ r + i) = pcomp n w m (pcNK T P i) (pcNK T P (2 ^ r)) := by
  unfold pcTK at h
  rw [strictB_eq, shl_one] at h
  exact Nat.eq_of_beq_eq_true h

theorem pcR_spec {K : Nat} {T P A B : Nat → Nat} {r : Nat}
    (h0 : pcRK n w (mask w) K T P A B r 0 4 = true)
    (hs : ∀ s < r, pcRK n w (mask w) K T P A B r (4 * (s / 4)) 4 = true) :
    canonK n w (mask w) (n * w) (pcNK T P (2 ^ r)) = true ∧
      (∃ a < 2 ^ r, pcomp n w (mask w) (pcNK T P (2 ^ r)) (pcNK T P (2 ^ r)) = pcNK T P a) ∧
      ∀ s < r, ∃ b < 2 ^ r, pcomp n w (mask w) (pcNK T P (2 ^ r)) (pcNK T P (2 ^ s)) =
        pcomp n w (mask w) (pcNK T P b) (pcNK T P (2 ^ r)) := by
  unfold pcRK at h0
  rw [strictB_eq, strictB_eq, shl_one, bAnd_eq, Bool.and_eq_true, strictB_eq, bAnd_eq,
    Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h0
  obtain ⟨hc, ha, hsq, -⟩ := h0
  refine ⟨hc, ⟨_, Nat.blt_eq.mp ha, Nat.eq_of_beq_eq_true hsq⟩, fun s hs' => ?_⟩
  have h1 := hs s hs'
  unfold pcRK at h1
  rw [strictB_eq, strictB_eq, shl_one, bAnd_eq, Bool.and_eq_true, strictB_eq, bAnd_eq,
    Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h1
  have h2 := allN_iff.1 h1.2.2.2 (s - 4 * (s / 4)) (by omega)
  have e : Nat.add (4 * (s / 4)) (s - 4 * (s / 4)) = s := by
    change 4 * (s / 4) + (s - 4 * (s / 4)) = s
    omega
  rw [strictB_eq, e] at h2
  have key : ∀ (c X : Bool), c = true → Bool.rec (motive := fun _ => Bool) true X c = true →
      X = true := by
    intro c X hc h
    subst hc
    exact h
  have h3 := key _ _ (Nat.blt_eq.mpr hs') h2
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, shl_one] at h3
  exact ⟨_, Nat.blt_eq.mp h3.1, Nat.eq_of_beq_eq_true h3.2⟩

theorem pcM_spec {k cnt p : Nat} {T G P S U PP : Nat → Nat}
    (h : pcMK n w (mask w) k cnt p T G P S U PP = true) :
    pcNK T P 0 = pidn n w ∧ canonK n w (mask w) (n * w) (pcNK T P 0) = true ∧
      (∀ i < cnt, r32 P i < cnt ∧ r32 S i < cnt ∧ r32 P (r32 S i) = i ∧
        pg w (mask w) (PP 0) (pg w (mask w) (T i) p) = i) ∧
      ∀ j < k, r32 U j < cnt ∧ G j = pcNK T P (r32 U j) := by
  unfold pcMK at h
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, hc, hi, hu⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, hc, fun i hi' => ?_, fun j hj => ?_⟩
  · have h2 := allN_iff.1 hi i hi'
    rw [bAnd_eq, Bool.and_eq_true, strictB_eq, bAnd_eq, Bool.and_eq_true, bAnd_eq,
      Bool.and_eq_true] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.blt_eq.mp h2.2.1, Nat.eq_of_beq_eq_true h2.2.2.1,
      Nat.eq_of_beq_eq_true h2.2.2.2⟩
  · have h2 := allN_iff.1 hu j hj
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h2
    exact ⟨Nat.blt_eq.mp h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem pcC_clH {k cnt p c : Nat} {T G GI CL P S U PP : Nat → Nat} (hn : n < 2 ^ 32) (hp : p < n)
    (hcl : ∀ i < cnt, ∀ i' < cnt, ∃ q < cnt,
      pcomp n w (mask w) (pcNK T P i) (pcNK T P i') = pcNK T P q)
    (hM : pcMK n w (mask w) k cnt p T G P S U PP = true)
    (hC : pcCK w (mask w) k cnt p T G CL c = true) (hc : c < cnt * (k + k)) :
    clHK n w (mask w) k cnt T G GI CL c = true := by
  obtain ⟨-, -, hI, hU⟩ := pcM_spec hM
  have hK : 0 < k + k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [Nat.add_zero, Nat.mul_zero] at hc
      exact absurd hc (Nat.not_lt_zero _)
    · omega
  unfold pcCK at hC
  unfold clHK
  cases e : Nat.blt (Nat.mod c (Nat.add k k)) k
  · rw [e] at hC
    exact hC
  · rw [e] at hC
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at hC
    obtain ⟨hq, hpt⟩ := hC
    have hq' : r32 CL c < cnt := Nat.blt_eq.mp hq
    have hj : c % (k + k) < k := Nat.blt_eq.mp e
    have hi : c / (k + k) < cnt := (Nat.div_lt_iff_lt_mul hK).2 hc
    obtain ⟨-, hs, hps, -⟩ := hI _ hi
    obtain ⟨hu, eu⟩ := hU _ hj
    have eT : T (c / (k + k)) = pcNK T P (r32 S (c / (k + k))) := by
      unfold pcNK
      rw [hps]
    obtain ⟨q, hqc, eq⟩ := hcl _ hs _ hu
    rw [← eT, ← eu] at eq
    have hpq : r32 P q < cnt := (hI q hqc).1
    have e1 : pg w (mask w) (T (r32 CL c)) p = pg w (mask w) (T (r32 P q)) p := by
      rw [Nat.eq_of_beq_eq_true hpt]
      change pg w (mask w) (T (c / (k + k))) (pg w (mask w) (G (c % (k + k))) p) = _
      rw [← CFSG.KS.PF.pg_pcomp hn hp, eq]
      rfl
    have e2 : r32 CL c = r32 P q := by
      rw [← (hI _ hq').2.2.2, ← (hI _ hpq).2.2.2, e1]
    unfold findPtK
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true]
    refine ⟨hq, ?_⟩
    change Nat.beq (T (r32 CL c))
      (pcomp n w (mask w) (T (c / (k + k))) (bothK k G GI (c % (k + k)))) = true
    rw [bothK_lt' hj, e2, eq]
    exact Nat.beq_refl _

end CFSG.KS.MulH

end
