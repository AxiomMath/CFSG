module

public import CFSG.Certificates.Kernel.J4Hub.BlockSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

private theorem brec_ite (b : Bool) (x y : Nat) :
    Bool.rec (motive := fun _ => Nat) y x b = if b = true then x else y := by
  cases b <;> rfl

private theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem land255 (x : Nat) : x &&& 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

private theorem land1 (x : Nat) : x &&& 1 = x % 2 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 1
  simpa using this

private theorem sr_eq (x n : Nat) : Nat.shiftRight x n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n

private theorem sl_eq (x n : Nat) : Nat.shiftLeft x n = x * 2 ^ n := Nat.shiftLeft_eq x n

private theorem step_cases (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx s ev : Nat)
    (h : 0 < CFSG.KC.Fam.bfsStep V vm G0 G1 mx s ev) :
    0 < s ∧ s % 256 < mx ∧ s / 256 / 2 < s % 256 ∧
      ((ev = 1 ∧ V (s % 256) = vm (V (s / 256 / 2)) (if s / 256 % 2 = 0 then G0 else G1) ∧
          CFSG.KC.Fam.bfsStep V vm G0 G1 mx s ev = s % 256 + 1 + 256 * (s / 256 + 1)) ∨
        CFSG.KC.Fam.bfsStep V vm G0 G1 mx s ev = s % 256 + 256 * (s / 256 + 1)) := by
  unfold CFSG.KC.Fam.bfsStep at h ⊢
  simp only [brec_ite, andB_eq', Nat.land_eq, land255, sr_eq, sl_eq, land1, Nat.reducePow,
    Nat.succ_eq_add_one, Nat.add_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h ⊢
  split_ifs at h ⊢ with c1 c2 c3 c4 c5 c6 c7 c8
  all_goals first
    | exact absurd h (lt_irrefl 0)
    | (refine ⟨by omega, by omega, by omega, ?_⟩
       first
        | (left; exact ⟨by omega, by assumption, by omega⟩)
        | (right; omega))

private theorem step_zero (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx ev : Nat) :
    CFSG.KC.Fam.bfsStep V vm G0 G1 mx 0 ev = 0 := by
  by_contra hne
  exact absurd (step_cases V vm G0 G1 mx 0 ev (Nat.pos_of_ne_zero hne)).1 (lt_irrefl 0)

private def BGood (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 c : Nat) : Prop :=
  ∀ k, 0 < k → k < c → ∃ i b, i < k ∧ V k = vm (V i) (if b = true then G1 else G0)

private def BInv (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx s : Nat) : Prop :=
  s = 0 ∨ (s % 256 ≤ mx ∧ BGood V vm G0 G1 (s % 256))

private theorem step_inv {V : Nat → Nat} {vm : Nat → Nat → Nat} {G0 G1 mx : Nat} (hmx : mx < 256)
    {s : Nat} (ev : Nat) (hi : BInv V vm G0 G1 mx s) :
    BInv V vm G0 G1 mx (CFSG.KC.Fam.bfsStep V vm G0 G1 mx s ev) := by
  rcases hi with rfl | ⟨hle, hg⟩
  · exact Or.inl (step_zero V vm G0 G1 mx ev)
  rcases Nat.eq_zero_or_pos (CFSG.KC.Fam.bfsStep V vm G0 G1 mx s ev) with h0 | h0
  · exact Or.inl h0
  obtain ⟨hs, hlt, hpar, hc⟩ := step_cases V vm G0 G1 mx s ev h0
  right
  rcases hc with ⟨-, hV, e⟩ | e
  · rw [e]
    have e1 : (s % 256 + 1 + 256 * (s / 256 + 1)) % 256 = s % 256 + 1 := by omega
    rw [e1]
    refine ⟨by omega, fun k hk0 hk => ?_⟩
    by_cases hk' : k < s % 256
    · exact hg k hk0 hk'
    · have : k = s % 256 := by omega
      subst this
      by_cases hb : s / 256 % 2 = 0
      · exact ⟨_, false, hpar, by simpa [hb] using hV⟩
      · exact ⟨_, true, hpar, by simpa [hb] using hV⟩
  · rw [e]
    have e1 : (s % 256 + 256 * (s / 256 + 1)) % 256 = s % 256 := by omega
    rw [e1]
    exact ⟨hle, hg⟩

private noncomputable def bfsChunk (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih2 J s => CFSG.KC.Loop.strictN
      (CFSG.KC.Fam.bfsStep V vm G0 G1 mx s (Nat.land J (nat_lit 255)))
      (ih2 (Nat.shiftRight J (nat_lit 8))))

private theorem bfsRun_cons (V : Nat → Nat) (vm : Nat → Nat → Nat) (G0 G1 mx C : Nat)
    (Cs : List Nat) (s : Nat) :
    CFSG.KC.Fam.bfsRun V vm G0 G1 mx (C :: Cs) s =
      CFSG.KC.Fam.bfsRun V vm G0 G1 mx Cs
        (bfsChunk V vm G0 G1 mx (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) s) :=
  strictN_eq' _ _

private theorem chunk_inv {V : Nat → Nat} {vm : Nat → Nat → Nat} {G0 G1 mx : Nat} (hmx : mx < 256) :
    ∀ n J s, BInv V vm G0 G1 mx s → BInv V vm G0 G1 mx (bfsChunk V vm G0 G1 mx n J s)
  | 0, _, _, h => h
  | n + 1, J, s, h => by
    have e : bfsChunk V vm G0 G1 mx (n + 1) J s = bfsChunk V vm G0 G1 mx n (Nat.shiftRight J 8)
        (CFSG.KC.Fam.bfsStep V vm G0 G1 mx s (Nat.land J 255)) := strictN_eq' _ _
    rw [e]
    exact chunk_inv hmx n _ _ (step_inv hmx _ h)

private theorem run_inv {V : Nat → Nat} {vm : Nat → Nat → Nat} {G0 G1 mx : Nat} (hmx : mx < 256) :
    ∀ (Cs : List Nat) s, BInv V vm G0 G1 mx s →
      BInv V vm G0 G1 mx (CFSG.KC.Fam.bfsRun V vm G0 G1 mx Cs s)
  | [], _, h => h
  | C :: Cs, s, h => by
    rw [bfsRun_cons]
    exact run_inv hmx Cs _ (chunk_inv hmx _ _ _ h)

theorem bfs_sound' (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {V : Nat → Nat} {G0 G1 mx sf : Nat} {Cs : List Nat}
    (hV : validM p S LV HV (V 0) = true)
    (hG0 : validM p nb L H G0 = true) (hG1 : validM p nb L H G1 = true)
    (h : Nat.beq (CFSG.KC.Fam.bfsRun V (vecR p w S d T LV HV RM) G0 G1 mx Cs 1) sf = true)
    (hsf : 0 < sf) (hcnt : Nat.land sf 255 = mx) :
    ∀ k < mx, ∃ l : List Bool, ordVec p d w (V k) =
      ordVec p d w (V 0) ᵥ* (l.map fun b => if b then ordMat p d w S G1 else ordMat p d w S G0).prod := by
  rw [Nat.land_eq, land255] at hcnt
  have hmx : mx < 256 := by omega
  rcases Nat.eq_zero_or_pos mx with rfl | hpos
  · intro k hk
    omega
  have hrun : CFSG.KC.Fam.bfsRun V (vecR p w S d T LV HV RM) G0 G1 mx Cs 1 = sf :=
    Nat.eq_of_beq_eq_true h
  have hinv := run_inv hmx Cs 1 (V := V) (vm := vecR p w S d T LV HV RM) (G0 := G0) (G1 := G1)
    (Or.inr ⟨by omega, fun k hk0 hk => absurd hk (by omega)⟩)
  rw [hrun] at hinv
  rcases hinv with h0 | ⟨-, hg⟩
  · omega
  rw [hcnt] at hg
  have hc0 := validV_canon hc hV
  have hM0 : Canon p d w G0 := by
    subst hnb
    exact validM_canon hc hG0
  have hM1 : Canon p d w G1 := by
    subst hnb
    exact validM_canon hc hG1
  have key : ∀ k < mx, CFSG.KC.LQT.SecS.VCanon p d w (V k) ∧ ∃ l : List Bool,
      ordVec p d w (V k) = ordVec p d w (V 0) ᵥ*
        (l.map fun b => if b then ordMat p d w S G1 else ordMat p d w S G0).prod := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨hc0, [], by simp⟩
      obtain ⟨i, b, hik, hVk⟩ := hg k hk0 hk
      obtain ⟨cp, l, hl⟩ := ih i hik (by omega)
      have hMb : Canon p d w (if b = true then G1 else G0) := by
        cases b
        · exact hM0
        · exact hM1
      obtain ⟨c1, e1⟩ := CFSG.KC.LQT.SecS.vecR_sound hc cp hMb
      rw [← hVk] at c1 e1
      refine ⟨c1, l ++ [b], ?_⟩
      have e2 : ordVec p d w (V k) = CFSG.KC.LQT.SecS.toVec p d w (V k) := rfl
      have e3 : ordVec p d w (V i) = CFSG.KC.LQT.SecS.toVec p d w (V i) := rfl
      rw [e2, e1, ← e3, hl, Matrix.vecMul_vecMul, List.map_append, List.prod_append]
      cases b <;> simp
  exact fun k hk => (key k hk).2

end CFSG.KS.J4Hub

end
