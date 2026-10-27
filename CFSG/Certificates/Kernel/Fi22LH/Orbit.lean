module

public import CFSG.Certificates.Kernel.Fi22LH.OrbSets
public import CFSG.Certificates.Kernel.Fi22LH.Rows
import CFSG.Certificates.Kernel.Fi22LH.OrbBfs
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.F3.ConjBFS
import CFSG.Sporadic.Th.CertificateChunks

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KC.F3Bfs
  CFSG.F3.Native.BfsSpec CFSG.KS.TW CFSG.KC.Enum

variable {D : LHData}

theorem bfs_tree {fa fb fp fl : Nat → Nat} {N : Nat} (hbfs : bfsOrderOK fa fb fp fl N = true) :
    ∀ k, 0 < k → k < N → fp k < k ∧ ((fl k = 1 ∧ fa (fp k) = k) ∨ (fl k = 2 ∧ fb (fp k) = k)) := by
  simp only [bfsOrderOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hbfs
  obtain ⟨-, -, hfold⟩ := hbfs
  have hCN : cnt fa fb fp fl N = N := by
    rw [foldUp_eq] at hfold
    exact hfold
  have hCz : ∀ t h, cnt fa fb fp fl h = 0 → cnt fa fb fp fl (h + t) = 0 := by
    intro t
    induction t with
    | zero => intro h e; exact e
    | succ t ih =>
      intro h e
      rw [← Nat.add_assoc, cnt_succ, ih h e]
      exact bfsStep_zero _ _ _ _ _
  have hCne : ∀ h ≤ N, 0 < N → cnt fa fb fp fl h ≠ 0 := by
    intro h hh hN e
    have := hCz (N - h) h e
    rw [Nat.add_sub_cancel' hh, hCN] at this
    omega
  have hP : ∀ h ≤ N, ∀ k, 0 < k → k < cnt fa fb fp fl h →
      fp k < k ∧ ((fl k = 1 ∧ fa (fp k) = k) ∨ (fl k = 2 ∧ fb (fp k) = k)) := by
    intro h
    induction h with
    | zero =>
      intro _ k hk0 hk
      have : cnt fa fb fp fl 0 = 1 := rfl
      omega
    | succ h ih =>
      intro hh k hk0 hk
      have hn0 := hCne (h + 1) hh (by omega)
      have hCs := cnt_succ fa fb fp fl h
      rw [bfsStep_eq] at hCs
      have hqn : h < cnt fa fb fp fl h := by
        by_contra hqn
        rw [if_neg hqn] at hCs
        exact hn0 hCs
      rw [if_pos hqn] at hCs
      have hn1z : bfsHit fp fl h 1 (fa h) (cnt fa fb fp fl h) ≠ 0 := by
        intro e
        rw [e, bfsHit_zero] at hCs
        exact hn0 hCs
      have hA := bfsHit_spec hn1z
      rw [hCs] at hn0 hk
      have hB := bfsHit_spec hn0
      rcases Nat.lt_or_ge k (cnt fa fb fp fl h) with hlt | hge
      · exact ih (by omega) k hk0 hlt
      · rcases hA with ⟨_, hA⟩ | ⟨hA1, hA2, hA3, hA4⟩
        · rw [hA] at hB hk
          rcases hB with ⟨_, hB⟩ | ⟨hB1, hB2, hB3, hB4⟩
          · omega
          · have : k = cnt fa fb fp fl h := by omega
            subst this
            exact ⟨by omega, Or.inr ⟨hB3, by rw [hB2]; exact hB1⟩⟩
        · rw [hA4] at hB hk
          rcases hB with ⟨_, hB⟩ | ⟨hB1, hB2, hB3, hB4⟩
          · have : k = cnt fa fb fp fl h := by omega
            subst this
            exact ⟨by omega, Or.inl ⟨hA3, by rw [hA2]; exact hA1⟩⟩
          · rcases Nat.lt_or_ge k (cnt fa fb fp fl h + 1) with h2 | h2
            · have : k = cnt fa fb fp fl h := by omega
              subst this
              exact ⟨by omega, Or.inl ⟨hA3, by rw [hA2]; exact hA1⟩⟩
            · have : k = cnt fa fb fp fl h + 1 := by omega
              subst this
              exact ⟨by omega, Or.inr ⟨hB3, by rw [hB2]; exact hB1⟩⟩
  intro k hk0 hk
  exact hP N (Nat.le_refl _) k hk0 (by rw [hCN]; exact hk)

theorem img_alpha (hO : OrbOK) (h : LHChecks D) {Q : Nat → Nat}
    (hs : ∀ s < 20, setSl Q D.al D.be s = true) {k : Nat} (hk : k < 14080) :
    imgBits orbL.alpha (bitsOfNat (sb (Q k))) = bitsOfNat (sb (Q (fd (Q k) 7722 16383))) := by
  refine BitsIs.eq_bitsOfNat (bitsIs_imgBits (bitsIs_bitsOfNat _) fun x hx _ => by
    rw [(ent_al hO h hx).1]; have := (ent_al hO h hx).2.1; omega) fun y hy => ?_
  rw [sb_pa hs hk]
  constructor
  · rintro ⟨x, hx, hm, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (sb_mem hs hk x).1 hm
    exact ⟨j, hj, (ent_al hO h hx).1.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ent (Q k) j, mem_lt hs hk hj, (sb_mem hs hk _).2 ⟨j, hj, rfl⟩,
      (ent_al hO h (mem_lt hs hk hj)).1⟩

theorem img_beta (hO : OrbOK) (h : LHChecks D) {Q : Nat → Nat}
    (hs : ∀ s < 20, setSl Q D.al D.be s = true) {k : Nat} (hk : k < 14080) :
    imgBits orbL.beta (bitsOfNat (sb (Q k))) = bitsOfNat (sb (Q (fd (Q k) 7736 16383))) := by
  refine BitsIs.eq_bitsOfNat (bitsIs_imgBits (bitsIs_bitsOfNat _) fun x hx _ => by
    rw [(ent_be hO h hx).1]; have := (ent_be hO h hx).2; omega) fun y hy => ?_
  rw [sb_pb hs hk]
  constructor
  · rintro ⟨x, hx, hm, rfl⟩
    obtain ⟨j, hj, rfl⟩ := (sb_mem hs hk x).1 hm
    exact ⟨j, hj, (ent_be hO h hx).1.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ent (Q k) j, mem_lt hs hk hj, (sb_mem hs hk _).2 ⟨j, hj, rfl⟩,
      (ent_be hO h (mem_lt hs hk hj)).1⟩

theorem sets_inj {Q : Nat → Nat} {lb m0 : Nat} (hw : walkOK Q lb m0 = true) :
    ∀ i < 14080, ∀ j < 14080, bitsOfNat (sb (Q i)) = bitsOfNat (sb (Q j)) → i = j :=
  fun i hi j hj e => sb_inj hw hi hj (bitsOfNat_inj (sb_lt_3520 _) (sb_lt_3520 _) e)

theorem orbit_eq_gen (hO : OrbOK) (h : LHChecks D) {Q : Nat → Nat} {lb m0 : Nat}
    (hs : ∀ s < 20, setSl Q D.al D.be s = true) (hbfs : orbBfsK Q = true)
    (hw : walkOK Q lb m0 = true) {B : Bits} (hB : B = bitsOfNat (sb (Q 0))) :
    lhOrbitBFS orbL.alpha orbL.beta B 20000 = orbDec Q := by
  rw [lhOrbitBFS_eq_of (N := 14080) (sets := fun k => bitsOfNat (sb (Q k)))
    (fa := fun k => fd (Q k) 7722 16383) (fb := fun k => fd (Q k) 7736 16383)
    (fp := fun k => fd (Q k) 7750 16383) (fl := fun k => fd (Q k) 7764 3) (by decide) (by decide)
    hB.symm (sets_inj hw) (fun k hk => ⟨pa_lt hs hk, img_alpha hO h hs hk⟩)
    (fun k hk => ⟨pb_lt hs hk, img_beta hO h hs hk⟩) hbfs]
  simp only [orbDec]

theorem orbit_eq0 (hO : OrbOK) (h : LHChecks D) :
    lhOrbitBFS orbL.alpha orbL.beta (bitsOf (lhData ())[0]!) 20000 = orbDec D.QA :=
  orbit_eq_gen hO h h.setA h.bfsA h.walkA (B0_eq h)

theorem orbit_eq1 (hO : OrbOK) (h : LHChecks D) :
    lhOrbitBFS orbL.alpha orbL.beta (bitsOf (lhData ())[1]!) 20000 = orbDec D.QB :=
  orbit_eq_gen hO h h.setB h.bfsB h.walkB (B1_eq h)

theorem orbDec_fields (Q : Nat → Nat) :
    (orbDec Q).pa = (Array.ofFn (n := 14080) fun k => fd (Q k.val) 7722 16383) ∧
    (orbDec Q).pb = (Array.ofFn (n := 14080) fun k => fd (Q k.val) 7736 16383) ∧
    (orbDec Q).par = (Array.ofFn (n := 14080) fun k => fd (Q k.val) 7750 16383) ∧
    (orbDec Q).lab = (Array.ofFn (n := 14080) fun k => fd (Q k.val) 7764 3) := by
  simp only [orbDec, and_self]

theorem ofFn_get (f : Nat → Nat) {k : Nat} (hk : k < 14080) :
    (Array.ofFn (n := 14080) fun i => f i.val)[k]! = f k := by
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem orbDec_get (Q : Nat → Nat) {k : Nat} (hk : k < 14080) :
    (orbDec Q).pa[k]! = fd (Q k) 7722 16383 ∧ (orbDec Q).pb[k]! = fd (Q k) 7736 16383 ∧
      (orbDec Q).par[k]! = fd (Q k) 7750 16383 ∧ (orbDec Q).lab[k]! = fd (Q k) 7764 3 := by
  obtain ⟨hpa, hpb, hpar, hlab⟩ := orbDec_fields Q
  rw [hpa, hpb, hpar, hlab]
  exact ⟨ofFn_get (fun k => fd (Q k) 7722 16383) hk, ofFn_get (fun k => fd (Q k) 7736 16383) hk,
    ofFn_get (fun k => fd (Q k) 7750 16383) hk, ofFn_get (fun k => fd (Q k) 7764 3) hk⟩

theorem keyFind_orb {Q : Nat → Nat} {lb m0 : Nat} (hw : walkOK Q lb m0 = true) {k : Nat}
    (hk : k < 14080) : keyFind (keyTable (orbDec Q).sets) (orbDec Q).sets[k]! = k := by
  unfold keyFind keyTable
  rw [orbDec_size, Std.HashMap.get?_eq_getElem?,
    foldl_insert_of' (fun k => canonKey (orbDec Q).sets[k]!) (fun i hi j hj e => ?_) hk]
  · rfl
  · rw [orbDec_sets Q hi, orbDec_sets Q hj] at e
    exact sb_inj hw hi hj (canonKey_inj (sb_lt _) (sb_lt _) e)

theorem orbitOK_gen (hO : OrbOK) (h : LHChecks D) {Q : Nat → Nat} {lb m0 : Nat}
    (hs : ∀ s < 20, setSl Q D.al D.be s = true) (hbfs : orbBfsK Q = true)
    (hw : walkOK Q lb m0 = true) {B : Bits} (hB : B = bitsOfNat (sb (Q 0))) :
    orbitOK orbL.alpha orbL.beta B (orbDec Q) (keyTable (orbDec Q).sets) = true := by
  obtain ⟨hpa, hpb, hpar, hlab⟩ := orbDec_fields Q
  have hal : ∀ x < 3510, ap orbL.alpha x < 3510 := fun x hx => by
    rw [(ent_al hO h hx).1]; exact (ent_al hO h hx).2.1
  have hbe : ∀ x < 3510, ap orbL.beta x < 3510 := fun x hx => by
    rw [(ent_be hO h hx).1]; exact (ent_be hO h hx).2
  have hset : ∀ k < 14080, BitsIs (orbDec Q).sets[k]! fun y => ∃ j < 351, ent (Q k) j = y :=
    fun k hk => by
      rw [orbDec_sets Q hk]
      exact (bitsIs_bitsOfNat _).congr fun y _ => sb_mem hs hk y
  unfold CFSG.Sporadic.Fi22.Native.orbitOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  have s1 : (orbDec Q).pa.size = 14080 := by rw [hpa, Array.size_ofFn]
  have s2 : (orbDec Q).pb.size = 14080 := by rw [hpb, Array.size_ofFn]
  have s3 : (orbDec Q).par.size = 14080 := by rw [hpar, Array.size_ofFn]
  have s4 : (orbDec Q).lab.size = 14080 := by rw [hlab, Array.size_ofFn]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨orbDec_size Q, s1⟩, s2⟩, s3⟩, s4⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allIn_iff]
    intro x hx
    rw [beq_iff_eq, orbDec_sets Q (by decide), hB]
  · refine CFSG.Sporadic.Th.parAll_eq_true_of fun k hk => ?_
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [(orbDec_get Q hk).1, (orbDec_get Q hk).2.1]
    refine ⟨⟨⟨pa_lt hs hk, pb_lt hs hk⟩, ?_⟩, ?_⟩
    · refine mapsOnto_of (hset k hk) (hset _ (pa_lt hs hk)) hal fun x hx => ?_
      rw [← sb_mem hs (pa_lt hs hk), sb_pa hs hk, (ent_al hO h hx).1]
      constructor
      · rintro ⟨j, hj, e⟩
        refine ⟨j, hj, ?_⟩
        rw [← (ent_al hO h (mem_lt hs hk hj)).2.2, ← (ent_al hO h hx).2.2, e]
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    · refine mapsOnto_of (hset k hk) (hset _ (pb_lt hs hk)) hbe fun x hx => ?_
      rw [← sb_mem hs (pb_lt hs hk), sb_pb hs hk, (ent_be hO h hx).1]
      constructor
      · rintro ⟨j, hj, e⟩
        exact ⟨j, hj, ent_be_inj hO h (mem_lt hs hk hj) hx e⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
  · rw [allIn_lo]
    intro k hk1 hk2
    obtain ⟨h1, h2⟩ := bfs_tree (fa := fun k => fd (Q k) 7722 16383)
      (fb := fun k => fd (Q k) 7736 16383) (fp := fun k => fd (Q k) 7750 16383)
      (fl := fun k => fd (Q k) 7764 3) (N := 14080) hbfs k (by omega) hk2
    have hp : fd (Q k) 7750 16383 < 14080 := by omega
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    rw [(orbDec_get Q hk2).2.2.1, (orbDec_get Q hk2).2.2.2, (orbDec_get Q hp).1,
      (orbDec_get Q hp).2.1]
    exact ⟨h1, h2⟩
  · refine CFSG.Sporadic.Th.parAll_eq_true_of fun k hk => ?_
    rw [beq_iff_eq]
    exact keyFind_orb hw hk

theorem c_orbit0 (hO : OrbOK) (h : LHChecks D) :
    orbitOK orbL.alpha orbL.beta (bitsOf (lhData ())[0]!) (orbDec D.QA)
      (keyTable (orbDec D.QA).sets) = true :=
  orbitOK_gen hO h h.setA h.bfsA h.walkA (B0_eq h)

theorem c_orbit1 (hO : OrbOK) (h : LHChecks D) :
    orbitOK orbL.alpha orbL.beta (bitsOf (lhData ())[1]!) (orbDec D.QB)
      (keyTable (orbDec D.QB).sets) = true :=
  orbitOK_gen hO h h.setB h.bfsB h.walkB (B1_eq h)

theorem c_keyFind (h : LHChecks D) :
    keyFind (keyTable (orbDec D.QA).sets) (bitsOf (lhData ())[1]!) = 14080 := by
  have hn : ∀ k < 14080, sb (D.QA k) ≠ bs D.lb1 := by
    intro k hk e
    have hni := h.notIn
    unfold notInK at hni
    rw [strictB_eq] at hni
    have := allN_iff.1 hni k hk
    rw [notB_eq, e, beq_true rfl] at this
    exact Bool.false_ne_true this
  unfold keyFind keyTable
  rw [orbDec_size, Std.HashMap.get?_eq_getElem?, B1_eq h,
    foldl_insert_none' (fun k => canonKey (orbDec D.QA).sets[k]!) fun k hk e => ?_]
  · rfl
  · rw [orbDec_sets _ hk] at e
    have := canonKey_inj (sb_lt _) (sb_lt _) e
    rw [sb_zero h.walkB] at this
    exact hn k hk this

end CFSG.KS.Fi22LH
