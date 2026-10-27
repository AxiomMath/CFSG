module

public import Certificates.Data.Kernel.VOrbRec
public import CFSG.Certificates.Kernel.Co1M.VOrbitFull

public section

namespace CFSG.KC.VOrbRec

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.VOrbFull CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

private theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

private theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

private theorem pw2_eq (w : Nat) : CFSG.KLie.CT.pw2 w = 2 ^ w := Nat.one_shiftLeft w

private theorem bit_eq (X i : Nat) : CFSG.KLie.CT.bit X i = X.testBit i := by
  have e : CFSG.KLie.CT.bit X i = Nat.beq ((X >>> i) % 2) 1 := by
    change Nat.beq ((X >>> i) &&& 1) 1 = _
    rw [Nat.and_one_is_mod]
  have h2 : X.testBit i = decide ((X >>> i) % 2 = 1) := by
    rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
  rw [e, h2]
  rcases Nat.mod_two_eq_zero_or_one (X >>> i) with h | h <;> rw [h] <;> rfl

private theorem closedAt_true {d MA MB M p : Nat} (h : closedAt d MA MB M p = true) :
    M.testBit (vmF d MA p) = true ∧ M.testBit (vmF d MB p) = true := by
  have e : closedAt d MA MB M p =
      (CFSG.KLie.CT.bit M (vmF d MA p) && CFSG.KLie.CT.bit M (vmF d MB p)) := andB_eq _ _
  rw [e, bit_eq, bit_eq, Bool.and_eq_true] at h
  exact h

private theorem recAt_cons_true {d MA MB M r acc : Nat} {R : List Nat}
    (h : recAt d MA MB M (r :: R) acc = true) :
    acc.testBit (r % 2 ^ d) = false ∧ acc.testBit (r >>> d) = true ∧
      (vmF d MA (r >>> d) = r % 2 ^ d ∨ vmF d MB (r >>> d) = r % 2 ^ d) ∧
      (M.testBit (vmF d MA (r % 2 ^ d)) = true ∧ M.testBit (vmF d MB (r % 2 ^ d)) = true) ∧
      recAt d MA MB M R (acc ||| 2 ^ (r % 2 ^ d)) = true := by
  have e : recAt d MA MB M (r :: R) acc =
      (strictB (r &&& (CFSG.KLie.CT.pw2 d - 1)) fun p => strictB (r >>> d) fun q =>
        CFSG.KLie.CT.andB (Nat.blt p (CFSG.KLie.CT.pw2 d))
          (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (CFSG.KLie.CT.bit acc p))
            (CFSG.KLie.CT.andB (CFSG.KLie.CT.bit acc q)
              (CFSG.KLie.CT.andB
                (CFSG.KLie.CT.orB (Nat.beq (vmF d MA q) p) (Nat.beq (vmF d MB q) p))
                (CFSG.KLie.CT.andB (closedAt d MA MB M p)
                  (recAt d MA MB M R (acc ||| CFSG.KLie.CT.pw2 p))))))) := rfl
  rw [e, strictB_eq, strictB_eq] at h
  simp only [andB_eq, orB_eq, notB_eq, bit_eq, pw2_eq, Nat.and_two_pow_sub_one_eq_mod,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at h
  obtain ⟨-, hp, hq, hpq, hcl, hR⟩ := h
  exact ⟨hp, hq, hpq, closedAt_true hcl, hR⟩

private theorem recAt_spec {d MA MB M : Nat} : ∀ (R : List Nat) (acc : Nat),
    recAt d MA MB M R acc = true →
      (∀ x, M.testBit x = true ↔ acc.testBit x = true ∨ x ∈ R.map (· % 2 ^ d)) ∧
      (R.map (· % 2 ^ d)).Nodup ∧ (∀ p ∈ R.map (· % 2 ^ d), acc.testBit p = false) ∧
      (∀ p ∈ R.map (· % 2 ^ d),
        M.testBit (vmF d MA p) = true ∧ M.testBit (vmF d MB p) = true) ∧
      ∀ T : Set Nat, (∀ x ∈ T, vmF d MA x ∈ T ∧ vmF d MB x ∈ T) →
        (∀ x, acc.testBit x = true → x ∈ T) → ∀ p ∈ R.map (· % 2 ^ d), p ∈ T
  | [], acc, h => by
    have hM : acc = M := by
      have e : recAt d MA MB M [] acc = Nat.beq acc M := rfl
      rw [e, Nat.beq_eq] at h
      exact h
    subst hM
    simp
  | r :: R, acc, h => by
    obtain ⟨hp, hq, hpq, hcl, hR⟩ := recAt_cons_true h
    obtain ⟨hM, hnd, hnew, hclR, hT⟩ := recAt_spec R _ hR
    have hacc : ∀ x, (acc ||| 2 ^ (r % 2 ^ d)).testBit x = true ↔
        acc.testBit x = true ∨ x = r % 2 ^ d := fun x => by
      rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_iff]
      exact or_congr_right eq_comm
    simp only [List.map_cons, List.mem_cons, List.nodup_cons, forall_eq_or_imp]
    refine ⟨fun x => ?_, ⟨fun hmem => ?_, hnd⟩, ⟨hp, fun p hpR => ?_⟩, ⟨hcl, hclR⟩,
      fun T hTcl hTacc => ?_⟩
    · rw [hM x, hacc x, or_assoc]
    · have h1 := hnew _ hmem
      have h2 := (hacc (r % 2 ^ d)).mpr (Or.inr rfl)
      rw [h1] at h2
      exact absurd h2 (by decide)
    · have h1 := hnew p hpR
      cases e : acc.testBit p
      · rfl
      · have h2 := (hacc p).mpr (Or.inl e)
        rw [h1] at h2
        exact absurd h2 (by decide)
    · have hqT : r >>> d ∈ T := hTacc _ hq
      have hpT : r % 2 ^ d ∈ T := by
        rcases hpq with e | e
        · rw [← e]
          exact (hTcl _ hqT).1
        · rw [← e]
          exact (hTcl _ hqT).2
      refine ⟨hpT, hT T hTcl fun x hx => ?_⟩
      rcases (hacc x).mp hx with hx | hx
      · exact hTacc x hx
      · rw [hx]
        exact hpT

private theorem length_rec : ∀ R : List Nat,
    (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) R : Nat) = R.length
  | [] => rfl
  | _ :: R => congrArg Nat.succ (length_rec R)

theorem vorbRecK_sound {d MA MB v₀ n M : Nat} {R : List Nat} (h : vorbRecK d MA MB v₀ n M R = true) :
    ∃ S : Finset Nat, S.card = n ∧ v₀ ∈ S ∧ (∀ x ∈ S, x < 2 ^ d) ∧
      (∀ x ∈ S, vmF d MA x ∈ S ∧ vmF d MB x ∈ S) ∧ (∀ x, x ∈ S ↔ M.testBit x = true) ∧
      ∀ T : Set Nat, v₀ ∈ T → (∀ x ∈ T, vmF d MA x ∈ T ∧ vmF d MB x ∈ T) → ∀ x ∈ S, x ∈ T := by
  classical
  have h' : CFSG.KLie.CT.andB (Nat.blt v₀ (CFSG.KLie.CT.pw2 d))
      (CFSG.KLie.CT.andB (Nat.beq (Nat.succ (List.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun _ _ ih => Nat.succ ih) R)) n)
      (CFSG.KLie.CT.andB (closedAt d MA MB M v₀) (recAt d MA MB M R (CFSG.KLie.CT.pw2 v₀)))) =
      true := h
  rw [length_rec] at h'
  simp only [andB_eq, pw2_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
  obtain ⟨hv0, hn, hcl0, hrec⟩ := h'
  obtain ⟨hM, hnd, hnew, hclR, hT⟩ := recAt_spec R _ hrec
  have hcl0' := closedAt_true hcl0
  have hM' : ∀ x, M.testBit x = true ↔ x = v₀ ∨ x ∈ R.map (· % 2 ^ d) := fun x => by
    rw [hM x, Nat.testBit_two_pow, decide_eq_true_iff]
    exact or_congr_left eq_comm
  have hv0R : v₀ ∉ R.map (· % 2 ^ d) := fun hmem => by
    have h1 := hnew v₀ hmem
    rw [Nat.testBit_two_pow, decide_eq_false_iff_not] at h1
    exact h1 rfl
  set S : Finset Nat := insert v₀ (R.map (· % 2 ^ d)).toFinset with hSdef
  have hmemS : ∀ x, x ∈ S ↔ M.testBit x = true := fun x => by
    rw [hSdef, Finset.mem_insert, List.mem_toFinset, hM']
  refine ⟨S, ?_, Finset.mem_insert_self _ _, fun x hx => ?_, fun x hx => ?_, hmemS,
    fun T hv0T hTcl x hx => ?_⟩
  · rw [hSdef, Finset.card_insert_of_notMem (by rwa [List.mem_toFinset]),
      List.toFinset_card_of_nodup hnd, List.length_map, ← hn]
  · rcases (hM' x).mp ((hmemS x).mp hx) with rfl | hx
    · exact hv0
    · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.mod_lt _ (Nat.two_pow_pos d)
  · rw [hmemS, hmemS]
    rcases (hM' x).mp ((hmemS x).mp hx) with rfl | hx
    · exact hcl0'
    · exact hclR x hx
  · rcases (hM' x).mp ((hmemS x).mp hx) with rfl | hx
    · exact hv0T
    · refine hT T hTcl (fun y hy => ?_) x hx
      rw [Nat.testBit_two_pow, decide_eq_true_iff] at hy
      rw [← hy]
      exact hv0T

theorem vorbRec_bfs {d MA MB v₀ n M : Nat} {R : List Nat} (h : vorbRecK d MA MB v₀ n M R = true)
    (hn : n < 2 ^ 30) :
    vOrbitOK d n (unpackR d MA) (unpackR d MB) (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n) =
        true ∧
      (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n).pts[0]! = v₀ ∧
      (CFSG.Perm.Native.treeBFS n 0 (lets (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n))
        #[0, 1]).pts.size = n ∧
      CFSG.Perm.Native.treeOK n 0
        (CFSG.Perm.Native.treeBFS n 0 (lets (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n)) #[0, 1])
        (lets (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n)) #[0, 1] = true ∧
      ∀ w, (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n).pts.contains w = M.testBit w := by
  obtain ⟨S, hS, hv0, hlt, hcl, hM, hmin⟩ := vorbRecK_sound h
  have hA : ∀ x ∈ S, vecMulN d (unpackR d MA) x ∈ S := fun x hx => by
    rw [CFSG.KC.F2W.vecMulN_unpackR]
    exact (hcl x hx).1
  have hB : ∀ x ∈ S, vecMulN d (unpackR d MB) x ∈ S := fun x hx => by
    rw [CFSG.KC.F2W.vecMulN_unpackR]
    exact (hcl x hx).2
  have hmin' : ∀ T : Set Nat, v₀ ∈ T →
      (∀ x ∈ T, vecMulN d (unpackR d MA) x ∈ T ∧ vecMulN d (unpackR d MB) x ∈ T) →
      ∀ x ∈ S, x ∈ T := fun T h0 hT => hmin T h0 fun x hx => by
    rw [← CFSG.KC.F2W.vecMulN_unpackR, ← CFSG.KC.F2W.vecMulN_unpackR]
    exact hT x hx
  obtain ⟨hsz, hasz, hbsz, h0, hmem, hinj, hao, hbo⟩ :=
    vOrbitBFS_full (d := d) (cA := unpackR d MA) (cB := unpackR d MB) hS hn hlt hv0 hA hB hmin'
  have hn0 : 0 < n := by
    have := Finset.card_pos.2 ⟨v₀, hv0⟩
    omega
  have hlt' : ∀ i < n, (vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n).pts[i]! < 2 ^ d :=
    fun i hi => hlt _ (hmem i hi)
  have hT := tree_of hn0 hn (fun i hi => (hao i hi).1) (fun i hi => (hbo i hi).1)
    (reach_of_min hinj hao hbo hn0 hmem (by rw [h0]; exact hmin'))
  refine ⟨orbit_ok_of hn hsz hasz hbsz hlt' hinj hao hbo, h0, hT.1, hT.2, fun w => ?_⟩
  set O := vOrbitBFS d (unpackR d MA) (unpackR d MB) v₀ n with hO
  have himg : (Finset.range n).image (fun i => O.pts[i]!) = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact hmem i (Finset.mem_range.1 hi)
    · rw [Finset.card_image_of_injOn (fun i hi j hj e => hinj i (Finset.mem_range.1 hi) j
        (Finset.mem_range.1 hj) e), Finset.card_range, hS]
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, ← hM, ← himg, Finset.mem_image]
  constructor
  · intro hw
    obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hw
    exact ⟨i, Finset.mem_range.2 (by omega), by rw [getElem!_pos O.pts i hi, e]⟩
  · rintro ⟨i, hi, e⟩
    have hi' : i < O.pts.size := by rw [hsz]; exact Finset.mem_range.1 hi
    exact Array.mem_iff_getElem.2 ⟨i, hi', by rw [← e, getElem!_pos O.pts i hi']⟩

end CFSG.KC.VOrbRec

end
