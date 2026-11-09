module

public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Sporadic.Schreier.PairWords
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.BfsPinBaseSound

public section

namespace CFSG.KC.Child3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

@[expose] noncomputable def repKB (n w : Nat) (GP GIP : Nat → Nat) (g : Nat) (CS OFF : List Nat)
    (CI E P L K S SI : Nat → Nat) (N cap : Nat) (bs : List Nat) (j : Nat) : Bool :=
  strictB (CI j) (fun i => strictB (lget OFF i) (fun o => strictB (lget CS i) (fun c =>
  strictB (Nat.sub j o) (fun k =>
  bAnd(Nat.blt i CS.length, bAnd(Nat.ble o j, bAnd(Nat.blt k c, bAnd(Nat.ble c cap,
  bAnd(canonK n w (mask w) (Nat.mul n w) (E j),
  bAnd(bIf(Nat.beq k 0, true, bAnd(Nat.blt (P j) k, bAnd(Nat.blt (L j) g,
    Nat.beq (cj n w GP GIP (L j) (E (Nat.add o (P j)))) (E j)))),
  bAnd(bIf(Nat.beq k 0, true, bIf(Nat.blt (Nat.succ k) c,
    lexLtK (P j) (L j) (P (Nat.succ j)) (L (Nat.succ j)), true)),
  bAnd(allN g (fun l => strictB (K (Nat.add (Nat.mul g j) l)) (fun q => bAnd(Nat.blt q c,
    bAnd(bs.all (fun b => Nat.beq (pg w (mask w) (E (Nat.add o q)) b)
      (pg w (mask w) (GP l) (pg w (mask w) (E j) (pg w (mask w) (GIP l) b)))),
      bIf(Nat.beq q 0, true, bIf(lexLtK k l (P (Nat.add o q)) (L (Nat.add o q)), false, true)))))),
  bAnd(Nat.blt (S j) N, bAnd(Nat.blt (SI j) N, bAnd(Nat.beq (S (SI j)) j,
    bIf(Nat.blt (Nat.succ j) N, Nat.blt (E (S j)) (E (S (Nat.succ j))), true))))))))))))))))

variable {n w g N cap : Nat} {GP GIP CI E P L K S SI : Nat → Nat} {CS OFF bs : List Nat}

theorem repKB_facts {j : Nat} (h : repKB n w GP GIP g CS OFF CI E P L K S SI N cap bs j = true) :
    CI j < CS.length ∧ lget OFF (CI j) ≤ j ∧ j - lget OFF (CI j) < lget CS (CI j) ∧
      canonK n w (mask w) (n * w) (E j) = true ∧
      (j - lget OFF (CI j) ≠ 0 → P j < j - lget OFF (CI j) ∧ L j < g ∧
        cj n w GP GIP (L j) (E (lget OFF (CI j) + P j)) = E j) ∧
      ∀ l < g, K (g * j + l) < lget CS (CI j) ∧
        bs.all (fun b => Nat.beq (pg w (mask w) (E (lget OFF (CI j) + K (g * j + l))) b)
          (pg w (mask w) (GP l) (pg w (mask w) (E j) (pg w (mask w) (GIP l) b)))) = true := by
  unfold repKB at h
  have e1 : ∀ a b : Nat, Nat.add a b = a + b := fun _ _ => rfl
  have e2 : ∀ a b : Nat, Nat.mul a b = a * b := fun _ _ => rfl
  have e3 : ∀ a b : Nat, Nat.sub a b = a - b := fun _ _ => rfl
  simp only [PF.strictB_eqP, bAnd_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq, e1, e2, e3,
    Nat.succ_eq_add_one] at h
  obtain ⟨h1, h2, h3, -, h5, h6, -, h8, -⟩ := h
  refine ⟨h1, h2, h3, h5, fun hk => ?_, fun l hl => ?_⟩
  · have hk0 : Nat.beq (j - lget OFF (CI j)) 0 = false := by
      cases e : Nat.beq (j - lget OFF (CI j)) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hk
    simp only [hk0, bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h6
    exact h6
  · have := allN_spec h8 l hl
    simp only [bAnd_iff, Nat.blt_eq] at this
    exact ⟨this.1, this.2.1⟩

theorem getD_mem_closure {m : Nat} (T : List (Equiv.Perm (Fin m))) (i : Nat) :
    T.getD i 1 ∈ Subgroup.closure {x | x ∈ T} := by
  by_cases hi : i < T.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact Subgroup.subset_closure (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Subgroup.one_mem _

theorem evalCodes_mem_closure {m : Nat} (T : List (Equiv.Perm (Fin m))) :
    ∀ wd : List Int, evalCodes T wd ∈ Subgroup.closure {x | x ∈ T}
  | [] => Subgroup.one_mem _
  | z :: wd => by
    rw [evalCodes]
    refine Subgroup.mul_mem _ ?_ (evalCodes_mem_closure T wd)
    split
    · exact getD_mem_closure T _
    · exact Subgroup.inv_mem _ (getD_mem_closure T _)

theorem getD_map_evalCodes_mem {m : Nat} (T : List (Equiv.Perm (Fin m))) (W : List (List Int))
    (i : Nat) : (W.map (evalCodes T)).getD i 1 ∈ Subgroup.closure {x | x ∈ T} := by
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    exact evalCodes_mem_closure T _
  · rw [List.getD_eq_default _ _ (by simpa using hi)]
    exact Subgroup.one_mem _

section Base

variable {H : Subgroup (Equiv.Perm (Fin n))} {gs reps : List (Equiv.Perm (Fin n))}

theorem pg_of_img {y : Equiv.Perm (Fin n)} {Y : Nat} (hy : imageList y = (unpack n w Y).toList)
    (i : Fin n) : ((y i : Fin n) : Nat) = pg w (mask w) Y i := by
  have hl : i.val < (imageList y).length := by simp [imageList]
  have e := List.getElem_of_eq hy hl
  simpa [imageList, unpack] using e

theorem eq_of_base_pg (hF : BaseFaithful H bs) {x z : Equiv.Perm (Fin n)} (hx : x ∈ H) (hz : z ∈ H)
    {X Z : Nat} (hX : imageList x = (unpack n w X).toList)
    (hZ : imageList z = (unpack n w Z).toList) (hw : 0 < w) (hX0 : X >>> (n * w) = 0)
    (hZ0 : Z >>> (n * w) = 0)
    (hb : ∀ b ∈ bs, b < n → pg w (mask w) X b = pg w (mask w) Z b) : X = Z := by
  have hxz : x = z := by
    refine inv_mul_eq_one.mp (hF (x⁻¹ * z) (H.mul_mem (H.inv_mem hx) hz) fun i hi => ?_)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [pg_of_img hZ, pg_of_img hX]
    exact (hb _ hi i.isLt).symm
  subst hxz
  refine PF.eq_of_fields hw hX0 hZ0 fun i hi => ?_
  rw [← pg_of_img hX ⟨i, hi⟩, ← pg_of_img hZ ⟨i, hi⟩]

variable (hsz : szOK n w = true)
    (hg : ∀ l < g, imageList (gs.getD l 1) = (unpack n w (GP l)).toList ∧ gs.getD l 1 ∈ H)
    (hp : ∀ l < g, permOK n w (mask w) (n * w) (GP l) (GIP l) = true)
    (hri : ∀ i < CS.length,
      imageList (reps.getD i 1) = (unpack n w (E (lget OFF i))).toList ∧ reps.getD i 1 ∈ H)
    (h : ∀ j < N, repKB n w GP GIP g CS OFF CI E P L K S SI N cap bs j = true)
include hsz hg hp hri h

theorem mem_of_repKB : ∀ j < N, ∃ x ∈ H, imageList x = (unpack n w (E j)).toList := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨h1, h2, -, -, h5, -⟩ := repKB_facts (h j hj)
    by_cases hk : j - lget OFF (CI j) = 0
    · have e : E j = E (lget OFF (CI j)) := congrArg E (by omega)
      obtain ⟨hr, hm⟩ := hri _ h1
      exact ⟨_, hm, e ▸ hr⟩
    · obtain ⟨hP, hL, hc⟩ := h5 hk
      obtain ⟨y, hy, hyi⟩ := ih (lget OFF (CI j) + P j) (by omega) (by omega)
      obtain ⟨hgi, hgm⟩ := hg (L j) hL
      refine ⟨gs.getD (L j) 1 * y * (gs.getD (L j) 1)⁻¹,
        H.mul_mem (H.mul_mem hgm hy) (H.inv_mem hgm), ?_⟩
      rw [← hc]
      exact mulK_rep hsz (mulK_rep hsz hgi hyi) (invK_rep hgi (hp _ hL))

theorem repK_of_repKB
    (hgc : ∀ l < g, canonK n w (mask w) (n * w) (GP l) = true ∧
      canonK n w (mask w) (n * w) (GIP l) = true)
    (hoff : offOK CS OFF N = true) (hF : BaseFaithful H bs) :
    ∀ j < N, repK n w GP GIP g CS OFF CI E P L K S SI N cap j = true := by
  have hM := mem_of_repKB hsz hg hp hri h
  obtain ⟨ho, hs⟩ := offOK_facts hoff
  intro j hj
  obtain ⟨h1, -, -, -, -, h6⟩ := repKB_facts (h j hj)
  have key : ∀ l < g, E (lget OFF (CI j) + K (g * j + l)) = cj n w GP GIP l (E j) := by
    intro l hl
    obtain ⟨hq, hb⟩ := h6 l hl
    have hN : lget OFF (CI j) + K (g * j + l) < N := by
      have := sum_take_le CS (CI j + 1)
      rw [sum_take_succ' CS h1] at this
      rw [lget_eq CS] at hq
      rw [ho _ h1]
      omega
    obtain ⟨x, hx, hxi⟩ := hM _ hN
    obtain ⟨y, hy, hyi⟩ := hM j hj
    obtain ⟨hgi, hgm⟩ := hg l hl
    have hzi := mulK_rep hsz (mulK_rep hsz hgi hyi) (invK_rep hgi (hp l hl))
    obtain ⟨hn24, hw, hX0, -⟩ := PF.canon_facts (repKB_facts (h _ hN)).2.2.2.1
    obtain ⟨-, -, -, hGr⟩ := PF.canon_facts (hgc l hl).2
    have hn : n < 2 ^ 32 := by omega
    refine eq_of_base_pg hF hx (H.mul_mem (H.mul_mem hgm hy) (H.inv_mem hgm)) hxi hzi (PF.w_pos hw)
      hX0 (PF.pcomp_shr _ _ hn (PF.w_pos hw)) fun b hb' hbn => ?_
    rw [List.all_eq_true] at hb
    unfold cj
    rw [Nat.eq_of_beq_eq_true (hb b hb'), PF.pg_pcomp hn hbn, PF.pg_pcomp hn (hGr b hbn)]
  have hB := h j hj
  unfold repKB at hB
  unfold repK
  simp only [PF.strictB_eqP, bAnd_iff] at hB ⊢
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hB
  refine ⟨b1, b2, b3, b4, b5, b6, b7, CFSG.KC.BfsPin.allN_intro fun l hl => ?_, b9⟩
  have hl' := allN_spec b8 l hl
  simp only [bAnd_iff] at hl' ⊢
  refine ⟨hl'.1, ?_, hl'.2.2⟩
  simp only [Nat.beq_eq]
  exact key l hl

end Base

end CFSG.KC.Child3

end
