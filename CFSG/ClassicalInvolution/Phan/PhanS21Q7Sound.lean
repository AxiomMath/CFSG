module

public import CFSG.ClassicalInvolution.Phan.PhanS21Q7SoundC
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7SoundD

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.Q

@[expose] def repVec (i : ℕ) : V7 :=
  ⟨gfDec (q7RepsData[i]!)[3]!, gfDec (q7RepsData[i]!)[4]!, gfDec (q7RepsData[i]!)[5]!,
    gfDec (q7RepsData[i]!)[6]!, gfDec (q7RepsData[i]!)[7]!, gfDec (q7RepsData[i]!)[8]!,
    gfDec (q7RepsData[i]!)[9]!⟩

theorem repVec_eq (i : ℕ) : repVec i = (rowN q7RepsData[i]!).dec := rfl

theorem colN_symm {x y : N7} (h : colN x y = true) : colN y x = true := by
  rw [colN_iff, ← col_toVec] at h ⊢
  exact Col.symm m0 h

theorem mem_q7Pts {c p : N7} (hp : p ∈ q7Pts c) :
    isFFN p = true ∧ colN e0N p = true ∧ colN c p = true := by
  unfold q7Pts at hp
  have h := (List.mem_filter.1 hp).2
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

noncomputable def ptN (A : FFPt m0) (p : N7) : FFPt m0 :=
  if h : isFFN p = true then FFPt.mk m0 ((isFF_toVec p.dec).2 ((isFFN_iff p).1 h)) else A

theorem ptN_rep (A : FFPt m0) {p : N7} (hp : isFFN p = true) :
    ∃ w : GF49, w ≠ 0 ∧ (ptN A p).1.rep = w • toVec p.dec := by
  have h : ptN A p = FFPt.mk m0 ((isFF_toVec p.dec).2 ((isFFN_iff p).1 hp)) := by
    unfold ptN
    split
    · rfl
    · contradiction
  rw [h]
  exact FFPt.mk_rep m0 _

theorem eq_ptN_of_rep (A : FFPt m0) {p : N7} (hp : isFFN p = true) {B : FFPt m0} {w : GF49}
    (hw : w ≠ 0) (h : B.1.rep = w • toVec p.dec) : B = ptN A p := by
  obtain ⟨c, hc, hrep⟩ := ptN_rep A hp
  rw [ffPt_eq_iff]
  refine ⟨w * c⁻¹, mul_ne_zero hw (inv_ne_zero hc), ?_⟩
  rw [hrep, h, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem adj_iff_colC {X Y : FFPt m0} {s t : GF49} {x y : V7} (hs : s ≠ 0) (ht : t ≠ 0)
    (hX : X.1.rep = s • toVec x) (hY : Y.1.rep = t • toVec y) :
    (ffGraph m0).Adj X Y ↔ colC x y = true := by
  show Col m0 X.1.rep Y.1.rep ↔ _
  rw [hX, hY, col_smul m0 hs ht, col_toVec]

theorem exists_pt_of_adj {cN : N7} (hc3 : cN.x3 = 1) {A C B : FFPt m0} {s t : GF49} (hs : s ≠ 0)
    (ht : t ≠ 0) (hA : A.1.rep = s • toVec e0C) (hC : C.1.rep = t • toVec cN.dec)
    (hAB : (ffGraph m0).Adj A B) (hCB : (ffGraph m0).Adj C B) :
    ∃ p ∈ q7Pts cN, B = ptN A p := by
  obtain ⟨bV, hbV⟩ : ∃ bV : V7, toVec bV = B.1.rep := ⟨ofVec B.1.rep, toVec_ofVec _⟩
  have hB : B.1.rep = (1 : GF49) • toVec bV := by rw [hbV, one_smul]
  have hb : isFFC bV = true := (isFF_toVec bV).1 (by rw [hbV]; exact B.2)
  have h0 : colC e0C bV = true := (adj_iff_colC hs one_ne_zero hA hB).1 hAB
  have hc : colC cN.dec bV = true := (adj_iff_colC ht one_ne_zero hC hB).1 hCB
  obtain ⟨u, p, hu, hp, hpb⟩ := exists_mem_pts hc3 hb h0 hc
  refine ⟨p, hp, eq_ptN_of_rep A (mem_q7Pts hp).1 (w := u⁻¹) (inv_ne_zero hu) ?_⟩
  rw [hpb, toVec_smulC, smul_smul, inv_mul_cancel₀ hu, one_smul, hB, one_smul]

theorem q7MuCheck_sound (h : q7MuCheck = true) {i : ℕ} (hi : i < q7RepsData.size)
    {A C : FFPt m0} (hA : ∃ s : GF49, s ≠ 0 ∧ A.1.rep = s • toVec e0C)
    (hC : ∃ t : GF49, t ≠ 0 ∧ C.1.rep = t • toVec (repVec i)) : MuConnectedAt m0 A C := by
  have hrow : q7RowCheck q7RepsData[i] = true := Array.all_eq_true.1 h i hi
  have hget : q7RepsData[i]! = q7RepsData[i] := getElem!_pos q7RepsData i hi
  rw [repVec_eq, hget] at hC
  unfold q7RowCheck at hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨⟨hc3, _⟩, hbfs⟩ := hrow
  obtain ⟨s, hs, hAs⟩ := hA
  obtain ⟨t, ht, hCt⟩ := hC
  have hL := bfsOk_sound colN (fun _ _ => colN_symm) hbfs
  intro B D hAB hCB hAD hCD
  obtain ⟨p, hp, rfl⟩ := exists_pt_of_adj hc3 hs ht hAs hCt hAB hCB
  obtain ⟨q, hq, rfl⟩ := exists_pt_of_adj hc3 hs ht hAs hCt hAD hCD
  refine Relation.ReflTransGen.lift (ptN A) (fun x y hxy => ?_) p q (hL p hp q hq)
  obtain ⟨hx, hy, hxy⟩ := hxy
  obtain ⟨hxff, hxe, hxc⟩ := mem_q7Pts hx
  obtain ⟨hyff, hye, hyc⟩ := mem_q7Pts hy
  obtain ⟨wx, hwx, hrx⟩ := ptN_rep A hxff
  obtain ⟨wy, hwy, hry⟩ := ptN_rep A hyff
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (adj_iff_colC hwx hwy hrx hry).2 ((colN_iff x y).1 hxy)
  · exact (adj_iff_colC hs hwx hAs hrx).2 (by rw [← e0N_dec]; exact (colN_iff _ _).1 hxe)
  · exact (adj_iff_colC hs hwy hAs hry).2 (by rw [← e0N_dec]; exact (colN_iff _ _).1 hye)
  · exact (adj_iff_colC ht hwx hCt hrx).2 ((colN_iff _ _).1 hxc)
  · exact (adj_iff_colC ht hwy hCt hry).2 ((colN_iff _ _).1 hyc)

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
