module

public import CFSG.Certificates.Kernel.SporSch.ChainKRepsL
public import Certificates.Data.Kernel.Spor.MClsQ

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.KS.Mathieu
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ClsSpec

variable {n w : Nat}

theorem recPos_sound (nw pm S c q x : Nat) (h : recPos nw pm S c q x < c) :
    blk S nw pm (recPos nw pm S c q x) = x := by
  unfold recPos at h ⊢
  simp only [Orb.nIf_eq, beq_dec, decide_eq_true_eq] at h ⊢
  split_ifs at h ⊢ with e
  · exact e
  · omega

theorem clsOKQ_facts {A Ai B Bi mx cap R qw : Nat} {BlL P Lb QA QB QT SL : List Nat}
    (hBl : ∀ x ∈ BlL, x < 2 ^ (n * w)) (hS : ∀ x ∈ SL, x < 2 ^ (n * w))
    (hP : ∀ x ∈ P, x < 2 ^ qw) (hLb : ∀ x ∈ Lb, x < 2 ^ qw) (hQA : ∀ x ∈ QA, x < 2 ^ qw)
    (hQB : ∀ x ∈ QB, x < 2 ^ qw) (hQT : ∀ x ∈ QT, x < 2 ^ qw)
    (h : clsOKQ n w (mask w) (n * w) (mask (n * w)) A Ai B Bi mx cap R (packL (n * w) BlL) qw
      (mask qw) (packL qw P) (packL qw Lb) (packL qw QA) (packL qw QB) (packL qw QT)
      (packL (n * w) SL) (lenN SL) = true) :
    SL.length ≤ cap ∧ ordC n w (mask w) R = mx ∧ BlL.getD 0 0 = R ∧
      (∀ k, k + 1 < SL.length → SL.getD k 0 < SL.getD (k + 1) 0) ∧
      (∀ k < SL.length, recPos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (QA.getD k 0)
          (conjK n w (mask w) A Ai (SL.getD k 0)) < SL.length ∧
        recPos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (QB.getD k 0)
          (conjK n w (mask w) B Bi (SL.getD k 0)) < SL.length) ∧
      (∀ k < SL.length, k ≠ 0 → P.getD k 0 < k ∧
        BlL.getD k 0 = if Lb.getD k 0 = 0 then conjK n w (mask w) A Ai (BlL.getD (P.getD k 0) 0)
          else conjK n w (mask w) B Bi (BlL.getD (P.getD k 0) 0)) ∧
      ((List.range SL.length).foldl (fun M k => mstep SL.length (fun k =>
        recPos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (QT.getD k 0) (BlL.getD k 0))
          k M) 0) >>> SL.length = 0 := by
  unfold clsOKQ at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h6, h8, h9, h10⟩ := h
  rw [lenN_eq'] at h1 h6 h8 h9 h10
  simp only [blk_packL hBl, blk_packL hS, blk_packL hP, blk_packL hLb, blk_packL hQA,
    blk_packL hQB, blk_packL hQT] at h3 h6 h8 h9 h10
  refine ⟨Nat.ble_eq.mp h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    fun k hk => ?_, fun k hk => ?_, fun k hk hk0 => ?_, ?_⟩
  · have := allN_iff.1 h6 k (by change k < SL.length - 1; omega)
    simpa [Nat.blt_eq] using this
  · have := allN_iff.1 h8 k hk
    simp only [Orb.strictB_eq, Bool.and_eq_true, Nat.blt_eq] at this
    exact this
  · have := allN_iff.1 h9 k hk
    simp only [Orb.bIf_eq, Orb.strictB_eq, Bool.and_eq_true, beq_dec,
      decide_eq_true_eq, hk0, ↓reduceIte, Nat.blt_eq, Orb.nIf_eq] at this
    exact this
  · have e := Nat.eq_of_beq_eq_true h10
    rw [Orb.shr_eq, foldUp_eq] at e
    rw [Nat.shiftRight_eq_div_pow]
    refine (congrArg (· / 2 ^ SL.length)
      (congrArg (fun f => (List.range SL.length).foldl f 0) ?_)).trans e
    funext M k
    simp only [Orb.strictN_eq, Orb.nIf_eq, Orb.bIf_eq, hasBit_eq, mstep]
    by_cases ha : recPos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length (QT.getD k 0)
      (BlL.getD k 0) < SL.length <;>
    by_cases hb : M.testBit (recPos (n * w) (mask (n * w)) (packL (n * w) SL) SL.length
      (QT.getD k 0) (BlL.getD k 0)) = true <;>
    simp_all

section Datum

variable {gA gB : Equiv.Perm (Fin n)} {A Ai B Bi : Nat} (hn : n < 2 ^ 32) (hw : 0 < w)
  (pA : PRep n w A gA) (pAi : PRep n w Ai gA⁻¹) (pB : PRep n w B gB) (pBi : PRep n w Bi gB⁻¹)
  {mx cap R qw : Nat} {BlL P Lb QA QB QT SL : List Nat} (hBl : ∀ x ∈ BlL, x < 2 ^ (n * w))
  (hS : ∀ x ∈ SL, x < 2 ^ (n * w))
  (hP : ∀ x ∈ P, x < 2 ^ qw) (hLb : ∀ x ∈ Lb, x < 2 ^ qw) (hQA : ∀ x ∈ QA, x < 2 ^ qw)
  (hQB : ∀ x ∈ QB, x < 2 ^ qw) (hQT : ∀ x ∈ QT, x < 2 ^ qw)
  (hc : clsOKQ n w (mask w) (n * w) (mask (n * w)) A Ai B Bi mx cap R (packL (n * w) BlL) qw
    (mask qw) (packL qw P) (packL qw Lb) (packL qw QA) (packL qw QB) (packL qw QT)
    (packL (n * w) SL) (lenN SL) = true)
  {r : Equiv.Perm (Fin n)} (pR : PRep n w R r) (hpos : 0 < SL.length)
include hn hw pA pAi pB pBi hBl hS hP hLb hQA hQB hQT hc pR hpos

theorem list_classQ :
    (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard = SL.length ∧
    ∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
        ∃ k < SL.length, PRep n w (SL.getD k 0) z := by
  set K := Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))
  set c := SL.length
  obtain ⟨-, -, h0, hinc1, hcl, htree, hmask⟩ := clsOKQ_facts hBl hS hP hLb hQA hQB hQT hc
  have hAK : gA ∈ K := Subgroup.subset_closure (by simp)
  have hBK : gB ∈ K := Subgroup.subset_closure (by simp)
  have hBLc : ∀ k < c, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r,
      PRep n w (BlL.getD k 0) z := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        refine ⟨r, ⟨1, K.one_mem, by simp⟩, ?_⟩
        rw [h0]
        exact pR
      · obtain ⟨hp, he⟩ := htree k hk hk0
        obtain ⟨z, hz, pz⟩ := ih _ hp (by omega)
        rw [he]
        split
        · exact ⟨gA * z * gA⁻¹, conj_mem_conjClass hAK hz, prep_conjK hn pA pAi pz⟩
        · exact ⟨gB * z * gB⁻¹, conj_mem_conjClass hBK hz, prep_conjK hn pB pBi pz⟩
  set q : Nat → Nat := fun k =>
    recPos (n * w) (mask (n * w)) (packL (n * w) SL) c (QT.getD k 0) (BlL.getD k 0)
  have hq := mask_facts hmask
  have hqv : ∀ k < c, SL.getD (q k) 0 = BlL.getD k 0 := fun k hk => by
    rw [← blk_packL hS]
    exact recPos_sound _ _ _ _ _ _ (hq k hk).1
  have hsurj : ∀ s < c, ∃ k < c, q k = s := by
    intro s hs
    let f : Fin c → Fin c := fun k => ⟨q k, (hq k k.2).1⟩
    have hf : Function.Injective f := fun a b e => by
      have e' : q a = q b := congrArg Fin.val e
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact absurd e' ((hq b b.2).2 a h)
      · exact Fin.ext h
      · exact absurd e'.symm ((hq a a.2).2 b h)
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨s, hs⟩
    exact ⟨k, k.2, congrArg Fin.val hk⟩
  have hSc : ∀ s < c, ∃ z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r,
      PRep n w (SL.getD s 0) z := by
    intro s hs
    obtain ⟨k, hk, rfl⟩ := hsurj s hs
    rw [hqv k hk]
    exact hBLc k hk
  have hshr : ∀ s, SL.getD s 0 >>> (n * w) = 0 := fun s => shr_of_lt (getD_lt hS s)
  have hinc := lt_of_consec (c := c) (ST := fun k => SL.getD k 0) hinc1
  have hmem : ∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass K r ↔
      ∃ k < c, PRep n w (SL.getD k 0) z := by
    intro z
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine conj_closed (S := {z | ∃ k < c, PRep n w (SL.getD k 0) z}) ?_ g hg r
        ⟨q 0, (hq 0 hpos).1, by rw [hqv 0 hpos, h0]; exact pR⟩
      rintro g' hg' z ⟨k, hk, pz⟩
      obtain ⟨hmA, hmB⟩ := hcl k hk
      rcases hg' with rfl | hg'
      · have e := recPos_sound _ _ _ _ _ _ hmA
        rw [blk_packL hS] at e
        exact ⟨_, hmA, by rw [e]; exact prep_conjK hn pA pAi pz⟩
      · rw [Set.mem_singleton_iff] at hg'
        subst hg'
        have e := recPos_sound _ _ _ _ _ _ hmB
        rw [blk_packL hS] at e
        exact ⟨_, hmB, by rw [e]; exact prep_conjK hn pB pBi pz⟩
    · rintro ⟨k, hk, pz⟩
      obtain ⟨z', hz', pz'⟩ := hSc k hk
      rw [prep_unique pz pz']
      exact hz'
  refine ⟨?_, hmem⟩
  refine Set.ncard_eq_of_bijective (fun k hk => Classical.choose (hSc k hk))
    (fun z hz => ?_) (fun k hk => (Classical.choose_spec (hSc k hk)).1) (fun i j hi hj e => ?_)
  · obtain ⟨k, hk, pz⟩ := (hmem z).1 hz
    exact ⟨k, hk, prep_unique (Classical.choose_spec (hSc k hk)).2 pz⟩
  · have p1 := (Classical.choose_spec (hSc i hi)).2
    have p2 := (Classical.choose_spec (hSc j hj)).2
    rw [e] at p1
    have eq : SL.getD i 0 = SL.getD j 0 := PF.eq_of_fields hw (hshr i) (hshr j) fun t ht => by
      rw [p1 ⟨t, ht⟩, p2 ⟨t, ht⟩]
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd eq (Nat.ne_of_lt (hinc i j h hj))
    · exact h
    · exact absurd eq (Nat.ne_of_gt (hinc j i h hi))

end Datum

theorem clsOneQ_eq (n w : Nat) (tA tB : List Nat) (mx cap qw : Nat) (QA QB QT : List Nat)
    (a b R : Nat) (BlL P Lb SL : List Nat) :
    clsOneQ n w tA tB mx cap qw QA QB QT (a, b, R, BlL, P, Lb, SL) =
      (allLtN (Nat.shiftLeft 1 (n * w)) BlL && allLtN (Nat.shiftLeft 1 (n * w)) SL &&
        allLtN (Nat.shiftLeft 1 qw) P && allLtN (Nat.shiftLeft 1 qw) Lb &&
        allLtN (Nat.shiftLeft 1 qw) QA && allLtN (Nat.shiftLeft 1 qw) QB &&
        allLtN (Nat.shiftLeft 1 qw) QT &&
        clsOKQ n w (mask w) (n * w) (mask (n * w)) (packL w tA) (pinvS n w (mask w) (packL w tA))
          (packL w tB) (pinvS n w (mask w) (packL w tB)) mx cap R (packL (n * w) BlL) qw (mask qw)
          (packL qw P) (packL qw Lb) (packL qw QA) (packL qw QB) (packL qw QT) (packL (n * w) SL)
          (lenN SL)) := by
  unfold clsOneQ
  simp only [Orb.strictB_eq, bAnd_eq, Nat.mul_eq, Bool.and_assoc]

theorem datum_factsQ {gA gB : Equiv.Perm (Fin n)} {tA tB : List Nat} (hA : tA = imageList gA)
    (hB : tB = imageList gB) (hsz : szOK n w = true) {mx cap qw : Nat} {QA QB QT : List Nat}
    {d : ClassDatum} (hc : clsOneQ n w tA tB mx cap qw QA QB QT d = true)
    (hpos : 0 < d.2.2.2.2.2.2.length) {r : Equiv.Perm (Fin n)} (pR : PRep n w d.2.2.1 r) :
    (CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r).ncard =
        d.2.2.2.2.2.2.length ∧ d.2.2.2.2.2.2.length ≤ cap ∧ orderOf r = mx ∧
    (∀ z, z ∈ CFSG.Sporadic.SmallOddCore.conjClass
      (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n)))) r ↔
        ∃ k < d.2.2.2.2.2.2.length, PRep n w (d.2.2.2.2.2.2.getD k 0) z) ∧
    (∀ i j, i < j → j < d.2.2.2.2.2.2.length →
      d.2.2.2.2.2.2.getD i 0 < d.2.2.2.2.2.2.getD j 0) ∧
    (∀ x ∈ d.2.2.2.2.2.2, x < 2 ^ (n * w)) ∧ d.2.2.1 < 2 ^ (n * w) := by
  obtain ⟨a, b, R, BlL, P, Lb, SL⟩ := d
  simp only at hpos pR ⊢
  subst hA hB
  have hf := szOK_facts hsz
  have hn := szOK_lt hsz
  have hw := PF.w_pos hf.2
  have hwn : n < 2 ^ w := by omega
  have pA := (prep_packL (g := gA) hf.2).1
  have pB := (prep_packL (g := gB) hf.2).1
  rw [clsOneQ_eq] at hc
  simp only [Bool.and_eq_true, allLtN_iff, and_assoc] at hc
  obtain ⟨hBl, hS, hP, hLb, hQA, hQB, hQT, hc⟩ := hc
  have e : Nat.shiftLeft 1 (n * w) = 2 ^ (n * w) := by rw [Orb.shl_eq', Nat.one_mul]
  have eq : Nat.shiftLeft 1 qw = 2 ^ qw := by rw [Orb.shl_eq', Nat.one_mul]
  rw [e] at hBl hS
  rw [eq] at hP hLb hQA hQB hQT
  have hcl := list_classQ hn hw pA (prep_pinvS hwn pA).1 pB (prep_pinvS hwn pB).1 hBl hS hP hLb
    hQA hQB hQT hc pR hpos
  obtain ⟨h1, h2, h3, h4, -⟩ := clsOKQ_facts hBl hS hP hLb hQA hQB hQT hc
  refine ⟨hcl.1, h1, (orderOf_of_ordC pR).trans h2, hcl.2,
    lt_of_consec (c := SL.length) (ST := fun k => SL.getD k 0) h4, hS, ?_⟩
  rw [← h3]
  exact getD_lt hBl 0

end CFSG.KS.SporSch.MOC

end
