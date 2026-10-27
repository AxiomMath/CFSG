module

public import CFSG.Certificates.Kernel.GMS78RuCzJBasic
import CFSG.Certificates.Kernel.Census.XsProof
import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import Certificates.Data.GMS78RuCzRigidCheck

public section

namespace CFSG.KC.GMS.CzJ

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS
open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

structure TabHyps (GS : List Nat) (cP : CFSG.KC.Census.ArrCertP) (PT RW LK : Nat → Nat)
    (PAR LAB INV : Nat) : Prop where
  hP : kPoints GS PT cP = true
  hPt : ∀ i < 2048, kPointAt GS PT LK PAR LAB i = true
  hK : kKeys PT = true
  hC : kCols cP LK = true
  hPL : kParLab cP PAR LAB = true
  hR : ∀ a < 2048, kRow LK RW PAR LAB a = true
  hI : ∀ a < 2048, kInv RW INV a = true

variable {GS : List Nat} {cP : CFSG.KC.Census.ArrCertP} {PT RW LK : Nat → Nat} {PAR LAB INV : Nat}

private theorem fget7_lt (u i : Nat) : fget u i 7 < 128 := by
  rw [fget_eq']
  exact Nat.mod_lt _ (by norm_num)

private theorem at'_eq (u i : Nat) : CFSG.KC.Census.at' 7 u i = fget u i 7 := by
  show Nat.land (Nat.shiftRight u (Nat.mul 7 i)) (CFSG.KS.mask 7) =
    Nat.land (Nat.shiftRight u (Nat.mul i 7)) (maskN 7)
  have e : Nat.mul 7 i = Nat.mul i 7 := Nat.mul_comm 7 i
  rw [e]
  rfl

private theorem czUnpack_size (u : Nat) : (czUnpack u).size = 128 := by
  simp [czUnpack]

private theorem czUnpack_get (u : Nat) {i : Nat} (hi : i < 128) : (czUnpack u)[i]! = fget u i 7 := by
  rw [czUnpack, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ hi, fget_eq', Nat.shiftRight_eq_div_pow,
    Nat.mul_comm 7 i]
  rfl

private theorem pc_fget (p q : Nat) {i : Nat} (hi : i < 128) :
    fget (czPc p q) i 7 = fget p (fget q i 7) 7 := by
  rw [← at'_eq, ← at'_eq, ← at'_eq]
  exact CFSG.KS.PackFld.pg_pcomp (by norm_num) hi

private theorem pid_fget {i : Nat} (hi : i < 128) : fget (CFSG.KC.Census.pid 128 7) i 7 = i := by
  have h := (CFSG.KC.Census.SP.pid_good_of_le (n := 128) (w := 7) (by norm_num) (by norm_num)).1
  have h2 : (CFSG.KC.Census.unpackP 128 7 (CFSG.KC.Census.pid 128 7))[i]! =
      (CFSG.Monster.B.Co2.Native.idA 128)[i]! := by rw [h]
  rw [CFSG.KC.Census.SP.unpackP_get, if_pos hi, at'_eq, CFSG.Monster.B.Co2.idA_get hi] at h2
  exact h2

private theorem pvalid_inj {u : Nat} (h : CFSG.KC.Census.pvalid 128 7 u = true) :
    ∀ i < 128, ∀ j < 128, fget u i 7 = fget u j 7 → i = j := by
  intro i hi j hj e
  rw [← at'_eq, ← at'_eq] at e
  exact (CFSG.KC.Census.inj_of_pvalid h).2 i hi j hj e

private theorem arr_ext128 {a b : Array Nat} (ha : a.size = 128) (hb : b.size = 128)
    (h : ∀ i < 128, a[i]! = b[i]!) : a = b := by
  refine Array.ext (ha.trans hb.symm) fun i h1 h2 => ?_
  have := h i (ha ▸ h1)
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

private theorem czUnpack_pc (p q : Nat) :
    czUnpack (czPc p q) = CFSG.Monster.B.Co2.Native.compA 128 (czUnpack p) (czUnpack q) := by
  refine arr_ext128 (czUnpack_size _) (by simp [CFSG.Monster.B.Co2.Native.compA]) fun i hi => ?_
  rw [CFSG.Monster.B.Co2.compA_get hi, czUnpack_get _ hi, czUnpack_get _ hi,
    czUnpack_get _ (fget7_lt _ _), pc_fget _ _ hi]

private theorem czUnpack_pid :
    czUnpack (CFSG.KC.Census.pid 128 7) = CFSG.Monster.B.Co2.Native.idA 128 := by
  refine arr_ext128 (czUnpack_size _) (by simp [CFSG.Monster.B.Co2.Native.idA]) fun i hi => ?_
  rw [CFSG.Monster.B.Co2.idA_get hi, czUnpack_get _ hi, pid_fget hi]

private theorem validA_czUnpack {u : Nat} (h : CFSG.KC.Census.pvalid 128 7 u = true) :
    validA 128 (czUnpack u) = true := by
  unfold validA
  apply CFSG.KC.Co2Mem.isInvA_invCand
  · intro i hi
    rw [czUnpack_get _ hi]
    exact fget7_lt _ _
  · intro i j hi hj e
    rw [czUnpack_get _ hi, czUnpack_get _ hj] at e
    exact pvalid_inj h i hi j hj e

private theorem keyA_czUnpack (u : Nat) : keyA 128 [0, 5, 3] (czUnpack u) = czKey u := by
  show _ = fget u 0 7 + (128 * fget u 5 7 + 16384 * fget u 3 7)
  simp only [keyA, List.map_cons, List.map_nil, Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.cast_id,
    czUnpack_get u (show 0 < 128 by norm_num), czUnpack_get u (show 5 < 128 by norm_num),
    czUnpack_get u (show 3 < 128 by norm_num)]
  omega

private theorem kPoints_parse (h : kPoints GS PT cP = true) :
    cP.pts.size = 2048 ∧ (∀ g ∈ GS, CFSG.KC.Census.pvalid 128 7 g = true) ∧ GS.length = 6 ∧
      ∀ j < 2048, cP.pts[j]! = PT j := by
  unfold kPoints at h
  simp only [andB_iff, neLen_eq, Nat.beq_eq, neAllL_iff, Array.length_toList] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj => ?_⟩
  have := czPtsK_spec h4 j (by simp only [Array.length_toList]; omega)
  rw [Nat.zero_add] at this
  rw [this, getElem!_pos cP.pts j (by omega)]
  simp

private theorem kCols_parse (h : kCols cP LK = true) :
    cP.edges.size = 2048 ∧ ∀ i < 2048, cP.edges[i]!.size = 6 ∧
      ∀ k < 6, cP.edges[i]!.getD k 0 = fget (LK k) i 11 := by
  unfold kCols at h
  simp only [andB_iff, neLen_eq, Nat.beq_eq, Array.length_toList] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun i hi => ?_⟩
  have := czColsK_spec h2 i (by simp only [Array.length_toList]; omega)
  simp only [Nat.zero_add, Array.getElem_toList] at this
  rw [getElem!_pos cP.edges i (by omega)]
  exact ⟨this.1, fun k hk => (this.2 k hk).symm⟩

private theorem kParLab_parse (h : kParLab cP PAR LAB = true) :
    (∀ i < 2048, cP.par[i]! = fget PAR i 11) ∧ ∀ i < 2048, cP.lab[i]! = fget LAB i 3 := by
  unfold kParLab at h
  simp only [andB_iff, neLen_eq, Nat.beq_eq, Array.length_toList] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := czFieldsK_spec h1 i (by simp only [Array.length_toList]; omega)
    rw [Nat.zero_add] at this
    rw [this, getElem!_pos cP.par i (by omega)]
    simp
  · have := czFieldsK_spec h2 i (by simp only [Array.length_toList]; omega)
    rw [Nat.zero_add] at this
    rw [this, getElem!_pos cP.lab i (by omega)]
    simp

private theorem kPointAt_parse {i : Nat} (h : kPointAt GS PT LK PAR LAB i = true) :
    CFSG.KC.Census.pvalid 128 7 (PT i) = true ∧
    (∀ k < 6, fget (LK k) i 11 < 2048 ∧ PT (fget (LK k) i 11) = czPc (GS.getD k 0) (PT i)) ∧
    ((i = 0 ∧ PT i = CFSG.KC.Census.pid 128 7) ∨
      (0 < i ∧ fget PAR i 11 < i ∧ fget LAB i 3 < 6 ∧
        PT i = czPc (GS.getD (fget LAB i 3) 0) (PT (fget PAR i 11)))) := by
  unfold kPointAt at h
  simp only [andB_iff, orB_iff, allN_iff', Nat.blt_eq, Nat.beq_eq, neGet_eq] at h
  exact h

private theorem kRow0_parse (h : kRow LK RW PAR LAB 0 = true) :
    ∀ b < 2048, fget (RW 0) b 11 = b := by
  have h' : allN 2048 (fun b => Nat.beq (fget (RW 0) b 11) b) = true := h
  intro b hb
  exact Nat.eq_of_beq_eq_true (allN_iff'.1 h' b hb)

private theorem kRow_parse {a : Nat} (ha : 0 < a) (h : kRow LK RW PAR LAB a = true) :
    ∀ b < 2048, fget (RW a) b 11 = fget (LK (fget LAB a 3)) (fget (RW (fget PAR a 11)) b 11) 11 := by
  have e : Nat.beq a 0 = false := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show a ≠ 0 by omega)
    rfl
  have h' : allN 2048 (fun b => Nat.beq (fget (RW a) b 11)
      (fget (LK (fget LAB a 3)) (fget (RW (fget PAR a 11)) b 11) 11)) = true := by
    unfold kRow at h
    rw [e] at h
    exact h
  intro b hb
  exact Nat.eq_of_beq_eq_true (allN_iff'.1 h' b hb)

private theorem kInv_parse {a : Nat} (h : kInv RW INV a = true) :
    fget (RW a) (fget INV a 11) 11 = 0 := by
  unfold kInv at h
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h.2

private structure Facts (GS : List Nat) (cP : CFSG.KC.Census.ArrCertP) (PT RW LK : Nat → Nat)
    (PAR LAB INV : Nat) : Prop where
  ptsSize : cP.pts.size = 2048
  gsValid : ∀ g ∈ GS, CFSG.KC.Census.pvalid 128 7 g = true
  gsLen : GS.length = 6
  pt : ∀ j < 2048, cP.pts[j]! = PT j
  edgesSize : cP.edges.size = 2048
  edgeRow : ∀ i < 2048, cP.edges[i]!.size = 6 ∧ ∀ k < 6, cP.edges[i]!.getD k 0 = fget (LK k) i 11
  par : ∀ i < 2048, cP.par[i]! = fget PAR i 11
  lab : ∀ i < 2048, cP.lab[i]! = fget LAB i 3
  valid : ∀ i < 2048, CFSG.KC.Census.pvalid 128 7 (PT i) = true
  edge : ∀ i < 2048, ∀ k < 6,
    fget (LK k) i 11 < 2048 ∧ PT (fget (LK k) i 11) = czPc (GS.getD k 0) (PT i)
  root : PT 0 = CFSG.KC.Census.pid 128 7
  tree : ∀ i < 2048, 0 < i → fget PAR i 11 < i ∧ fget LAB i 3 < 6 ∧
    PT i = czPc (GS.getD (fget LAB i 3) 0) (PT (fget PAR i 11))
  keys : ∀ i < 2048, ∀ j < 2048, czKey (PT i) = czKey (PT j) → i = j
  row0 : ∀ b < 2048, fget (RW 0) b 11 = b
  row : ∀ a < 2048, 0 < a → ∀ b < 2048,
    fget (RW a) b 11 = fget (LK (fget LAB a 3)) (fget (RW (fget PAR a 11)) b 11) 11
  inv : ∀ a < 2048, fget (RW a) (fget INV a 11) 11 = 0

private theorem facts (H : TabHyps GS cP PT RW LK PAR LAB INV) : Facts GS cP PT RW LK PAR LAB INV := by
  obtain ⟨p1, p2, p3, p4⟩ := kPoints_parse H.hP
  obtain ⟨c1, c2⟩ := kCols_parse H.hC
  obtain ⟨l1, l2⟩ := kParLab_parse H.hPL
  refine ⟨p1, p2, p3, p4, c1, c2, l1, l2, fun i hi => (kPointAt_parse (H.hPt i hi)).1,
    fun i hi => (kPointAt_parse (H.hPt i hi)).2.1, ?_, ?_, kKeys_spec H.hK,
    kRow0_parse (H.hR 0 (by norm_num)), fun a ha hpos => kRow_parse hpos (H.hR a ha),
    fun a ha => kInv_parse (H.hI a ha)⟩
  · rcases (kPointAt_parse (H.hPt 0 (by norm_num))).2.2 with h | h
    · exact h.2
    · exact absurd h.1 (lt_irrefl 0)
  · intro i hi hpos
    rcases (kPointAt_parse (H.hPt i hi)).2.2 with h | h
    · exact absurd h.1 (by omega)
    · exact h.2

private theorem sem (H : Facts GS cP PT RW LK PAR LAB INV) :
    ∀ a < 2048, ∀ b < 2048, ∀ x < 128,
      fget (PT (fget (RW a) b 11)) x 7 = fget (PT a) (fget (PT b) x 7) 7 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro ha b hb x hx
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · rw [H.row0 b hb, H.root, pid_fget (fget7_lt _ _)]
  · obtain ⟨hpa, hla, hPa⟩ := H.tree a ha hpos
    have he := fget11_lt (RW (fget PAR a 11)) b
    obtain ⟨-, hE⟩ := H.edge _ he _ hla
    rw [H.row a ha hpos b hb, hE, pc_fget _ _ hx, ih _ hpa (by omega) b hb x hx, hPa,
      pc_fget _ _ (fget7_lt (PT b) x)]

private theorem pt_ext (H : Facts GS cP PT RW LK PAR LAB INV) {i j : Nat} (hi : i < 2048)
    (hj : j < 2048) (h : ∀ x < 128, fget (PT i) x 7 = fget (PT j) x 7) : i = j := by
  refine H.keys i hi j hj ?_
  unfold czKey
  rw [h 0 (by norm_num), h 5 (by norm_num), h 3 (by norm_num)]

private theorem row_inj (H : Facts GS cP PT RW LK PAR LAB INV) {a i j : Nat} (ha : a < 2048)
    (hi : i < 2048) (hj : j < 2048) (e : fget (RW a) i 11 = fget (RW a) j 11) : i = j := by
  refine pt_ext H hi hj fun x hx => ?_
  have h := sem H a ha i hi x hx
  rw [e, sem H a ha j hj x hx] at h
  exact (pvalid_inj (H.valid a ha) _ (fget7_lt _ _) _ (fget7_lt _ _) h).symm


private def cU (cP : CFSG.KC.Census.ArrCertP) : ArrCert :=
  ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩

private def LU (cP : CFSG.KC.Census.ArrCertP) : Array (Array Nat) :=
  (Array.range 6).map (leftIdx 2048 (cU cP))

private theorem getD0 (a : Array Nat) (i : Nat) : a.getD i 0 = a[i]! := by
  rw [Array.getElem!_eq_getD]
  rfl

private theorem getDA (a : Array (Array Nat)) (i : Nat) : a.getD i #[] = a[i]! := by
  rw [Array.getElem!_eq_getD]
  rfl

private theorem tab_get (n : Nat) (f : Nat → Nat) {j : Nat} (hj : j < n) : (tab n f)[j]! = f j := by
  unfold tab
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

private theorem tab_get_ge (n : Nat) (f : Nat → Nat) {j : Nat} (hj : n ≤ j) : (tab n f)[j]! = 0 := by
  unfold tab
  rw [getElem!_neg _ j (by simpa using hj)]
  rfl

private theorem par_eq (H : Facts GS cP PT RW LK PAR LAB INV) {a : Nat} (ha : a < 2048) :
    ix (cU cP).par a = fget PAR a 11 := by
  show cP.par.getD a 0 = _
  rw [getD0, H.par a ha]

private theorem lab_eq (H : Facts GS cP PT RW LK PAR LAB INV) {a : Nat} (ha : a < 2048) :
    ix (cU cP).lab a = fget LAB a 3 := by
  show cP.lab.getD a 0 = _
  rw [getD0, H.lab a ha]

private theorem leftIdx_get (H : Facts GS cP PT RW LK PAR LAB INV) {k j : Nat} (hk : k < 6)
    (hj : j < 2048) : (leftIdx 2048 (cU cP) k)[j]! = fget (LK k) j 11 := by
  unfold leftIdx
  rw [tab_get _ _ hj]
  show (cP.edges.getD j #[]).getD k 0 = _
  rw [getDA]
  exact (H.edgeRow j hj).2 k hk

private theorem LU_getD {k : Nat} (hk : k < 6) : (LU cP).getD k #[] = leftIdx 2048 (cU cP) k := by
  rw [getDA]
  unfold LU
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

private theorem tabRow_size (c : ArrCert) (L : Array (Array Nat)) :
    ∀ f a, (tabRow 2048 c L f a).size = 2048 := by
  intro f
  induction f with
  | zero => intro a; simp [tabRow, CFSG.Monster.B.Co2.Native.idA]
  | succ f ih =>
    intro a
    by_cases h : a = 0
    · simp [tabRow, h, CFSG.Monster.B.Co2.Native.idA]
    · simp [tabRow, h, CFSG.Monster.B.Co2.Native.compA]

private theorem tabRow_get (H : Facts GS cP PT RW LK PAR LAB INV) :
    ∀ f a, a < 2048 → a < f → ∀ b < 2048,
      (tabRow 2048 (cU cP) (LU cP) f a)[b]! = fget (RW a) b 11 := by
  intro f
  induction f with
  | zero => intro a _ h; omega
  | succ f ih =>
    intro a ha hf b hb
    simp only [tabRow]
    by_cases h0 : a = 0
    · subst h0
      rw [if_pos rfl, CFSG.Monster.B.Co2.idA_get hb, H.row0 b hb]
    · rw [if_neg h0, CFSG.Monster.B.Co2.compA_get hb]
      have hpos : 0 < a := Nat.pos_of_ne_zero h0
      obtain ⟨hpa, hla, -⟩ := H.tree a ha hpos
      rw [par_eq H ha, lab_eq H ha, ih _ (by omega) (by omega) b hb, LU_getD hla,
        leftIdx_get H hla (fget11_lt _ _), H.row a ha hpos b hb]

private theorem tabOf_getD {a : Nat} (ha : a < 2048) :
    (tabOf 2048 (cU cP) 6).getD a #[] = tabRow 2048 (cU cP) (LU cP) 2048 a := by
  rw [getDA]
  show ((Array.range 2048).map fun a => tabRow 2048 (cU cP) (LU cP) 2048 a)[a]! = _
  rw [getElem!_pos _ a (by simpa using ha)]
  simp

private theorem tabOf_getD_ge {a : Nat} (ha : 2048 ≤ a) : (tabOf 2048 (cU cP) 6).getD a #[] = #[] := by
  rw [getDA]
  show ((Array.range 2048).map fun a => tabRow 2048 (cU cP) (LU cP) 2048 a)[a]! = _
  rw [getElem!_neg _ a (by simpa using ha)]
  rfl

private theorem mt_def (M : Array (Array Nat)) (a b : Nat) : mt M a b = (M.getD a #[]).getD b 0 :=
  rfl

private theorem ix_def (A : Array Nat) (k : Nat) : ix A k = A.getD k 0 := rfl

private theorem invOf_def (n : Nat) (M : Array (Array Nat)) :
    invOf n M = tab n fun a => ix (CFSG.Monster.B.Co2.Native.invCand n (M.getD a #[])) 0 := rfl

private theorem mt_eq' (H : Facts GS cP PT RW LK PAR LAB INV) {a b : Nat} (ha : a < 2048)
    (hb : b < 2048) : mt (tabOf 2048 (cU cP) 6) a b = fget (RW a) b 11 := by
  rw [mt_def, tabOf_getD ha, getD0, tabRow_get H 2048 a ha ha b hb]

private theorem mt_lt' (H : Facts GS cP PT RW LK PAR LAB INV) (a b : Nat) :
    mt (tabOf 2048 (cU cP) 6) a b < 2048 := by
  by_cases ha : a < 2048
  · by_cases hb : b < 2048
    · rw [mt_eq' H ha hb]
      exact fget11_lt _ _
    · rw [mt_def, tabOf_getD ha, getD0, getElem!_neg _ _ (by rw [tabRow_size]; omega)]
      show 0 < 2048
      norm_num
  · rw [mt_def, tabOf_getD_ge (by omega)]
    simp

private theorem inv_eq' (H : Facts GS cP PT RW LK PAR LAB INV) {a : Nat} (ha : a < 2048) :
    ix (invOf 2048 (tabOf 2048 (cU cP) 6)) a = fget INV a 11 := by
  rw [invOf_def, ix_def, getD0, tab_get _ _ ha, tabOf_getD ha, ix_def, getD0]
  have hb : ∀ i < 2048, (tabRow 2048 (cU cP) (LU cP) 2048 a)[i]! < 2048 := fun i hi => by
    rw [tabRow_get H 2048 a ha ha i hi]
    exact fget11_lt _ _
  have hi : ∀ i j, i < 2048 → j < 2048 → (tabRow 2048 (cU cP) (LU cP) 2048 a)[i]! =
      (tabRow 2048 (cU cP) (LU cP) 2048 a)[j]! → i = j := fun i j hi hj e => by
    rw [tabRow_get H 2048 a ha ha i hi, tabRow_get H 2048 a ha ha j hj] at e
    exact row_inj H ha hi hj e
  have := CFSG.KC.Co2Mem.invCand_spec hb hi (fget INV a 11) (fget11_lt _ _)
  rwa [tabRow_get H 2048 a ha ha _ (fget11_lt _ _), H.inv a ha] at this

private theorem inv_lt' (H : Facts GS cP PT RW LK PAR LAB INV) (a : Nat) :
    ix (invOf 2048 (tabOf 2048 (cU cP) 6)) a < 2048 := by
  by_cases ha : a < 2048
  · rw [inv_eq' H ha]
    exact fget11_lt _ _
  · rw [invOf_def, ix_def, getD0, tab_get_ge _ _ (by omega)]
    norm_num

private theorem tabI' (H : Facts GS cP PT RW LK PAR LAB INV) :
    TabI (tabOf 2048 (cU cP) 6) (invOf 2048 (tabOf 2048 (cU cP) 6)) (cU cP) RW PAR LAB INV :=
  ⟨fun _ ha _ hb => mt_eq' H ha hb, mt_lt' H, fun _ ha => inv_eq' H ha, inv_lt' H,
    fun _ ha => par_eq H ha, fun _ ha => lab_eq H ha, fun a ha hpos => (H.tree a ha hpos).1,
    fun a ha hpos => (H.tree a ha hpos).2.1⟩

private theorem gIdx_eq (H : Facts GS cP PT RW LK PAR LAB INV) {k : Nat} (hk : k < 6) :
    gIdx (cU cP) k = fget (LK k) 0 11 := by
  show (cP.edges.getD 0 #[]).getD k 0 = _
  rw [getDA]
  exact (H.edgeRow 0 (by norm_num)).2 k hk

private theorem gIdx_map (H : Facts GS cP PT RW LK PAR LAB INV) :
    (List.range 6).map (gIdx (cU cP)) = (List.range 6).map fun k => fget (LK k) 0 11 :=
  List.map_congr_left fun k hk => gIdx_eq H (List.mem_range.1 hk)

private theorem tree_rel (H : Facts GS cP PT RW LK PAR LAB INV) {a : Nat} (ha : a < 2048)
    (hpos : 0 < a) :
    mt (tabOf 2048 (cU cP) 6) (((List.range 6).map (gIdx (cU cP))).getD (ix (cU cP).lab a) 0)
      (ix (cU cP).par a) = a := by
  obtain ⟨hpa, hla, hPa⟩ := H.tree a ha hpos
  have eg : ((List.range 6).map (gIdx (cU cP))).getD (fget LAB a 3) 0 =
      fget (LK (fget LAB a 3)) 0 11 := by
    rw [List.getD_eq_getElem?_getD]
    simp [hla, gIdx_eq H hla]
  obtain ⟨hg, hPg⟩ := H.edge 0 (by norm_num) _ hla
  rw [lab_eq H ha, par_eq H ha, eg, mt_eq' H hg (by omega)]
  refine pt_ext H (fget11_lt _ _) ha fun x hx => ?_
  rw [sem H _ hg _ (by omega) x hx, hPg, H.root, hPa, pc_fget _ _ hx,
    pc_fget _ _ (fget7_lt _ _), pid_fget (fget7_lt _ _)]

private theorem tableOK' (H : Facts GS cP PT RW LK PAR LAB INV) :
    tableOK 2048 (cU cP) (tabOf 2048 (cU cP) 6) (invOf 2048 (tabOf 2048 (cU cP) 6))
      ((List.range 6).map (gIdx (cU cP))) = true := by
  unfold tableOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨?_, fun a ha => ?_⟩, fun a ha => ⟨inv_lt' H a, ?_⟩⟩
  · show (cP.pts.map czUnpack).size = 2048
    rw [Array.size_map, H.ptsSize]
  · rcases Nat.eq_zero_or_pos a with h | h
    · exact Or.inl h
    · exact Or.inr (tree_rel H ha h)
  · rw [inv_eq' H ha, mt_eq' H ha (fget11_lt _ _), H.inv a ha]


private theorem gs_get (H : Facts GS cP PT RW LK PAR LAB INV) {k : Nat} (hk : k < 6) :
    ((GS.map czUnpack).toArray)[k]! = czUnpack (GS.getD k 0) := by
  have hk' : k < GS.length := by rw [H.gsLen]; exact hk
  rw [getElem!_pos _ k (by simpa using hk'), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk']
  simp

private theorem gs_mem (H : Facts GS cP PT RW LK PAR LAB INV) {k : Nat} (hk : k < 6) :
    GS.getD k 0 ∈ GS := by
  have hk' : k < GS.length := by rw [H.gsLen]; exact hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  exact List.getElem_mem _

private theorem pts_get (H : Facts GS cP PT RW LK PAR LAB INV) {i : Nat} (hi : i < 2048) :
    (cU cP).pts[i]! = czUnpack (PT i) := by
  show (cP.pts.map czUnpack)[i]! = _
  rw [CFSG.KC.Census.SP.map_get czUnpack cP.pts (by rw [H.ptsSize]; exact hi), H.pt i hi]

private theorem edge_get (H : Facts GS cP PT RW LK PAR LAB INV) {i k : Nat} (hi : i < 2048)
    (hk : k < 6) : ((cU cP).edges[i]!)[k]! = fget (LK k) i 11 := by
  show (cP.edges[i]!)[k]! = _
  rw [← getD0]
  exact (H.edgeRow i hi).2 k hk

private theorem pts_size (H : Facts GS cP PT RW LK PAR LAB INV) : (cU cP).pts.size = 2048 := by
  show (cP.pts.map czUnpack).size = 2048
  rw [Array.size_map, H.ptsSize]

private theorem point_ok (H : Facts GS cP PT RW LK PAR LAB INV) {i : Nat} (hi : i < 2048) :
    arrPointOK (leftA 128 (GS.map czUnpack).toArray) ((GS.map czUnpack).toArray).size
      (validA 128) (cU cP) i = true := by
  have hs : ((GS.map czUnpack).toArray).size = 6 := by simp [H.gsLen]
  rw [hs]
  unfold arrPointOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, fun k hk => ?_⟩, ?_⟩
  · rw [pts_get H hi]
    exact validA_czUnpack (H.valid i hi)
  · exact (H.edgeRow i hi).1
  · obtain ⟨he, hPe⟩ := H.edge i hi k hk
    rw [edge_get H hi hk, pts_size H]
    refine ⟨he, ?_⟩
    rw [pts_get H he, pts_get H hi, hPe, czUnpack_pc]
    unfold leftA
    rw [gs_get H hk]
  · rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · right
      obtain ⟨hpa, hla, hPa⟩ := H.tree i hi h
      have ep : (cU cP).par[i]! = fget PAR i 11 := H.par i hi
      have el : (cU cP).lab[i]! = fget LAB i 3 := H.lab i hi
      rw [ep, el]
      refine ⟨⟨hpa, hla⟩, ?_⟩
      rw [pts_get H hi, pts_get H (by omega), hPa, czUnpack_pc]
      unfold leftA
      rw [gs_get H hla]

private theorem keys_ok (H : Facts GS cP PT RW LK PAR LAB INV) :
    (((cU cP).pts.toList.map (keyA 128 [0, 5, 3])).mergeSort
      (fun a b => decide (a ≤ b))).Pairwise (· < ·) := by
  have e : (cU cP).pts.toList.map (keyA 128 [0, 5, 3]) = cP.pts.toList.map czKey := by
    show (cP.pts.map czUnpack).toList.map _ = _
    rw [Array.toList_map, List.map_map]
    exact List.map_congr_left fun u _ => keyA_czUnpack u
  rw [e]
  have hnd : (cP.pts.toList.map czKey).Nodup := by
    rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij hk
    have hsz := H.ptsSize
    simp only [List.length_map, Array.length_toList] at hi hj
    simp only [List.getElem_map, Array.getElem_toList] at hk
    rw [← getElem!_pos cP.pts i hi, ← getElem!_pos cP.pts j hj, H.pt i (by omega),
      H.pt j (by omega)] at hk
    have := H.keys i (by omega) j (by omega) hk
    omega
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (cP.pts.toList.map czKey)
  have hn := (List.mergeSort_perm (cP.pts.toList.map czKey)
    (fun a b : Nat => decide (a ≤ b))).nodup_iff.2 hnd
  exact (hs.and hn).imp fun h => lt_of_le_of_ne (of_decide_eq_true h.1) h.2

private theorem enumOK' (H : Facts GS cP PT RW LK PAR LAB INV) :
    enumOK 128 (GS.map czUnpack).toArray [0, 5, 3] (cU cP) = true := by
  unfold enumOK arrCertOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨?_, ⟨⟨⟨?_, ?_⟩, fun i hi => point_ok H (by rw [← pts_size H]; exact hi)⟩, keys_ok H⟩⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    have hk6 : k < 6 := by simpa [H.gsLen] using hk
    rw [gs_get H hk6]
    exact validA_czUnpack (H.gsValid _ (gs_mem H hk6))
  · rw [pts_size H]
    norm_num
  · rw [pts_get H (by norm_num), H.root, czUnpack_pid]

theorem czJ_enumOK (H : TabHyps GS cP PT RW LK PAR LAB INV) :
    enumOK 128 (GS.map czUnpack).toArray [0, 5, 3]
      ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ = true :=
  enumOK' (facts H)

theorem czJ_tabI (H : TabHyps GS cP PT RW LK PAR LAB INV) :
    TabI (tabOf 2048 ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ 6)
      (invOf 2048 (tabOf 2048 ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ 6))
      ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ RW PAR LAB INV :=
  tabI' (facts H)

theorem czJ_gIdx (H : TabHyps GS cP PT RW LK PAR LAB INV) :
    (List.range 6).map (gIdx ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩) =
      (List.range 6).map fun k => fget (LK k) 0 11 :=
  gIdx_map (facts H)

theorem czJ_tableOK (H : TabHyps GS cP PT RW LK PAR LAB INV) :
    tableOK 2048 ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩
      (tabOf 2048 ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ 6)
      (invOf 2048 (tabOf 2048 ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩ 6))
      ((List.range 6).map (gIdx ⟨cP.pts.map czUnpack, cP.edges, cP.par, cP.lab⟩)) = true :=
  tableOK' (facts H)

end CFSG.KC.GMS.CzJ

end
