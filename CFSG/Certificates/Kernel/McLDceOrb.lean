module

public import CFSG.Certificates.Kernel.McLDcePsi
public import CFSG.Certificates.Kernel.DceTwCore

namespace CFSG.Certificates.McLD

open CFSG.KC CFSG.KC.McL.Mat

def GInv (ok : ℕ → Bool) (S : ℕ) : Prop := ∀ j, j + 1 < S → ok j = true

noncomputable def gInner (ok : ℕ → Bool) (n S : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun _ ih2 S => Loop.strictN (Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (Nat.succ S)
        (Th.andB (Nat.blt (nat_lit 0) S) (ok (Nat.sub S (nat_lit 1))))) ih2) n S

noncomputable def gRun (ok : ℕ → Bool) (Cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun S => S)
    (fun C _ ih S => Loop.strictN (gInner ok (Nat.land C (nat_lit 65535)) S) ih) Cs

theorem gInner_inv (ok : ℕ → Bool) : ∀ n S, GInv ok S → GInv ok (gInner ok n S)
  | 0, _, h => h
  | n + 1, S, h => by
    change GInv ok (Loop.strictN (Bool.rec (motive := fun _ => ℕ) 0 (Nat.succ S)
      (Th.andB (Nat.blt 0 S) (ok (Nat.sub S 1)))) (gInner ok n))
    rw [strictN_eq]
    apply gInner_inv ok n
    cases hc : Th.andB (Nat.blt 0 S) (ok (Nat.sub S 1))
    · intro k hk
      exact absurd hk (Nat.not_lt_zero _)
    · rw [andB_iff, Nat.blt_eq] at hc
      intro k hk
      change k + 1 < S + 1 at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h k hk
      · have e : k = Nat.sub S 1 := by
          change k = S - 1
          omega
        rw [e]
        exact hc.2

theorem gRun_inv (ok : ℕ → Bool) : ∀ (Cs : List ℕ) (S : ℕ), GInv ok S → GInv ok (gRun ok Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change GInv ok (Loop.strictN (gInner ok (Nat.land C 65535) S) (gRun ok Cs))
    rw [strictN_eq]
    exact gRun_inv ok Cs _ (gInner_inv ok _ _ h)

theorem runGom_eq (HB GB OB : ℕ → ℕ) (I0 nH : ℕ) (Cs : List ℕ) (S : ℕ) :
    McL.Dce.runGom HB GB OB I0 nH Cs S = gRun (McL.Dce.gomOK HB GB OB I0 nH) Cs S := rfl

public theorem runGom_ok {HB GB OB : ℕ → ℕ} {I0 nH NO : ℕ} {Cg : List ℕ}
    (h : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true) :
    ∀ j < NO, McL.Dce.gomOK HB GB OB I0 nH j = true := by
  have hi := gRun_inv (McL.Dce.gomOK HB GB OB I0 nH) Cg 1 (fun k hk => absurd hk (by omega))
  rw [← runGom_eq, Nat.eq_of_beq_eq_true h] at hi
  exact fun j hj => hi j (by omega)

public theorem gomOK_spec {HB GB OB : ℕ → ℕ} {I0 nH j : ℕ}
    (h : McL.Dce.gomOK HB GB OB I0 nH j = true) :
    McL.Dce.lo20 (McL.Dce.e40 GB j) < nH ∧ McL.Dce.hi20 (McL.Dce.e40 GB j) < nH ∧
      McL.Dce.pt OB j = vecmul (McL.Dce.pt OB I0) (McL.Dce.mat HB (McL.Dce.lo20 (McL.Dce.e40 GB j))) ∧
      mul25 (McL.Dce.mat HB (McL.Dce.lo20 (McL.Dce.e40 GB j)))
        (McL.Dce.mat HB (McL.Dce.hi20 (McL.Dce.e40 GB j))) = ident := by
  unfold McL.Dce.gomOK at h
  beta_reduce at h
  rw [andB_iff, andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq, Nat.beq_eq] at h
  exact h

@[expose] public noncomputable def gE (LT TL NL : ℕ) (HB GB : ℕ → ℕ) (j : ℕ) : Mg LT TL NL :=
  mE LT TL NL (McL.Dce.mat HB (McL.Dce.lo20 (McL.Dce.e40 GB j)))

variable {LT LI TL NL : ℕ}

public theorem gE_mem (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB GB OB : ℕ → ℕ} {I0 nH NO : ℕ} {Ch Cg : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true) :
    ∀ j < NO, InM LT TL NL (McL.Dce.mat HB (McL.Dce.lo20 (McL.Dce.e40 GB j))) ∧
      InM LT TL NL (McL.Dce.mat HB (McL.Dce.hi20 (McL.Dce.e40 GB j))) := by
  intro j hj
  obtain ⟨h1, h2, -, -⟩ := gomOK_spec (runGom_ok hgom j hj)
  have hH := hdr_mem hTL hNL hlet hhdr
  exact ⟨hH _ h1, hH _ h2⟩

public theorem gE_orbit (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB GB OB : ℕ → ℕ} {I0 nH NO : ℕ} {Ch Cg : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true) :
    ∀ j < NO, actV (toVec (McL.Dce.pt OB I0)) ((gE LT TL NL HB GB j : Mg LT TL NL) : Mat25ˣ) =
      toVec (McL.Dce.pt OB j) := by
  intro j hj
  obtain ⟨-, -, h3, -⟩ := gomOK_spec (runGom_ok hgom j hj)
  unfold gE
  rw [← toVec_vecmul_actV (mE_val (gE_mem hTL hNL hlet hhdr hgom j hj).1), ← h3]

def SortInv (get : ℕ → ℕ) (m S : ℕ) : Prop :=
  S = 0 ∨ ∃ L : List ℕ, (∀ q ∈ L, q < m ∧ 0 < get q ∧ get q ≤ S >>> 20) ∧
    L.Pairwise (fun a b => get b < get a) ∧ S % 2 ^ 20 ≤ L.length + 1

theorem m20_eq : (1048575 : ℕ) = 2 ^ 20 - 1 := rfl

theorem lor_shl_mod (a b k : ℕ) : (a ||| b <<< k) % 2 ^ k = a % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < k
  · simp [hi]
  · simp [hi]

theorem lor_shl_shr (a b k : ℕ) : (a ||| b <<< k) >>> k = (a >>> k) ||| b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  simp

theorem le_lor_right (a b : ℕ) : b ≤ a ||| b := by
  rw [Nat.or_comm]
  exact Nat.left_le_or

theorem pw_mem {R : ℕ → ℕ → Prop} : ∀ {L : List ℕ}, L.Pairwise R → ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
    R a b ∨ R b a
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: L, h, a, ha, b, hb, hab => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with e1 | ha'
    · rcases List.mem_cons.1 hb with e2 | hb'
      · exact absurd (e1.trans e2.symm) hab
      · rw [e1]
        exact Or.inl (h.1 b hb')
    · rcases List.mem_cons.1 hb with e2 | hb'
      · rw [e2]
        exact Or.inr (h.1 a ha')
      · exact pw_mem h.2 a ha' b hb' hab

noncomputable def sortOne (get : ℕ → ℕ) (m q S : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0)
    (Nat.lor (Nat.succ (Nat.land S McL.Dce.M20)) (Nat.shiftLeft (get q) (nat_lit 20)))
    (Th.andB (Nat.blt (nat_lit 0) S) (Th.andB (Nat.blt q m) (Nat.blt (Nat.shiftRight S (nat_lit 20)) (get q))))

theorem sortOne_inv (get : ℕ → ℕ) (m q S : ℕ) (h : SortInv get m S) :
    SortInv get m (sortOne get m q S) := by
  unfold sortOne
  cases hc : Th.andB (Nat.blt 0 S) (Th.andB (Nat.blt q m) (Nat.blt (Nat.shiftRight S 20) (get q)))
  · exact Or.inl rfl
  rw [andB_iff, andB_iff, Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at hc
  obtain ⟨hS, hq, hv⟩ := hc
  change S >>> 20 < get q at hv
  rcases h with h | ⟨L, hL, hP, hc⟩
  · omega
  have hge : get q ≤ (Nat.succ (S &&& 1048575) ||| get q <<< 20) >>> 20 := by
    rw [lor_shl_shr]
    exact le_lor_right _ _
  refine Or.inr ⟨q :: L, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨hq, by omega, hge⟩
    · obtain ⟨h1, h2, h3⟩ := hL r hr
      exact ⟨h1, h2, by
        change get r ≤ (Nat.succ (S &&& 1048575) ||| get q <<< 20) >>> 20
        omega⟩
  · refine List.Pairwise.cons (fun b hb => ?_) hP
    have := (hL b hb).2.2
    omega
  · change (Nat.succ (S &&& 1048575) ||| get q <<< 20) % 2 ^ 20 ≤ _
    rw [lor_shl_mod, m20_eq, Nat.and_two_pow_sub_one_eq_mod, List.length_cons]
    have := Nat.mod_le (Nat.succ (S % 2 ^ 20)) (2 ^ 20)
    omega

theorem sortInner_inv (get : ℕ → ℕ) (qb m : ℕ) : ∀ (n J S : ℕ), SortInv get m S →
    SortInv get m (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
      (fun _ ih2 J S => (fun q => Loop.strictN (sortOne get m q S) (ih2 (Nat.shiftRight J qb)))
        (McL.Dce.bits J (nat_lit 0) qb)) n J S)
  | 0, _, _, h => h
  | n + 1, J, S, h => by
    change SortInv get m (Loop.strictN (sortOne get m (McL.Dce.bits J 0 qb) S)
      (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => (fun q => Loop.strictN (sortOne get m q S) (ih2 (Nat.shiftRight J qb)))
          (McL.Dce.bits J (nat_lit 0) qb)) n (Nat.shiftRight J qb)))
    rw [strictN_eq]
    exact sortInner_inv get qb m n _ _ (sortOne_inv get m _ S h)

theorem runSorted_inv (get : ℕ → ℕ) (qb m : ℕ) : ∀ (Cs : List ℕ) (S : ℕ), SortInv get m S →
    SortInv get m (McL.Dce.runSorted get qb m Cs S)
  | [], _, h => h
  | C :: Cs, S, h => by
    change SortInv get m (Loop.strictN (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
        (fun _ ih2 J S => (fun q => Loop.strictN (sortOne get m q S) (ih2 (Nat.shiftRight J qb)))
          (McL.Dce.bits J (nat_lit 0) qb))
        (Nat.land C (nat_lit 65535)) (Nat.shiftRight C (nat_lit 16)) S)
      (McL.Dce.runSorted get qb m Cs))
    rw [strictN_eq]
    exact runSorted_inv get qb m Cs _ (sortInner_inv get qb m _ _ _ h)

public theorem runSorted_spec {get : ℕ → ℕ} {qb m S1 : ℕ} {Cs : List ℕ}
    (h : Nat.beq (McL.Dce.runSorted get qb m Cs 1) S1 = true)
    (hc : Nat.beq (McL.Dce.sortedCount S1) m = true) :
    (∀ q < m, 0 < get q) ∧ ∀ q < m, ∀ q' < m, get q = get q' → q = q' := by
  classical
  have h1 : SortInv get m 1 := Or.inr ⟨[], by simp, List.Pairwise.nil, by simp⟩
  have hi := runSorted_inv get qb m Cs 1 h1
  rw [Nat.eq_of_beq_eq_true h] at hi
  have hc' := Nat.eq_of_beq_eq_true hc
  change (S1 &&& 1048575) - 1 = m at hc'
  rw [m20_eq, Nat.and_two_pow_sub_one_eq_mod] at hc'
  rcases hi with h0 | ⟨L, hL, hP, hcnt⟩
  · subst h0
    have : m = 0 := by simpa using hc'.symm
    subst this
    exact ⟨fun q hq => absurd hq (Nat.not_lt_zero _), fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  have hne : L.Pairwise (fun a b => get a ≠ get b) := hP.imp (fun h => (Nat.ne_of_lt h).symm)
  have hnd : L.Nodup := hne.imp (fun h e => h (congrArg get e))
  have hsub : L.toFinset ⊆ Finset.range m := fun q hq =>
    Finset.mem_range.2 (hL q (List.mem_toFinset.1 hq)).1
  have hcard : (Finset.range m).card ≤ L.toFinset.card := by
    rw [Finset.card_range, List.toFinset_card_of_nodup hnd]
    omega
  have heq : L.toFinset = Finset.range m := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : ∀ q < m, q ∈ L := fun q hq => by
    have : q ∈ L.toFinset := by
      rw [heq]
      exact Finset.mem_range.2 hq
    exact List.mem_toFinset.1 this
  refine ⟨fun q hq => (hL q (hmem q hq)).2.1, fun q hq q' hq' e => ?_⟩
  by_contra hne'
  rcases pw_mem hP q (hmem q hq) q' (hmem q' hq') hne' with h3 | h3 <;> omega

public theorem orb_hyp (hTL : TL = 3) (hNL : NL = 4) (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB GB TB OB RR : ℕ → ℕ} {NR nH nT NO I0 NORD qT qO sT sO : ℕ} {Ch Cg Ct Cts Cos : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true)
    (hTS : Nat.beq (McL.Dce.runSorted (McL.Dce.tSig HB TB) qT nT Cts 1) sT = true)
    (hTSn : Nat.beq (McL.Dce.sortedCount sT) nT = true)
    (hOS : Nat.beq (McL.Dce.runSorted (McL.Dce.pt OB) qO NO Cos 1) sO = true)
    (hOSn : Nat.beq (McL.Dce.sortedCount sO) NO = true)
    (hI0 : I0 < NO) (hT5 : nT * NO = NORD)
    (hM : Nat.card (Mg LT TL NL) ≠ 0 ∧ Nat.card (Mg LT TL NL) ≤ NORD) :
    DceTw.Orb (Mg LT TL NL) NORD (Fin 25 → ZMod 2) actV (toVec (McL.Dce.pt OB I0))
      (fun j => toVec (McL.Dce.pt OB j)) (gE LT TL NL HB GB) NO I0 (sigE LT TL NL HB TB) nT where
  finM := Nat.finite_of_card_ne_zero hM.1
  cardM := hM.2
  act_one := actV_one
  act_mul := actV_mul
  orbit := gE_orbit hTL hNL hlet hhdr hgom
  ω_inj := fun j hj j' hj' e =>
    (runSorted_spec hOS hOSn).2 j hj j' hj'
      (eq_of_toVec_eq (land_rowMask_lt _) (land_rowMask_lt _) e)
  I0_lt := hI0
  ωI0 := rfl
  stab := stab_hyp hTL hNL hlet hhdr hpsi
  σ_inj := fun e he e' he' h => by
    have hm := psi_mem hTL hNL hlet hhdr hpsi
    have h1 := mE_val (hm e he).1
    have h2 := mE_val (hm e' he').1
    unfold sigE at h
    rw [h] at h1
    exact (runSorted_spec hTS hTSn).2 e he e' he'
      (eq_of_toMat_eq (mat_lt _ _) (mat_lt _ _) (h1.symm.trans h2))
  nord := hT5

public theorem card_Mg_eq (hTL : TL = 3) (hNL : NL = 4)
    (hlet : McL.Dce.lettersOK LT LI TL NL = true)
    {HB GB TB OB RR : ℕ → ℕ} {NR nH nT NO I0 NORD qT qO sT sO : ℕ} {Ch Cg Ct Cts Cos : List ℕ}
    (hhdr : Nat.beq (McL.Dce.runHdr HB LT TL NL Ch 1) (nH + 1) = true)
    (hgom : Nat.beq (McL.Dce.runGom HB GB OB I0 nH Cg 1) (NO + 1) = true)
    (hpsi : Nat.beq (McL.Dce.runT HB TB OB RR LT TL NL NR nH nT I0 Ct 1) (nT + 1) = true)
    (hTS : Nat.beq (McL.Dce.runSorted (McL.Dce.tSig HB TB) qT nT Cts 1) sT = true)
    (hTSn : Nat.beq (McL.Dce.sortedCount sT) nT = true)
    (hOS : Nat.beq (McL.Dce.runSorted (McL.Dce.pt OB) qO NO Cos 1) sO = true)
    (hOSn : Nat.beq (McL.Dce.sortedCount sO) NO = true)
    (hI0 : I0 < NO) (hT5 : nT * NO = NORD)
    (hM : Nat.card (Mg LT TL NL) ≠ 0 ∧ Nat.card (Mg LT TL NL) ≤ NORD) :
    Nat.card (Mg LT TL NL) = NORD :=
  (DceTw.decompO (orb_hyp hTL hNL hlet hhdr hgom hpsi hTS hTSn hOS hOSn hI0 hT5 hM)).1

end CFSG.Certificates.McLD
