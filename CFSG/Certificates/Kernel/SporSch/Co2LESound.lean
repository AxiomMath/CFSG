
module

public import Certificates.Data.Kernel.SporSch.Co2LE
public import CFSG.Certificates.Kernel.SporSch.LeftEnum
public import CFSG.Certificates.Kernel.SporSch.MatInj
public import CFSG.Certificates.Kernel.SporSch.Co2MSound
public import CFSG.Certificates.Kernel.Co2InvS.Enum
public import CFSG.Certificates.Kernel.Spor.RawSlSound

set_option exponentiation.threshold 600

public section

namespace CFSG.KS.Co2LE

open CFSG.KC.Enum CFSG.KS.Co2M CFSG.KC.Bfs CFSG.KS.MatRep CFSG.KS.MatInj CFSG.KS.LeftEnum
open CFSG.RankThree.Native.F2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Schreier CFSG.KS

variable {V : Array ℕ} {PV : ℕ}

@[expose] noncomputable def LL (V : Array ℕ) (R : ℕ → ℕ) (N : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := N) fun k => permOfMat 22 V (eM R k.val)

theorem LL_size (R : ℕ → ℕ) (N : ℕ) : (LL V R N).size = N := Array.size_ofFn

theorem LL_get (R : ℕ → ℕ) {N k : ℕ} (hk : k < N) : (LL V R N)[k]! = permOfMat 22 V (eM R k) := by
  rw [getElem!_pos _ k (by rw [LL_size]; exact hk)]
  simp [LL]

theorem eM_lt (R : ℕ → ℕ) (k : ℕ) : eM R k < 2 ^ (22 * 22) :=
  Nat.and_lt_two_pow _ (by decide)

structure VOK (V : Array ℕ) (PV : ℕ) : Prop where
  good : Good 22 V
  size : V.size = 2300
  get : ∀ i < 2300, V[i]! = VG PV i
  spans : Spans 22 V

structure Recs (R GM : ℕ → ℕ) (PV ng N : ℕ) : Prop where
  ok : ∀ k < N, recK R GM PV ng N k = true
  zero : eM R 0 = I22
  one : mR R ng 0 = 1
  pos : 0 < N

@[expose] def GensRep (V : Array ℕ) (gens : Array (Array ℕ)) (GM : ℕ → ℕ) (ng : ℕ) : Prop :=
  gens.size = ng ∧ ∀ j < ng, ∃ M', Rep 22 V gens[j]! (GM j) M'

section

variable {R GM : ℕ → ℕ} {ng N : ℕ} {gens : Array (Array ℕ)}

theorem blt_lt' {a b : ℕ} (h : Nat.blt a b = true) : a < b := by rwa [Nat.blt_eq] at h

theorem lt_blt' {a b : ℕ} (h : a < b) : Nat.blt a b = true := by rwa [Nat.blt_eq]

theorem rec_spec {k : ℕ} (h : recK R GM PV ng N k = true) :
    (∀ j < ng, tR R k j < N ∧ eM R (tR R k j) = mmK (eM R k) (GM j)) ∧ k < mR R ng k ∧
      optIs (rRow (tR R) ng k (mR R ng k)) (nextR R ng N k) = true ∧
      (0 < k → pR R ng k < k ∧ lR R ng k < ng ∧ tR R (pR R ng k) (lR R ng k) = k) ∧
      sR R ng k < N ∧ (k + 1 < N → codeK PV (eM R (sR R ng k)) <
        codeK PV (eM R (sR R ng (k + 1)))) := by
  unfold recK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨h4, h5⟩ := (bAnd_iff _ _).1 h4
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h5
  refine ⟨fun j hj => ?_, blt_lt' h2, h3, fun hk => ?_, blt_lt' h5, fun hk => ?_⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h1 j hj)
    exact ⟨blt_lt' a, Nat.eq_of_beq_eq_true b⟩
  · have hk0 : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun h => by
      have := Nat.eq_of_beq_eq_true h
      omega
    rw [hk0] at h4
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h4
    obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
    exact ⟨blt_lt' a, blt_lt' b, Nat.eq_of_beq_eq_true c⟩
  · have hb : Nat.blt (Nat.succ k) N = true := lt_blt' hk
    rw [hb] at h6
    exact blt_lt' h6

theorem optIs_eq {o : Option ℕ} {m : ℕ} (h : optIs o m = true) : o = some m := by
  cases o with
  | none => exact absurd h (by simp [optIs])
  | some a =>
    have : Nat.beq a m = true := h
    rw [Nat.eq_of_beq_eq_true this]

variable (hV : VOK V PV) (hR : Recs R GM PV ng N)
include hV hR

omit hR in
theorem vmK_V {i : ℕ} (hi : i < 2300) (X : ℕ) : vmK (VG PV i) X = vmul 22 V[i]! X := by
  rw [vmK_eq, hV.get i hi]

theorem entry_rep (hg : GensRep V gens GM ng) :
    ∀ k < N, ∃ M', Rep 22 V (permOfMat 22 V (eM R k)) (eM R k) M' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨idM 22, ?_⟩
      have h := rep_idA hV.good
      rw [hR.zero, I22_eq]
      rw [← permOfMat_idM hV.good.hd hV.good.nodup hV.good.lt] at h
      exact h
    · obtain ⟨hp, hl, ht⟩ := (rec_spec (hR.ok k hk)).2.2.2.1 hk0
      obtain ⟨Mp, hMp⟩ := ih _ hp (by omega)
      obtain ⟨Ml, hMl⟩ := hg.2 _ hl
      have he := ((rec_spec (hR.ok (pR R ng k) (by omega))).1 _ hl).2
      rw [ht, mmK_eq] at he
      have h := rep_compA hV.good hMl hMp
      rw [← he] at h
      exact ⟨_, ⟨rfl, h.2⟩⟩

omit hR in
theorem keyA_perm (X : ℕ) :
    keyA (permOfMat 22 V X) = vidx V (vmul 22 V[0]! X) +
      2300 * (vidx V (vmul 22 V[1]! X) + 2300 * vidx V (vmul 22 V[3]! X)) := by
  unfold keyA
  rw [permOfMat_get (by rw [hV.size]; norm_num), permOfMat_get (by rw [hV.size]; norm_num),
    permOfMat_get (by rw [hV.size]; norm_num)]

theorem leftEnum_facts (hg : GensRep V gens GM ng) {cap : ℕ} (hcap : N ≤ cap) :
    (leftEnum gens cap).elems = LL V R N ∧ enumOK gens N (leftEnum gens cap) = true ∧
      ∀ k < N, ∃ M', Rep 22 V (LL V R N)[k]! (eM R k) M' := by
  have hrep := entry_rep hV hR hg
  have hrepL : ∀ k < N, ∃ M', Rep 22 V (LL V R N)[k]! (eM R k) M' := fun k hk => by
    rw [LL_get R hk]
    exact hrep k hk
  have hE : ∀ i < N, ∀ j < gens.size, tR R i j < N ∧
      (LL V R N)[tR R i j]! = compA 2300 gens[j]! (LL V R N)[i]! := by
    intro i hi j hj
    rw [hg.1] at hj
    obtain ⟨ht, he⟩ := (rec_spec (hR.ok i hi)).1 j hj
    refine ⟨ht, ?_⟩
    obtain ⟨Mi, hMi⟩ := hrepL i hi
    obtain ⟨Mj, hMj⟩ := hg.2 j hj
    have h := rep_compA hV.good hMj hMi
    rw [hV.size] at h
    rw [h.1, LL_get R ht, he, mmK_eq]
  have hkey : ∀ a < N, ∀ b < N, keyA (LL V R N)[a]! = keyA (LL V R N)[b]! → a = b := by
    have hs : ∀ i < N, sR R ng i < N := fun i hi => (rec_spec (hR.ok i hi)).2.2.2.2.1
    have hlt : ∀ i, i + 1 < N → codeK PV (eM R (sR R ng i)) < codeK PV (eM R (sR R ng (i + 1))) :=
      fun i hi => (rec_spec (hR.ok i (by omega))).2.2.2.2.2 hi
    have hinj := CFSG.KC.Co2InvS.sorted_inj (f := fun k => codeK PV (eM R k)) hs hlt
    intro a ha b hb e
    obtain ⟨Ma, hMa⟩ := hrepL a ha
    obtain ⟨Mb, hMb⟩ := hrepL b hb
    rw [hMa.1, hMb.1, keyA_perm hV, keyA_perm hV] at e
    have hd : ∀ (i : ℕ) (hi : i < 2300) (X : ℕ), (∀ v ∈ V, vmul 22 v X ∈ V) →
        vidx V (vmul 22 V[i]! X) < 2300 := fun i hi X hX => by
      rw [← hV.size]
      exact (getElem_vidx (hX _ (mem_of_lt (by rw [hV.size]; exact hi)))).1
    have d0a := hd 0 (by norm_num) _ hMa.2.1
    have d1a := hd 1 (by norm_num) _ hMa.2.1
    have d3a := hd 3 (by norm_num) _ hMa.2.1
    have d0b := hd 0 (by norm_num) _ hMb.2.1
    have d1b := hd 1 (by norm_num) _ hMb.2.1
    have d3b := hd 3 (by norm_num) _ hMb.2.1
    have veq : ∀ (i : ℕ) (hi : i < 2300), vidx V (vmul 22 V[i]! (eM R a)) =
        vidx V (vmul 22 V[i]! (eM R b)) → vmul 22 V[i]! (eM R a) = vmul 22 V[i]! (eM R b) := by
      intro i hi h
      have hi' : i < V.size := by rw [hV.size]; exact hi
      rw [← (getElem_vidx (hMa.2.1 _ (mem_of_lt hi'))).2,
        ← (getElem_vidx (hMb.2.1 _ (mem_of_lt hi'))).2, h]
    have e0 := veq 0 (by norm_num) (by omega)
    have e1 := veq 1 (by norm_num) (by omega)
    have e3 := veq 3 (by norm_num) (by omega)
    refine hinj a ha b hb ?_
    simp only [codeK, vmK_V hV (by norm_num : 0 < 2300), vmK_V hV (by norm_num : 1 < 2300),
      vmK_V hV (by norm_num : 3 < 2300), e0, e1, e3]
  let M : ℕ → ℕ := fun k => if k < N then mR R ng k else N
  have hM0 : M 0 = 1 := by
    simp only [M, hR.pos, ↓reduceIte, hR.one]
  have hMN : M N = N := by simp [M]
  have hM : ∀ k < N, k < M k ∧ rRow (tR R) gens.size k (M k) = some (M (k + 1)) := by
    intro k hk
    obtain ⟨-, h1, h2, -⟩ := rec_spec (hR.ok k hk)
    have eM1 : M k = mR R ng k := by simp [M, hk]
    have eM2 : M (k + 1) = nextR R ng N k := by
      unfold nextR
      by_cases h : k + 1 < N
      · rw [lt_blt' h]
        simp [M, h]
      · have hb : Nat.blt (Nat.succ k) N = false := by
          rw [Bool.eq_false_iff]
          intro hh
          exact h (blt_lt' hh)
        rw [hb]
        simp [M, h]
    rw [eM1, eM2, hg.1]
    exact ⟨h1, optIs_eq h2⟩
  have h0 : (LL V R N)[0]! = idA 2300 := by
    rw [LL_get R hR.pos, hR.zero, I22_eq, permOfMat_idM hV.good.hd hV.good.nodup hV.good.lt,
      hV.size]
  have hinv : ∀ k < N, isInvA 2300 (LL V R N)[k]! (invCand 2300 (LL V R N)[k]!) = true := by
    intro k hk
    obtain ⟨Mk, hMk⟩ := hrepL k hk
    rw [hMk.1, ← hV.size, invCand_permOfMat hV.good.hd hV.good.nodup hV.good.lt hMk.2]
    exact isInvA_permOfMat hV.good.hd hV.good.nodup hV.good.lt hMk.2
  have hcore := leftEnum_replay (gens := gens) (LL_size R N) hR.pos h0 hkey hE hM0 hMN hM hcap
  exact ⟨hcore.1, enumOK_of_replay (LL_size R N) hR.pos h0 hkey hE hM0 hMN hM hinv hcap, hrepL⟩

theorem conjOK_of (hg : GensRep V gens GM ng) {cap : ℕ} (hcap : N ≤ cap)
    {conj pis : Array (Array ℕ)} {nc w : ℕ} {C C' PI : ℕ → ℕ} (hc : conj.size = nc)
    (hcr : ∀ i < nc, Rep 22 V conj[i]! (C i) (C' i))
    (hpis : ∀ i < nc, ∀ k < N, (pis[i]!)[k]! = pg w (mask w) (PI i) k)
    (hk : ∀ i < nc, ∀ k < N, conjK R (C i) (C' i) (PI i) w N k = true) :
    conjOK conj pis N (leftEnum gens cap) = true := by
  obtain ⟨he, -, hrepL⟩ := leftEnum_facts hV hR hg hcap
  unfold conjOK
  rw [he, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [hc] at hi
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k hkN
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (hk i hi k hkN)
  have hp := blt_lt' h1
  rw [hpis i hi k hkN, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hp, ?_⟩
  obtain ⟨Mk, hMk⟩ := hrepL k hkN
  have r1 := rep_compA hV.good (hcr i hi) hMk
  have r2 := rep_invCand hV.good (hcr i hi)
  have r3 := rep_compA hV.good r1 r2
  rw [hV.size] at r1 r2 r3
  rw [r3.1, LL_get R hp, Nat.eq_of_beq_eq_true h2, mmK_eq, mmK_eq]
  exact eqA_refl _ _

theorem centerIdx_eq (hg : GensRep V gens GM ng) {cap : ℕ} (hcap : N ≤ cap) :
    centerIdx gens N (leftEnum gens cap) = (List.range N).filter (centK R GM ng) := by
  obtain ⟨he, -, hrepL⟩ := leftEnum_facts hV hR hg hcap
  unfold centerIdx
  rw [he]
  refine List.filter_congr fun k hk => ?_
  have hkN := List.mem_range.1 hk
  obtain ⟨Mk, hMk⟩ := hrepL k hkN
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, hg.1]
  have hj : ∀ j < ng, commA (LL V R N)[k]! gens[j]! =
      Nat.beq (mmK (GM j) (eM R k)) (mmK (eM R k) (GM j)) := by
    intro j hj
    obtain ⟨Mj, hMj⟩ := hg.2 j hj
    have r1 := rep_compA hV.good hMk hMj
    have r2 := rep_compA hV.good hMj hMk
    unfold commA
    rw [← hV.size, r1.1, r2.1, eqA_permOfMat hV.spans r1.2.1 r2.2.1 (mmul_lt _ _) (mmul_lt _ _),
      mmK_eq, mmK_eq]
  constructor
  · intro h
    exact CFSG.KS.Raw.allN_of_forall fun j hj' => by rw [← hj j hj']; exact h j hj'
  · intro h j hj'
    rw [hj j hj']
    exact allN_spec h j hj'

theorem coreOK_of (hg : GensRep V gens GM ng) {cap : ℕ} (hcap : N ≤ cap)
    {conj pis : Array (Array ℕ)} {nc w : ℕ} {C C' PI : ℕ → ℕ} (hc : conj.size = nc)
    (hcr : ∀ i < nc, Rep 22 V conj[i]! (C i) (C' i))
    (hpis : ∀ i < nc, ∀ k < N, (pis[i]!)[k]! = pg w (mask w) (PI i) k)
    (hk : ∀ i < nc, ∀ k < N, conjK R (C i) (C' i) (PI i) w N k = true) {cen : List ℕ}
    (hcen : ((List.range N).filter (centK R GM ng) == cen) = true) :
    coreOK gens conj pis N cen (leftEnum gens cap) = true := by
  unfold coreOK
  rw [(leftEnum_facts hV hR hg hcap).2.1, conjOK_of hV hR hg hcap hc hcr hpis hk,
    centerIdx_eq hV hR hg hcap, hcen]
  rfl

omit hV hR in
theorem eqA_entry {k : ℕ} (hk : k < N) {t : Array ℕ} {Z Z' : ℕ} (ht : Rep 22 V t Z Z')
    (h : eM R k = Z) : eqA 2300 (LL V R N)[k]! t = true := by
  rw [LL_get R hk, ht.1, h]
  exact eqA_refl _ _

end

end CFSG.KS.Co2LE

end
