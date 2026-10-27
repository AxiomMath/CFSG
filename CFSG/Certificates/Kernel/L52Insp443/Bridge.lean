module

public import Certificates.Data.Kernel.L52Insp443.Tab
public import CFSG.Certificates.Kernel.Misc.GL52MatSound
public import CFSG.Literature.GL52Basic
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.Misc.GL52Ech
import CFSG.Certificates.Kernel.Misc.GL52MatProved
import CFSG.Certificates.Kernel.Misc.GL52Sol

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.Misc.GLM.Ech CFSG.KC.Misc.GLM.Pf
  CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix

theorem andB_true {a b : Bool} : CFSG.KC.Ord.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem recAnd_iff (p : ℕ → Bool) : ∀ k : ℕ,
    (Nat.rec (motive := fun _ => Bool) true (fun i acc => CFSG.KC.Ord.andB (p i) acc) k : Bool) = true ↔
      ∀ i < k, p i = true
  | 0 => by simp
  | k + 1 => by
    change CFSG.KC.Ord.andB (p k) (Nat.rec (motive := fun _ => Bool) true (fun i acc => CFSG.KC.Ord.andB (p i) acc) k) =
      true ↔ _
    rw [andB_true, recAnd_iff p k]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h k (by omega), fun i hi => h i (by omega)⟩

theorem par5_land : ∀ r v : Fin 32, par5 (Nat.land r v) ≤ 1 ∧
    ((par5 (Nat.land r v) : ℕ) : ZMod 2) =
      bvo 5 0 r 0 * bvo 5 0 v 0 + bvo 5 0 r 1 * bvo 5 0 v 1 + bvo 5 0 r 2 * bvo 5 0 v 2 +
        bvo 5 0 r 3 * bvo 5 0 v 3 + bvo 5 0 r 4 * bvo 5 0 v 4 := by
  decide +kernel

theorem recLor_testBit (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) : ∀ k j : ℕ,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) i)) k :
      ℕ).testBit j = (decide (j < k) && decide (f j = 1))
  | 0, j => by simp
  | k + 1, j => by
    change (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) i)) k) (f k <<< k)).testBit j = _
    rw [lor_testBit, recLor_testBit f hf k j, Nat.testBit_shiftLeft]
    rcases Nat.lt_trichotomy j k with h | rfl | h
    · have h1 : ¬ (k ≤ j) := by omega
      simp [h, h1, show j < k + 1 by omega]
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf j) with h0 | h0 <;> simp [h0]
    · have hb : (f k).testBit (j - k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show f k < 2 ^ 1 by have := hf k; omega)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h1 : ¬ (j < k) := by omega
      by_cases h2 : j = k + 1 - 1
      · omega
      · simp [h1, hb, show ¬ j < k + 1 by omega]

theorem rowK_lt (c i : ℕ) : rowK c i < 32 := by
  unfold rowK
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem bvo_row' (A : Mat) (i : Fin 5) : bvo 5 0 (rowK (mcode A) i) = A i := by
  funext j
  change (if (rowK (mcode A) i).testBit (j + 0) then (1 : ZMod 2) else 0) = A i j
  rw [Nat.add_zero, rowK_bit, decide_eq_true j.isLt, Bool.true_and, mcode_bit]
  generalize A i j = x
  revert x
  decide

theorem mvK_mcode (A : Mat) {v : ℕ} (hv : v < 32) :
    mvK (mcode A) v < 32 ∧ bvo 5 0 (mvK (mcode A) v) = A *ᵥ bvo 5 0 v := by
  set f : ℕ → ℕ := fun i => par5 (Nat.land (rowK (mcode A) i) v) with hfdef
  have hf : ∀ i, f i ≤ 1 := fun i =>
    (par5_land ⟨_, rowK_lt (mcode A) i⟩ ⟨v, hv⟩).1
  have he : mvK (mcode A) v =
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) i)) 5 := rfl
  have hbit := recLor_testBit f hf 5
  rw [he]
  refine ⟨?_, ?_⟩
  · rw [show (32 : ℕ) = 2 ^ 5 from rfl]
    refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
    rw [hbit]
    simp [show ¬ j < 5 by omega]
  · funext i
    change (if (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) i)) 5 : ℕ).testBit (i + 0) then (1 : ZMod 2)
        else 0) = _
    rw [Nat.add_zero, hbit, decide_eq_true i.isLt, Bool.true_and]
    have h1 := (par5_land ⟨_, rowK_lt (mcode A) i⟩ ⟨v, hv⟩).2
    change ((f i : ℕ) : ZMod 2) = _ at h1
    have hfi : (if decide (f i = 1) = true then (1 : ZMod 2) else 0) = ((f i : ℕ) : ZMod 2) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf i) with h0 | h0 <;> simp [h0]
    rw [hfi, h1, mulVec, dotProduct, Fin.sum_univ_five]
    have hr := bvo_row' A i
    simp only [Fin.isValue] at hr ⊢
    rw [← hr]

@[expose] def mdec (c : ℕ) : Mat := fun i j => if c.testBit (5 * i + j) then 1 else 0

theorem mcode_mdec {c : ℕ} (hc : c < 2 ^ 25) : mcode (mdec c) = c := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 25 with hq | hq
  · have e : q = 5 * ((⟨q / 5, by omega⟩ : Fin 5) : ℕ) + ((⟨q % 5, by omega⟩ : Fin 5) : ℕ) := by
      simp only
      omega
    rw [e, mcode_bit, mdec]
    cases c.testBit _ <;> rfl
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (mcode_lt _)
      (Nat.pow_le_pow_right (by norm_num) hq)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hq))]

open scoped Classical in
@[expose] noncomputable def gD (c : ℕ) : G :=
  if h : IsUnit (mdec c) then h.unit else 1

theorem unitK_iff {c : ℕ} : unitK c = true ↔ c < 2 ^ 25 ∧ rankK c = 5 := by
  unfold unitK
  rw [andB_true, Nat.blt_eq, Nat.beq_eq]
  exact Iff.rfl

theorem gD_val {c : ℕ} (h : unitK c = true) : ((gD c : G) : Mat) = mdec c := by
  obtain ⟨hc, hr⟩ := unitK_iff.mp h
  have hu : IsUnit (mdec c) := by
    rw [isUnit_iff_rank5, ← rankK_mcode, mcode_mdec hc, hr]
  unfold gD
  rw [dif_pos hu]
  rfl

theorem mcode_gD {c : ℕ} (h : unitK c = true) : mcode ((gD c : G) : Mat) = c := by
  rw [gD_val h, mcode_mdec (unitK_iff.mp h).1]

theorem symm_vecEquiv : ∀ v : Fin 32, ∀ j : Fin 5, vecEquiv.symm v j = bvo 5 0 v j := by
  decide +kernel

theorem ptVec_eq (i : Fin 31) : ptVec i = bvo 5 0 (i + 1) := by
  funext j
  exact symm_vecEquiv i.succ j

theorem rep_of_tabK {g : G} {T : Table} (hT : tabK (mcode (g : Mat)) T = true) :
    Rep 31 T (glPerm g) := by
  have h := (recAnd_iff (fun i => Nat.beq (mvK (mcode (g : Mat)) (Nat.succ i))
    (Nat.succ (ap T i))) 31).mp hT
  intro i hi
  have hi' := Nat.eq_of_beq_eq_true (h i hi)
  obtain ⟨hlt, hmv⟩ := mvK_mcode (g : Mat) (show i + 1 < 32 by omega)
  have hj : ap T i < 31 := by
    change mvK (mcode (g : Mat)) (i + 1) = ap T i + 1 at hi'
    omega
  rw [idx_of_lt _ hi, Equiv.Perm.smul_def]
  have e := (glPerm_apply_eq_iff g ⟨i, hi⟩ ⟨ap T i, hj⟩).mpr (by
    rw [ptVec_eq, ptVec_eq]
    change (g : Mat) *ᵥ bvo 5 0 (i + 1) = bvo 5 0 (ap T i + 1)
    rw [← hmv]
    change bvo 5 0 (mvK (mcode (g : Mat)) (i + 1)) = _
    rw [show mvK (mcode (g : Mat)) (i + 1) = ap T i + 1 from hi'])
  rw [e]

theorem tabsK_cons (c : ℕ) (cs : List ℕ) (T : Table) (Ts : List Table) :
    tabsK (c :: cs) (T :: Ts) = CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (unitK c) (tabK c T)) (tabsK cs Ts) := rfl

theorem forall₂_of_tabsK : ∀ {cs : List ℕ} {Ts : List Table}, tabsK cs Ts = true →
    List.Forall₂ (Rep 31) Ts (cs.map fun c => glPerm (gD c)) ∧ ∀ c ∈ cs, unitK c = true
  | [], [], _ => ⟨List.Forall₂.nil, by simp⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: cs, T :: Ts, h => by
    rw [tabsK_cons, andB_true, andB_true] at h
    obtain ⟨⟨hu, hT⟩, hr⟩ := h
    obtain ⟨h1, h2⟩ := forall₂_of_tabsK hr
    refine ⟨List.Forall₂.cons ?_ h1, ?_⟩
    · rw [← mcode_gD hu] at hT
      exact rep_of_tabK hT
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hu
      · exact h2 d hd

theorem diagK_eq : ∀ bs : List ℕ, diagK bs = bs.map fun b => (b, b)
  | [] => rfl
  | b :: bs => by
    change (b, b) :: diagK bs = _
    rw [diagK_eq bs]
    rfl

theorem solCntK_eq (ps : List (ℕ × ℕ)) :
    solCntK ps = unitCntK (elimK ps (25 * ps.length) 25).2 := by
  unfold solCntK
  rw [Nat.mul_eq]

@[expose] def psF (f : ℕ → G) (bs : List ℕ) : List (Mat × Mat) :=
  bs.map fun b => (((f b : G) : Mat), ((f b : G) : Mat))

theorem comm_iff_val (g h : G) : g * h = h * g ↔ (g : Mat) * (h : Mat) = (h : Mat) * (g : Mat) := by
  rw [Units.ext_iff, Units.val_mul, Units.val_mul]

theorem mem_psF_iff (f : ℕ → G) (bs : List ℕ) (g : G) :
    (∀ p ∈ psF f bs, (g : Mat) * p.1 = p.2 * (g : Mat)) ↔ ∀ b ∈ bs, g * f b = f b * g := by
  unfold psF
  rw [List.forall_mem_map]
  exact forall₂_congr fun b _ => (comm_iff_val g (f b)).symm

theorem codes_psF (f : ℕ → G) : ∀ {bs : List ℕ}, (∀ b ∈ bs, mcode ((f b : G) : Mat) = b) →
    ((psF f bs).map fun p => (mcode p.1, mcode p.2)) = diagK bs
  | [], _ => rfl
  | b :: bs, h => by
    have ih := codes_psF f (bs := bs) fun c hc => h c (List.mem_cons_of_mem b hc)
    unfold psF at ih ⊢
    rw [List.map_cons, List.map_cons, ih, h b List.mem_cons_self]
    rfl

theorem length_psF (f : ℕ → G) (bs : List ℕ) : (psF f bs).length = (diagK bs).length := by
  unfold psF
  rw [diagK_eq, List.length_map, List.length_map]

theorem card_cent_of_codes (f : ℕ → G) {bs : List ℕ} (hf : ∀ b ∈ bs, mcode ((f b : G) : Mat) = b) :
    Nat.card {g : G // ∀ b ∈ bs, g * f b = f b * g} = solCntK (diagK bs) := by
  have h := solCnt_sound (psF f bs)
  rw [codes_psF f hf, length_psF] at h
  rw [solCntK_eq, ← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (mem_psF_iff f bs g).symm)

theorem card_cent_gD {bs : List ℕ} (hu : ∀ b ∈ bs, unitK b = true) :
    Nat.card {g : G // ∀ b ∈ bs, g * gD b = gD b * g} = solCntK (diagK bs) :=
  card_cent_of_codes gD fun b hb => mcode_gD (hu b hb)

end CFSG.KC.L52I

end
