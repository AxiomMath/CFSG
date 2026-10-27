module

public import Certificates.Data.Kernel.Co1M.ThirteenScan
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.Co1Seven.CenSound
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.VecKSound
public import CFSG.Certificates.Kernel.Co1M.C16954Glue
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 4000

namespace CFSG.KC.Co1ThirteenGlue

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2 CFSG.KC.Co1B
  CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.VecK CFSG.KD.Co1Thirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance Matrix

local notation "M24" => Matrix (Fin 24) (Fin 24) (ZMod 2)

theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem eqBB_eq (a b : Bool) : eqBB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, fun h => by
    induction n with
    | zero => rfl
    | succ n ih =>
      change CFSG.KLie.CT.andB (f n) (allN n f) = true
      rw [andB_eq, Bool.and_eq_true]
      exact ⟨h n (by omega), ih fun i hi => h i (by omega)⟩⟩

theorem allL_iff {α : Type} {f : α → Bool} : ∀ L : List α, allL f L = true ↔ ∀ a ∈ L, f a = true
  | [] => by simp [allL]
  | a :: L => by
    change CFSG.KLie.CT.andB (f a) (allL f L) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, allL_iff L, List.forall_mem_cons]

theorem memL_iff (w : Nat) : ∀ L : List Nat, memL L w = true ↔ w ∈ L
  | [] => by simp [memL]
  | a :: L => by
    change CFSG.KLie.CT.orB (Nat.beq a w) (memL L w) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, memL_iff w L, Nat.beq_eq, List.mem_cons, eq_comm]

theorem nodupK_nodup : ∀ L : List Nat, nodupK L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
    change CFSG.KLie.CT.andB (allL (fun b => CFSG.KLie.CT.notB (Nat.beq a b)) L) (nodupK L) = true at h
    rw [andB_eq, Bool.and_eq_true, allL_iff] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodupK_nodup L h.2⟩
    have h1 := h.1 a ha
    rw [notB_eq, Nat.beq_refl] at h1
    exact absurd h1 (by decide)

theorem lenL_eq : ∀ L : List Nat, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenL_eq L)

theorem lenP_eq : ∀ L : List (Nat × Bool), lenP L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenP_eq L)

theorem getL_eq : ∀ (L : List Nat) (i : Nat) (h : i < L.length), getL 0 L i = L[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, i + 1, h => getL_eq L i (by simpa using h)

theorem getL_mem {L : List Nat} {i : Nat} (h : i < L.length) : getL 0 L i ∈ L := by
  rw [getL_eq L i h]
  exact List.getElem_mem h

theorem getP_eq : ∀ (L : List (Nat × Bool)) (i : Nat) (h : i < L.length), getP L i = L[i].1
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, i + 1, h => getP_eq L i (by simpa using h)

theorem pw2_eq (b : Nat) : pw2 b = 2 ^ b := Nat.one_shiftLeft b

theorem orbL_succ (T u n : Nat) : orbL T u (n + 1) = u :: orbL T (vmF 24 T u) n := rfl

theorem orbL_length (T : Nat) : ∀ (n u : Nat), (orbL T u n).length = n
  | 0, _ => rfl
  | n + 1, u => by rw [orbL_succ, List.length_cons, orbL_length T n]

theorem forall_orbL {T : Nat} {P : Nat → Prop} (hT : ∀ v, P v → P (vmF 24 T v)) :
    ∀ (n u : Nat), P u → ∀ w ∈ orbL T u n, P w
  | 0, _, _, w, hw => absurd hw List.not_mem_nil
  | n + 1, u, hu, w, hw => by
    rw [orbL_succ, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact forall_orbL hT n _ (hT u hu) w hw

theorem rep_one : MRep (unpackR 24 oneK) 1 := by
  rw [← CFSG.KC.Co1B.one_eq]
  exact MRep.one

theorem rep_mulWK {A B : Nat} {g h : GL24} (hA : MRep (unpackR 24 A) g)
    (hB : MRep (unpackR 24 B) h) : MRep (unpackR 24 (mulWK A B)) (g * h) := by
  have e := CFSG.KS.SporSch.M24.mul_unpackW A B
  rw [← CFSG.KS.SporSch.M24.unpackR_eq_unpack, ← CFSG.KS.SporSch.M24.unpackR_eq_unpack,
    ← CFSG.KS.SporSch.M24.unpackR_eq_unpack] at e
  rw [← e]
  exact hA.mul hB

theorem rep_powWK {A : Nat} {g : GL24} (hA : MRep (unpackR 24 A) g) (n : Nat) :
    MRep (unpackR 24 (powWK A n)) (g ^ n) := by
  have e := CFSG.KS.SporSch.M24.unpack_powWK A n
  rw [← CFSG.KS.SporSch.M24.unpackR_eq_unpack, ← CFSG.KS.SporSch.M24.unpackR_eq_unpack] at e
  rw [e]
  exact hA.pow n

theorem eq_of_eqK {A B : Nat} {g h : GL24} (hA : MRep (unpackR 24 A) g)
    (hB : MRep (unpackR 24 B) h) (e : eqK A B = true) : g = h := by
  rw [← beq_unpack, beq_iff_eq] at e
  rw [e] at hA
  exact hA.eq hB

theorem unpackR_lt (A i : Nat) (hi : i < 24) : (unpackR 24 A)[i]?.getD 0 < 2 ^ 24 := by
  have e : (unpackR 24 A)[i]? = some (A / 2 ^ (24 * i) % 2 ^ 24) := by
    unfold unpackR
    rw [Array.getElem?_ofFn]
    simp [hi]
  rw [e, Option.getD_some]
  exact Nat.mod_lt _ (by norm_num)

theorem eqK_of_eq {A B : Nat} {g : GL24} (hA : MRep (unpackR 24 A) g)
    (hB : MRep (unpackR 24 B) g) : eqK A B = true := by
  rw [← beq_unpack, beq_iff_eq]
  unfold MRep at hA hB
  have hm : rowsMatrix 24 (unpackR 24 A) = rowsMatrix 24 (unpackR 24 B) := by rw [hA, hB]
  have hrow : ∀ i < 24, (unpackR 24 A)[i]?.getD 0 = (unpackR 24 B)[i]?.getD 0 := by
    intro i hi
    refine toVecD_injective (unpackR_lt A i hi) (unpackR_lt B i hi) (funext fun j => ?_)
    have := congrFun (congrFun hm ⟨i, hi⟩) j
    rwa [rowsMatrix_apply, rowsMatrix_apply] at this
  have hs : ∀ X : Nat, (unpackR 24 X).size = 24 := fun X => by simp [unpackR]
  refine Array.ext (by rw [hs, hs]) fun i h1 h2 => ?_
  have hi : i < 24 := by rwa [hs] at h1
  have := hrow i hi
  rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at this

theorem act_rep {A : Nat} {g : GL24} (hA : MRep (unpackR 24 A) g) (w : Nat) :
    toVecD 24 (vmF 24 (trK 24 A) w) = (g : M24) *ᵥ toVecD 24 w :=
  (CFSG.KC.Co1ElevenGlue.mulVec_of_rep hA w).symm

theorem vmF_lt24 (T w : Nat) : vmF 24 T w < 2 ^ 24 := CFSG.KC.F2W.vmF_lt 24 _ _

theorem xor_lt24 {a b : Nat} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) : Nat.xor a b < 2 ^ 24 :=
  Nat.xor_lt_two_pow ha hb

theorem toVecD_two_pow (i : Fin 24) : toVecD 24 (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem comm_mul' {a b y : GL24} (ha : a * y = y * a) (hb : b * y = y * b) :
    a * b * y = y * (a * b) := by
  rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem comm_inv' {a y : GL24} (ha : a * y = y * a) : a⁻¹ * y = y * a⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha, mul_assoc, mul_inv_cancel, mul_one]

theorem comm_pow'' {a y : GL24} (ha : a * y = y * a) (t : ℕ) :
    a * y ^ t = y ^ t * a := by
  induction t with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ t ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, ha, mul_assoc]

theorem comm_pow' {a y : GL24} (ha : a * y = y * a) (t : ℕ) :
    a ^ t * y = y * a ^ t := by
  induction t with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ t ih => rw [pow_succ, mul_assoc, ha, ← mul_assoc, ih, mul_assoc]

theorem eq_of_inv_mul {a b : GL24} (h : a⁻¹ * b = 1) : a = b := by
  rw [← mul_one a, ← h, ← mul_assoc, mul_inv_cancel, one_mul]

theorem eq_of_mem_zpowers_three {K : Type*} [Group K] {z w : K} (hz : orderOf z = 3)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z ∨ w = z * z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [← zpow_mod_orderOf, hz]
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  generalize k % ((3 : ℕ) : ℤ) = r at h0 h3 ⊢
  interval_cases r
  · exact Or.inl (zpow_zero z)
  · exact Or.inr (Or.inl (zpow_one z))
  · exact Or.inr (Or.inr (zpow_two z))

theorem toVecD_surj (w : Vec24) : ∃ x < 2 ^ 24, toVecD 24 x = w := by
  refine ⟨CFSG.Sporadic.SmallF2.Native.ofBits 24 fun j => if h : j < 24 then decide (w ⟨j, h⟩ = 1) else false,
    ofBits_lt 24 _, ?_⟩
  funext j
  rw [toVecD_ofBits]
  simp only [j.isLt, dite_true]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hz (w j) with h | h <;> simp [h]

section Cent


theorem mulVec_inv_mul (c : GL24) (v : Vec24) :
    ((c⁻¹ : GL24) : M24) *ᵥ ((c : M24) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mem_certX_mulVec_iff {c : GL24} (hc : c ∈ GA) (v : Vec24) :
    (c : M24) *ᵥ v ∈ certX ↔ v ∈ certX := by
  refine ⟨fun h => ?_, mulVec_mem_certX hc⟩
  have := mulVec_mem_certX (GA.inv_mem hc) h
  rwa [mulVec_inv_mul] at this

variable {mem : Nat → Bool} (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX)
include hmem

theorem mem_congr {c : GL24} (hc : c ∈ GA) {a a' : Nat} (ha : a < 2 ^ 24) (ha' : a' < 2 ^ 24)
    (e : toVecD 24 a' = (c : M24) *ᵥ toVecD 24 a) : mem a' = mem a := by
  apply Bool.eq_iff_iff.2
  rw [hmem a' ha', hmem a ha, e]
  exact mem_certX_mulVec_iff hc _

omit hmem in
theorem commute_pow {c Y : GL24} (hcY : c * Y = Y * c) (k : Nat) :
    (c : M24) * ((Y ^ k : GL24) : M24) = ((Y ^ k : GL24) : M24) * (c : M24) := by
  have e := congrArg (fun z : GL24 => (z : M24)) (comm_pow'' hcY k)
  simpa only [Units.val_mul] using e

omit hmem in
theorem mulVec_comm {c Y : GL24} (hcY : c * Y = Y * c) (k : Nat) (v : Vec24) :
    (c : M24) *ᵥ (((Y ^ k : GL24) : M24) *ᵥ v) = ((Y ^ k : GL24) : M24) *ᵥ ((c : M24) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, commute_pow hcY]

theorem tauK_congr {c Y : GL24} (hc : c ∈ GA) (hcY : c * Y = Y * c) :
    ∀ (ts : List (Nat × Bool)), (∀ p ∈ ts, ∃ k, ∀ w, toVecD 24 (vmF 24 p.1 w) =
      ((Y ^ k : GL24) : M24) *ᵥ toVecD 24 w) →
    ∀ {w w' : Nat}, w < 2 ^ 24 → w' < 2 ^ 24 → toVecD 24 w' = (c : M24) *ᵥ toVecD 24 w →
      tauK mem ts w' = tauK mem ts w
  | [], _, _, _, _, _, _ => rfl
  | p :: ts, hts, w, w', hw, hw', e => by
    change CFSG.KLie.CT.andB (eqBB (mem (Nat.xor w' (vmF 24 p.1 w'))) p.2) (tauK mem ts w') =
      CFSG.KLie.CT.andB (eqBB (mem (Nat.xor w (vmF 24 p.1 w))) p.2) (tauK mem ts w)
    obtain ⟨k, hk⟩ := hts p List.mem_cons_self
    have hm : mem (Nat.xor w' (vmF 24 p.1 w')) = mem (Nat.xor w (vmF 24 p.1 w)) := by
      refine mem_congr hmem hc (xor_lt24 hw (vmF_lt24 _ _)) (xor_lt24 hw' (vmF_lt24 _ _)) ?_
      change toVecD 24 (w' ^^^ vmF 24 p.1 w') = _ *ᵥ toVecD 24 (w ^^^ vmF 24 p.1 w)
      rw [toVecD_xor, toVecD_xor, hk, hk, e, Matrix.mulVec_add, mulVec_comm hcY]
    rw [hm, tauK_congr hc hcY ts (fun q hq => hts q (List.mem_cons_of_mem p hq)) hw hw' e]

end Cent

section Main


@[expose] noncomputable def vG (I J : GL24) (r : Nat) : GL24 :=
  if r = 0 then 1 else if r = 1 then I else if r = 2 then J else I * J

@[expose] noncomputable def cG (Y I J E : GL24) (t : Nat) : GL24 :=
  Y ^ (t / 12) * vG I J (t / 3 % 4) * E ^ (t % 3)

theorem rep_vK {Ik Jk : Nat} {I J : GL24} (hI : MRep (unpackR 24 Ik) I)
    (hJ : MRep (unpackR 24 Jk) J) {r : Nat} (hr : r < 4) :
    MRep (unpackR 24 (vK Ik Jk r)) (vG I J r) := by
  interval_cases r
  · exact rep_one
  · exact hI
  · exact hJ
  · exact rep_mulWK hI hJ

theorem elem_of_dag {M MI : Nat → Nat} {N : Nat} {ws : List (List Nat)}
    (hdag : CFSG.KS.SporSch.M24.dagWK M MI 2 N ws = true)
    (hA : MRep (unpackR 24 (M 0)) A₁) (hB : MRep (unpackR 24 (M 1)) A₂) {i : Nat} (hi : i < N) :
    ∃ X : GL24, X ∈ GA ∧ MRep (unpackR 24 (M i)) X := by
  have hd := CFSG.KS.SporSch.M24.dagWK_sound (base := (List.range 2).map fun i =>
    CFSG.KS.Raw.unpack 24 24 (M i)) rfl hdag
  obtain ⟨ds, hds⟩ : ∃ ds, ws.map CFSG.Sporadic.Co1Schreier.Native.decWord = ds := ⟨_, rfl⟩
  rw [hds] at hd
  have hb : List.Forall₂ MRep ((List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (M i))
      [A₁, A₂] := by
    have e : ((List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (M i)) =
        [unpackR 24 (M 0), unpackR 24 (M 1)] := by
      rw [CFSG.KS.SporSch.M24.unpackR_eq_unpack, CFSG.KS.SporSch.M24.unpackR_eq_unpack]
      rfl
    rw [e]
    exact .cons hA (.cons hB .nil)
  have hrep := dag_rep hb ds (by rw [hd])
  rw [hd] at hrep
  have hGA : ∀ g ∈ dagG [A₁, A₂] ds, g ∈ GA := dagG_mem (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with e | e
    · rw [e]
      exact A₁_mem
    · rw [e]
      exact A₂_mem) ds
  have h1 := getD_rep hrep MRep.one i
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
    ← CFSG.KS.SporSch.M24.unpackR_eq_unpack] at h1
  exact ⟨_, getD_mem_of_forall hGA _, h1⟩

theorem pow_ne_of_ordK {X : Nat} {g : GL24} {n : Nat} (hX : MRep (unpackR 24 X) g)
    (ho : CFSG.KD.Co1Thirteen.ordK X n = true) : g ^ n = 1 ∧ g ≠ 1 := by
  unfold CFSG.KD.Co1Thirteen.ordK at ho
  rw [andB_eq, Bool.and_eq_true, notB_eq, Bool.not_eq_true'] at ho
  refine ⟨eq_of_eqK (rep_powWK hX n) rep_one ho.1, fun h1 => ?_⟩
  rw [h1] at hX
  rw [eqK_of_eq hX rep_one] at ho
  exact absurd ho.2 (by decide)

theorem comm_of_commK {X Yk : Nat} {g Y : GL24} (hX : MRep (unpackR 24 X) g)
    (hY : MRep (unpackR 24 Yk) Y) (hc : CFSG.KD.Co1Thirteen.commK X Yk = true) :
    g * Y = Y * g :=
  eq_of_eqK (rep_mulWK hX hY) (rep_mulWK hY hX) hc

theorem orderOf_thirteen {Y : GL24} (h : Y ^ 13 = 1 ∧ Y ≠ 1) : orderOf Y = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_eq_prime h.1 h.2

theorem test_act {Yk : Nat} {Y : GL24} (hRY : MRep (unpackR 24 Yk) Y) {tk : List Nat}
    {ts : List (Nat × Bool)} (htk : Nat.beq (lenL tk) (lenP ts) = true)
    (hts : allN (lenL tk) (fun n => Nat.beq (getP ts n) (trK 24 (powWK Yk (getL 0 tk n)))) = true) :
    ∀ p ∈ ts, ∃ k, ∀ w, toVecD 24 (vmF 24 p.1 w) = ((Y ^ k : GL24) : M24) *ᵥ toVecD 24 w := by
  rw [Nat.beq_eq, lenL_eq, lenP_eq] at htk
  rw [lenL_eq, allN_iff] at hts
  intro p hp
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hp
  have e := Nat.eq_of_beq_eq_true (hts n (by omega))
  rw [getP_eq ts n hn] at e
  refine ⟨getL 0 tk n, fun w => ?_⟩
  rw [e]
  exact act_rep (rep_powWK hRY _) w

section Scan

variable {mem : Nat → Bool} (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX)
  {ts : List (Nat × Bool)} {Q : List Nat}
  (hscan : ∀ w < 2 ^ 24, toVecD 24 w ∈ certX → tauK mem ts w = true → w ∈ Q) {Y : GL24}
  (htest : ∀ p ∈ ts, ∃ k, ∀ w, toVecD 24 (vmF 24 p.1 w) = ((Y ^ k : GL24) : M24) *ᵥ toVecD 24 w)
include hmem hscan htest

theorem mapQ {c : GL24} (hc : c ∈ GA) (hcY : c * Y = Y * c) {u : Nat} (hu : u < 2 ^ 24)
    (hmu : mem u = true) (htu : tauK mem ts u = true) :
    ∃ w < 2 ^ 24, toVecD 24 w = (c : M24) *ᵥ toVecD 24 u ∧ w ∈ Q := by
  obtain ⟨w, hw, e⟩ := toVecD_surj ((c : M24) *ᵥ toVecD 24 u)
  refine ⟨w, hw, e, hscan w hw ?_ ?_⟩
  · rw [e]
    exact mulVec_mem_certX hc ((hmem u hu).1 hmu)
  · rw [tauK_congr hmem hc hcY ts htest hu hw e]
    exact htu

omit hmem hscan htest in
theorem fix_xorMask {c : GL24} : ∀ (V : List Nat), (∀ v ∈ V, v < 2 ^ 24 ∧
    (c : M24) *ᵥ toVecD 24 v = toVecD 24 v) → ∀ m,
    xorMask V m < 2 ^ 24 ∧ (c : M24) *ᵥ toVecD 24 (xorMask V m) = toVecD 24 (xorMask V m) := by
  intro V
  induction V with
  | nil =>
    intro _ m
    refine ⟨Nat.two_pow_pos 24, ?_⟩
    change (c : M24) *ᵥ toVecD 24 0 = toVecD 24 0
    rw [toVecD_zero, Matrix.mulVec_zero]
  | cons v V ih =>
    intro hv m
    have ih' := ih (fun x hx => hv x (List.mem_cons_of_mem v hx)) (m >>> 1)
    have hv' := hv v List.mem_cons_self
    have hsel : ∀ b : Bool, Bool.rec (motive := fun _ => Nat) 0 v b < 2 ^ 24 ∧
        (c : M24) *ᵥ toVecD 24 (Bool.rec (motive := fun _ => Nat) 0 v b) =
          toVecD 24 (Bool.rec (motive := fun _ => Nat) 0 v b) := by
      intro b
      cases b
      · refine ⟨Nat.two_pow_pos 24, ?_⟩
        change (c : M24) *ᵥ toVecD 24 0 = toVecD 24 0
        rw [toVecD_zero, Matrix.mulVec_zero]
      · exact hv'
    obtain ⟨hs1, hs2⟩ := hsel (Nat.beq (Nat.land m 1) 1)
    change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 v (Nat.beq (Nat.land m 1) 1))
        (xorMask V (Nat.shiftRight m 1)) < 2 ^ 24 ∧ _
    refine ⟨xor_lt24 hs1 ih'.1, ?_⟩
    change (c : M24) *ᵥ toVecD 24 (_ ^^^ xorMask V (m >>> 1)) =
      toVecD 24 (_ ^^^ xorMask V (m >>> 1))
    rw [toVecD_xor, Matrix.mulVec_add, hs2, ih'.2]

omit hmem hscan htest in
theorem fix_orbL {c : GL24} (hcY : c * Y = Y * c) {T : Nat}
    (hT : ∀ w, toVecD 24 (vmF 24 T w) = (Y : M24) *ᵥ toVecD 24 w) (n u : Nat) (hu : u < 2 ^ 24)
    (hcu : (c : M24) *ᵥ toVecD 24 u = toVecD 24 u) :
    ∀ w ∈ orbL T u n, w < 2 ^ 24 ∧ (c : M24) *ᵥ toVecD 24 w = toVecD 24 w := by
  refine forall_orbL (P := fun w => w < 2 ^ 24 ∧ (c : M24) *ᵥ toVecD 24 w = toVecD 24 w)
    ?_ n u ⟨hu, hcu⟩
  rintro v ⟨-, hv⟩
  refine ⟨vmF_lt24 _ _, ?_⟩
  have e := mulVec_comm hcY 1 (toVecD 24 v)
  rw [pow_one] at e
  rw [hT, e, hv]

theorem stab_trivial {T : Nat} (hT : ∀ w, toVecD 24 (vmF 24 T w) = (Y : M24) *ᵥ toVecD 24 w)
    {u₁ u₂ : Nat} {UM : List Nat} (hu₁' : u₁ < 2 ^ 24) (hu₂' : u₂ < 2 ^ 24)
    (hu₂ : mem u₂ = true) (htu₂ : tauK mem ts u₂ = true)
    (htwo : twoK mem Q u₂ (orbL T u₁ 13) = true)
    (hunit : unitK (orbL T u₁ 12 ++ orbL T u₂ 12) UM = true)
    {c : GL24} (hc : c ∈ GA) (hcY : c * Y = Y * c)
    (hfix : (c : M24) *ᵥ toVecD 24 u₁ = toVecD 24 u₁) : c = 1 := by
  obtain ⟨w, hw, e, hwQ⟩ := mapQ hmem hscan htest hc hcY hu₂' hu₂ htu₂
  have hP := fix_orbL hcY hT 13 u₁ hu₁' hfix
  unfold twoK at htwo
  rw [allL_iff] at htwo
  have h2 := htwo w hwQ
  rw [orB_eq, Bool.or_eq_true, notB_eq, Bool.not_eq_true'] at h2
  have hall : allN 13 (fun k => eqBB (mem (Nat.xor w (getL 0 (orbL T u₁ 13) k)))
      (mem (Nat.xor u₂ (getL 0 (orbL T u₁ 13) k)))) = true := by
    rw [allN_iff]
    intro k hk
    have hk' := hP _ (getL_mem (by rw [orbL_length]; exact hk))
    rw [eqBB_eq, beq_iff_eq]
    refine mem_congr hmem hc (xor_lt24 hu₂' hk'.1) (xor_lt24 hw hk'.1) ?_
    change toVecD 24 (w ^^^ _) = _ *ᵥ toVecD 24 (u₂ ^^^ _)
    rw [toVecD_xor, toVecD_xor, Matrix.mulVec_add, e, hk'.2]
  rcases h2 with h2 | h2
  · have hwu : w = u₂ := Nat.eq_of_beq_eq_true h2
    rw [hwu] at e
    have hV : ∀ v ∈ orbL T u₁ 12 ++ orbL T u₂ 12,
        v < 2 ^ 24 ∧ (c : M24) *ᵥ toVecD 24 v = toVecD 24 v := by
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact fix_orbL hcY hT 12 u₁ hu₁' hfix v hv
      · exact fix_orbL hcY hT 12 u₂ hu₂' e.symm v hv
    unfold unitK at hunit
    rw [allN_iff] at hunit
    apply Units.ext
    rw [Units.val_one]
    refine Matrix.ext_of_mulVec_single fun b => ?_
    have hb := Nat.eq_of_beq_eq_true (hunit b b.2)
    have hm := (fix_xorMask _ hV (getL 0 UM b)).2
    rw [hb, pw2_eq, toVecD_two_pow] at hm
    rw [Matrix.one_mulVec]
    exact hm
  · exact absurd (h2.symm.trans hall) (by decide)

end Scan

theorem comm_of_mem_cent {Y : GL24} {hY : Y ∈ GA} {c : GA}
    (hc : c ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) : (c : GL24) * Y = Y * c := by
  have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
  exact h1

theorem mem_cent_of_comm {Y : GL24} {hY : Y ∈ GA} {c : GA} (hc : (c : GL24) * Y = Y * c) :
    c ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact hc

theorem card_cent_le {Y : GL24} (hY : Y ∈ GA) {Q : List Nat} (hQ : Nat.beq (lenL Q) 156 = true)
    {u₁ : Nat}
    (hmapQ : ∀ c : GL24, c ∈ GA → c * Y = Y * c →
      ∃ w < 2 ^ 24, toVecD 24 w = (c : M24) *ᵥ toVecD 24 u₁ ∧ w ∈ Q)
    (hstab : ∀ c : GL24, c ∈ GA → c * Y = Y * c → (c : M24) *ᵥ toVecD 24 u₁ = toVecD 24 u₁ →
      c = 1) :
    Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) ≤ 156 := by
  classical
  set Qv := (Q.map (toVecD 24)).toFinset
  have hf : ∀ c : Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA),
      (((c : GA) : GL24) : M24) *ᵥ toVecD 24 u₁ ∈ Qv := by
    intro c
    obtain ⟨w, -, e, hwQ⟩ := hmapQ _ (c : GA).2 (comm_of_mem_cent c.2)
    rw [← e]
    exact List.mem_toFinset.2 (List.mem_map_of_mem hwQ)
  have hinj : Function.Injective fun c : Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA) =>
      (⟨_, hf c⟩ : Qv) := by
    intro c d e
    simp only [Subtype.mk.injEq] at e
    have h1 : ((c : GA) : GL24)⁻¹ * (d : GA) = 1 := by
      refine hstab _ (GA.mul_mem (GA.inv_mem (c : GA).2) (d : GA).2)
        (comm_mul' (comm_inv' (comm_of_mem_cent c.2)) (comm_of_mem_cent d.2)) ?_
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← e, mulVec_inv_mul]
    exact Subtype.ext (Subtype.ext (eq_of_inv_mul h1))
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at h1
  refine h1.trans ((List.toFinset_card_le _).trans ?_)
  rw [List.length_map, ← lenL_eq]
  exact (Nat.eq_of_beq_eq_true hQ).le

theorem rep_CT {Yk Ik Jk Ek : Nat} {Y I J E : GL24} (hRY : MRep (unpackR 24 Yk) Y)
    (hRI : MRep (unpackR 24 Ik) I) (hRJ : MRep (unpackR 24 Jk) J) (hRE : MRep (unpackR 24 Ek) E)
    {CT : List Nat} (hcent : centK Yk Ik Jk Ek CT = true) :
    CT.length = 156 ∧ ∀ t < 156, MRep (unpackR 24 (getL 0 CT t)) (cG Y I J E t) := by
  unfold centK at hcent
  rw [andB_eq, Bool.and_eq_true, allN_iff, lenL_eq] at hcent
  obtain ⟨hCTl, hCT⟩ := hcent
  refine ⟨Nat.eq_of_beq_eq_true hCTl, fun t ht => ?_⟩
  have e := hCT t ht
  rw [← beq_unpack, beq_iff_eq] at e
  rw [e]
  exact rep_mulWK (rep_mulWK (rep_powWK hRY _) (rep_vK hRI hRJ (Nat.mod_lt _ (by norm_num))))
    (rep_powWK hRE _)

theorem cG_mem {Y I J E : GL24} (hY : Y ∈ GA) (hI : I ∈ GA) (hJ : J ∈ GA) (hE : E ∈ GA) (t : Nat) :
    cG Y I J E t ∈ GA := by
  have hv : ∀ r, vG I J r ∈ GA := by
    intro r
    unfold vG
    split_ifs
    · exact GA.one_mem
    · exact hI
    · exact hJ
    · exact GA.mul_mem hI hJ
  exact GA.mul_mem (GA.mul_mem (GA.pow_mem hY _) (hv _)) (GA.pow_mem hE _)

theorem cG_comm {Y I J E : GL24} (hIY : I * Y = Y * I) (hJY : J * Y = Y * J)
    (hEY : E * Y = Y * E) (t : Nat) : cG Y I J E t * Y = Y * cG Y I J E t := by
  have hv : ∀ r, vG I J r * Y = Y * vG I J r := by
    intro r
    unfold vG
    split_ifs
    · rw [one_mul, mul_one]
    · exact hIY
    · exact hJY
    · exact comm_mul' hIY hJY
  exact comm_mul' (comm_mul' (comm_pow' rfl _) (hv _)) (comm_pow' hEY _)

theorem cG_inj {Y I J E : GL24} {CT : List Nat} (hCTl : CT.length = 156)
    (hrepCT : ∀ t < 156, MRep (unpackR 24 (getL 0 CT t)) (cG Y I J E t)) {u₁ : Nat}
    (hnd : nodupK (CT.map fun g => vmF 24 (trK 24 g) u₁) = true)
    {s t : Nat} (hs : s < 156) (ht : t < 156) (e : cG Y I J E s = cG Y I J E t) : s = t := by
  have hnd' := nodupK_nodup _ hnd
  have hl : (CT.map (fun g => vmF 24 (trK 24 g) u₁)).length = 156 := by
    rw [List.length_map, hCTl]
  have hval : ∀ r (hr : r < 156), toVecD 24 ((CT.map (fun g => vmF 24 (trK 24 g) u₁))[r]'(by
      rw [hl]; exact hr)) = (cG Y I J E r : M24) *ᵥ toVecD 24 u₁ := by
    intro r hr
    rw [List.getElem_map, ← getL_eq CT r (by rw [hCTl]; exact hr)]
    exact act_rep (hrepCT r hr) u₁
  have h1 := toVecD_injective (by rw [List.getElem_map]; exact vmF_lt24 _ _)
    (by rw [List.getElem_map]; exact vmF_lt24 _ _)
    ((hval s hs).trans ((congrArg (fun g : GL24 => (g : M24) *ᵥ toVecD 24 u₁) e).trans
      (hval t ht).symm))
  exact (List.Nodup.getElem_inj_iff hnd').1 h1

theorem cent_eq {Y I J E : GL24} (hY : Y ∈ GA) (hI : I ∈ GA) (hJ : J ∈ GA) (hE : E ∈ GA)
    (hIY : I * Y = Y * I) (hJY : J * Y = Y * J) (hEY : E * Y = Y * E)
    (hinj : ∀ {s t : Nat}, s < 156 → t < 156 → cG Y I J E s = cG Y I J E t → s = t)
    (hle : Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) ≤ 156) :
    Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) = 156 ∧
      ∀ g ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA), ∃ t < 156,
        (g : GL24) = cG Y I J E t := by
  have : Finite GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  let F : Fin 156 → Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA) := fun t =>
    ⟨⟨cG Y I J E t, cG_mem hY hI hJ hE t⟩, mem_cent_of_comm (cG_comm hIY hJY hEY t)⟩
  have hFinj : Function.Injective F := by
    intro s t e
    simp only [F, Subtype.mk.injEq] at e
    exact Fin.ext (hinj s.2 t.2 e)
  have hge := Nat.card_le_card_of_injective F hFinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hge
  have hcard := le_antisymm hle hge
  have hFbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).2 ⟨hFinj, by rw [hcard, Nat.card_eq_fintype_card,
      Fintype.card_fin]⟩
  refine ⟨hcard, fun g hg => ?_⟩
  obtain ⟨t, ht⟩ := hFbij.2 ⟨g, hg⟩
  simp only [F, Subtype.mk.injEq] at ht
  exact ⟨t, t.2, by rw [← ht]⟩

theorem conj_three {g z : GA} (hz3 : orderOf z = 3) (hgz : g * z * g⁻¹ ∈ Subgroup.zpowers z) :
    g * z = z * g ∨ g * z = z * z * g := by
  have hconj : g * z = g * z * g⁻¹ * g := (inv_mul_cancel_right (g * z) g).symm
  rcases eq_of_mem_zpowers_three hz3 hgz with e | e | e
  · exfalso
    have hz1 : z = 1 := mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.1 e)
    rw [hz1, orderOf_one] at hz3
    exact absurd hz3 (by decide)
  · left
    rw [hconj, e]
  · right
    rw [hconj, e]

theorem norm_GA {Y : GL24} {hY : Y ∈ GA} {CT : List Nat} (hCTl : CT.length = 156)
    (hnorm : CFSG.KD.Co1Thirteen.normK CT = true)
    (hall : ∀ g ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA), ∃ t < 156,
      MRep (unpackR 24 (getL 0 CT t)) (g : GL24))
    (g : GA) (hg : g ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA))
    (z : GA) (hz : z ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA))
    (hz3 : orderOf z = 3) (hgz : g * z * g⁻¹ ∈ Subgroup.zpowers z) : g ^ 39 = 1 := by
  obtain ⟨s, hs, hRg⟩ := hall g hg
  obtain ⟨t, ht, hRz⟩ := hall z hz
  have hz1' : (z : GL24) ≠ 1 := by
    intro e
    have hz1 : z = 1 := Subtype.ext e
    rw [hz1, orderOf_one] at hz3
    exact absurd hz3 (by decide)
  have hz3' : (z : GL24) ^ 3 = 1 := by
    have e := pow_orderOf_eq_one z
    rw [hz3] at e
    rw [← Subgroup.coe_pow, e, Subgroup.coe_one]
  unfold CFSG.KD.Co1Thirteen.normK at hnorm
  rw [allL_iff] at hnorm
  have h1 := hnorm _ (getL_mem (by rw [hCTl]; exact ht))
  rw [orB_eq, Bool.or_eq_true, notB_eq, Bool.not_eq_true', andB_eq, Bool.and_eq_false_iff,
    notB_eq, Bool.not_eq_false', allL_iff] at h1
  rcases h1 with (h1 | h1) | h1
  · rw [eqK_of_eq (rep_powWK hRz 3) (by rw [hz3']; exact rep_one)] at h1
    exact absurd h1 (by decide)
  · exact absurd (eq_of_eqK hRz rep_one h1) hz1'
  have h2 := h1 _ (getL_mem (by rw [hCTl]; exact hs))
  rw [orB_eq, Bool.or_eq_true, notB_eq, Bool.not_eq_true', orB_eq, Bool.or_eq_false_iff] at h2
  rcases h2 with ⟨ha, hb⟩ | h2
  · rcases conj_three hz3 hgz with e | e
    · have e' := congrArg (fun a : GA => (a : GL24)) e
      simp only [Subgroup.coe_mul] at e'
      rw [eqK_of_eq (rep_mulWK hRg hRz) (by rw [e']; exact rep_mulWK hRz hRg)] at ha
      exact absurd ha (by decide)
    · have e' := congrArg (fun a : GA => (a : GL24)) e
      simp only [Subgroup.coe_mul] at e'
      rw [eqK_of_eq (rep_mulWK hRg hRz) (by rw [e']; exact rep_mulWK (rep_mulWK hRz hRz) hRg)]
        at hb
      exact absurd hb (by decide)
  · have e := eq_of_eqK (rep_powWK (rep_powWK hRg 3) 13) rep_one h2
    apply Subtype.ext
    have e39 : (39 : ℕ) = 3 * 13 := rfl
    rw [Subgroup.coe_pow, Subgroup.coe_one, e39, pow_mul]
    exact e

theorem thirteen_GA {mem : Nat → Bool} {M MI : Nat → Nat} {N : Nat} {ws : List (List Nat)}
    {ix tk : List Nat} {ts : List (Nat × Bool)} {Q : List Nat} {u₁ u₂ : Nat} {UM CT : List Nat}
    (h : thirteenOK mem M MI N ws ix tk ts Q u₁ u₂ UM CT = true)
    (hA : MRep (unpackR 24 (M 0)) A₁) (hB : MRep (unpackR 24 (M 1)) A₂)
    (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX)
    (hscan : ∀ w < 2 ^ 24, toVecD 24 w ∈ certX → tauK mem ts w = true → w ∈ Q)
    (hu₁ : mem u₁ = true) (hu₂ : mem u₂ = true) :
    ∃ Y : GL24, ∃ hY : Y ∈ GA, orderOf Y = 13 ∧
      Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) = 156 ∧
      ∀ g ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA),
        ∀ z ∈ Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA),
          orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1 := by
  unfold thirteenOK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hdag, hix4, hixN, hoY, hoE, hoI, hoJ, hcE, hcI, hcJ, htk, hts, hQ, hu₁l, hu₂l, -, -,
    htu₁, htu₂, htwo, hunit, hcent, hnd, hnorm⟩ := h
  rw [Nat.beq_eq, lenL_eq] at hix4
  rw [allL_iff] at hixN
  have hixN' : ∀ k < 4, getL 0 ix k < N := fun k hk =>
    Eq.mp Nat.blt_eq (hixN _ (getL_mem (by omega)))
  obtain ⟨Y, hY, hRY⟩ := elem_of_dag hdag hA hB (hixN' 0 (by norm_num))
  obtain ⟨E, hE, hRE⟩ := elem_of_dag hdag hA hB (hixN' 1 (by norm_num))
  obtain ⟨I, hI, hRI⟩ := elem_of_dag hdag hA hB (hixN' 2 (by norm_num))
  obtain ⟨J, hJ, hRJ⟩ := elem_of_dag hdag hA hB (hixN' 3 (by norm_num))
  have hoY13 := orderOf_thirteen (pow_ne_of_ordK hRY hoY)
  have hEY := comm_of_commK hRE hRY hcE
  have hIY := comm_of_commK hRI hRY hcI
  have hJY := comm_of_commK hRJ hRY hcJ
  have htest := test_act hRY htk hts
  have hu₁' : u₁ < 2 ^ 24 := by rw [← pw2_eq]; exact Eq.mp Nat.blt_eq hu₁l
  have hu₂' : u₂ < 2 ^ 24 := by rw [← pw2_eq]; exact Eq.mp Nat.blt_eq hu₂l
  have hT : ∀ w, toVecD 24 (vmF 24 (trK 24 (M (getL 0 ix 0))) w) = (Y : M24) *ᵥ toVecD 24 w :=
    act_rep hRY
  have hle := card_cent_le hY hQ (fun c hc hcY => mapQ hmem hscan htest hc hcY hu₁' hu₁ htu₁)
    (fun c hc hcY hfix => stab_trivial hmem hscan htest hT hu₁' hu₂' hu₂ htu₂ htwo hunit hc hcY
      hfix)
  obtain ⟨hCTl, hrepCT⟩ := rep_CT hRY hRI hRJ hRE hcent
  obtain ⟨hcard, hall⟩ := cent_eq hY hI hJ hE hIY hJY hEY (cG_inj hCTl hrepCT hnd) hle
  refine ⟨Y, hY, hoY13, hcard, norm_GA hCTl hnorm fun g hg => ?_⟩
  obtain ⟨t, ht, e⟩ := hall g hg
  exact ⟨t, ht, by rw [e]; exact hrepCT t ht⟩

end Main

@[expose] def NoEvenN {K : Type*} [Group K] (x : K) : Prop :=
  ∀ g ∈ Subgroup.centralizer ({x} : Set K), ∀ z ∈ Subgroup.centralizer ({x} : Set K),
    orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1

theorem noEvenN_map {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {x : K}
    (h : NoEvenN x) : NoEvenN (e x) := by
  have hmem : ∀ a : K', a ∈ Subgroup.centralizer ({e x} : Set K') →
      e.symm a ∈ Subgroup.centralizer ({x} : Set K) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ha]
  intro g hg z hz hz3 hgz
  have hz3' : orderOf (e.symm z) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz3
  have hgz' : e.symm g * e.symm z * (e.symm g)⁻¹ ∈ Subgroup.zpowers (e.symm z) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgz
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, hk, map_mul, map_mul, map_inv]
  have h39 := h _ (hmem g hg) _ (hmem z hz) hz3' hgz'
  have := congrArg e h39
  rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this

theorem noEvenN_of_centralizer_eq {K : Type*} [Group K] {x x' : K}
    (hc : Subgroup.centralizer ({x'} : Set K) = Subgroup.centralizer ({x} : Set K))
    (h : NoEvenN x) : NoEvenN x' := by
  intro g hg z hz
  rw [hc] at hg hz
  exact h g hg z hz

theorem facts_of_conj_pow13 {K K' : Type*} [Group K] [Group K'] [Finite K'] (φ : K ≃* K')
    {y : K} {p : ℕ} [Fact p.Prime] (hy : orderOf (φ y) = p)
    (hfac : (Nat.card K').factorization p = 1) (hN : NoEvenN y) {c : ℕ}
    (hc : Nat.card (Subgroup.centralizer ({y} : Set K)) = c) {x : K'} (hx : orderOf x = p) :
    Nat.card (Subgroup.centralizer ({x} : Set K')) = c ∧ NoEvenN x := by
  obtain ⟨g, k, hxk⟩ := exists_conj_pow_of_factorization_eq_one hfac hy hx
  have hk1 : (φ y) ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hxk
    rw [hxk, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hpow := centralizer_pow_eq_of_prime hy hk1
  refine ⟨?_, ?_⟩
  · rw [hxk, card_centralizer_conj_eq, hpow, card_centralizer_mulEquiv_apply, hc]
  · have h1 : NoEvenN ((φ y) ^ k) := noEvenN_of_centralizer_eq hpow (noEvenN_map φ hN)
    have h2 := noEvenN_map (MulAut.conj g) h1
    rwa [MulAut.conj_apply, ← hxk] at h2


theorem factorization_Co1_thirteen :
    (Nat.card CFSG.Blueprint.NativeSporadic.Co1).factorization 13 = 1 := by
  rw [CFSG.Sporadic.Co1.card_Co1,
    show (4157776806543360000 : ℕ) = 13 * 319828985118720000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem co1_thirteen_of_GA {Y : GL24} (hY : Y ∈ GA) (hoY : orderOf Y = 13)
    (hcard : Nat.card (Subgroup.centralizer ({(⟨Y, hY⟩ : GA)} : Set GA)) = 156)
    (hN : NoEvenN (⟨Y, hY⟩ : GA)) (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
      NoEvenN x := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Finite CFSG.Blueprint.NativeSporadic.Co1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
  have hy : orderOf (co1MatEquiv.symm (⟨Y, hY⟩ : GA)) = 13 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hoY]
  exact @facts_of_conj_pow13 GA CFSG.Blueprint.NativeSporadic.Co1 GA.toGroup Units.instGroup _
    co1MatEquiv.symm ⟨Y, hY⟩ 13 _ hy factorization_Co1_thirteen hN 156 hcard x hx

theorem co1_thirteen_of_check {mem : Nat → Bool} {M MI : Nat → Nat} {N : Nat}
    {ws : List (List Nat)} {ix tk : List Nat} {ts : List (Nat × Bool)} {Q : List Nat}
    {u₁ u₂ : Nat} {UM CT : List Nat}
    (h : thirteenOK mem M MI N ws ix tk ts Q u₁ u₂ UM CT = true)
    (hA : MRep (unpackR 24 (M 0)) A₁) (hB : MRep (unpackR 24 (M 1)) A₂)
    (hmem : ∀ w < 2 ^ 24, mem w = true ↔ toVecD 24 w ∈ certX)
    (hscan : ∀ w < 2 ^ 24, toVecD 24 w ∈ certX → tauK mem ts w = true → w ∈ Q)
    (hu₁ : mem u₁ = true) (hu₂ : mem u₂ = true)
    (x : CFSG.Blueprint.NativeSporadic.Co1) (hx : orderOf x = 13) :
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) = 156 ∧
      ∀ g ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
        ∀ z ∈ Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1),
          orderOf z = 3 → g * z * g⁻¹ ∈ Subgroup.zpowers z → g ^ 39 = 1 := by
  obtain ⟨Y, hY, hoY, hcard, hN⟩ := thirteen_GA h hA hB hmem hscan hu₁ hu₂
  exact co1_thirteen_of_GA hY hoY hcard hN x hx

end CFSG.KC.Co1ThirteenGlue

end
