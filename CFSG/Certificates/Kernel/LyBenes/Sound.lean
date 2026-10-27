module

public import Certificates.Data.Kernel.LyBenes.Check
public import CFSG.Certificates.Kernel.YModel.NetSem
public import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.KDense.SortSound

public section

namespace CFSG.KC.LyBenes

open Equiv CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.YModel.Sem

theorem acts_netsApply_one {k : Nat} {Ns : List Nat} (hv : ∀ N ∈ Ns, StagesValid k N) :
    Acts k 1 (compN k Ns) (netsApply k (Nat.shiftLeft 1 k) 1 Ns) := by
  have h := acts_netsApply (k := k) (P := 1) Ns hv
  rwa [← repU_one' k, ← shl1] at h

theorem acts_netApply_one {k N : Nat} (hv : StagesValid k N) :
    Acts k 1 (benesPerm k N) (netApply k (Nat.shiftLeft 1 k) 1 N) := by
  have h := acts_netApply (k := k) (P := 1) hv
  rwa [← repU_one' k, ← shl1] at h

theorem testBit_acts_idPlane {k u r : Nat} {f F : Nat → Nat} (hF : Acts k 1 f F) (hu : u < k)
    (hr : r < 2 ^ k) : (F (idPlane (Nat.shiftLeft 1 k) u)).testBit r = (f r).testBit u := by
  have h := hF.2 (idPlane (Nat.shiftLeft 1 k) u) 0 (by decide) r hr
  simp only [Nat.mul_zero, Nat.zero_add] at h
  rw [h, shl1, idPlane_testBit hu, decide_eq_true (hF.1 r hr), Bool.true_and]

theorem planesId_sound {k : Nat} {Ns : List Nat} (hv : ∀ N ∈ Ns, StagesValid k N)
    (h : planesId k Ns = true) : ∀ r < 2 ^ k, compN k Ns r = r := by
  have hA := acts_netsApply_one hv
  have hb := recAll_right (P := fun b => Nat.beq (netsApply k (Nat.shiftLeft 1 k) 1 Ns
    (idPlane (Nat.shiftLeft 1 k) b)) (idPlane (Nat.shiftLeft 1 k) b)) k h
  intro r hr
  apply eq_of_bits (hA.1 r hr) hr
  intro u hu
  have e := congrArg (fun x => Nat.testBit x r) (Nat.eq_of_beq_eq_true (hb u hu))
  rw [testBit_acts_idPlane hA hu hr, shl1, idPlane_testBit hu, decide_eq_true hr,
    Bool.true_and] at e
  exact e

theorem planesEq_sound {k N : Nat} {Ns : List Nat} (hv : ∀ M ∈ Ns, StagesValid k M)
    (hN : StagesValid k N) (h : planesEq k Ns N = true) :
    ∀ r < 2 ^ k, compN k Ns r = benesPerm k N r := by
  have hA := acts_netsApply_one hv
  have hB := acts_netApply_one hN
  have hb := recAll_right (P := fun b => Nat.beq (netsApply k (Nat.shiftLeft 1 k) 1 Ns
    (idPlane (Nat.shiftLeft 1 k) b)) (netApply k (Nat.shiftLeft 1 k) 1 N
      (idPlane (Nat.shiftLeft 1 k) b))) k h
  intro r hr
  apply eq_of_bits (hA.1 r hr) (hB.1 r hr)
  intro u hu
  have e := congrArg (fun x => Nat.testBit x r) (Nat.eq_of_beq_eq_true (hb u hu))
  rw [testBit_acts_idPlane hA hu hr, testBit_acts_idPlane hB hu hr] at e
  exact e

@[expose] def NRep (k n N : Nat) (g : Perm (Fin n)) : Prop := ∀ a : Fin n, benesPerm k N a = g a

theorem compN_map {k n : Nat} {α : Type*} (net : α → Nat) (gf : α → Perm (Fin n)) :
    ∀ w : List α, (∀ x ∈ w, NRep k n (net x) (gf x)) →
      ∀ a : Fin n, compN k (w.map net) a = ((w.map gf).prod a : Nat)
  | [], _, a => rfl
  | x :: w, h, a => by
    have ih := compN_map net gf w (fun y hy => h y (List.mem_cons_of_mem _ hy)) a
    change benesPerm k (net x) (compN k (w.map net) a) = _
    rw [ih, h x List.mem_cons_self, List.map_cons, List.prod_cons, Perm.mul_apply]

theorem prod_eq_one {k n : Nat} (hn : n ≤ 2 ^ k) {α : Type*} (net : α → Nat)
    (gf : α → Perm (Fin n)) (w : List α) (hr : ∀ x ∈ w, NRep k n (net x) (gf x))
    (hid : ∀ r < 2 ^ k, compN k (w.map net) r = r) : (w.map gf).prod = 1 := by
  refine Equiv.ext fun a => Fin.ext ?_
  rw [← compN_map net gf w hr a, hid a (by omega)]
  rfl

theorem NRep.inv {k n N M : Nat} {g : Perm (Fin n)} (hN : NRep k n N g) (hn : n ≤ 2 ^ k)
    (h : ∀ r < 2 ^ k, compN k [M, N] r = r) : NRep k n M g⁻¹ := by
  intro b
  have e := h (g⁻¹ b) (by omega)
  change benesPerm k M (benesPerm k N (g⁻¹ b)) = (g⁻¹ b : Nat) at e
  have hb : g (g⁻¹ b) = b := by rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
  rw [hN (g⁻¹ b), hb] at e
  exact e

theorem land_ones_lt' (x w : Nat) : Nat.land x (ones w) < 2 ^ w :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [nland, Nat.testBit_and, KDense.SortAux.testBit_ones, decide_eq_false (by omega),
      Bool.and_false]

theorem testBit_rawOf (T : Nat → Nat) {j s : Nat} (hj : j < 15) (hs : s < 75735) :
    (rawOf T).testBit (75735 * j + s) = (T j).testBit s := by
  have h := (testBit_planes (S := 75735) (fun j => Nat.land (T j) (ones 75735)) 15
    (fun b _ => land_ones_lt' (T b) 75735)).1 j hj s hs
  refine h.trans ?_
  change (Nat.land (T j) (ones 75735)).testBit s = _
  rw [nland, Nat.testBit_and, KDense.SortAux.testBit_ones, decide_eq_true hs, Bool.and_true]

theorem testBit_tabPlane {RAW b a : Nat} (ha : a < 66825) :
    (tabPlane RAW b).testBit a = RAW.testBit (17 * a + b) := by
  have h1 : a < 131072 := by omega
  unfold tabPlane
  simp only [nlor, nland, nxor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    KDense.SortAux.testBit_ones]
  rw [KDense.SortAux.testBit_rawPlane (rec := 17) (n := 131072) (h := 17) (by decide) (by norm_num)]
  simp [ha, h1]

theorem tabPlane_lt (RAW b : Nat) : tabPlane RAW b < 2 ^ 131072 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have h1 : ¬ i < 66825 := by omega
  have h2 : ¬ i < 131072 := by omega
  unfold tabPlane
  simp only [nlor, nland, nxor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor,
    KDense.SortAux.testBit_ones]
  simp [h1, h2]

theorem testBit_tabPlanes (T : Nat → Nat) {u a : Nat} (hu : u < 17) (ha : a < 66825) :
    (tabPlanes T).testBit (131072 * u + a) = (rawOf T).testBit (17 * a + u) := by
  have h := (testBit_planes (S := 131072) (fun b => tabPlane (rawOf T) b) 17
    (fun b _ => tabPlane_lt _ _)).1 u hu a (by omega)
  refine Eq.trans ?_ (h.trans (testBit_tabPlane ha))
  exact congrArg (fun x => Nat.testBit x (131072 * u + a)) (strictN_eq (rawOf T) fun RAW =>
    Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.lor acc (Nat.shiftLeft (tabPlane RAW b) (Nat.mul b 131072))) 17)

theorem bindOK_sound {T : Nat → Nat} {N : Nat} (h : bindOK T N = true) :
    StagesValid 17 N ∧ ∀ a < 66825,
      benesPerm 17 N a = Enum.pg 17 (KS.mask 17) (T (a / 4455)) (a % 4455) := by
  obtain ⟨h1, h2⟩ := andB_true h
  have hv := stagesValid_of_netValid h1
  refine ⟨hv, fun a ha => ?_⟩
  have e := Nat.eq_of_beq_eq_true h2
  have hW : (131072 : Nat) = 2 ^ 17 := by norm_num
  have ha' : a < 2 ^ 17 := by omega
  apply eq_of_bits (benesPerm_lt hv ha') (KS.PackFld.pg_lt 17 _ _)
  intro u hu
  have e1 := congrArg (fun x => Nat.testBit x (131072 * u + a)) e
  rw [(testBit_netApply hW hv (idP 17)).1 u hu a (by omega), testBit_tabPlanes T hu ha] at e1
  have e2 : (idP 17).testBit (131072 * u + benesPerm 17 N a) = (benesPerm 17 N a).testBit u := by
    rw [hW]
    exact testBit_idP hu (benesPerm_lt hv ha')
  rw [e2] at e1
  have e3 : 17 * a + u = 75735 * (a / 4455) + (17 * (a % 4455) + u) := by omega
  rw [e1, KS.PackFld.testBit_pgM, decide_eq_true hu, Bool.true_and, e3,
    testBit_rawOf T (j := a / 4455) (s := 17 * (a % 4455) + u) (by omega) (by omega)]

end CFSG.KC.LyBenes

end
