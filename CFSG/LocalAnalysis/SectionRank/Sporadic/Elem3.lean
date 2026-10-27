module

public import CFSG.Open.Defs
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.SectionRank.Native
open scoped Matrix

section Group

variable {G : Type*} [Group G]

theorem exists_isElemAbelian_of_injective {p : ℕ} {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) {k : ℕ}
    (hA : Nat.card A = p ^ k) (f : A →* G) (hf : Function.Injective f) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  refine ⟨f.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

noncomputable def elem3PowHom {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 3 = 1) : (Fin r → Multiplicative (ZMod 3)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

open scoped IsMulCommutative in
theorem exists_elemAbelian_of_commuting {r : ℕ} (u : Fin r → G) (hpow : ∀ i, u i ^ 3 = 1)
    (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 3, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 3 = 1 := fun i => Subtype.ext (by simpa [v] using hpow i)
  let φ : (Fin r → Multiplicative (ZMod 3)) →* G := C.subtype.comp (elem3PowHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, elem3PowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  refine exists_isElemAbelian_of_injective (p := 3) (k := r) mul_comm (fun a => ?_) ?_ φ ?_
  · funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    generalize Multiplicative.toAdd (a i) = z
    revert z
    decide
  · simp [Nat.card_eq_fintype_card]
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
    funext i
    exact Multiplicative.toAdd.injective (congrFun h0 i)

end Group

theorem exists_elemAbelian_units {M : Type*} [Monoid M] (S : Submonoid M) {r : ℕ}
    (x : Fin r → M) (hS : ∀ i, x i ∈ S) (hpow : ∀ i, x i ^ 3 = 1)
    (hcomm : ∀ i j, x i * x j = x j * x i)
    (hker : ∀ a : Fin r → Fin 3, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ E : Subgroup Sˣ, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  have h3 : ∀ i, (⟨x i, hS i⟩ : S) ^ 3 = 1 := fun i => Subtype.ext (by simpa using hpow i)
  let u : Fin r → Sˣ := fun i => Units.ofPowEqOne _ 3 (h3 i) (by norm_num)
  let f : Sˣ →* M := S.subtype.comp (Units.coeHom S)
  have hf : ∀ i (n : ℕ), f (u i ^ n) = x i ^ n := fun i n => by
    rw [map_pow]
    rfl
  refine exists_elemAbelian_of_commuting u (fun i => Units.pow_ofPowEqOne _ _)
    (fun i j => Units.ext (Subtype.ext (hcomm i j))) (fun a ha h => hker a ha ?_)
  have := congrArg f h
  rwa [map_list_prod, List.map_ofFn, map_one, Function.comp_def, funext fun i => hf i _] at this

@[expose] def enc : (r : ℕ) → (Fin r → Fin 3) → ℕ
  | 0, _ => 0
  | r + 1, a => (a 0 : ℕ) + 3 * enc r (Fin.tail a)

theorem enc_lt : ∀ (r : ℕ) (a : Fin r → Fin 3), enc r a < 3 ^ r
  | 0, _ => by simp [enc]
  | r + 1, a => by
    have := enc_lt r (Fin.tail a)
    have := (a 0).isLt
    rw [enc, pow_succ]
    omega

theorem eq_zero_of_enc_eq_zero : ∀ (r : ℕ) (a : Fin r → Fin 3), enc r a = 0 → a = 0
  | 0, a, _ => funext fun i => i.elim0
  | r + 1, a, h => by
    rw [enc] at h
    have h0 : (a 0 : ℕ) = 0 := by omega
    have ht := eq_zero_of_enc_eq_zero r (Fin.tail a) (by omega)
    funext i
    refine Fin.cases (Fin.ext h0) (fun j => ?_) i
    exact congrFun ht j

structure OpsSpec {M V : Type} (O : Ops M V) (p d : ℕ) where
  toMat : M → Matrix (Fin d) (Fin d) (ZMod p)
  toVec : V → Fin d → ZMod p
  WF : M → Prop
  VWF : V → Prop
  decode_wf (s : String) : WF (O.decode s)
  toMat_decode (s : String) : toMat (O.decode s) = NativeSporadic.decode p d 1 s
  mul_wf {X Y : M} : WF X → WF Y → WF (O.mul X Y)
  toMat_mul {X Y : M} : WF X → WF Y → toMat (O.mul X Y) = toMat X * toMat Y
  one_wf : WF O.one
  toMat_one : toMat O.one = 1
  toMat_eq {X Y : M} : WF X → WF Y → O.eq X Y = true → toMat X = toMat Y
  vmul_wf {v : V} {X : M} : VWF v → WF X → VWF (O.vmul v X)
  toVec_vmul {v : V} {X : M} : VWF v → WF X → toVec (O.vmul v X) = toVec v ᵥ* toMat X
  unit_wf (k : ℕ) : VWF (O.unit k)
  toVec_ne {u w : V} : O.vne u w = true → toVec u ≠ toVec w

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem pow_spec {X : M} (hX : Sp.WF X) (e : ℕ) :
    Sp.WF (O.pow X e) ∧ Sp.toMat (O.pow X e) = Sp.toMat X ^ e := by
  induction e using Nat.strong_induction_on generalizing X with
  | _ e ih =>
    rw [Ops.pow]
    by_cases he : e = 0
    · rw [ite_eq_left he, he, pow_zero]
      exact ⟨Sp.one_wf, Sp.toMat_one⟩
    rw [ite_eq_right he]
    by_cases he1 : e = 1
    · rw [ite_eq_left he1, he1, pow_one]
      exact ⟨hX, rfl⟩
    rw [ite_eq_right he1]
    have hXX := Sp.mul_wf hX hX
    obtain ⟨hY, hYm⟩ := ih (e / 2) (by omega) hXX
    rw [Sp.toMat_mul hX hX, ← sq, ← pow_mul] at hYm
    by_cases ho : e % 2 = 1
    · rw [ite_eq_left ho]
      refine ⟨Sp.mul_wf hX hY, ?_⟩
      rw [Sp.toMat_mul hX hY, hYm, ← pow_succ']
      congr 1
      omega
    · rw [ite_eq_right ho]
      refine ⟨hY, ?_⟩
      rw [hYm]
      congr 1
      omega

theorem app_spec {X : M} (hX : Sp.WF X) (n : ℕ) {v : V} (hv : Sp.VWF v) :
    Sp.VWF (O.app X n v) ∧ Sp.toVec (O.app X n v) = Sp.toVec v ᵥ* Sp.toMat X ^ n := by
  induction n generalizing v with
  | zero => exact ⟨hv, by rw [Ops.app, pow_zero, Matrix.vecMul_one]⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (Sp.vmul_wf hv hX)
    refine ⟨h1, ?_⟩
    rw [Ops.app, h2, Sp.toVec_vmul hv hX, Matrix.vecMul_vecMul, ← pow_succ']

theorem appDigits_spec : ∀ (xs : List M), (∀ X ∈ xs, Sp.WF X) →
    ∀ (a : Fin xs.length → Fin 3) {v : V}, Sp.VWF v →
      Sp.VWF (O.appDigits xs (enc _ a) v) ∧ Sp.toVec (O.appDigits xs (enc _ a) v) =
        Sp.toVec v ᵥ* (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod
  | [], _, a, v, hv => ⟨hv, by simp [Ops.appDigits]⟩
  | X :: xs, hxs, a, v, hv => by
    have hX := hxs X List.mem_cons_self
    have h0 := (a 0).isLt
    have hd : (enc (xs.length + 1) a) % 3 = (a 0 : ℕ) := by rw [enc]; omega
    have hq : (enc (xs.length + 1) a) / 3 = enc xs.length (Fin.tail a) := by rw [enc]; omega
    obtain ⟨w1, f1⟩ := Sp.app_spec hX (a 0 : ℕ) hv
    obtain ⟨w2, f2⟩ := appDigits_spec xs (fun Y hY => hxs Y (List.mem_cons_of_mem _ hY))
      (Fin.tail a) w1
    change Sp.VWF (O.appDigits xs (enc (xs.length + 1) a / 3)
        (O.app X (enc (xs.length + 1) a % 3) v)) ∧
      Sp.toVec (O.appDigits xs (enc (xs.length + 1) a / 3)
        (O.app X (enc (xs.length + 1) a % 3) v)) = _
    rw [hd, hq, List.ofFn_succ, List.prod_cons]
    refine ⟨w2, ?_⟩
    rw [f2, f1, Matrix.vecMul_vecMul]
    rfl

theorem ne_one_of_kerOK {xs : List M} (hxs : ∀ X ∈ xs, Sp.WF X) {tests : List ℕ}
    (h : O.kerOK xs tests = true) (a : Fin xs.length → Fin 3) (ha : a ≠ 0) :
    (List.ofFn fun i => Sp.toMat xs[i] ^ (a i : ℕ)).prod ≠ 1 := by
  intro hone
  have hlt := enc_lt _ a
  have hpos : enc _ a ≠ 0 := fun h0 => ha (eq_zero_of_enc_eq_zero _ a h0)
  unfold Ops.kerOK at h
  rw [List.all_eq_true] at h
  obtain ⟨k, -, hk⟩ := List.any_eq_true.1 (h (enc _ a - 1) (List.mem_range.2 (by omega)))
  rw [show enc _ a - 1 + 1 = enc _ a by omega] at hk
  unfold Ops.moved at hk
  apply Sp.toVec_ne hk
  rw [(Sp.appDigits_spec xs hxs a (Sp.unit_wf k)).2, hone, Matrix.vecMul_one]

theorem pairwise_of_commsOK : ∀ {xs : List M}, (∀ X ∈ xs, Sp.WF X) → O.commsOK xs = true →
    xs.Pairwise fun X Y => Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat X
  | [], _, _ => List.Pairwise.nil
  | X :: xs, hxs, h => by
    rw [Ops.commsOK, Bool.and_eq_true, List.all_eq_true] at h
    have hX := hxs X List.mem_cons_self
    refine List.pairwise_cons.2 ⟨fun Y hY => ?_,
      pairwise_of_commsOK (fun Z hZ => hxs Z (List.mem_cons_of_mem _ hZ)) h.2⟩
    have hY' := hxs Y (List.mem_cons_of_mem _ hY)
    have := Sp.toMat_eq (Sp.mul_wf hX hY') (Sp.mul_wf hY' hX) (h.1 Y hY)
    rwa [Sp.toMat_mul hX hY', Sp.toMat_mul hY' hX] at this

section Regs

variable [Inhabited M] (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

def RegsOK (R : Array M) : Prop := ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S

omit Sp in
theorem getElem!_setIfInBounds_of_lt {R : Array M} {k r : ℕ} (hr : r < R.size) (x : M) :
    (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem step_ok {R : Array M} (hR : Sp.RegsOK S R) {op : Op} (hop : op.lt R.size = true) :
    (O.step R op).size = R.size ∧ Sp.RegsOK S (O.step R op) := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, hk⟩ := hop
    have hs : (O.step R (.mul i j k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨wj, mj⟩ := hR j hj
      exact ⟨Sp.mul_wf wi wj, by rw [Sp.toMat_mul wi wj]; exact S.mul_mem mi mj⟩
    · exact hR r hr
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, hk⟩ := hop
    have hs : (O.step R (.pow e i k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [getElem!_setIfInBounds_of_lt hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨w, m⟩ := Sp.pow_spec wi e
      exact ⟨w, by rw [m]; exact S.pow_mem mi e⟩
    · exact hR r hr

theorem run_ok (prog : List Op) {R : Array M} (hR : Sp.RegsOK S R)
    (hprog : prog.all (Op.lt R.size) = true) :
    (O.run prog R).size = R.size ∧ Sp.RegsOK S (O.run prog R) := by
  induction prog generalizing R with
  | nil => exact ⟨rfl, hR⟩
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    obtain ⟨hs, hok⟩ := Sp.step_ok S hR hprog.1
    have := ih hok (by rw [hs]; exact hprog.2)
    simp only [Ops.run, List.foldl_cons] at this ⊢
    rw [this.1, hs]
    exact ⟨rfl, this.2⟩

theorem initRegs_ok {A B : M} (hA : Sp.WF A ∧ Sp.toMat A ∈ S) (hB : Sp.WF B ∧ Sp.toMat B ∈ S)
    (n : ℕ) : (O.initRegs A B n).size = n ∧ Sp.RegsOK S (O.initRegs A B n) := by
  have hs : (O.initRegs A B n).size = n := by simp [Ops.initRegs]
  refine ⟨hs, fun r hr => ?_⟩
  rw [hs] at hr
  unfold Ops.initRegs
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  split
  · exact hA
  split
  · exact hB
  · exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact S.one_mem⟩

end Regs

theorem exists_of_check [Inhabited M] (D : Data) (h : O.check D = true) :
    ∃ E : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ D.outs.length := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hprog⟩, houts⟩, hel⟩ := h
  have hA : Sp.WF (O.decode D.seedA) ∧ Sp.toMat (O.decode D.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.seedB) ∧ Sp.toMat (O.decode D.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := Sp.initRegs_ok S hA hB D.nregs
  obtain ⟨hs, hok⟩ := Sp.run_ok S D.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.prog (O.initRegs (O.decode D.seedA) (O.decode D.seedB) D.nregs)
  rw [hs0] at hs
  set xs := D.outs.map fun r => R[r]!
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.elemOK at hel
  simp only [Bool.and_eq_true] at hel
  obtain ⟨⟨hcube, hcomm⟩, hker⟩ := hel
  have hpair := Sp.pairwise_of_commsOK hw hcomm
  rw [← List.length_map (f := fun r => R[r]!)]
  refine exists_elemAbelian_units S (fun i : Fin xs.length => Sp.toMat xs[i])
    (fun i => (hxs _ (List.getElem_mem _)).2) (fun i => ?_) (fun i j => ?_)
    (Sp.ne_one_of_kerOK hw hker)
  · have hX := hw _ (List.getElem_mem i.isLt)
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf
      (List.all_eq_true.1 hcube _ (List.getElem_mem i.isLt))
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  · rcases lt_trichotomy i j with hij | rfl | hij
    · exact List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij
    · rfl
    · exact (List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij).symm

end OpsSpec

end CFSG.SectionRank
