module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Ref
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step410

public section

namespace CFSG.ComponentClassification.AS81.Q47

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow
open Matrix

@[expose] def arrOf (x : Equiv.Perm (Fin 64)) : Array ℕ := Array.ofFn fun v => (x v : ℕ)

theorem rep_arrOf (x : Equiv.Perm (Fin 64)) : Rep 64 (arrOf x) x := fun v => by
  rw [arrOf, getElem!_pos _ v.val (by simp), Array.getElem_ofFn]

theorem key3_eq {t u : Array ℕ} {x : Equiv.Perm (Fin 64)} (ht : Rep 64 t x) (hu : Rep 64 u x) :
    key3 t = key3 u := by
  simp only [key3]
  rw [ht.apply (by norm_num : 1 < 64), ht.apply (by norm_num : 4 < 64),
    ht.apply (by norm_num : 16 < 64), hu.apply (by norm_num : 1 < 64),
    hu.apply (by norm_num : 4 < 64), hu.apply (by norm_num : 16 < 64)]

theorem key3_mul {a b t : Array ℕ} {x y : Equiv.Perm (Fin 64)} (ha : Rep 64 a x)
    (hb : Rep 64 b y) (ht : Rep 64 t (x * y)) : key3 t = key3Mul a b := by
  simp only [key3, key3Mul]
  rw [ht.apply (by norm_num : 1 < 64), ht.apply (by norm_num : 4 < 64),
    ht.apply (by norm_num : 16 < 64), hb.apply (by norm_num : 1 < 64),
    hb.apply (by norm_num : 4 < 64), hb.apply (by norm_num : 16 < 64), ha.apply (Fin.isLt _),
    ha.apply (Fin.isLt _), ha.apply (Fin.isLt _)]
  rfl

@[expose] noncomputable def tabAt (gs : List (Array ℕ)) (Ms : List (List ℕ))
    (x : Equiv.Perm (Fin 64)) : List ℕ :=
  Ms[(keyTable (certN 64 gs).pts)[key3 (arrOf x)]!]!

theorem tableOK_parts {L : Array (Array ℕ)} {Ms : List (List ℕ)} {d p : ℕ} {one : List ℕ}
    {mul : List ℕ → List ℕ → Bool} {scal : List ℕ → Bool} (h : tableOK L Ms d p one mul scal) :
    Ms.length = L.size ∧ L[0]! = idA 64 ∧ (∀ i < L.size, (keyTable L)[key3 L[i]!]! = i) ∧
      (∀ m ∈ Ms, m.length = d * d ∧ ∀ x ∈ m, x < p) ∧ Ms[0]! = one ∧
      (∀ i < L.size, ∀ j < L.size,
        mul (matMul d p Ms[i]! Ms[j]!) Ms[(keyTable L)[key3Mul L[i]! L[j]!]!]! = true) ∧
      ∀ i < L.size, i ≠ 0 → scal Ms[i]! = false := by
  simp only [tableOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun i hi hi0 => (h7 i hi).resolve_left hi0⟩

section Table

variable {gs : List (Array ℕ)} {N : ℕ} {Ms : List (List ℕ)} {d p : ℕ} {one : List ℕ}
  {mul : List ℕ → List ℕ → Bool} {scal : List ℕ → Bool}

theorem exists_idx (hg : enumCheckN 64 gs N = true)
    (ht : tableOK (certN 64 gs).pts Ms d p one mul scal = true) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ grpN 64 gs) :
    ∃ i < (certN 64 gs).pts.size, (keyTable (certN 64 gs).pts)[key3 (arrOf x)]! = i ∧
      Rep 64 (certN 64 gs).pts[i]! x := by
  obtain ⟨-, -, hT, -⟩ := tableOK_parts ht
  obtain ⟨t, htm, hrt⟩ := (mem_grpN_iff hg).1 hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htm
  have hi' : i < (certN 64 gs).pts.size := by simpa [eltsN] using hi
  have hrt' : Rep 64 (certN 64 gs).pts[i]! x := by
    rw [getElem!_pos _ i hi']
    simpa [eltsN] using hrt
  refine ⟨i, hi', ?_, hrt'⟩
  rw [key3_eq (rep_arrOf x) hrt', hT i hi']

theorem tabAt_mul (hg : enumCheckN 64 gs N = true)
    (ht : tableOK (certN 64 gs).pts Ms d p one mul scal = true) {x y : Equiv.Perm (Fin 64)}
    (hx : x ∈ grpN 64 gs) (hy : y ∈ grpN 64 gs) :
    mul (matMul d p (tabAt gs Ms x) (tabAt gs Ms y)) (tabAt gs Ms (x * y)) = true := by
  obtain ⟨-, -, -, -, -, hmul, -⟩ := tableOK_parts ht
  obtain ⟨i, hi, hix, hri⟩ := exists_idx hg ht hx
  obtain ⟨j, hj, hjy, hrj⟩ := exists_idx hg ht hy
  have hk : key3 (arrOf (x * y)) = key3Mul (certN 64 gs).pts[i]! (certN 64 gs).pts[j]! :=
    key3_mul hri hrj (rep_arrOf _)
  simp only [tabAt]
  rw [hix, hjy, hk]
  exact hmul i hi j hj

theorem tabAt_one (hg : enumCheckN 64 gs N = true)
    (ht : tableOK (certN 64 gs).pts Ms d p one mul scal = true) : tabAt gs Ms 1 = one := by
  obtain ⟨-, h0, hT, -, h1, -⟩ := tableOK_parts ht
  have hpos : 0 < (certN 64 gs).pts.size := by
    have := enumOK_spec (range_lt 64) (enumOK_of_enumCheckN hg)
    have h := (this.1 1).1 (one_mem _)
    obtain ⟨i, hi, -⟩ := h
    omega
  have hk : key3 (arrOf 1) = key3 (certN 64 gs).pts[0]! := by
    rw [h0]
    exact key3_eq (rep_arrOf 1) rep_idA
  simp only [tabAt]
  rw [hk, hT 0 hpos, h1]

theorem eq_one_of_tabAt (hg : enumCheckN 64 gs N = true)
    (ht : tableOK (certN 64 gs).pts Ms d p one mul scal = true) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ grpN 64 gs) (hs : scal (tabAt gs Ms x) = true) : x = 1 := by
  obtain ⟨-, h0, -, -, -, -, hscal⟩ := tableOK_parts ht
  obtain ⟨i, hi, hix, hri⟩ := exists_idx hg ht hx
  have : i = 0 := by
    by_contra hi0
    have := hscal i hi hi0
    simp only [tabAt] at hs
    rw [hix] at hs
    rw [hs] at this
    exact absurd this (by decide)
  subst this
  rw [h0] at hri
  exact hri.unique rep_idA

theorem tabAt_mem (hg : enumCheckN 64 gs N = true)
    (ht : tableOK (certN 64 gs).pts Ms d p one mul scal = true) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ grpN 64 gs) : tabAt gs Ms x ∈ Ms := by
  obtain ⟨hlen, -⟩ := tableOK_parts ht
  obtain ⟨i, hi, hix, -⟩ := exists_idx hg ht hx
  simp only [tabAt]
  rw [hix, getElem!_pos Ms i (by omega)]
  exact List.getElem_mem _

end Table

@[expose] def matOf (d p : ℕ) (m : List ℕ) : Matrix (Fin d) (Fin d) (ZMod p) :=
  Matrix.of fun r c => (m[d * r.val + c.val]! : ZMod p)

theorem matMul_get {d p : ℕ} {a b : List ℕ} {r c : ℕ} (hr : r < d) (hc : c < d) :
    (matMul d p a b)[d * r + c]! =
      ((List.range d).map fun k => a[d * r + k]! * b[d * k + c]!).sum % p := by
  have he : d * r + c < d * d := by nlinarith
  rw [matMul, getElem!_pos _ _ (by simpa using he), List.getElem_map, List.getElem_range]
  have h1 : (d * r + c) / d = r := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
  have h2 : (d * r + c) % d = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [h1, h2]
  congr 2
  apply List.map_congr_left
  intro k _
  rw [mul_comm r d, mul_comm k d]

theorem matOf_matMul (d p : ℕ) (a b : List ℕ) :
    matOf d p (matMul d p a b) = matOf d p a * matOf d p b := by
  ext r c
  simp only [matOf, Matrix.of_apply, Matrix.mul_apply]
  rw [matMul_get r.2 c.2, ZMod.natCast_mod, Nat.cast_list_sum, List.map_map]
  have e : ((List.range d).map (fun k => ((a[d * r.val + k]! * b[d * k + c.val]! : ℕ) :
      ZMod p))).sum = ∑ j : Fin d, ((a[d * r.val + j.val]! * b[d * j.val + c.val]! : ℕ) :
      ZMod p) := by
    rw [← Finset.sum_range (fun k => ((a[d * r.val + k]! * b[d * k + c.val]! : ℕ) : ZMod p))]
    rfl
  have e2 : (Nat.cast ∘ fun k => a[d * r.val + k]! * b[d * k + c.val]!) =
      (fun k => ((a[d * r.val + k]! * b[d * k + c.val]! : ℕ) : ZMod p)) := rfl
  rw [e2, e]
  push_cast
  rfl

theorem eq_of_matOf_eq {d p : ℕ} [NeZero p] {m m' : List ℕ} (hl : m.length = d * d)
    (hl' : m'.length = d * d) (hm : ∀ x ∈ m, x < p) (hm' : ∀ x ∈ m', x < p)
    (h : matOf d p m = matOf d p m') : m = m' := by
  refine List.ext_getElem (hl.trans hl'.symm) fun e he he' => ?_
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [hl, h0] at he
      omega
    · exact h0
  have hr : e / d < d := by
    rw [Nat.div_lt_iff_lt_mul hd]
    rw [hl] at he
    exact he
  have hc : e % d < d := Nat.mod_lt _ hd
  have hentry := congrFun (congrFun h ⟨e / d, hr⟩) ⟨e % d, hc⟩
  simp only [matOf, Matrix.of_apply] at hentry
  have he2 : d * (e / d) + e % d = e := Nat.div_add_mod e d
  rw [he2, getElem!_pos m e he, getElem!_pos m' e he'] at hentry
  have := congrArg ZMod.val hentry
  rwa [ZMod.val_cast_of_lt (hm _ (List.getElem_mem he)),
    ZMod.val_cast_of_lt (hm' _ (List.getElem_mem he'))] at this

theorem tableCheck_parts (h : tableCheck = true) :
    tableOK (certN 64 q47YGens).pts q47YMat 3 2 [1, 0, 0, 0, 1, 0, 0, 0, 1] (· == ·)
      (· == [1, 0, 0, 0, 1, 0, 0, 0, 1]) = true ∧
    tableOK (certN 64 q47NGens).pts q47NMat 2 7 [1, 0, 0, 1] projEq7
      (fun m => m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!) = true ∧
    q47NMat.all (fun m => det7 m != 0) = true := by
  simp only [tableCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem matOf_one3 : matOf 3 2 [1, 0, 0, 0, 1, 0, 0, 0, 1] = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

theorem matOf_one2 : matOf 2 7 [1, 0, 0, 1] = 1 := by
  ext r c
  fin_cases r <;> fin_cases c <;> rfl

section Iso

variable (hq : refCheck = true) (hb : tableCheck = true)

@[expose] noncomputable def ystarMat : ↥ystar →* Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun x := matOf 3 2 (tabAt q47YGens q47YMat x)
  map_one' := by
    show matOf 3 2 (tabAt q47YGens q47YMat 1) = 1
    rw [tabAt_one (refCheck_parts hq).1 (tableCheck_parts hb).1, matOf_one3]
  map_mul' x y := by
    have h := tabAt_mul (refCheck_parts hq).1 (tableCheck_parts hb).1 x.2 y.2
    rw [beq_iff_eq] at h
    show matOf 3 2 (tabAt q47YGens q47YMat (x * y)) = _
    rw [← h, matOf_matMul]

theorem ystarMat_injective : Function.Injective (ystarMat hq hb).toHomUnits := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hY := (refCheck_parts hq).1
  have ht := (tableCheck_parts hb).1
  have h1 : ystarMat hq hb x = 1 := by
    have := congrArg Units.val hx
    simpa using this
  have hmem := tabAt_mem hY ht x.2
  obtain ⟨-, -, -, hent, -⟩ := tableOK_parts ht
  have he : tabAt q47YGens q47YMat x = [1, 0, 0, 0, 1, 0, 0, 0, 1] := by
    refine eq_of_matOf_eq (d := 3) (p := 2) (hent _ hmem).1 rfl (hent _ hmem).2 (by decide) ?_
    rw [matOf_one3]
    exact h1
  exact Subtype.ext (eq_one_of_tabAt hY ht x.2 (by rw [he]; rfl))

@[expose] noncomputable def ystarEquiv : ↥ystar ≃* GL (Fin 3) (ZMod 2) :=
  MulEquiv.ofBijective (ystarMat hq hb).toHomUnits
    ((ystarMat_injective hq hb).bijective_of_nat_card_le (by
      rw [card_GL32, card_ystar hq]))

end Iso

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem det_matOf_ne_zero {m : List ℕ} (h : det7 m ≠ 0) : (matOf 2 7 m).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp only [matOf, Matrix.of_apply]
  norm_num
  intro hc
  apply h
  have h1 : (m[1]! * m[2]! % 7 : ℕ) ≤ m[0]! * m[3]! % 7 + 7 := by
    have := Nat.mod_lt (m[1]! * m[2]!) (by norm_num : 0 < 7)
    omega
  have hz : ((det7 m : ℕ) : ZMod 7) = 0 := by
    rw [det7, ZMod.natCast_mod, Nat.cast_sub h1, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod]
    push_cast
    rw [show (7 : ZMod 7) = 0 from rfl, add_zero]
    exact sub_eq_zero.mpr (by simpa [sub_eq_zero] using hc)
  have hlt : det7 m < 7 := Nat.mod_lt _ (by norm_num)
  have := congrArg ZMod.val hz
  rwa [ZMod.val_cast_of_lt hlt, ZMod.val_zero] at this

theorem getElem!_map_mul_mod {m : List ℕ} {l p : ℕ} (e : ℕ) :
    (m.map fun x => x * l % p)[e]! = m[e]! * l % p := by
  by_cases he : e < m.length
  · rw [getElem!_pos _ e (by simpa using he), List.getElem_map, getElem!_pos m e he]
  · rw [getElem!_neg _ e (by simpa using he), getElem!_neg m e he]
    simp

theorem matOf_map_mul (d p : ℕ) (m : List ℕ) (l : ℕ) :
    matOf d p (m.map fun x => x * l % p) = (l : ZMod p) • matOf d p m := by
  ext r c
  simp only [matOf, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, getElem!_map_mul_mod,
    ZMod.natCast_mod, Nat.cast_mul]
  ring

section IsoN

theorem enumCheck_nstar (hq : refCheck = true) : enumCheckN 64 q47NGens 336 = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    refCheck_parts hq
  exact h

theorem det7_tabAt (hq : refCheck = true) (hb : tableCheck = true) {x : Equiv.Perm (Fin 64)}
    (hx : x ∈ nstar) :
    det7 (tabAt q47NGens q47NMat x) ≠ 0 := by
  have hmem := tabAt_mem (enumCheck_nstar hq) (tableCheck_parts hb).2.1 hx
  have := List.all_eq_true.1 (tableCheck_parts hb).2.2 _ hmem
  simpa using this

@[expose] noncomputable def nstarGL (hq : refCheck = true) (hb : tableCheck = true) (x : ↥nstar) :
    GL (Fin 2) (ZMod 7) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (matOf 2 7 (tabAt q47NGens q47NMat x))
    (det_matOf_ne_zero (det7_tabAt hq hb x.2))

theorem coe_nstarGL (hq : refCheck = true) (hb : tableCheck = true) (x : ↥nstar) :
    ((nstarGL hq hb x : GL (Fin 2) (ZMod 7)) : Matrix (Fin 2) (Fin 2) (ZMod 7)) =
      matOf 2 7 (tabAt q47NGens q47NMat x) := rfl

theorem nstarGL_mul (hq : refCheck = true) (hb : tableCheck = true) (x y : ↥nstar) :
    ∃ u : (ZMod 7)ˣ,
    nstarGL hq hb x * nstarGL hq hb y =
      nstarGL hq hb (x * y) * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have h := tabAt_mul (enumCheck_nstar hq) (tableCheck_parts hb).2.1 x.2 y.2
  simp only [projEq7, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨l, hl7, hl0, hl⟩ := h
  have hu : IsUnit (l : ZMod 7) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have := congrArg ZMod.val h0
    rw [ZMod.val_cast_of_lt hl7, ZMod.val_zero] at this
    exact hl0 this
  refine ⟨hu.unit, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_nstarGL hq hb,
    coe_nstarGL hq hb, coe_nstarGL hq hb, ← matOf_matMul, hl, matOf_map_mul]
  show _ = _ * Matrix.scalar (Fin 2) ((hu.unit : (ZMod 7)ˣ) : ZMod 7)
  rw [Matrix.scalar_apply, ← smul_eq_mul_diagonal, IsUnit.unit_spec]
  rfl

@[expose] noncomputable def nstarPGL (hq : refCheck = true) (hb : tableCheck = true) :
    ↥nstar →* ProjGenLinGroup (Fin 2) (ZMod 7) where
  toFun x := ProjGenLinGroup.mk (nstarGL hq hb x)
  map_one' := by
    have h1 : nstarGL hq hb 1 = 1 := Units.ext (by
      rw [coe_nstarGL hq hb]
      show matOf 2 7 (tabAt q47NGens q47NMat 1) = 1
      rw [tabAt_one (enumCheck_nstar hq) (tableCheck_parts hb).2.1, matOf_one2])
    show ProjGenLinGroup.mk (nstarGL hq hb 1) = 1
    rw [h1, map_one]
  map_mul' x y := by
    obtain ⟨u, hu⟩ := nstarGL_mul hq hb x y
    show ProjGenLinGroup.mk (nstarGL hq hb (x * y)) =
      ProjGenLinGroup.mk (nstarGL hq hb x) * ProjGenLinGroup.mk (nstarGL hq hb y)
    rw [← map_mul, hu, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

theorem nstarPGL_injective (hq : refCheck = true) (hb : tableCheck = true) :
    Function.Injective (nstarPGL hq hb) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have ht := (tableCheck_parts hb).2.1
  have hx' : ProjGenLinGroup.mk (nstarGL hq hb x) = 1 := hx
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
  obtain ⟨u, hu⟩ := hx'
  have hM : matOf 2 7 (tabAt q47NGens q47NMat x) = Matrix.scalar (Fin 2) (u : ZMod 7) := by
    rw [← coe_nstarGL hq hb, ← hu]
    rfl
  have hmem := tabAt_mem (enumCheck_nstar hq) ht x.2
  obtain ⟨-, -, -, hent, -⟩ := tableOK_parts ht
  obtain ⟨hlen, hlt⟩ := hent _ hmem
  set m := tabAt q47NGens q47NMat x
  have entry : ∀ r c : Fin 2,
      (m[2 * r.val + c.val]! : ZMod 7) = Matrix.scalar (Fin 2) (u : ZMod 7) r c :=
    fun r c => by rw [← hM]; rfl
  have hval : ∀ e, e < 4 → m[e]! < 7 := fun e he => hlt _ (by
    rw [getElem!_pos m e (by omega)]
    exact List.getElem_mem _)
  have cast_inj : ∀ a b : ℕ, a < 7 → b < 7 → (a : ZMod 7) = b → a = b := fun a b ha hb e => by
    have := congrArg ZMod.val e
    rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this
  have e01 : (m[1]! : ZMod 7) = 0 := by
    have := entry 0 1
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at this
    exact this
  have e10 : (m[2]! : ZMod 7) = 0 := by
    have := entry 1 0
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)] at this
    exact this
  have e00 : (m[0]! : ZMod 7) = u := by
    have := entry 0 0
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  have e11 : (m[3]! : ZMod 7) = u := by
    have := entry 1 1
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
    exact this
  have h1 : m[1]! = 0 := cast_inj _ 0 (hval 1 (by norm_num)) (by norm_num) (by rw [e01]; rfl)
  have h2 : m[2]! = 0 := cast_inj _ 0 (hval 2 (by norm_num)) (by norm_num) (by rw [e10]; rfl)
  have h03 : m[0]! = m[3]! := cast_inj _ _ (hval 0 (by norm_num)) (hval 3 (by norm_num))
    (by rw [e00, e11])
  refine Subtype.ext (eq_one_of_tabAt (enumCheck_nstar hq) ht x.2 ?_)
  show (m[1]! == 0 && m[2]! == 0 && m[0]! == m[3]!) = true
  rw [h1, h2, h03]
  simp

@[expose] noncomputable def nstarEquiv (hq : refCheck = true) (hb : tableCheck = true) :
    ↥nstar ≃* ProjGenLinGroup (Fin 2) (ZMod 7) :=
  have : Finite (ProjGenLinGroup (Fin 2) (ZMod 7)) :=
    Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  MulEquiv.ofBijective (nstarPGL hq hb)
    ((nstarPGL_injective hq hb).bijective_of_nat_card_le (by
      rw [card_PGL27, card_nstar hq]))

end IsoN

end CFSG.ComponentClassification.AS81.Q47
