module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3
public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank

open CFSG.Blueprint CFSG.SectionRank.Native
open scoped Matrix commutatorElement

namespace LocalWitness

variable {G : Type*} [Group G]

theorem commutator_pow_eq {x y : G} (h : Commute ⁅x, y⁆ x) (n : ℕ) :
    ⁅x, y⁆ ^ n = ⁅x ^ n, y⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' : Commute ⁅x ^ n, y⁆ x := ih ▸ h.pow_left n
    calc ⁅x, y⁆ ^ (n + 1) = ⁅x ^ n, y⁆ * ⁅x, y⁆ := by rw [pow_succ, ih]
      _ = ⁅x ^ n, y⁆ * x * y * x⁻¹ * y⁻¹ := by rw [commutatorElement_def]; group
      _ = x * ⁅x ^ n, y⁆ * y * x⁻¹ * y⁻¹ := by rw [h'.eq]
      _ = ⁅x ^ (n + 1), y⁆ := by simp only [commutatorElement_def]; group

theorem y_mul_x_pow {x y : G} {r : ℕ} (hr : 0 < r) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hz : ⁅x, y⁆ ^ r = 1) (i : ℕ) :
    y * x ^ i = x ^ i * y * ⁅x, y⁆ ^ ((r - 1) * i) := by
  set z := ⁅x, y⁆ with hzdef
  have hzinv : z ^ (r - 1) = z⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hr, hz]
  have hyx : y * x = x * y * z ^ (r - 1) := by
    rw [hzinv]
    calc y * x = z⁻¹ * x * y := by rw [hzdef, commutatorElement_def]; group
      _ = x * z⁻¹ * y := by rw [hzx.inv_left.eq]
      _ = x * (z⁻¹ * y) := by group
      _ = x * (y * z⁻¹) := by rw [hzy.inv_left.eq]
      _ = x * y * z⁻¹ := by group
  induction i with
  | zero => simp
  | succ i ih =>
    have hc : Commute (z ^ ((r - 1) * i)) x := hzx.pow_left _
    calc y * x ^ (i + 1) = (y * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = x ^ i * y * (z ^ ((r - 1) * i) * x) := by rw [ih]; group
      _ = x ^ i * y * (x * z ^ ((r - 1) * i)) := by rw [hc.eq]
      _ = x ^ i * (y * x) * z ^ ((r - 1) * i) := by group
      _ = x ^ i * (x * y * z ^ (r - 1)) * z ^ ((r - 1) * i) := by rw [hyx]
      _ = x ^ (i + 1) * y * (z ^ (r - 1) * z ^ ((r - 1) * i)) := by rw [pow_succ]; group
      _ = x ^ (i + 1) * y * z ^ ((r - 1) * (i + 1)) := by
        rw [← pow_add, show r - 1 + (r - 1) * i = (r - 1) * (i + 1) by ring]

theorem mem_closure_normalForm {x y : G} {r : ℕ} (hr : 0 < r) (hx : x ^ r = 1)
    (hy : y ^ r = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) {g : G}
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) :
    ∃ i j k : ℕ, i < r ∧ j < r ∧ k < r ∧ g = x ^ i * y ^ j * ⁅x, y⁆ ^ k := by
  set z := ⁅x, y⁆ with hzdef
  have hz : z ^ r = 1 := by rw [hzdef, commutator_pow_eq hzx, hx, commutatorElement_one_left]
  let P : G → Prop := fun g => ∃ i j k : ℕ, g = x ^ i * y ^ j * z ^ k
  have hxP : ∀ g, P g → P (x * g) := by
    rintro g ⟨i, j, k, rfl⟩
    exact ⟨i + 1, j, k, by rw [pow_succ']; group⟩
  have hyP : ∀ g, P g → P (y * g) := by
    rintro g ⟨i, j, k, rfl⟩
    refine ⟨i, j + 1, (r - 1) * i + k, ?_⟩
    have hc : Commute (z ^ ((r - 1) * i)) (y ^ j) := (hzy.pow_left _).pow_right _
    calc y * (x ^ i * y ^ j * z ^ k) = (y * x ^ i) * y ^ j * z ^ k := by
          simp only [mul_assoc]
      _ = x ^ i * y * (z ^ ((r - 1) * i) * y ^ j) * z ^ k := by
        rw [y_mul_x_pow hr hzx hzy hz, ← hzdef]; simp only [mul_assoc]
      _ = x ^ i * y * (y ^ j * z ^ ((r - 1) * i)) * z ^ k := by rw [hc.eq]
      _ = x ^ i * y ^ (j + 1) * z ^ ((r - 1) * i + k) := by
        rw [pow_succ', pow_add]; simp only [mul_assoc]
  have hxinv : x⁻¹ = x ^ (r - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hr, hx]
  have hyinv : y⁻¹ = y ^ (r - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hr, hy]
  have hpowP : ∀ (s : G), (∀ g, P g → P (s * g)) → ∀ n g, P g → P (s ^ n * g) := by
    intro s hs n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih => intro g hg; rw [pow_succ', mul_assoc]; exact hs _ (ih g hg)
  have hP : P g := by
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_left s hs g _ ih =>
      rcases hs with rfl | rfl
      · exact hxP _ ih
      · exact hyP _ ih
    | inv_mul_cancel s hs g _ ih =>
      rcases hs with rfl | rfl
      · rw [hxinv]; exact hpowP _ hxP _ _ ih
      · rw [hyinv]; exact hpowP _ hyP _ _ ih
  obtain ⟨i, j, k, rfl⟩ := hP
  exact ⟨i % r, j % r, k % r, Nat.mod_lt _ hr, Nat.mod_lt _ hr, Nat.mod_lt _ hr, by
    rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hz]⟩

theorem card_closure_eq_cube {x y : G} {r : ℕ} (hr : 0 < r) (hx : x ^ r = 1) (hy : y ^ r = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hinj : Function.Injective fun t : Fin r × Fin r × Fin r =>
      x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ)) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 3 := by
  set Q := Subgroup.closure ({x, y} : Set G)
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hzQ : ⁅x, y⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hxQ hyQ) (Q.inv_mem hxQ)) (Q.inv_mem hyQ)
  let F : Fin r × Fin r × Fin r → Q := fun t =>
    ⟨x ^ (t.1 : ℕ) * y ^ (t.2.1 : ℕ) * ⁅x, y⁆ ^ (t.2.2 : ℕ),
      Q.mul_mem (Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)) (Q.pow_mem hzQ _)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun s t hst => hinj (congrArg Subtype.val hst), fun g => ?_⟩
    obtain ⟨i, j, k, hi, hj, hk, hg⟩ := mem_closure_normalForm hr hx hy hzx hzy g.2
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_prod, Nat.card_fin]
  ring

theorem card_closure_eq_sq {x y : G} {r : ℕ} (hr : 0 < r) (hx : x ^ r = 1) (hy : y ^ r = 1)
    (hxy : x * y = y * x)
    (hinj : Function.Injective fun t : Fin r × Fin r => x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ)) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 2 := by
  have hz : ⁅x, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hxy
  set Q := Subgroup.closure ({x, y} : Set G)
  have hxQ : x ∈ Q := Subgroup.subset_closure (by simp)
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  let F : Fin r × Fin r → Q := fun t =>
    ⟨x ^ (t.1 : ℕ) * y ^ (t.2 : ℕ), Q.mul_mem (Q.pow_mem hxQ _) (Q.pow_mem hyQ _)⟩
  have hF : Function.Bijective F := by
    refine ⟨fun s t hst => hinj (congrArg Subtype.val hst), fun g => ?_⟩
    obtain ⟨i, j, k, hi, hj, -, hg⟩ := mem_closure_normalForm hr hx hy
      (by rw [hz]; exact Commute.one_left x) (by rw [hz]; exact Commute.one_left y) g.2
    rw [hz, one_pow, mul_one] at hg
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_fin]
  ring

theorem add_mul_lt {r i m n : ℕ} (hi : i < r) (hm : m < n) : i + r * m < r * n :=
  calc i + r * m < r + r * m := by omega
    _ = r * (m + 1) := by ring
    _ ≤ r * n := Nat.mul_le_mul_left _ hm

variable {M : Type*} [Monoid M] (S : Submonoid M)

noncomputable abbrev valHom : Sˣ →* M := S.subtype.comp (Units.coeHom S)

theorem valHom_injective : Function.Injective (valHom S) := fun _ _ h =>
  Units.ext (Subtype.ext h)

@[expose] noncomputable def unitOf {X : M} (hX : X ∈ S) {n : ℕ} (hn : n ≠ 0) (h : X ^ n = 1) : Sˣ :=
  Units.ofPowEqOne ⟨X, hX⟩ n (Subtype.ext (by simpa using h)) hn

theorem valHom_unitOf {X : M} (hX : X ∈ S) {n : ℕ} (hn : n ≠ 0) (h : X ^ n = 1) :
    valHom S (unitOf S hX hn h) = X := by
  simp [valHom, unitOf]

theorem unitOf_pow {X : M} (hX : X ∈ S) {n : ℕ} (hn : n ≠ 0) (h : X ^ n = 1) :
    unitOf S hX hn h ^ n = 1 :=
  Units.pow_ofPowEqOne _ _

theorem valHom_inv_of_pow {u : Sˣ} {n : ℕ} (hn : n ≠ 0) (h : u ^ n = 1) :
    valHom S u⁻¹ = valHom S u ^ (n - 1) := by
  rw [← map_pow]
  congr 1
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), h]

end LocalWitness

open LocalWitness

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

omit Sp in
private theorem getElem!_setIfInBounds_of_lt' [Inhabited M] {R : Array M} {k r : ℕ}
    (hr : r < R.size) (x : M) :
    (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem regsOf_ok [Inhabited M] {seedA seedB : String} {nregs : ℕ} {prog : List Op}
    (hprog : prog.all (Op.lt nregs) = true) {r : ℕ} (hr : r < nregs) :
    Sp.WF (O.regsOf seedA seedB nregs prog)[r]! ∧
      Sp.toMat (O.regsOf seedA seedB nregs prog)[r]! ∈
        NativeSporadic.seedMonoid p d 1 seedA seedB := by
  set S := NativeSporadic.seedMonoid p d 1 seedA seedB
  let Inv : Array M → Prop := fun R => R.size = nregs ∧
    ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S
  have hA : Sp.WF (O.decode seedA) ∧ Sp.toMat (O.decode seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode seedB) ∧ Sp.toMat (O.decode seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have hinit : Inv (O.initRegs (O.decode seedA) (O.decode seedB) nregs) := by
    have hs : (O.initRegs (O.decode seedA) (O.decode seedB) nregs).size = nregs := by
      simp [Ops.initRegs]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    unfold Ops.initRegs
    rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    split
    · exact hA
    split
    · exact hB
    · exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact S.one_mem⟩
  have hstep : ∀ R op, Inv R → op.lt nregs = true → Inv (O.step R op) := by
    rintro R op ⟨hs, hR⟩ hop
    cases op with
    | mul i j k =>
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨⟨hi, hj⟩, -⟩ := hop
      have hs' : (O.step R (.mul i j k)).size = R.size := by simp [Ops.step, Array.set!]
      refine ⟨hs'.trans hs, fun r hr => ?_⟩
      rw [hs'] at hr
      simp only [Ops.step, Array.set!]
      rw [getElem!_setIfInBounds_of_lt' hr]
      split
      · obtain ⟨wi, mi⟩ := hR i (by omega)
        obtain ⟨wj, mj⟩ := hR j (by omega)
        exact ⟨Sp.mul_wf wi wj, by rw [Sp.toMat_mul wi wj]; exact S.mul_mem mi mj⟩
      · exact hR r hr
    | pow e i k =>
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
      obtain ⟨hi, -⟩ := hop
      have hs' : (O.step R (.pow e i k)).size = R.size := by simp [Ops.step, Array.set!]
      refine ⟨hs'.trans hs, fun r hr => ?_⟩
      rw [hs'] at hr
      simp only [Ops.step, Array.set!]
      rw [getElem!_setIfInBounds_of_lt' hr]
      split
      · obtain ⟨wi, mi⟩ := hR i (by omega)
        obtain ⟨w, m⟩ := Sp.pow_spec wi e
        exact ⟨w, by rw [m]; exact S.pow_mem mi e⟩
      · exact hR r hr
  have hrun : ∀ (prog : List Op) R, Inv R → prog.all (Op.lt nregs) = true →
      Inv (O.run prog R) := by
    intro prog
    induction prog with
    | nil => intro R hR _; exact hR
    | cons op prog ih =>
      intro R hR hp
      rw [List.all_cons, Bool.and_eq_true] at hp
      simp only [Ops.run, List.foldl_cons] at ih ⊢
      exact ih _ (hstep R op hR hp.1) hp.2
  obtain ⟨hs, hok⟩ := hrun prog _ hinit hprog
  exact hok r (by rw [hs]; exact hr)

theorem appBase_two {X Y : M} (hX : Sp.WF X) (hY : Sp.WF Y) (b n : ℕ) {v : V} (hv : Sp.VWF v) :
    Sp.toVec (O.appBase b [X, Y] n v) =
      Sp.toVec v ᵥ* (Sp.toMat X ^ (n % b) * Sp.toMat Y ^ (n / b % b)) := by
  simp only [Ops.appBase]
  obtain ⟨w1, f1⟩ := Sp.app_spec hX (n % b) hv
  rw [(Sp.app_spec hY (n / b % b) w1).2, f1, Matrix.vecMul_vecMul]

theorem appBase_three {X Y Z : M} (hX : Sp.WF X) (hY : Sp.WF Y) (hZ : Sp.WF Z) (b n : ℕ) {v : V}
    (hv : Sp.VWF v) :
    Sp.toVec (O.appBase b [X, Y, Z] n v) = Sp.toVec v ᵥ*
      (Sp.toMat X ^ (n % b) * Sp.toMat Y ^ (n / b % b) * Sp.toMat Z ^ (n / b / b % b)) := by
  simp only [Ops.appBase]
  obtain ⟨w1, f1⟩ := Sp.app_spec hX (n % b) hv
  obtain ⟨w2, f2⟩ := Sp.app_spec hY (n / b % b) w1
  rw [(Sp.app_spec hZ (n / b / b % b) w2).2, f2, f1, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul,
    Matrix.mul_assoc]

theorem toVec_ne_of_distinctOK [Inhabited V] {vs : Array V} (h : O.distinctOK vs = true)
    {i j : ℕ} (hi : i < vs.size) (hj : j < vs.size) (hij : i ≠ j) :
    Sp.toVec vs[i]! ≠ Sp.toVec vs[j]! := by
  unfold Ops.distinctOK at h
  rw [List.all_eq_true] at h
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have := List.all_eq_true.1 (h j (List.mem_range.2 hj)) i (List.mem_range.2 hlt)
    exact (Sp.toVec_ne this).symm
  · exact Sp.toVec_ne (List.all_eq_true.1 (h i (List.mem_range.2 hi)) j (List.mem_range.2 hlt))

theorem toMat_of_conjOK {X Y W : M} (hX : Sp.WF X) (hY : Sp.WF Y) (hW : Sp.WF W)
    (h : O.conjOK X Y W = true) : Sp.toMat X * Sp.toMat Y = Sp.toMat W * Sp.toMat X := by
  have := Sp.toMat_eq (Sp.mul_wf hX hY) (Sp.mul_wf hW hX) h
  rwa [Sp.toMat_mul hX hY, Sp.toMat_mul hW hX] at this

theorem pow_eq_one_of_check {X : M} (hX : Sp.WF X) {n : ℕ} (h : O.eq (O.pow X n) O.one = true) :
    Sp.toMat X ^ n = 1 := by
  have := Sp.toMat_eq (Sp.pow_spec hX n).1 Sp.one_wf h
  rwa [(Sp.pow_spec hX n).2, Sp.toMat_one] at this

theorem square_of_check [Inhabited M] [Inhabited V] (D : SqData) (h : O.squareCheck D = true) :
    ∃ x y g : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      x ^ D.r = 1 ∧ y ^ D.r = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set _)) = D.r ^ 2 ∧
      g * x * g⁻¹ = x ^ D.a * y ^ D.c ∧ g * y * g⁻¹ = x ^ D.b * y ^ D.d := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.squareCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hrx⟩, hry⟩, hrh⟩, hr⟩, hoh⟩, hXr⟩, hYr⟩, hHo⟩, hXY⟩, hHX⟩,
    hHY⟩, hnf⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  obtain ⟨wX, mX⟩ := Sp.regsOf_ok hprog hrx
  obtain ⟨wY, mY⟩ := Sp.regsOf_ok hprog hry
  obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hrh
  have eX := Sp.pow_eq_one_of_check wX hXr
  have eY := Sp.pow_eq_one_of_check wY hYr
  have eH := Sp.pow_eq_one_of_check wH hHo
  let x := unitOf S mX hr.ne' eX
  let y := unitOf S mY hr.ne' eY
  let g := unitOf S mH hoh.ne' eH
  have fx : valHom S x = Sp.toMat R[D.rx]! := rfl
  have fy : valHom S y = Sp.toMat R[D.ry]! := rfl
  have fg : valHom S g = Sp.toMat R[D.rh]! := rfl
  have hxy : x * y = y * x := valHom_injective S (by
    rw [map_mul, map_mul, fx, fy]
    have := Sp.toMat_eq (Sp.mul_wf wX wY) (Sp.mul_wf wY wX) hXY
    rwa [Sp.toMat_mul wX wY, Sp.toMat_mul wY wX] at this)
  have conj : ∀ {w : Sˣ} {W : M}, Sp.WF W → valHom S w = Sp.toMat W → ∀ {u : Sˣ} {U : M},
      Sp.WF U → valHom S u = Sp.toMat U → O.conjOK R[D.rh]! U W = true → g * u * g⁻¹ = w := by
    intro w W hW hw u U hU hu hc
    rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    rw [map_mul, map_mul, fg, hu, hw]
    exact Sp.toMat_of_conjOK wH hU hW hc
  refine ⟨x, y, g, unitOf_pow S mX _ eX, unitOf_pow S mY _ eY, hxy, ?_, ?_, ?_⟩
  · refine card_closure_eq_sq hr (unitOf_pow S mX _ eX) (unitOf_pow S mY _ eY) hxy ?_
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hm := congrArg (valHom S) hij
    simp only [map_mul, map_pow, fx, fy] at hm
    unfold Ops.normalFormOK at hnf
    set vs := Array.ofFn (n := D.r ^ [R[D.rx]!, R[D.ry]!].length) fun n =>
      O.appBase D.r [R[D.rx]!, R[D.ry]!] n.val (O.unit D.t)
    have hvs : ∀ n < D.r ^ 2, Sp.toVec vs[n]! = Sp.toVec (O.unit D.t) ᵥ*
        (Sp.toMat R[D.rx]! ^ (n % D.r) * Sp.toMat R[D.ry]! ^ (n / D.r % D.r)) := by
      intro n hn'
      rw [getElem!_pos vs n (by simpa [vs] using hn'), Array.getElem_ofFn]
      exact Sp.appBase_two wX wY D.r n (Sp.unit_wf D.t)
    have hcode : ∀ (i j : Fin D.r), (i + D.r * j : ℕ) < D.r ^ 2 ∧
        (i + D.r * j : ℕ) % D.r = i ∧ (i + D.r * j : ℕ) / D.r % D.r = j := by
      intro i j
      have := i.isLt
      have := j.isLt
      refine ⟨by nlinarith, by simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt], ?_⟩
      rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt i.isLt, zero_add,
        Nat.mod_eq_of_lt j.isLt]
    obtain ⟨c1, c2, c3⟩ := hcode i j
    obtain ⟨c1', c2', c3'⟩ := hcode i' j'
    by_contra hne
    have hcne : (i + D.r * j : ℕ) ≠ i' + D.r * j' := by
      intro hc
      apply hne
      have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
      have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have hsz : vs.size = D.r ^ 2 := by simp [vs]
    apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
    rw [hvs _ c1, hvs _ c1', c2, c3, c2', c3', hm]
  · refine conj (Sp.mul_wf (Sp.pow_spec wX _).1 (Sp.pow_spec wY _).1) ?_ wX fx hHX
    rw [map_mul, map_pow, map_pow, fx, fy, Sp.toMat_mul (Sp.pow_spec wX _).1 (Sp.pow_spec wY _).1,
      (Sp.pow_spec wX _).2, (Sp.pow_spec wY _).2]
  · refine conj (Sp.mul_wf (Sp.pow_spec wX _).1 (Sp.pow_spec wY _).1) ?_ wY fy hHY
    rw [map_mul, map_pow, map_pow, fx, fy, Sp.toMat_mul (Sp.pow_spec wX _).1 (Sp.pow_spec wY _).1,
      (Sp.pow_spec wX _).2, (Sp.pow_spec wY _).2]

theorem valHom_commutator {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))} {x y : Sˣ} {r : ℕ}
    (hr : 0 < r) (hx : x ^ r = 1) (hy : y ^ r = 1) {X Y : M} (wX : Sp.WF X) (wY : Sp.WF Y)
    (fx : valHom S x = Sp.toMat X) (fy : valHom S y = Sp.toMat Y) :
    valHom S ⁅x, y⁆ = Sp.toMat (O.commM r X Y) := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, valHom_inv_of_pow S hr.ne' hx,
    valHom_inv_of_pow S hr.ne' hy, fx, fy]
  unfold Ops.commM
  rw [Sp.toMat_mul (Sp.mul_wf (Sp.mul_wf wX wY) (Sp.pow_spec wX _).1) (Sp.pow_spec wY _).1,
    Sp.toMat_mul (Sp.mul_wf wX wY) (Sp.pow_spec wX _).1, Sp.toMat_mul wX wY,
    (Sp.pow_spec wX _).2, (Sp.pow_spec wY _).2]

theorem commM_wf {X Y : M} (wX : Sp.WF X) (wY : Sp.WF Y) (r : ℕ) : Sp.WF (O.commM r X Y) := by
  unfold Ops.commM
  exact Sp.mul_wf (Sp.mul_wf (Sp.mul_wf wX wY) (Sp.pow_spec wX _).1) (Sp.pow_spec wY _).1

theorem cubic_of_check [Inhabited M] [Inhabited V] (D : CubData) (h : O.cubicCheck D = true) :
    ∃ x y g : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
      x ^ D.r = 1 ∧ y ^ D.r = 1 ∧ ⁅x, y⁆ ≠ 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      Nat.card (Subgroup.closure ({x, y} : Set _)) = D.r ^ 3 ∧
      g * x * g⁻¹ = x ^ D.a * y ^ D.b * ⁅x, y⁆ ^ D.k ∧
      g * y * g⁻¹ = x ^ D.c * y ^ D.d * ⁅x, y⁆ ^ D.l ∧ g * ⁅x, y⁆ * g⁻¹ = ⁅x, y⁆ ^ D.μ := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold Ops.cubicCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hrx⟩, hry⟩, hrh⟩, hr⟩, hoh⟩, hXr⟩, hYr⟩, hHo⟩, hZt⟩,
    hZX⟩, hZY⟩, hHX⟩, hHY⟩, hHZ⟩, hnf⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  obtain ⟨wX, mX⟩ := Sp.regsOf_ok hprog hrx
  obtain ⟨wY, mY⟩ := Sp.regsOf_ok hprog hry
  obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hrh
  have eX := Sp.pow_eq_one_of_check wX hXr
  have eY := Sp.pow_eq_one_of_check wY hYr
  have eH := Sp.pow_eq_one_of_check wH hHo
  let x := unitOf S mX hr.ne' eX
  let y := unitOf S mY hr.ne' eY
  let g := unitOf S mH hoh.ne' eH
  have fx : valHom S x = Sp.toMat R[D.rx]! := valHom_unitOf S _ _ _
  have fy : valHom S y = Sp.toMat R[D.ry]! := valHom_unitOf S _ _ _
  have fg : valHom S g = Sp.toMat R[D.rh]! := valHom_unitOf S _ _ _
  have hx : x ^ D.r = 1 := unitOf_pow S mX _ eX
  have hy : y ^ D.r = 1 := unitOf_pow S mY _ eY
  set Z := O.commM D.r R[D.rx]! R[D.ry]!
  have wZ : Sp.WF Z := Sp.commM_wf wX wY D.r
  have fz : valHom S ⁅x, y⁆ = Sp.toMat Z := Sp.valHom_commutator hr hx hy wX wY fx fy
  have comm : ∀ {u : Sˣ} {U : M}, Sp.WF U → valHom S u = Sp.toMat U →
      O.eq (O.mul Z U) (O.mul U Z) = true → Commute ⁅x, y⁆ u := by
    intro u U hU hu hc
    apply valHom_injective S
    rw [map_mul, map_mul, fz, hu]
    have := Sp.toMat_eq (Sp.mul_wf wZ hU) (Sp.mul_wf hU wZ) hc
    rwa [Sp.toMat_mul wZ hU, Sp.toMat_mul hU wZ] at this
  have conj : ∀ {w : Sˣ} {W : M}, Sp.WF W → valHom S w = Sp.toMat W → ∀ {u : Sˣ} {U : M},
      Sp.WF U → valHom S u = Sp.toMat U → O.conjOK R[D.rh]! U W = true → g * u * g⁻¹ = w := by
    intro w W hW hw u U hU hu hc
    rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    rw [map_mul, map_mul, fg, hu, hw]
    exact Sp.toMat_of_conjOK wH hU hW hc
  have word : ∀ i j k : ℕ, Sp.WF (O.mul (O.mul (O.pow R[D.rx]! i) (O.pow R[D.ry]! j))
        (O.pow Z k)) ∧ valHom S (x ^ i * y ^ j * ⁅x, y⁆ ^ k) = Sp.toMat (O.mul (O.mul
          (O.pow R[D.rx]! i) (O.pow R[D.ry]! j)) (O.pow Z k)) := by
    intro i j k
    have w1 := Sp.mul_wf (Sp.pow_spec wX i).1 (Sp.pow_spec wY j).1
    refine ⟨Sp.mul_wf w1 (Sp.pow_spec wZ k).1, ?_⟩
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, fx, fy, fz,
      Sp.toMat_mul w1 (Sp.pow_spec wZ k).1, Sp.toMat_mul (Sp.pow_spec wX i).1 (Sp.pow_spec wY j).1,
      (Sp.pow_spec wX i).2, (Sp.pow_spec wY j).2, (Sp.pow_spec wZ k).2]
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply Sp.toVec_ne hZt
    rw [Sp.toVec_vmul (Sp.unit_wf _) wZ, ← fz, h1, map_one, Matrix.vecMul_one]
  have hzx : Commute ⁅x, y⁆ x := comm wX fx hZX
  have hzy : Commute ⁅x, y⁆ y := comm wY fy hZY
  refine ⟨x, y, g, hx, hy, hz1, hzx, hzy, ?_, conj (word _ _ _).1 (word _ _ _).2 wX fx hHX,
    conj (word _ _ _).1 (word _ _ _).2 wY fy hHY, conj (Sp.pow_spec wZ _).1 ?_ wZ fz hHZ⟩
  · refine card_closure_eq_cube hr hx hy hzx hzy ?_
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hijk
    have hm := congrArg (valHom S) hijk
    simp only [map_mul, map_pow, fx, fy, fz] at hm
    unfold Ops.normalFormOK at hnf
    set vs := Array.ofFn (n := D.r ^ [R[D.rx]!, R[D.ry]!, Z].length) fun n =>
      O.appBase D.r [R[D.rx]!, R[D.ry]!, Z] n.val (O.unit D.t)
    have hvs : ∀ n < D.r ^ 3, Sp.toVec vs[n]! = Sp.toVec (O.unit D.t) ᵥ*
        (Sp.toMat R[D.rx]! ^ (n % D.r) * Sp.toMat R[D.ry]! ^ (n / D.r % D.r) *
          Sp.toMat Z ^ (n / D.r / D.r % D.r)) := by
      intro n hn'
      rw [getElem!_pos vs n (by simpa [vs] using hn'), Array.getElem_ofFn]
      exact Sp.appBase_three wX wY wZ D.r n (Sp.unit_wf D.t)
    have hcode : ∀ (i j k : Fin D.r), (i + D.r * (j + D.r * k) : ℕ) < D.r ^ 3 ∧
        (i + D.r * (j + D.r * k) : ℕ) % D.r = i ∧
        (i + D.r * (j + D.r * k) : ℕ) / D.r % D.r = j ∧
        (i + D.r * (j + D.r * k) : ℕ) / D.r / D.r % D.r = k := by
      intro i j k
      have hi := i.isLt
      have hj := j.isLt
      have hk := k.isLt
      have e1 : (i + D.r * (j + D.r * k) : ℕ) / D.r = j + D.r * k := by
        rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hi, zero_add]
      have e2 : (j + D.r * k : ℕ) / D.r = k := by
        rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hj, zero_add]
      refine ⟨by
        rw [show D.r ^ 3 = D.r * (D.r * D.r) by ring]
        exact add_mul_lt hi (add_mul_lt hj hk), by
        simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi], ?_, ?_⟩
      · rw [e1]; simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
      · rw [e1, e2, Nat.mod_eq_of_lt hk]
    obtain ⟨c1, c2, c3, c4⟩ := hcode i j k
    obtain ⟨c1', c2', c3', c4'⟩ := hcode i' j' k'
    by_contra hne
    have hcne : (i + D.r * (j + D.r * k) : ℕ) ≠ i' + D.r * (j' + D.r * k') := by
      intro hc
      apply hne
      have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
      have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
      have e3 : (k : ℕ) = k' := by rw [← c4, ← c4', hc]
      exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e3))
    have hsz : vs.size = D.r ^ 3 := by simp [vs]
    apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
    rw [hvs _ c1, hvs _ c1', c2, c3, c4, c2', c3', c4', hm]
  · rw [map_pow, fz, (Sp.pow_spec wZ _).2]

end OpsSpec

end CFSG.SectionRank
