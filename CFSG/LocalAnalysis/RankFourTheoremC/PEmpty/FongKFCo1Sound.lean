module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import Certificates.Data.Co1Gen

public section

namespace CFSG.SectionRank

open CFSG.Blueprint CFSG.SectionRank.Native CFSG.SectionRank.Native.Co1Gen
open scoped Matrix
open CFSG.SectionRank.LocalWitness

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

section Closure

variable (T : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

def LstOK (xs : List M) : Prop := ∀ x ∈ xs, Sp.WF x ∧ Sp.toMat x ∈ T

theorem lstOK_foldl {cand : List M} (hc : Sp.LstOK T cand) :
    ∀ acc : List M, Sp.LstOK T acc →
      Sp.LstOK T (cand.foldl (fun acc y => if acc.any (O.eq y) then acc else acc ++ [y]) acc) := by
  induction cand with
  | nil => exact fun acc h => h
  | cons y ys ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    refine ih (fun z hz => hc z (List.mem_cons_of_mem _ hz)) _ ?_
    split
    · exact hacc
    · intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hacc z hz
      · rw [List.mem_singleton] at hz
        rw [hz]
        exact hc y List.mem_cons_self

omit Sp in
theorem mem_foldl {cand : List M} :
    ∀ (acc : List M) (z : M), z ∈ acc →
      z ∈ cand.foldl (fun acc y => if acc.any (O.eq y) then acc else acc ++ [y]) acc := by
  induction cand with
  | nil => exact fun acc z h => h
  | cons y ys ih =>
    intro acc z hz
    simp only [List.foldl_cons]
    refine ih _ z ?_
    split
    · exact hz
    · exact List.mem_append_left _ hz

theorem lstOK_step {gens xs : List M} (hg : Sp.LstOK T gens) (hx : Sp.LstOK T xs) :
    Sp.LstOK T (O.co1GenStep gens xs) := by
  unfold Ops.co1GenStep
  refine Sp.lstOK_foldl T ?_ _ hx
  intro y hy
  rw [List.mem_flatMap] at hy
  obtain ⟨x, hxm, hy⟩ := hy
  rw [List.mem_map] at hy
  obtain ⟨g, hgm, rfl⟩ := hy
  obtain ⟨wx, mx⟩ := hx x hxm
  obtain ⟨wg, mg⟩ := hg g hgm
  exact ⟨Sp.mul_wf wx wg, by rw [Sp.toMat_mul wx wg]; exact T.mul_mem mx mg⟩

theorem lstOK_aux {gens : List M} (hg : Sp.LstOK T gens) :
    ∀ (n : ℕ) (xs : List M), Sp.LstOK T xs → Sp.LstOK T (O.co1GenAux gens n xs)
  | 0, xs, hx => hx
  | n + 1, xs, hx => by
    unfold Ops.co1GenAux
    split
    · exact hx
    · exact lstOK_aux hg n _ (Sp.lstOK_step T hg hx)

omit Sp in
theorem mem_step {gens xs : List M} {z : M} (hz : z ∈ xs) : z ∈ O.co1GenStep gens xs :=
  mem_foldl _ z hz

omit Sp in
theorem mem_aux {gens : List M} :
    ∀ (n : ℕ) (xs : List M) (z : M), z ∈ xs → z ∈ O.co1GenAux gens n xs
  | 0, xs, z, hz => hz
  | n + 1, xs, z, hz => by
    unfold Ops.co1GenAux
    split
    · exact hz
    · exact mem_aux n _ z (mem_step hz)

theorem closure_le_of_closed {gens xs : List M} (hgw : ∀ g ∈ gens, Sp.WF g)
    (hxs : ∀ x ∈ xs, Sp.WF x) (hone : O.one ∈ xs) (hcl : O.co1GenClosed gens xs = true)
    {t : Matrix (Fin d) (Fin d) (ZMod p)}
    (ht : t ∈ Submonoid.closure (Sp.toMat '' {g | g ∈ gens})) : ∃ y ∈ xs, Sp.toMat y = t := by
  induction ht using Submonoid.closure_induction_right with
  | one => exact ⟨O.one, hone, Sp.toMat_one⟩
  | mul_right x hx y hy ih =>
    obtain ⟨y0, hy0, rfl⟩ := ih
    obtain ⟨g, hg, rfl⟩ := hy
    have hgm : g ∈ gens := hg
    unfold Ops.co1GenClosed at hcl
    rw [List.all_eq_true] at hcl
    have h1 := List.all_eq_true.1 (hcl y0 hy0) g hgm
    obtain ⟨z, hz, hzeq⟩ := List.any_eq_true.1 h1
    refine ⟨z, hz, ?_⟩
    have := Sp.toMat_eq (Sp.mul_wf (hxs y0 hy0) (hgw g hgm)) (hxs z hz) hzeq
    rw [Sp.toMat_mul (hxs y0 hy0) (hgw g hgm)] at this
    exact this.symm

end Closure

section Units

variable {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))}

omit Sp in
theorem exists_unit_of_mem_closure (G₀ : Set Sˣ) {x : Matrix (Fin d) (Fin d) (ZMod p)}
    (hx : x ∈ Submonoid.closure (LocalWitness.valHom S '' G₀)) :
    ∃ w ∈ Subgroup.closure G₀, LocalWitness.valHom S w = x := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, Subgroup.subset_closure hg, rfl⟩
  | one => exact ⟨1, Subgroup.one_mem _, map_one _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨w₁, hw₁, rfl⟩ := ihx
    obtain ⟨w₂, hw₂, rfl⟩ := ihy
    exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, map_mul _ _ _⟩

omit Sp in
theorem isPGroup_of_closed (G₀ : Set Sˣ) (hord : ∀ g ∈ G₀, g ^ 5 = 1)
    (hT : ∀ t ∈ Submonoid.closure (LocalWitness.valHom S '' G₀), t ^ 625 = 1) :
    IsPGroup 5 (Subgroup.closure G₀) := by
  have key : ∀ w ∈ Subgroup.closure G₀,
      LocalWitness.valHom S w ∈ Submonoid.closure (LocalWitness.valHom S '' G₀) ∧
        LocalWitness.valHom S w⁻¹ ∈ Submonoid.closure (LocalWitness.valHom S '' G₀) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      have hm : LocalWitness.valHom S x ∈ Submonoid.closure (LocalWitness.valHom S '' G₀) :=
        Submonoid.subset_closure ⟨x, hx, rfl⟩
      refine ⟨hm, ?_⟩
      have : LocalWitness.valHom S x⁻¹ = LocalWitness.valHom S x ^ (5 - 1) :=
        LocalWitness.valHom_inv_of_pow S (by norm_num) (hord x hx)
      rw [this]
      exact Submonoid.pow_mem _ hm _
    | one => exact ⟨by simpa using Submonoid.one_mem _, by simpa using Submonoid.one_mem _⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨?_, ?_⟩
      · rw [map_mul]; exact Submonoid.mul_mem _ ihx.1 ihy.1
      · rw [mul_inv_rev, map_mul]; exact Submonoid.mul_mem _ ihy.2 ihx.2
    | inv x hx ih => exact ⟨ih.2, by rw [inv_inv]; exact ih.1⟩
  intro w
  refine ⟨4, ?_⟩
  apply Subtype.ext
  apply LocalWitness.valHom_injective S
  have h1 := hT _ (key w.1 w.2).1
  have h2 : ((w ^ 5 ^ 4 : Subgroup.closure G₀) : Sˣ) = (w : Sˣ) ^ 625 := by
    rw [Subgroup.coe_pow]
    norm_num
  rw [h2, Subgroup.coe_one, map_pow, map_one]
  exact h1

end Units


section Regs

variable [Inhabited M] (S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)))

@[expose] def co1GenRegsOK (R : Array M) : Prop := ∀ r < R.size, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S

omit Sp in
theorem co1Gen_getElem!_setIfInBounds {R : Array M} {k r : ℕ} (hr : r < R.size) (x : M) :
    (R.setIfInBounds k x)[r]! = if k = r then x else R[r]! := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_setIfInBounds,
    getElem!_pos R r hr]

theorem co1Gen_step_ok {R : Array M} (hR : Sp.co1GenRegsOK S R) {op : Op}
    (hop : op.lt R.size = true) :
    (O.step R op).size = R.size ∧ Sp.co1GenRegsOK S (O.step R op) := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, hk⟩ := hop
    have hs : (O.step R (.mul i j k)).size = R.size := by
      simp [Ops.step, Array.set!]
    refine ⟨hs, fun r hr => ?_⟩
    rw [hs] at hr
    simp only [Ops.step, Array.set!]
    rw [co1Gen_getElem!_setIfInBounds hr]
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
    rw [co1Gen_getElem!_setIfInBounds hr]
    split
    · obtain ⟨wi, mi⟩ := hR i hi
      obtain ⟨w, m⟩ := Sp.pow_spec wi e
      exact ⟨w, by rw [m]; exact S.pow_mem mi e⟩
    · exact hR r hr

theorem co1Gen_run_ok (prog : List Op) {R : Array M} (hR : Sp.co1GenRegsOK S R)
    (hprog : prog.all (Op.lt R.size) = true) :
    (O.run prog R).size = R.size ∧ Sp.co1GenRegsOK S (O.run prog R) := by
  induction prog generalizing R with
  | nil => exact ⟨rfl, hR⟩
  | cons op prog ih =>
    rw [List.all_cons, Bool.and_eq_true] at hprog
    obtain ⟨hs, hok⟩ := Sp.co1Gen_step_ok S hR hprog.1
    have := ih hok (by rw [hs]; exact hprog.2)
    simp only [Ops.run, List.foldl_cons] at this ⊢
    rw [this.1, hs]
    exact ⟨rfl, this.2⟩

end Regs

omit Sp in
theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] (H : Subgroup G) [Finite H] {g : G}
    (h : ∀ s ∈ H, g * s * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  have hcard : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hx' : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
  have : y = x := (MulAut.conj g).injective (by simpa using hyx)
  rw [← this]
  exact hy

theorem plane_sound [Inhabited M] [Inhabited V] {nregs : ℕ} {seedA seedB : String}
    {prog : List Op} (hprog : prog.all (Op.lt nregs) = true) (Pl : Co1Gen.Plane)
    (h : O.co1GenPlane nregs (O.regsOf seedA seedB nregs prog) Pl = true) :
    ∃ (uu vv : (NativeSporadic.seedMonoid p d 1 seedA seedB)ˣ)
      (N : Set (NativeSporadic.seedMonoid p d 1 seedA seedB)ˣ),
      valHom _ uu = Sp.toMat (O.regsOf seedA seedB nregs prog)[Pl.u]! ∧
      valHom _ vv = Sp.toMat (O.regsOf seedA seedB nregs prog)[Pl.v]! ∧
      uu ^ 5 = 1 ∧ vv ^ 5 = 1 ∧ uu * vv = vv * uu ∧
      Nat.card (Subgroup.closure ({uu, vv} : Set _)) = 5 ^ 2 ∧
      (∀ g ∈ N, g ∈ Subgroup.normalizer
        ((Subgroup.closure ({uu, vv} : Set _) : Subgroup _) : Set _)) ∧
      (∀ n ∈ Pl.norms, ∃ g ∈ N,
        valHom _ g = Sp.toMat (O.regsOf seedA seedB nregs prog)[n.reg]!) ∧
      (∀ g ∈ N, ∃ n ∈ Pl.norms,
        valHom _ g = Sp.toMat (O.regsOf seedA seedB nregs prog)[n.reg]!) ∧
      (∀ n ∈ Pl.norms, Sp.WF (O.regsOf seedA seedB nregs prog)[n.reg]!) ∧
      Sp.WF (O.regsOf seedA seedB nregs prog)[Pl.u]! ∧
      Sp.WF (O.regsOf seedA seedB nregs prog)[Pl.v]! := by
  set S := NativeSporadic.seedMonoid p d 1 seedA seedB
  set R := O.regsOf seedA seedB nregs prog
  unfold Ops.co1GenPlane at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hu, hv⟩, hU5⟩, hV5⟩, hcomm⟩, hnf⟩, hnorms⟩ := h
  obtain ⟨wU, mU⟩ := Sp.regsOf_ok hprog hu
  obtain ⟨wV, mV⟩ := Sp.regsOf_ok hprog hv
  have eU := Sp.pow_eq_one_of_check wU hU5
  have eV := Sp.pow_eq_one_of_check wV hV5
  let uu := unitOf S mU (by norm_num : (5 : ℕ) ≠ 0) eU
  let vv := unitOf S mV (by norm_num : (5 : ℕ) ≠ 0) eV
  have fu : valHom S uu = Sp.toMat R[Pl.u]! := rfl
  have fv : valHom S vv = Sp.toMat R[Pl.v]! := rfl
  have huv : uu * vv = vv * uu := valHom_injective S (by
    rw [map_mul, map_mul, fu, fv]
    have := Sp.toMat_eq (Sp.mul_wf wU wV) (Sp.mul_wf wV wU) hcomm
    rwa [Sp.toMat_mul wU wV, Sp.toMat_mul wV wU] at this)
  have hcard : Nat.card (Subgroup.closure ({uu, vv} : Set Sˣ)) = 5 ^ 2 := by
    refine card_closure_eq_sq (by norm_num) (unitOf_pow S mU _ eU) (unitOf_pow S mV _ eV) huv ?_
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hm := congrArg (valHom S) hij
    simp only [map_mul, map_pow, fu, fv] at hm
    unfold Ops.normalFormOK at hnf
    set vs := Array.ofFn (n := 5 ^ [R[Pl.u]!, R[Pl.v]!].length) fun n =>
      O.appBase 5 [R[Pl.u]!, R[Pl.v]!] n.val (O.unit Pl.t)
    have hvs : ∀ n < 5 ^ 2, Sp.toVec vs[n]! = Sp.toVec (O.unit Pl.t) ᵥ*
        (Sp.toMat R[Pl.u]! ^ (n % 5) * Sp.toMat R[Pl.v]! ^ (n / 5 % 5)) := by
      intro n hn'
      rw [getElem!_pos vs n (by simpa [vs] using hn'), Array.getElem_ofFn]
      exact Sp.appBase_two wU wV 5 n (Sp.unit_wf Pl.t)
    have hcode : ∀ (i j : Fin 5), (i + 5 * j : ℕ) < 5 ^ 2 ∧
        (i + 5 * j : ℕ) % 5 = i ∧ (i + 5 * j : ℕ) / 5 % 5 = j := by
      intro i j
      have := i.isLt
      have := j.isLt
      refine ⟨by omega, by omega, by omega⟩
    obtain ⟨c1, c2, c3⟩ := hcode i j
    obtain ⟨c1', c2', c3'⟩ := hcode i' j'
    by_contra hne
    have hcne : (i + 5 * j : ℕ) ≠ i' + 5 * j' := by
      intro hc
      apply hne
      have e1 : (i : ℕ) = i' := by rw [← c2, ← c2', hc]
      have e2 : (j : ℕ) = j' := by rw [← c3, ← c3', hc]
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have hsz : vs.size = 5 ^ 2 := by simp [vs]
    apply Sp.toVec_ne_of_distinctOK hnf (by rw [hsz]; exact c1) (by rw [hsz]; exact c1') hcne
    rw [hvs _ c1, hvs _ c1', c2, c3, c2', c3', hm]
  set H : Subgroup Sˣ := Subgroup.closure ({uu, vv} : Set Sˣ) with hH
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have huH : uu ∈ H := Subgroup.subset_closure (by simp)
  have hvH : vv ∈ H := Subgroup.subset_closure (by simp)
  have hmk : ∀ n ∈ Pl.norms, ∃ g : Sˣ, valHom S g = Sp.toMat R[n.reg]! ∧
      g ∈ Subgroup.normalizer (H : Set Sˣ) := by
    intro n hn
    have hn1 := List.all_eq_true.1 hnorms n hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn1
    obtain ⟨⟨⟨hreg, hord⟩, hHo⟩, hconj⟩ := hn1
    obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hreg
    have eH := Sp.pow_eq_one_of_check wH hHo
    let g := unitOf S mH hord.ne' eH
    have fg : valHom S g = Sp.toMat R[n.reg]! := rfl
    have key : ∀ (s : Sˣ) (Sm : M), Sp.WF Sm → valHom S s = Sp.toMat Sm →
        ((List.range 5).any fun a => (List.range 5).any fun b =>
          O.conjOK R[n.reg]! Sm (O.mul (O.pow R[Pl.u]! a) (O.pow R[Pl.v]! b))) = true →
        g * s * g⁻¹ ∈ H := by
      intro s Sm wS fs hc
      obtain ⟨a, -, hc⟩ := List.any_eq_true.1 hc
      obtain ⟨b, -, hc⟩ := List.any_eq_true.1 hc
      have wW : Sp.WF (O.mul (O.pow R[Pl.u]! a) (O.pow R[Pl.v]! b)) :=
        Sp.mul_wf (Sp.pow_spec wU a).1 (Sp.pow_spec wV b).1
      have hmat := Sp.toMat_of_conjOK wH wS wW hc
      have hW : valHom S (uu ^ a * vv ^ b) =
          Sp.toMat (O.mul (O.pow R[Pl.u]! a) (O.pow R[Pl.v]! b)) := by
        rw [map_mul, map_pow, map_pow, fu, fv, Sp.toMat_mul (Sp.pow_spec wU a).1 (Sp.pow_spec wV b).1,
          (Sp.pow_spec wU a).2, (Sp.pow_spec wV b).2]
      have : g * s * g⁻¹ = uu ^ a * vv ^ b := by
        rw [mul_inv_eq_iff_eq_mul]
        apply valHom_injective S
        rw [map_mul, map_mul, fg, fs, hW]
        exact hmat
      rw [this]
      exact H.mul_mem (H.pow_mem huH a) (H.pow_mem hvH b)
    have hgu := key uu R[Pl.u]! wU fu (List.all_eq_true.1 hconj _ (by simp))
    have hgv := key vv R[Pl.v]! wV fv (List.all_eq_true.1 hconj _ (by simp))
    refine ⟨g, fg, mem_normalizer_of_conj_mem H (fun x hx => ?_)⟩
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hgu
      · exact hgv
    | one => simpa using H.one_mem
    | mul x y hx hy ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact H.mul_mem ihx ihy
    | inv x hx ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact H.inv_mem ih
  refine ⟨uu, vv, {g | (∃ n ∈ Pl.norms, valHom S g = Sp.toMat R[n.reg]!) ∧
    g ∈ Subgroup.normalizer (H : Set Sˣ)}, fu, fv, unitOf_pow S mU _ eU, unitOf_pow S mV _ eV, huv,
    hcard, fun g hg => hg.2, fun n hn => ?_, fun g hg => ?_, fun n hn => ?_, wU, wV⟩
  · obtain ⟨g, hg1, hg2⟩ := hmk n hn
    exact ⟨g, ⟨⟨n, hn, hg1⟩, hg2⟩, hg1⟩
  · obtain ⟨⟨n, hn, hgn⟩, -⟩ := hg
    exact ⟨n, hn, hgn⟩
  · have hn1 := List.all_eq_true.1 hnorms n hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn1
    exact (Sp.regsOf_ok hprog hn1.1.1.1).1


omit Sp in
theorem isElemAbelian_closure_pair {G : Type*} [Group G] {p : ℕ} {u v : G} (huv : u * v = v * u)
    (hu : u ^ p = 1) (hv : v ^ p = 1) :
    CFSG.Open.IsElemAbelian p (Subgroup.closure ({u, v} : Set G)) := by
  have hcomm : IsMulCommutative (Subgroup.closure ({u, v} : Set G)) :=
    Subgroup.isMulCommutative_closure (by
      rintro x hx y hy -
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | exact Commute.refl _ | exact huv | exact huv.symm)
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => rcases hx with rfl | rfl <;> assumption
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := Subtype.ext_iff.1
      (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem co1Gen_of_check [Inhabited M] [Inhabited V] (D : Co1Gen.Data)
    (h : O.co1GenCheck D = true) :
    ∃ (P₀ : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ)
      (Sg : Fin 2 → Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ)
      (N : Fin 2 → Set (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ),
      IsPGroup 5 P₀ ∧ (∀ i, Sg i ≤ P₀) ∧
      (∀ i, ∃ E : Subgroup (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ,
        E ≤ Sg i ∧ CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2) ∧
      (∀ i, ∀ n ∈ N i, n ∈ Subgroup.normalizer (Sg i : Set _)) ∧
      Subgroup.closure (⋃ i, N i) = ⊤ := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB with hS
  unfold Ops.co1GenCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, hprog⟩, hA2⟩, hB3⟩, hpg5⟩, hcl⟩, hx625⟩, hpl1⟩, hpl2⟩, hlen⟩,
    hprog2⟩, hrA⟩, hrB⟩, hAeq⟩, hBeq⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog with hR
  have wA : Sp.WF (O.decode D.seedA) := Sp.decode_wf _
  have wB : Sp.WF (O.decode D.seedB) := Sp.decode_wf _
  have mA : Sp.toMat (O.decode D.seedA) ∈ S := by
    rw [Sp.toMat_decode]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  have mB : Sp.toMat (O.decode D.seedB) ∈ S := by
    rw [Sp.toMat_decode]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  have eA := Sp.pow_eq_one_of_check wA hA2
  have eB := Sp.pow_eq_one_of_check wB hB3
  let a := unitOf S mA (by norm_num : (2 : ℕ) ≠ 0) eA
  let b := unitOf S mB (by norm_num : (3 : ℕ) ≠ 0) eB
  have fa : valHom S a = Sp.toMat (O.decode D.seedA) := rfl
  have fb : valHom S b = Sp.toMat (O.decode D.seedB) := rfl
  have hab : Subgroup.closure ({a, b} : Set Sˣ) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have himg : valHom S '' ({a, b} : Set Sˣ) =
        {Sp.toMat (O.decode D.seedA), Sp.toMat (O.decode D.seedB)} := by
      rw [Set.image_pair, fa, fb]
    have hu : (u.val : Matrix (Fin d) (Fin d) (ZMod p)) ∈
        Submonoid.closure (valHom S '' ({a, b} : Set Sˣ)) := by
      rw [himg, Sp.toMat_decode, Sp.toMat_decode]
      exact u.val.2
    obtain ⟨w, hw, hwu⟩ := exists_unit_of_mem_closure ({a, b} : Set Sˣ) hu
    have : w = u := valHom_injective S hwu
    rw [← this]
    exact hw
  obtain ⟨uu1, vv1, N1, fu1, fv1, hu1, hv1, huv1, hcard1, hn1, hc1, hb1, hw1, hwu1, hwv1⟩ :=
    Sp.plane_sound hprog D.plane1 hpl1
  obtain ⟨uu2, vv2, N2, fu2, fv2, hu2, hv2, huv2, hcard2, hn2, hc2, hb2, hw2, hwu2, hwv2⟩ :=
    Sp.plane_sound hprog D.plane2 hpl2
  set pg : List M := [R[D.plane1.u]!, R[D.plane1.v]!, R[D.plane2.u]!, R[D.plane2.v]!] with hpg
  have hgw : ∀ g ∈ pg, Sp.WF g := by
    intro g hg
    simp only [hpg, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption
  set Tg := Submonoid.closure (Sp.toMat '' {g | g ∈ pg}) with hTg
  have hgT : Sp.LstOK Tg pg := fun g hg => ⟨hgw g hg, Submonoid.subset_closure ⟨g, hg, rfl⟩⟩
  set xs := O.co1GenClosure pg D.fuelP with hxs
  have hxsOK : Sp.LstOK Tg xs := by
    refine lstOK_aux Sp Tg hgT D.fuelP [O.one] ?_
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact Tg.one_mem⟩
  have hone : O.one ∈ xs := mem_aux D.fuelP [O.one] O.one (List.mem_singleton_self _)
  set G₀ : Set Sˣ := {uu1, vv1, uu2, vv2} with hG₀
  have hsub : valHom S '' G₀ ⊆ Sp.toMat '' {g | g ∈ pg} := by
    rintro _ ⟨g, hg, rfl⟩
    simp only [hG₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨R[D.plane1.u]!, by simp [hpg], fu1.symm⟩
    · exact ⟨R[D.plane1.v]!, by simp [hpg], fv1.symm⟩
    · exact ⟨R[D.plane2.u]!, by simp [hpg], fu2.symm⟩
    · exact ⟨R[D.plane2.v]!, by simp [hpg], fv2.symm⟩
  have hT625 : ∀ t ∈ Submonoid.closure (valHom S '' G₀), t ^ 625 = 1 := by
    intro t ht
    have ht' : t ∈ Tg := Submonoid.closure_mono hsub ht
    obtain ⟨y, hy, rfl⟩ := Sp.closure_le_of_closed hgw (fun x hx => (hxsOK x hx).1) hone hcl ht'
    exact Sp.pow_eq_one_of_check (hxsOK y hy).1 (List.all_eq_true.1 hx625 y hy)
  have hord : ∀ g ∈ G₀, g ^ 5 = 1 := by
    intro g hg
    simp only [hG₀, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption
  have hP₀ : IsPGroup 5 (Subgroup.closure G₀) := isPGroup_of_closed G₀ hord hT625
  have hgen : Subgroup.closure (N1 ∪ N2) = ⊤ := by
    set ns : List M := (D.plane1.norms ++ D.plane2.norms).map fun n => R[n.reg]! with hns
    set init : Array M := Array.ofFn (n := D.nregs2) fun r => (ns[r.val]?).getD O.one with hinit
    set T₂ := Submonoid.closure (valHom S '' (N1 ∪ N2)) with hT₂
    have hmemns : ∀ x ∈ ns, Sp.WF x ∧ Sp.toMat x ∈ T₂ := by
      intro x hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
      rcases List.mem_append.1 hn with hn | hn
      · obtain ⟨g, hgN, hgv⟩ := hc1 n hn
        exact ⟨hw1 n hn, by rw [← hgv]; exact Submonoid.subset_closure ⟨g, Or.inl hgN, rfl⟩⟩
      · obtain ⟨g, hgN, hgv⟩ := hc2 n hn
        exact ⟨hw2 n hn, by rw [← hgv]; exact Submonoid.subset_closure ⟨g, Or.inr hgN, rfl⟩⟩
    have hsz : init.size = D.nregs2 := by simp [hinit]
    have hget : ∀ r (hr : r < D.nregs2), init[r]! = (ns[r]?).getD O.one := by
      intro r hr
      have hr' : r < init.size := by rw [hsz]; exact hr
      rw [getElem!_pos init r hr']
      simp [hinit]
    have hR0 : Sp.co1GenRegsOK T₂ init := by
      intro r hr
      have hr2 : r < D.nregs2 := by rw [← hsz]; exact hr
      rw [hget r hr2]
      cases hx : ns[r]? with
      | none =>
        show Sp.WF O.one ∧ Sp.toMat O.one ∈ T₂
        exact ⟨Sp.one_wf, by rw [Sp.toMat_one]; exact T₂.one_mem⟩
      | some x =>
        exact hmemns x (List.mem_of_getElem? hx)
    obtain ⟨hsz2, hok⟩ := Sp.co1Gen_run_ok T₂ D.prog2 hR0 (by rw [hsz]; exact hprog2)
    have hrA' := hok D.rA (by rw [hsz2, hsz]; exact hrA)
    have hrB' := hok D.rB (by rw [hsz2, hsz]; exact hrB)
    have mA2 : Sp.toMat (O.decode D.seedA) ∈ T₂ := by
      have := Sp.toMat_eq hrA'.1 wA hAeq
      rw [← this]
      exact hrA'.2
    have mB2 : Sp.toMat (O.decode D.seedB) ∈ T₂ := by
      have := Sp.toMat_eq hrB'.1 wB hBeq
      rw [← this]
      exact hrB'.2
    obtain ⟨wa, hwa, hwav⟩ := exists_unit_of_mem_closure (N1 ∪ N2) mA2
    obtain ⟨wb, hwb, hwbv⟩ := exists_unit_of_mem_closure (N1 ∪ N2) mB2
    have ha : a ∈ Subgroup.closure (N1 ∪ N2) := by
      have : wa = a := valHom_injective S (by rw [hwav, fa])
      rw [← this]
      exact hwa
    have hb : b ∈ Subgroup.closure (N1 ∪ N2) := by
      have : wb = b := valHom_injective S (by rw [hwbv, fb])
      rw [← this]
      exact hwb
    rw [eq_top_iff, ← hab, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  refine ⟨Subgroup.closure G₀, ![Subgroup.closure ({uu1, vv1} : Set Sˣ),
    Subgroup.closure ({uu2, vv2} : Set Sˣ)], ![N1, N2], hP₀, ?_, ?_, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    refine ⟨Subgroup.closure_mono ?_, Subgroup.closure_mono ?_⟩
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [hG₀]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp [hG₀]
  · rw [Fin.forall_fin_two]
    exact ⟨⟨_, le_rfl, isElemAbelian_closure_pair huv1 hu1 hv1, hcard1⟩,
      ⟨_, le_rfl, isElemAbelian_closure_pair huv2 hu2 hv2, hcard2⟩⟩
  · rw [Fin.forall_fin_two]
    exact ⟨hn1, hn2⟩
  · have : (⋃ i, (![N1, N2] : Fin 2 → Set Sˣ) i) = N1 ∪ N2 := by
      ext x
      simp [Fin.exists_fin_two]
    rw [this]
    exact hgen

end OpsSpec

end CFSG.SectionRank
