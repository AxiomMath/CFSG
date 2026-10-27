module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
import all CFSG.Fischer.F4
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
public import CFSG.Certificates.Kernel.F4M3BSound
public import Certificates.Data.Kernel.F4T7B

public section

namespace CFSG.KC.F4T7B

open CFSG.Fischer CFSG.KC.F4M3B CFSG.RankThree.PartTwo.Sec10.KS1012GL34
  CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

@[expose] def lbF (x : F4) : Bool := lb x.code

@[expose] def hbF (x : F4) : Bool := hb x.code

@[expose] def f4 (n : Nat) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def bits (A : M3) : MatT Bool :=
  ⟨lbF A.a00, hbF A.a00, lbF A.a01, hbF A.a01, lbF A.a02, hbF A.a02, lbF A.a10, hbF A.a10,
    lbF A.a11, hbF A.a11, lbF A.a12, hbF A.a12, lbF A.a20, hbF A.a20, lbF A.a21, hbF A.a21,
    lbF A.a22, hbF A.a22⟩

@[expose] def vb (w : V3) : VT Bool := ⟨lbF w.x, hbF w.x, lbF w.y, hbF w.y, lbF w.z, hbF w.z⟩

@[expose] def ptOf (u : Pt) : V3 := ⟨f4 u.1, f4 u.2.1, f4 u.2.2⟩

@[expose] def PtOK (u : Pt) : Prop := u.1 < 4 ∧ u.2.1 < 4 ∧ u.2.2 < 4

theorem add_l (x y : F4) : lbF (x + y) = boolOps.x (lbF x) (lbF y) := by
  revert x y
  decide

theorem add_h (x y : F4) : hbF (x + y) = boolOps.x (hbF x) (hbF y) := by
  revert x y
  decide

theorem kl_e (x : F4) (n : Nat) (hn : n < 4) :
    kl boolOps n (lbF x) (hbF x) = lbF (x * f4 n) := by
  revert x
  interval_cases n <;> decide

theorem kh_e (x : F4) (n : Nat) (hn : n < 4) :
    kh boolOps n (lbF x) (hbF x) = hbF (x * f4 n) := by
  revert x
  interval_cases n <;> decide

theorem eq_e (x : F4) (n : Nat) (hn : n < 4) :
    (lit boolOps (cl n) (lbF x) && lit boolOps (ch n) (hbF x)) = decide (x = f4 n) := by
  revert x
  interval_cases n <;> decide

theorem fmul_lt (a b : Nat) : fmul a b < 4 := by
  unfold fmul
  cases xor (cl a && cl b) (ch a && ch b) <;>
    cases xor (xor (cl a && ch b) (ch a && cl b)) (ch a && ch b) <;> decide

theorem fmul_e (a b : Nat) (ha : a < 4) (hb : b < 4) : f4 (fmul a b) = f4 a * f4 b := by
  interval_cases a <;> interval_cases b <;> decide

theorem smul_ok (c : Nat) (u : Pt) : PtOK (smul c u) :=
  ⟨fmul_lt _ _, fmul_lt _ _, fmul_lt _ _⟩

theorem ptOf_smul (c : Nat) (u : Pt) (hc : c < 4) (hu : PtOK u) :
    ptOf (smul c u) = smulV (f4 c) (ptOf u) := by
  simp only [ptOf, smul, smulV, fmul_e c _ hc hu.1, fmul_e c _ hc hu.2.1, fmul_e c _ hc hu.2.2]

theorem img_bits (A : M3) (u : Pt) (hu : PtOK u) :
    img boolOps (bits A) u = vb (mulV A (ptOf u)) := by
  obtain ⟨h1, h2, h3⟩ := hu
  simp only [img, bits, vb, mulV, ptOf, add_l, add_h, kl_e _ _ h1, kl_e _ _ h2, kl_e _ _ h3,
    kh_e _ _ h1, kh_e _ _ h2, kh_e _ _ h3]

theorem eqV_vb (w : V3) (e : Pt) (he : PtOK e) :
    eqV boolOps (vb w) e = decide (w = ptOf e) := by
  obtain ⟨h1, h2, h3⟩ := he
  obtain ⟨x, y, z⟩ := w
  simp only [eqV, vb, a_bool, Bool.and_assoc]
  rw [← Bool.and_assoc (lit boolOps (cl e.1) (lbF x)), eq_e _ _ h1,
    ← Bool.and_assoc (lit boolOps (cl e.2.1) (lbF y)), eq_e _ _ h2, eq_e _ _ h3]
  simp only [ptOf, V3.mk.injEq, Bool.decide_and]

theorem mulOf_vb (w : V3) (u : Pt) (hu : PtOK u) :
    mulOf boolOps (vb w) u = NZL.any fun c => w == smulV c (ptOf u) := by
  simp only [mulOf, bor_bool, eqV_vb _ _ (smul_ok _ _), ptOf_smul 1 _ (by decide) hu,
    ptOf_smul 2 _ (by decide) hu, ptOf_smul 3 _ (by decide) hu]
  simp only [NZL, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  rfl

theorem all_congr' {γ : Type} {l : List γ} {p q : γ → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem any_congr' {γ : Type} {l : List γ} {p q : γ → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem andL_bool (l : List Bool) : andL boolOps l = l.all id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [andL, List.foldr_cons, List.all_cons] at ih ⊢
    rw [ih]
    rfl

theorem orL_bool (l : List Bool) : orL boolOps l = l.any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [orL, List.foldr_cons, List.any_cons] at ih ⊢
    rw [bor_bool, ih]
    rfl

theorem stabT_bits (A : M3) (om : List Pt) (hom : ∀ u ∈ om, PtOK u) :
    stabT boolOps (mtab boolOps (bits A) om) = stabOf (om.map ptOf) ((om.map ptOf).map (mulV A)) := by
  simp only [stabT, mtab, stabOf, andL_bool, orL_bool, List.all_map, List.any_map, List.map_map]
  apply all_congr'
  intro u hu
  simp only [Function.comp]
  rw [orL_bool, List.any_map]
  apply any_congr'
  intro v hv
  simp only [Function.comp, id]
  rw [img_bits A u (hom u hu), mulOf_vb _ v (hom v hv)]

theorem cmul_code (x y : F4) : (x * y).code = CFSG.Quasithin.H13.L34.cmul x.code y.code := by
  revert x y
  decide

theorem cadd_code (x y : F4) : (x + y).code = CFSG.Quasithin.H13.L34.cadd x.code y.code := by
  revert x y
  decide

@[expose] def toL (A : M3) : CFSG.Quasithin.H13.L34.M3 :=
  ⟨A.a00.code, A.a01.code, A.a02.code, A.a10.code, A.a11.code, A.a12.code, A.a20.code,
    A.a21.code, A.a22.code⟩

theorem detL_six (A : M3) : Light.detL A =
    A.a00 * (A.a11 * A.a22) + A.a01 * (A.a12 * A.a20) + A.a02 * (A.a10 * A.a21) +
      (A.a02 * (A.a11 * A.a20) + A.a01 * (A.a10 * A.a22) + A.a00 * (A.a12 * A.a21)) := by
  have hs : ∀ a b : F4, a - b = a + b := fun _ _ => rfl
  have hn : ∀ a : F4, -a = a := fun _ => rfl
  simp only [Light.detL, hs, hn]
  ring

theorem det_toL (A : M3) : CFSG.Quasithin.H13.L34.M3.det (toL A) = (Light.detL A).code := by
  rw [detL_six]
  simp only [cmul_code, cadd_code, CFSG.Quasithin.H13.L34.M3.det,
    CFSG.Quasithin.H13.L34.M3.add3, toL]

theorem bits_eq (A : M3) : bits A = ofM3 (toL A) := rfl

theorem det_bits (A : M3) :
    isOne boolOps (F4M3B.detL boolOps (bits A)) (detH boolOps (bits A)) =
      decide (Light.detL A = 1) := by
  rw [bits_eq, detL_ofM3, detH_ofM3, isOne_enc, det_toL]
  have h1 : ∀ x : F4, x.code = 1 ↔ x = 1 := by decide
  simp only [decide_eq_decide]
  exact h1 _

theorem stabX_bits (A : M3) (om : List Pt) (hom : ∀ u ∈ om, PtOK u) :
    stabX boolOps (bits A) om =
      (decide (Light.detL A = 1) && stabOf (om.map ptOf) ((om.map ptOf).map (mulV A))) := by
  rw [stabX, a_bool, det_bits, stabT_bits A om hom]

theorem omC_ok (i : Fin 6) : ∀ u ∈ omC i.val, PtOK u := by
  unfold PtOK
  revert i
  decide

theorem omC_map (i : Fin 6) : (omC i.val).map ptOf = omegaL i.val := by
  revert i
  decide

theorem stabX_omC (A : M3) (i : Fin 6) :
    stabX boolOps (bits A) (omC i.val) = (decide (Light.detL A = 1) && stabLn i.val A) := by
  rw [stabX_bits A _ (omC_ok i), omC_map, stabLn]

end CFSG.KC.F4T7B

end
