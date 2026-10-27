module

public import CFSG.Certificates.Kernel.LocalQTM11GrpProved
public import Certificates.Data.Kernel.LocalQT.M11Perm
import all CFSG.Certificates.Kernel.LocalQTM11GrpProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11Inputs

public section

namespace CFSG.KC.LQT.M

open Equiv Finset CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W

namespace CntP

open GrpP

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def ordGo (x r p : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun r ih p => Bool.rec (motive := fun _ => Bool)
      (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq p (one 11))) (ih (mul 11 p x))) (Nat.beq p (one 11)) (Nat.beq r 0)) r p

theorem orderK_eq (x m : ℕ) : orderK x m = ordGo x m x := rfl

theorem ordGo_code (x : Perm (Fin 11)) : ∀ (r j : ℕ),
    ordGo (P.code x) (r + 1) (P.code (x ^ j)) = true ↔
      (∀ i < r, x ^ (j + i) ≠ 1) ∧ x ^ (j + r) = 1
  | 0, j => by
    change Nat.beq (P.code (x ^ j)) (one 11) = true ↔ _
    rw [code_one, beq_code h11]
    simp
  | r + 1, j => by
    change CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq (P.code (x ^ j)) (one 11)))
      (ordGo (P.code x) (r + 1) (mul 11 (P.code (x ^ j)) (P.code x))) = true ↔ _
    rw [code_mul h11, ← pow_succ, andB_iff, notB_iff, code_one, beq_code h11, ordGo_code x r (j + 1)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · rcases i with _ | i
        · simpa using h1
        · have e : j + (i + 1) = j + 1 + i := by omega
          rw [e]
          exact h2 i (by omega)
      · have e : j + (r + 1) = j + 1 + r := by omega
        rw [e]
        exact h3
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, ?_⟩
      · have e : j + 1 + i = j + (i + 1) := by omega
        rw [e]
        exact h1 (i + 1) (by omega)
      · have e : j + 1 + r = j + (r + 1) := by omega
        rw [e]
        exact h2

theorem orderK_code (x : Perm (Fin 11)) {m : ℕ} (hm : 0 < m) :
    orderK (P.code x) m = CFSG.Sporadic.Schreier.orderIs x m := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  apply Bool.eq_iff_iff.2
  rw [CFSG.Sporadic.Schreier.orderIs_iff x hm, orderOf_eq_iff hm, orderK_eq]
  have e := ordGo_code x r 1
  rw [pow_one] at e
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rwa [Nat.add_comm] at h2, fun k hk hk0 => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk0.ne'
    rw [Nat.add_comm]
    exact h1 i (by omega)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, by rwa [Nat.add_comm]⟩
    rw [Nat.add_comm]
    exact h2 (i + 1) (by omega) (by omega)

open CFSG.QuasithinUnique.Setup.X1 in
theorem wordK_code (x y : Perm (Fin 11)) : wordK (P.code x) (P.code y) = P.code (m11Word x y) := by
  unfold wordK
  rw [strictN_eq, code_mul h11, code_mul h11, code_mul h11, code_mul h11, code_mul h11,
    code_mul h11, code_mul h11]
  rfl

theorem ord4M_code (x : Perm (Fin 11)) : ord4M (P.code x) = true ↔ x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  unfold ord4M
  rw [letB_eq, code_mul h11, code_mul h11, andB_iff, notB_iff, code_one, beq_code h11, beq_code h11]
  have e4 : x ^ 4 = x * x * (x * x) := by simp [pow_succ, mul_assoc]
  rw [e4, pow_two]

theorem invoM_code (x : Perm (Fin 11)) : invoM (P.code x) = true ↔ x ≠ 1 ∧ x * x = 1 := by
  unfold invoM
  rw [andB_iff, notB_iff, code_one, beq_code h11, code_mul h11, beq_code h11]

theorem pwM_go (x : Perm (Fin 11)) (e nb : ℕ) (h0 : e / 2 ^ nb = 0)
    (hb : ∀ k < nb, e / 2 ^ (nb - (k + 1)) = 2 * (e / 2 ^ (nb - k)) +
      Bool.rec (motive := fun _ => ℕ) 0 1
        (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) :
    ∀ k ≤ nb, (Nat.rec (motive := fun _ => ℕ) (one 11)
      (fun k acc => CFSG.KC.Loop.strictN (mul 11 acc acc) fun a2 =>
        Bool.rec (motive := fun _ => ℕ) a2 (mul 11 a2 (P.code x))
          (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) k : ℕ) =
      P.code (x ^ (e / 2 ^ (nb - k)))
  | 0, _ => by
    change one 11 = _
    rw [Nat.sub_zero, h0, pow_zero, code_one]
  | k + 1, hk => by
    change CFSG.KC.Loop.strictN (mul 11 _ _) _ = _
    rw [strictN_eq, pwM_go x e nb h0 hb k (by omega), code_mul h11, hb k (by omega)]
    cases Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k)))
    · change P.code _ = P.code (x ^ (2 * (e / 2 ^ (nb - k)) + 0))
      rw [Nat.add_zero, two_mul, pow_add]
    · change mul 11 (P.code _) (P.code x) = P.code (x ^ (2 * (e / 2 ^ (nb - k)) + 1))
      rw [code_mul h11, pow_succ, two_mul, pow_add]

theorem pwM_code (x : Perm (Fin 11)) (e nb : ℕ) (h0 : e / 2 ^ nb = 0)
    (hb : ∀ k < nb, e / 2 ^ (nb - (k + 1)) = 2 * (e / 2 ^ (nb - k)) +
      Bool.rec (motive := fun _ => ℕ) 0 1
        (Nat.blt 0 (Nat.land e (Nat.shiftLeft 1 (Nat.sub (Nat.sub nb 1) k))))) :
    pwM (P.code x) e nb = P.code (x ^ e) := by
  have h := pwM_go x e nb h0 hb nb le_rfl
  rw [Nat.sub_self, pow_zero, Nat.div_one] at h
  exact h

theorem pwM495 (x : Perm (Fin 11)) : pwM (P.code x) 495 9 = P.code (x ^ 495) :=
  pwM_code x 495 9 (by decide) (by decide)

theorem pwM16 (x : Perm (Fin 11)) : pwM (P.code x) 16 5 = P.code (x ^ 16) :=
  pwM_code x 16 5 (by decide) (by decide)

theorem oddK_code (x : Perm (Fin 11)) : oddK (P.code x) = true ↔ x ≠ 1 ∧ x ^ 495 = 1 := by
  unfold oddK
  rw [andB_iff, notB_iff, code_one, beq_code h11, pwM495, beq_code h11]

theorem exists_codes : ∀ {L : List ℕ}, allL L (permK 11) = true →
    ∃ Ls : List (Perm (Fin 11)), Ls.map P.code = L
  | [], _ => ⟨[], rfl⟩
  | x :: L, h => by
    rw [allL_iff] at h
    obtain ⟨σ, hσ⟩ := exists_of_permK (n := 11) (h x (by simp))
    obtain ⟨Ls, hL⟩ := exists_codes ((allL_iff _ _).2 fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact ⟨σ :: Ls, by rw [List.map_cons, hσ, hL]⟩

theorem getK_eq' : ∀ (l : List ℕ) (i : ℕ), CFSG.KC.LQT.S.getK l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    change CFSG.KC.LQT.S.getK l (Nat.sub (i + 1) 1) = _
    rw [Nat.sub_eq, Nat.add_sub_cancel, getK_eq' l i]
    rfl

theorem getW_eq : ∀ (W : List (List ℕ)) (i : ℕ), getW W i = W.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: W, i + 1 => by
    change getW W (Nat.sub (i + 1) 1) = _
    rw [Nat.sub_eq, Nat.add_sub_cancel, getW_eq W i]
    rfl

theorem getD_code (Ro : List (Perm (Fin 11))) {i : ℕ} (hi : i < Ro.length) :
    (Ro.map P.code).getD i 0 = P.code (Ro.getD i 1) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

theorem getD_mem {α : Type*} (l : List α) (d : α) {i : ℕ} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem sum_range_getD {α : Type*} (l : List α) (f : α → ℕ) (d : α) :
    ∑ i ∈ range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp [Nat.add_comm]

theorem rec_sum_list (F : ℕ → ℕ) (L : List ℕ) :
    List.rec (motive := fun _ => ℕ) 0 (fun r _ ih => Nat.add (F r) ih) L = (L.map F).sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Nat.add (F x) _ = _
    rw [ih, List.map_cons, List.sum_cons]
    rfl

theorem rec_len {α : Type*} (L : List α) :
    List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Nat.succ _ = _
    rw [ih, List.length_cons]

theorem rec_all (F : List ℕ → Bool) (L : List (List ℕ)) :
    List.rec (motive := fun _ => Bool) true (fun l _ ih => CFSG.KC.Ord.andB (F l) ih) L = true ↔
      ∀ l ∈ L, F l = true := by
  induction L with
  | nil => simp
  | cons x L ih =>
    change CFSG.KC.Ord.andB (F x) _ = true ↔ _
    rw [andB_iff, ih]
    simp

theorem tripL_iff (LX LI : List ℕ) : tripL LX LI = true ↔ ∀ x ∈ LX, rowT x LI = true := by
  induction LX with
  | nil => simp [tripL]
  | cons x LX ih =>
    change CFSG.KC.Ord.andB (rowT x LI) (tripL LX LI) = true ↔ _
    rw [andB_iff, ih]
    simp

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 in
theorem cntY_code (x : Perm (Fin 11)) (Lf : List (Perm (Fin 11))) :
    cntY (P.code x) (Lf.map P.code) =
      (Lf.filter fun y => orderIs (x * y) 11 && orderIs (m11Word x y) 3).length := by
  induction Lf with
  | nil => rfl
  | cons y Lf ih =>
    change Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1
      (CFSG.KC.Ord.andB (orderK (mul 11 (P.code x) (P.code y)) 11) (orderK (wordK (P.code x) (P.code y)) 3)))
      (cntY (P.code x) (Lf.map P.code)) = _
    rw [ih, code_mul h11, wordK_code, orderK_code _ (by norm_num), orderK_code _ (by norm_num),
      List.filter_cons]
    cases orderIs (x * y) 11 <;> cases orderIs (m11Word x y) 3 <;> simp [CFSG.KC.Ord.andB, Nat.add_comm]

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 in
theorem cntL_code (Li Lf : List (Perm (Fin 11))) :
    cntL (Li.map P.code) (Lf.map P.code) = (Li.map fun x =>
      (Lf.filter fun y => orderIs (x * y) 11 && orderIs (m11Word x y) 3).length).sum := by
  induction Li with
  | nil => rfl
  | cons x Li ih =>
    change Nat.add (cntY (P.code x) (Lf.map P.code)) (cntL (Li.map P.code) (Lf.map P.code)) = _
    rw [ih, cntY_code, List.map_cons, List.sum_cons]
    rfl

theorem length_filter_product {α β : Type*} (A : List α) (B : List β) (p : α × β → Bool) :
    ((A ×ˢ B).filter p).length = (A.map fun x => (B.filter fun y => p (x, y)).length).sum := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    rw [List.product_cons, List.filter_append, List.length_append, ih, List.map_cons, List.sum_cons,
      List.filter_map, List.length_map]
    rfl

variable {gA gB : Perm (Fin 11)} {CA CB : ℕ} {R1 R2 R3 R4 : List ℕ} {W1 W2 W3 W4 : List (List ℕ)}

theorem brec_eq (b : Bool) (x : ℕ) :
    Bool.rec (motive := fun _ => ℕ) 0 x b = if b = true then x else 0 := by
  cases b <;> rfl

theorem sum_okIx (k : ℕ) (g : ℕ → ℕ) :
    (∑ b ∈ range 11, if okIx k b = true then g b else 0) = ∑ b ∈ Ico k 11, g b := by
  rw [← Finset.sum_filter]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, okIx, Nat.ble_eq]
  omega

theorem rho_val (ha : P.code gA = CA) (hb : P.code gB = CB) {k : ℕ} {R : List ℕ}
    {W : List (List ℕ)} (h : repsOK [CA, CB] k R W = true) {j : ℕ} (hj : j < 11) (hk : k ≤ j) :
    (∀ i (hi : i < k), rho gA gB W j ⟨i, by omega⟩ = ⟨i, by omega⟩) ∧
      (rho gA gB W j ⟨k, by omega⟩ : ℕ) = j := by
  obtain ⟨e, f1, f2⟩ := rep_code ha hb h hj hk
  rw [e] at f1 f2
  refine ⟨fun i hi => Fin.ext ?_, ?_⟩
  · rw [← img_fin _ (by omega)]
    exact f1 i hi
  · rw [← img_fin _ (by omega)]
    exact f2

theorem mul_fix {σ τ : Perm (Fin 11)} {i : Fin 11} (h : τ i = i) : (σ * τ) i = σ i := by
  rw [Perm.mul_apply, h]

theorem quad_inj (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {a b c d a' b' c' d' : ℕ}
    (ha1 : a < 11) (hb1 : 1 ≤ b) (hb2 : b < 11) (hc1 : 2 ≤ c) (hc2 : c < 11) (hd1 : 3 ≤ d)
    (hd2 : d < 11) (ha1' : a' < 11) (hb1' : 1 ≤ b') (hb2' : b' < 11) (hc1' : 2 ≤ c')
    (hc2' : c' < 11) (hd1' : 3 ≤ d') (hd2' : d' < 11)
    (e : rho gA gB W1 a * rho gA gB W2 b * rho gA gB W3 c * rho gA gB W4 d =
      rho gA gB W1 a' * rho gA gB W2 b' * rho gA gB W3 c' * rho gA gB W4 d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have r1 := rho_val ha hb hG.r1 ha1 (Nat.zero_le _)
  have r1' := rho_val ha hb hG.r1 ha1' (Nat.zero_le _)
  have r2 := rho_val ha hb hG.r2 hb2 hb1
  have r2' := rho_val ha hb hG.r2 hb2' hb1'
  have r3 := rho_val ha hb hG.r3 hc2 hc1
  have r3' := rho_val ha hb hG.r3 hc2' hc1'
  have r4 := rho_val ha hb hG.r4 hd2 hd1
  have r4' := rho_val ha hb hG.r4 hd2' hd1'
  have v0 := congrArg (fun σ : Perm (Fin 11) => (σ ⟨0, by norm_num⟩ : ℕ)) e
  rw [mul_fix (r4.1 0 (by norm_num)), mul_fix (r3.1 0 (by norm_num)), mul_fix (r2.1 0 (by norm_num)),
    mul_fix (r4'.1 0 (by norm_num)), mul_fix (r3'.1 0 (by norm_num)),
    mul_fix (r2'.1 0 (by norm_num)), r1.2, r1'.2] at v0
  subst v0
  have e2 : rho gA gB W2 b * rho gA gB W3 c * rho gA gB W4 d =
      rho gA gB W2 b' * rho gA gB W3 c' * rho gA gB W4 d' := by
    apply mul_left_cancel (a := rho gA gB W1 a)
    simpa only [mul_assoc] using e
  have v1 := congrArg (fun σ : Perm (Fin 11) => (σ ⟨1, by norm_num⟩ : ℕ)) e2
  rw [mul_fix (r4.1 1 (by norm_num)), mul_fix (r3.1 1 (by norm_num)),
    mul_fix (r4'.1 1 (by norm_num)), mul_fix (r3'.1 1 (by norm_num)), r2.2, r2'.2] at v1
  subst v1
  have e3 : rho gA gB W3 c * rho gA gB W4 d = rho gA gB W3 c' * rho gA gB W4 d' := by
    apply mul_left_cancel (a := rho gA gB W2 b)
    simpa only [mul_assoc] using e2
  have v2 := congrArg (fun σ : Perm (Fin 11) => (σ ⟨2, by norm_num⟩ : ℕ)) e3
  rw [mul_fix (r4.1 2 (by norm_num)), mul_fix (r4'.1 2 (by norm_num)), r3.2, r3'.2] at v2
  subst v2
  have e4 := mul_left_cancel e3
  have v3 := congrArg (fun σ : Perm (Fin 11) => (σ ⟨3, by norm_num⟩ : ℕ)) e4
  rw [r4.2, r4'.2] at v3
  exact ⟨rfl, rfl, rfl, v3⟩

theorem cntM_eq (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {E : List (Perm (Fin 11))}
    (hE : ∀ g, g ∈ E ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11)))) (f : ℕ → Bool) :
    cntM R1 R2 R3 R4 f = (E.toFinset.filter fun g => f (P.code g) = true).card := by
  have e1 : cntM R1 R2 R3 R4 f = ∑ a ∈ range 11, ∑ b ∈ Ico 1 11, ∑ c ∈ Ico 2 11, ∑ d ∈ Ico 3 11,
      if f (mul 11 (mul 11 (mul 11 (genAt 11 R1 a) (genAt 11 R2 b)) (genAt 11 R3 c))
        (genAt 11 R4 d)) = true then 1 else 0 := by
    simp only [cntM, strictN_eq, rec_sum, brec_eq, sum_okIx]
  let T : Finset (ℕ × ℕ × ℕ × ℕ) := range 11 ×ˢ Ico 1 11 ×ˢ Ico 2 11 ×ˢ Ico 3 11
  have mT : ∀ t : ℕ × ℕ × ℕ × ℕ, t ∈ T ↔ t.1 < 11 ∧ (1 ≤ t.2.1 ∧ t.2.1 < 11) ∧
      (2 ≤ t.2.2.1 ∧ t.2.2.1 < 11) ∧ (3 ≤ t.2.2.2 ∧ t.2.2.2 < 11) := by
    intro t
    simp [T, Finset.mem_product, Finset.mem_Ico]
  let pK : ℕ × ℕ × ℕ × ℕ → ℕ := fun t => mul 11 (mul 11 (mul 11 (genAt 11 R1 t.1)
    (genAt 11 R2 t.2.1)) (genAt 11 R3 t.2.2.1)) (genAt 11 R4 t.2.2.2)
  let φ : ℕ × ℕ × ℕ × ℕ → Perm (Fin 11) := fun t => rho gA gB W1 t.1 * rho gA gB W2 t.2.1 *
    rho gA gB W3 t.2.2.1 * rho gA gB W4 t.2.2.2
  have hpK : ∀ t ∈ T, pK t = P.code (φ t) := by
    intro t ht
    obtain ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩⟩ := (mT t).1 ht
    simp only [pK, φ]
    rw [(rep_code ha hb hG.r1 h1 (Nat.zero_le _)).1, (rep_code ha hb hG.r2 h3 h2).1,
      (rep_code ha hb hG.r3 h5 h4).1, (rep_code ha hb hG.r4 h7 h6).1, code_mul h11,
      code_mul h11, code_mul h11]
  have e2 : (∑ a ∈ range 11, ∑ b ∈ Ico 1 11, ∑ c ∈ Ico 2 11, ∑ d ∈ Ico 3 11,
      if f (mul 11 (mul 11 (mul 11 (genAt 11 R1 a) (genAt 11 R2 b)) (genAt 11 R3 c))
        (genAt 11 R4 d)) = true then 1 else 0) = (T.filter fun t => f (pK t) = true).card := by
    simp only [T, Finset.card_filter, Finset.sum_product, pK]
  rw [e1, e2]
  refine Finset.card_bij (fun t _ => φ t) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    rw [List.mem_toFinset, hE, ← hpK t ht.1]
    obtain ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩⟩ := (mT t).1 ht.1
    have hI : InS gA gB W1 W2 W3 W4 (φ t) := by
      unfold InS
      exact ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, rfl⟩
    exact ⟨(inS_iff ha hb hG _).1 hI, ht.2⟩
  · intro t ht t' ht' e
    rw [Finset.mem_filter] at ht ht'
    obtain ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩⟩ := (mT t).1 ht.1
    obtain ⟨h1', ⟨h2', h3'⟩, ⟨h4', h5'⟩, ⟨h6', h7'⟩⟩ := (mT t').1 ht'.1
    obtain ⟨q1, q2, q3, q4⟩ := quad_inj ha hb hG h1 h2 h3 h4 h5 h6 h7 h1' h2' h3' h4' h5' h6' h7' e
    obtain ⟨a, b, c, d⟩ := t
    obtain ⟨a', b', c', d'⟩ := t'
    simp only at q1 q2 q3 q4
    rw [q1, q2, q3, q4]
  · intro g hg
    rw [Finset.mem_filter, List.mem_toFinset, hE] at hg
    have hI := (inS_iff ha hb hG g).2 hg.1
    unfold InS at hI
    obtain ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, h7, rfl⟩ := hI
    have ht : (a, b, c, d) ∈ T := (mT _).2 ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, ⟨h6, h7⟩⟩
    refine ⟨(a, b, c, d), ?_, rfl⟩
    rw [Finset.mem_filter, hpK _ ht]
    exact ⟨ht, hg.2⟩

variable {G : Subgroup (Perm (Fin 11))}

theorem class_card (S : Finset (Perm (Fin 11))) (mS : ∀ g, g ∈ S ↔ g ∈ G) (ρ : Perm (Fin 11)) :
    (S.image fun g => g * ρ * g⁻¹).card * (S.filter fun g => g * ρ = ρ * g).card = S.card := by
  rw [Finset.card_eq_sum_card_image (fun g => g * ρ * g⁻¹) S]
  refine (Finset.sum_const_nat fun x hx => ?_).symm
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hx
  have hG : h ∈ G := (mS h).1 hh
  refine Finset.card_nbij' (fun g => h⁻¹ * g) (fun c => h * c) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Finset.mem_coe, Finset.mem_filter] at hg ⊢
    refine ⟨(mS _).2 (G.mul_mem (G.inv_mem hG) ((mS g).1 hg.1)), ?_⟩
    calc h⁻¹ * g * ρ = h⁻¹ * (g * ρ * g⁻¹) * g := by group
      _ = h⁻¹ * (h * ρ * h⁻¹) * g := by rw [hg.2]
      _ = ρ * (h⁻¹ * g) := by group
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    refine ⟨(mS _).2 (G.mul_mem hG ((mS c).1 hc.1)), ?_⟩
    calc h * c * ρ * (h * c)⁻¹ = h * (c * ρ) * c⁻¹ * h⁻¹ := by group
      _ = h * (ρ * c) * c⁻¹ * h⁻¹ := by rw [hc.2]
      _ = h * ρ * h⁻¹ := by group
  · intro g _
    simp
  · intro c _
    simp

theorem conj_back {h x ρ : Perm (Fin 11)} (e : x = h * ρ * h⁻¹) : h⁻¹ * x * h = ρ := by
  rw [e]
  group

theorem div_class (S : Finset (Perm (Fin 11))) (mS : ∀ g, g ∈ S ↔ g ∈ G) {N : ℕ}
    (hN : S.card = N) (ρ : Perm (Fin 11)) :
    N / (S.filter fun g => g * ρ = ρ * g).card = (S.image fun g => g * ρ * g⁻¹).card := by
  have h1 : (1 : Perm (Fin 11)) ∈ S.filter fun g => g * ρ = ρ * g :=
    Finset.mem_filter.2 ⟨(mS 1).2 G.one_mem, by simp⟩
  refine Nat.div_eq_of_eq_mul_left (Finset.card_pos.2 ⟨1, h1⟩) ?_
  rw [← hN, class_card S mS ρ]

theorem classes_cover (S : Finset (Perm (Fin 11))) (mS : ∀ g, g ∈ S ↔ g ∈ G)
    (X : Finset (Perm (Fin 11))) (Ro : List (Perm (Fin 11)))
    (hsub : ∀ i < Ro.length, ∀ g ∈ G, g * Ro.getD i 1 * g⁻¹ ∈ X)
    (hdis : ∀ i < Ro.length, ∀ j < Ro.length, i < j → ∀ g ∈ G, g * Ro.getD i 1 * g⁻¹ ≠ Ro.getD j 1)
    (hsum : X.card = (Ro.map fun ρ => (S.image fun g => g * ρ * g⁻¹).card).sum) :
    ∀ x ∈ X, ∃ i < Ro.length, ∃ h ∈ G, x = h * Ro.getD i 1 * h⁻¹ := by
  let U := (range Ro.length).biUnion fun i => S.image fun g => g * Ro.getD i 1 * g⁻¹
  have hU : U ⊆ X := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    exact hsub i (Finset.mem_range.1 hi) g ((mS g).1 hg)
  have hdisj : ∀ i ∈ range Ro.length, ∀ j ∈ range Ro.length, i ≠ j →
      Disjoint (S.image fun g => g * Ro.getD i 1 * g⁻¹) (S.image fun g => g * Ro.getD j 1 * g⁻¹) := by
    have key : ∀ i < Ro.length, ∀ j < Ro.length, i < j → ∀ g ∈ G, ∀ k ∈ G,
        g * Ro.getD i 1 * g⁻¹ ≠ k * Ro.getD j 1 * k⁻¹ := by
      intro i hi j hj hij g hg k hk e
      refine hdis i hi j hj hij (k⁻¹ * g) (G.mul_mem (G.inv_mem hk) hg) ?_
      calc k⁻¹ * g * Ro.getD i 1 * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * Ro.getD i 1 * g⁻¹) * k := by group
        _ = k⁻¹ * (k * Ro.getD j 1 * k⁻¹) * k := by rw [e]
        _ = Ro.getD j 1 := by group
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨k, hk, e⟩ := Finset.mem_image.1 hx'
    rw [Finset.mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i hi j hj h g ((mS g).1 hg) k ((mS k).1 hk) e.symm
    · exact key j hj i hi h k ((mS k).1 hk) g ((mS g).1 hg) e
  have hcard : U.card = X.card := by
    rw [Finset.card_biUnion hdisj, hsum,
      sum_range_getD Ro (fun ρ => (S.image fun g => g * ρ * g⁻¹).card) 1]
  have hUX := Finset.eq_of_subset_of_card_le hU hcard.ge
  intro x hx
  rw [← hUX] at hx
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
  exact ⟨i, Finset.mem_range.1 hi, g, (mS g).1 hg, rfl⟩

theorem conj_pow' (h u : Perm (Fin 11)) (n : ℕ) : (h⁻¹ * u * h) ^ n = h⁻¹ * u ^ n * h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    group

theorem conj_mem {h u : Perm (Fin 11)} (hh : h ∈ G) (hu : u ∈ G) : h⁻¹ * u * h ∈ G :=
  G.mul_mem (G.mul_mem (G.inv_mem hh) hu) hh

theorem conj_mem' {h u : Perm (Fin 11)} (hh : h ∈ G) (hu : u ∈ G) : h * u * h⁻¹ ∈ G :=
  G.mul_mem (G.mul_mem hh hu) (G.inv_mem hh)

theorem e4054_spec {CA CB : ℕ} {RO : List ℕ} {CI : List (List ℕ)} {T0 : ℕ} {S0 C0 : List ℕ}
    (ha : P.code gA = CA) (hb : P.code gB = CB) {x : Perm (Fin 11)}
    (h : e4054 CA CB RO CI T0 S0 C0 (P.code x) = true) :
    (x = 1 ∨ ¬ x * gA = gA * x ∨ ¬ x * gB = gB * x) ∧
    (∀ i < RO.length, comm 11 (P.code x) (RO.getD i 0) = true →
      ¬ (x ^ 4 = 1 ∧ x ^ 2 ≠ 1) ∧ (x ≠ 1 → x * x = 1 → P.code x ∈ CI.getD i [])) ∧
    (mul 11 (P.code x) (P.code x) = T0 → P.code x ∈ S0) ∧
    (comm 11 (P.code x) T0 = true → P.code x ∈ C0) := by
  unfold e4054 at h
  rw [andB_iff, andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [orB_iff, orB_iff, notB_iff, notB_iff, code_one, beq_code h11, ← ha, ← hb, comm_code h11,
    comm_code h11] at h1
  rw [impB_iff, beq_iff, CFSG.KC.LQT.S.memL_iff] at h3
  rw [impB_iff, CFSG.KC.LQT.S.memL_iff] at h4
  rw [allN_iff, CFSG.KC.LQT.S.lenL_eq] at h2
  refine ⟨h1, fun i hi hc => ?_, h3, h4⟩
  have k := impB_iff.1 (h2 i hi) (by rwa [getK_eq'])
  rw [andB_iff, notB_iff, ord4M_code, impB_iff, invoM_code, CFSG.KC.LQT.S.memL_iff, getW_eq] at k
  exact ⟨k.1, fun h1 h2 => k.2 ⟨h1, h2⟩⟩

end CntP

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CntP GrpP in
theorem s4135_codes (gA gB : Perm (Fin 11)) (E Gs : List (Perm (Fin 11)))
    (hE : ∀ g, g ∈ E ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11)))) (hn : E.Nodup)
    {CA CB N : ℕ} {LI LF WI LG R1 R2 R3 R4 : List ℕ} {W1 W2 W3 W4 : List (List ℕ)}
    (ha : CFSG.KC.LQT.S.code gA = CA) (hb : CFSG.KC.LQT.S.code gB = CB)
    (hgs : Gs.map CFSG.KC.LQT.S.code = LG)
    (hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true)
    (hk : c4135 R1 R2 R3 R4 CA LI LF WI LG = true)
    (hm : ∀ a < 11, m4135 R1 R2 R3 R4 LI LF a = true) (hc : cntOK LI LF N = true)
    (ht : tripL LI LI = true) (hp : p4135 LI LF WI = true) :
    (((E.filter (orderIs · 2) ×ˢ E.filter (orderIs · 4)).filter
          fun q => orderIs (q.1 * q.2) 11 && orderIs (m11Word q.1 q.2) 3).length = N)
    ∧ (((E.filter (orderIs · 2)).all fun x => (E.filter (orderIs · 2)).all fun y =>
          !(x * y == y * x) || (E.filter (orderIs · 2)).all fun z =>
            !(x * z == z * x && y * z == z * y) || (x == z || x == y || x == y * z || y == z)) =
        true)
    ∧ (((E.filter (orderIs · 2)).all fun x => (E.map fun h => h * gA * h⁻¹).contains x) = true)
    ∧ ((Gs.all fun g => (E.filter (orderIs · 2)).contains g) = true) := by
  rw [codeS] at ha hb
  have hgs' : Gs.map P.code = LG := hgs
  have hG := gf_of (gA := gA) (gB := gB) hg
  unfold c4135 at hk
  rw [andB_iff, andB_iff, andB_iff, andB_iff, andB_iff] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hk
  unfold p4135 at hp
  rw [andB_iff, andB_iff] at hp
  obtain ⟨pI, pF, pW⟩ := hp
  obtain ⟨Li, rfl⟩ := exists_codes pI
  obtain ⟨Lf, rfl⟩ := exists_codes pF
  have sift_mem : ∀ σ, siftM R1 R2 R3 R4 (P.code σ) = true →
      σ ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) :=
    fun σ h => (inS_iff ha hb hG σ).1 (siftM_spec ha hb hG h)
  have hLi : ∀ x ∈ Li, x ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) :=
    fun x hx => sift_mem x ((allL_map Li _).1 k1 x hx)
  have hLf : ∀ x ∈ Lf, x ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) :=
    fun x hx => sift_mem x ((allL_map Lf _).1 k2 x hx)
  have nI : Li.Nodup := (CFSG.KC.LQT.S.distinctL_map h11 Li).1 k3
  have nF : Lf.Nodup := (CFSG.KC.LQT.S.distinctL_map h11 Lf).1 k4
  have hall : allM R1 R2 R3 R4 (fun x => CFSG.KC.Ord.andB (CFSG.KC.LQT.S.iffB (orderK x 2)
      (CFSG.KC.LQT.S.memL x (Li.map P.code))) (CFSG.KC.LQT.S.iffB (orderK x 4)
      (CFSG.KC.LQT.S.memL x (Lf.map P.code)))) = true := (allN_iff _ _).2 hm
  have mem2 : ∀ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))),
      (orderIs g 2 = true ↔ g ∈ Li) ∧ (orderIs g 4 = true ↔ g ∈ Lf) := by
    intro g hg'
    have h := allM_closure ha hb hg hall hg'
    rw [andB_iff, iffB_iff', iffB_iff', CFSG.KC.LQT.S.memL_iff, CFSG.KC.LQT.S.memL_iff,
      mem_map_code h11, mem_map_code h11, orderK_code g (by norm_num),
      orderK_code g (by norm_num)] at h
    exact h
  have pA : List.Perm (E.filter (orderIs · 2)) Li := by
    rw [List.perm_ext_iff_of_nodup (hn.filter _) nI]
    intro g
    rw [List.mem_filter, hE]
    constructor
    · rintro ⟨h1, h2⟩
      exact (mem2 g h1).1.1 h2
    · intro h
      exact ⟨hLi g h, (mem2 g (hLi g h)).1.2 h⟩
  have pB : List.Perm (E.filter (orderIs · 4)) Lf := by
    rw [List.perm_ext_iff_of_nodup (hn.filter _) nF]
    intro g
    rw [List.mem_filter, hE]
    constructor
    · rintro ⟨h1, h2⟩
      exact (mem2 g h1).2.1 h2
    · intro h
      exact ⟨hLf g h, (mem2 g (hLf g h)).2.2 h⟩
  have mA : ∀ g, g ∈ E.filter (orderIs · 2) ↔ g ∈ Li := fun g => pA.mem_iff
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc' : (Li.map fun x => (Lf.filter fun y =>
        orderIs (x * y) 11 && orderIs (m11Word x y) 3).length).sum = N := by
      rw [← cntL_code]
      exact beq_iff.1 hc
    rw [length_filter_product, ← hc', (pA.map _).sum_eq]
    congr 1
    apply List.map_congr_left
    intro x _
    exact (pB.filter _).length_eq
  · rw [List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro y hy
    rw [mA] at hx hy
    have r := (tripL_iff _ _).1 ht (P.code x) (List.mem_map_of_mem hx)
    unfold rowT at r
    rw [allL_map] at r
    have r := r y hy
    rw [orB_iff, notB_iff, comm_code h11, allL_map] at r
    rw [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    by_cases hxy : x * y = y * x
    · right
      rw [List.all_eq_true]
      intro z hz
      rw [mA] at hz
      have r := (r.resolve_left (fun h => h hxy)) z hz
      rw [orB_iff, notB_iff, andB_iff, comm_code h11, comm_code h11, orB_iff, orB_iff, orB_iff,
        beq_code h11, beq_code h11, code_mul h11, beq_code h11, beq_code h11] at r
      rw [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne,
        beq_eq_false_iff_ne]
      by_cases hz' : x * z = z * x ∧ y * z = z * y
      · right
        rcases r.resolve_left (fun h => h hz') with h | h | h | h <;> simp [h]
      · left
        rcases not_and_or.1 hz' with h | h
        · exact Or.inl h
        · exact Or.inr h
    · left
      exact hxy
  · rw [List.all_eq_true]
    intro x hx
    rw [mA] at hx
    have k := (allL_map Li _).1 k5 x hx
    rw [anyL_iff] at k
    obtain ⟨w, hw, k⟩ := k
    rw [andB_iff, andB_iff] at k
    obtain ⟨-, ks, kc⟩ := k
    obtain ⟨g, hgw⟩ := exists_of_permK (n := 11) ((allL_iff _ _).1 pW w hw)
    rw [← hgw] at ks kc
    rw [← ha, conj_code h11, beq_code h11] at kc
    simpa using List.mem_map.2 ⟨g, (hE g).2 (sift_mem g ks), kc⟩
  · rw [List.all_eq_true]
    intro g hg'
    have k := (allL_iff _ _).1 k6 (P.code g) (by rw [← hgs']; exact List.mem_map_of_mem hg')
    rw [andB_iff, orderK_code g (by norm_num)] at k
    have hm' : g ∈ E.filter (orderIs · 2) := List.mem_filter.2 ⟨(hE g).2 (sift_mem g k.1), k.2⟩
    simpa using hm'

open CFSG.QuasithinUnique.Fin253 in
theorem CntP.lpow_eq (u : Perm (Fin 11)) : ∀ n, lpow m11mul 1 u n = u ^ n
  | 0 => rfl
  | n + 1 => by
    change m11mul u (lpow m11mul 1 u n) = u ^ (n + 1)
    rw [CntP.lpow_eq u n, m11mul, CFSG.Sporadic.Schreier.tab_eq, pow_succ']

open CFSG.QuasithinUnique.Fin253 in
theorem CntP.lpow_mul (u : Perm (Fin 11)) :
    ∀ n, lpow (fun a b : Perm (Fin 11) => a * b) 1 u n = u ^ n
  | 0 => rfl
  | n + 1 => by
    change u * lpow (fun a b : Perm (Fin 11) => a * b) 1 u n = u ^ (n + 1)
    rw [CntP.lpow_mul u n, pow_succ']

open CFSG.QuasithinUnique.Fin253 in
theorem CntP.m11mul_eq : m11mul = fun a b => a * b := by
  funext a b
  exact CFSG.Sporadic.Schreier.tab_eq _

open CFSG.QuasithinUnique.Fin253 in
theorem CntP.m11inv_eq : m11inv = fun a => a⁻¹ := by
  funext a
  exact CFSG.Sporadic.Schreier.tab_eq _

open CFSG.QuasithinUnique.Fin253 CntP GrpP in
theorem s4054_codes (gA gB : Perm (Fin 11)) (E : List (Perm (Fin 11)))
    (hE : ∀ g, g ∈ E ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11)))) (hn : E.Nodup)
    {CA CB T0 : ℕ} {RO S0 C0 R1 R2 R3 R4 : List ℕ} {CI W1 W2 W3 W4 : List (List ℕ)}
    (ha : CFSG.KC.LQT.S.code gA = CA) (hb : CFSG.KC.LQT.S.code gB = CB)
    (hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true)
    (hk : c4054 R1 R2 R3 R4 RO CI T0 S0 C0 = true)
    (hm : ∀ a < 11, m4054 R1 R2 R3 R4 CA CB RO CI T0 S0 C0 a = true)
    (hp : p4054 RO T0 S0 C0 = true) :
    let I := E.filter fun t => decide (t ≠ 1 ∧ m11mul t t = 1)
    let O := E.filter fun u => decide (lpow m11mul 1 u 4 = 1 ∧ lpow m11mul 1 u 2 ≠ 1)
    (CenterOK m11mul 1 E)
    ∧ (OddOK m11mul 1 495 E I O)
    ∧ (QuatAll m11mul 1 E I)
    ∧ (CoreAll m11mul 1 m11inv E I) := by
  simp only [CenterOK, OddOK, QuatAll, CoreAll, QuatOK, CoreOK, lpow_eq, lpow_mul, m11mul_eq,
    m11inv_eq]
  rw [codeS] at ha hb
  set G := Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) with hGdef
  have hG := gf_of (gA := gA) (gB := gB) hg
  simp only [c4054, CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, andB_iff] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, -, k12, k13, k14, k15, k16, -⟩ := hk
  unfold p4054 at hp
  rw [andB_iff, andB_iff, andB_iff] at hp
  obtain ⟨pT, pR, pS, pC⟩ := hp
  obtain ⟨τ, rfl⟩ := exists_of_permK (n := 11) pT
  obtain ⟨Ro, rfl⟩ := exists_codes pR
  obtain ⟨Sl, rfl⟩ := exists_codes pS
  obtain ⟨Cl, rfl⟩ := exists_codes pC
  have mG : ∀ g, g ∈ E.toFinset ↔ g ∈ G := fun g => by rw [List.mem_toFinset, hE]
  have hcnt := fun f => cntM_eq ha hb hG hE f
  have hcard : E.toFinset.card = 7920 := by
    have h := beq_iff.1 k1
    rw [hcnt] at h
    simpa using h
  have sift_mem : ∀ σ, siftM R1 R2 R3 R4 (P.code σ) = true → σ ∈ G :=
    fun σ h => (inS_iff ha hb hG σ).1 (siftM_spec ha hb hG h)
  have hall : allM R1 R2 R3 R4 (e4054 CA CB (Ro.map P.code) CI (P.code τ) (Sl.map P.code)
      (Cl.map P.code)) = true := (allN_iff _ _).2 hm
  have ev := fun (x : Perm (Fin 11)) (hx : x ∈ G) =>
    e4054_spec (gA := gA) (gB := gB) ha hb (allM_closure ha hb hg hall hx)
  have hgA : gA ∈ E := (hE gA).2 (Subgroup.subset_closure (by simp))
  have hgB : gB ∈ E := (hE gB).2 (Subgroup.subset_closure (by simp))
  have hτ : τ ∈ G := sift_mem τ k7
  rw [invoM_code] at k8
  have hdiv : ∀ ρ : Perm (Fin 11), Nat.div 7920 (cntM R1 R2 R3 R4 fun x => comm 11 x (P.code ρ)) =
      (E.toFinset.image fun g => g * ρ * g⁻¹).card := by
    intro ρ
    rw [hcnt, ← div_class E.toFinset mG hcard ρ]
    have hf : (E.toFinset.filter fun g => comm 11 (P.code g) (P.code ρ) = true) =
        E.toFinset.filter fun g => g * ρ = ρ * g :=
      Finset.filter_congr fun g _ => comm_code h11 g ρ
    rw [hf]
    rfl
  have hinv : ∀ t ∈ G, t ≠ 1 → t * t = 1 → ∃ h ∈ G, t = h * τ * h⁻¹ := by
    have hc := classes_cover E.toFinset mG (E.toFinset.filter fun g => invoM (P.code g) = true) [τ]
      (fun i hi g hg => by
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp only [List.getD_cons_zero]
        rw [Finset.mem_filter, mG, invoM_code]
        refine ⟨conj_mem' hg hτ, fun e => k8.1 ?_, ?_⟩
        · calc τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
            _ = 1 := by rw [e]; group
        · calc g * τ * g⁻¹ * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ := by group
            _ = 1 := by rw [k8.2]; group)
      (fun i hi j hj hij => by simp at hi hj; omega)
      (by
        have k9' := beq_iff.1 k9
        rw [hdiv τ, hcnt] at k9'
        rw [k9']
        simp)
    intro t ht h1 h2
    obtain ⟨i, hi, h, hh, e⟩ := hc t (by rw [Finset.mem_filter, mG, invoM_code]; exact ⟨ht, h1, h2⟩)
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    exact ⟨h, hh, e⟩
  have hRo : ∀ i < Ro.length, Ro.getD i 1 ∈ G ∧ Ro.getD i 1 ≠ 1 ∧ Ro.getD i 1 ^ 495 = 1 := by
    intro i hi
    have k := (allL_map Ro _).1 k2 _ (getD_mem Ro 1 hi)
    rw [andB_iff, oddK_code] at k
    exact ⟨sift_mem _ k.1, k.2⟩
  have hodd : ∀ x ∈ G, x ≠ 1 → x ^ 495 = 1 →
      ∃ i < Ro.length, ∃ h ∈ G, x = h * Ro.getD i 1 * h⁻¹ := by
    have hc := classes_cover E.toFinset mG (E.toFinset.filter fun g => oddK (P.code g) = true) Ro
      (fun i hi g hg => by
        obtain ⟨-, h1, h2⟩ := hRo i hi
        rw [Finset.mem_filter, mG, oddK_code]
        refine ⟨conj_mem' hg (hRo i hi).1, fun e => h1 ?_, ?_⟩
        · calc Ro.getD i 1 = g⁻¹ * (g * Ro.getD i 1 * g⁻¹) * g := by group
            _ = 1 := by rw [e]; group
        · rw [conj_pow, h2]
          group)
      (fun i hi j hj hij g hgG e => by
        rw [allN_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at k3
        have k := (allN_iff _ _).1 (k3 i hi) j hj
        rw [impB_iff] at k
        have k := allM_closure ha hb hg (k (blt_iff.2 hij)) hgG
        rw [notB_iff, getK_eq', getK_eq', getD_code Ro hi, getD_code Ro hj, conj_code h11,
          beq_code h11] at k
        exact k e)
      (by
        have k4' := beq_iff.1 k4
        rw [hcnt] at k4'
        rw [k4', rec_sum_list, List.map_map]
        exact congrArg List.sum (List.map_congr_left fun ρ _ => by
          rw [Function.comp_apply]
          exact hdiv ρ))
    intro x hx h1 h2
    exact hc x (by rw [Finset.mem_filter, mG, oddK_code]; exact ⟨hx, h1, h2⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases (ev z ((hE z).1 hz)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨gA, hgA, h⟩
    · exact Or.inr ⟨gB, hgB, h⟩
  · intro x hx h1 h2
    obtain ⟨i, hi, h, hh, e⟩ := hodd x ((hE x).1 hx) h1 h2
    have hρ : ∀ u ∈ G, u * x = x * u → h⁻¹ * u * h ∈ G ∧
        comm 11 (P.code (h⁻¹ * u * h)) ((Ro.map P.code).getD i 0) = true := by
      intro u hu hux
      refine ⟨conj_mem hh hu, ?_⟩
      rw [getD_code Ro hi, comm_code h11, ← conj_back e]
      calc h⁻¹ * u * h * (h⁻¹ * x * h) = h⁻¹ * (u * x) * h := by group
        _ = h⁻¹ * (x * u) * h := by rw [hux]
        _ = h⁻¹ * x * h * (h⁻¹ * u * h) := by group
    refine ⟨fun u hu hux => ?_, fun t ht s hs hts hcomm => ?_⟩
    · rw [List.mem_filter, decide_eq_true_eq] at hu
      obtain ⟨hu1, hu2⟩ := hρ u ((hE u).1 hu.1) hux
      refine ((ev _ hu1).2.1 i (by simpa using hi) hu2).1 ⟨?_, ?_⟩
      · rw [conj_pow', hu.2.1]
        group
      · intro e'
        apply hu.2.2
        calc u ^ 2 = h * (h⁻¹ * u * h) ^ 2 * h⁻¹ := by rw [conj_pow']; group
          _ = 1 := by rw [e']; group
    · rw [List.mem_filter, List.mem_filter, decide_eq_true_eq, decide_eq_true_eq] at ht hs
      obtain ⟨⟨htE, ht1, ht2⟩, htx⟩ := ht
      obtain ⟨⟨hsE, hs1, hs2⟩, hsx⟩ := hs
      obtain ⟨tG, tc⟩ := hρ t ((hE t).1 htE) htx
      obtain ⟨sG, sc⟩ := hρ s ((hE s).1 hsE) hsx
      have hinvol : ∀ v : Perm (Fin 11), v ≠ 1 → v * v = 1 →
          h⁻¹ * v * h ≠ 1 ∧ h⁻¹ * v * h * (h⁻¹ * v * h) = 1 := by
        intro v hv1 hv2
        refine ⟨fun e' => hv1 ?_, ?_⟩
        · calc v = h * (h⁻¹ * v * h) * h⁻¹ := by group
            _ = 1 := by rw [e']; group
        · calc h⁻¹ * v * h * (h⁻¹ * v * h) = h⁻¹ * (v * v) * h := by group
            _ = 1 := by rw [hv2]; group
      have hi' : i < (Ro.map P.code).length := by simpa using hi
      have mt := ((ev _ tG).2.1 i hi' tc).2 (hinvol t ht1 ht2).1 (hinvol t ht1 ht2).2
      have ms := ((ev _ sG).2.1 i hi' sc).2 (hinvol s hs1 hs2).1 (hinvol s hs1 hs2).2
      have hlen : i < CI.length := by
        rw [← rec_len, ← beq_iff.1 k5, CFSG.KC.LQT.S.lenL_eq, List.length_map]
        exact hi
      have kl := (rec_all _ CI).1 k6 _ (getD_mem CI [] hlen)
      rw [allL_iff] at kl
      have kl := kl _ mt
      rw [allL_iff] at kl
      have kl := kl _ ms
      rw [impB_iff, notB_iff, notB_iff, beq_code h11, comm_code h11] at kl
      refine kl (fun e' => hts ?_) ?_
      · calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
          _ = h * (h⁻¹ * s * h) * h⁻¹ := by rw [e']
          _ = s := by group
      · calc h⁻¹ * t * h * (h⁻¹ * s * h) = h⁻¹ * (t * s) * h := by group
          _ = h⁻¹ * (s * t) * h := by rw [hcomm]
          _ = h⁻¹ * s * h * (h⁻¹ * t * h) := by group
  · intro t ht
    rw [List.mem_filter, decide_eq_true_eq] at ht
    obtain ⟨htE, ht1, ht2⟩ := ht
    obtain ⟨h, hh, e⟩ := hinv t ((hE t).1 htE) ht1 ht2
    have hS : ∀ y ∈ Sl, y ∈ G ∧ y * y = τ := by
      intro y hy
      have k := (allL_map Sl _).1 k10 y hy
      rw [andB_iff, code_mul h11, beq_code h11] at k
      exact ⟨sift_mem y k.1, k.2⟩
    have hroot : ∀ y, y ∈ E → y * y = t → h⁻¹ * y * h ∈ Sl := by
      intro y hy hyy
      have hy' := conj_mem hh ((hE y).1 hy)
      have k := (ev _ hy').2.2.1
      rw [code_mul h11, mem_map_code h11] at k
      refine k (congrArg P.code ?_)
      calc h⁻¹ * y * h * (h⁻¹ * y * h) = h⁻¹ * (y * y) * h := by group
        _ = τ := by rw [hyy, e]; group
    have hconjS : ∀ y ∈ Sl, h * y * h⁻¹ ∈ E.filter fun y => decide (y * y = t) := by
      intro y hy
      rw [List.mem_filter, decide_eq_true_eq, hE]
      refine ⟨conj_mem' hh (hS y hy).1, ?_⟩
      rw [e]
      calc h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
        _ = h * τ * h⁻¹ := by rw [(hS y hy).2]
    have hlenS : 3 ≤ Sl.length := by
      have k := Nat.le_of_ble_eq_true k13
      rwa [CFSG.KC.LQT.S.lenL_eq, List.length_map] at k
    have nS : Sl.Nodup := by
      have k : CFSG.KC.LQT.S.distinctL (Sl.map P.code) = true := (andB_iff.1 (andB_iff.1 k12).2).2
      exact (CFSG.KC.LQT.S.distinctL_map h11 Sl).1 k
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨y, hy⟩ : ∃ y, y ∈ Sl := List.exists_mem_of_length_pos (by omega)
      exact List.ne_nil_of_mem (hconjS y hy)
    · intro y hy y' hy'
      rw [List.mem_filter, decide_eq_true_eq] at hy hy'
      have m1 := hroot y hy.1 hy.2
      have m2 := hroot y' hy'.1 hy'.2
      have k := (allL_map Sl _).1 k14 _ m1
      rw [allL_map] at k
      have k := k _ m2
      rw [letB_eq, code_mul h11, orB_iff, orB_iff, code_one, beq_code h11, beq_code h11, code_mul h11,
        beq_code h11] at k
      have ep : h⁻¹ * y * h * (h⁻¹ * y' * h) = h⁻¹ * (y * y') * h := by group
      rw [ep] at k
      rcases k with k | k | k
      · left
        calc y * y' = h * (h⁻¹ * (y * y') * h) * h⁻¹ := by group
          _ = 1 := by rw [k]; group
      · right
        left
        rw [e]
        calc y * y' = h * (h⁻¹ * (y * y') * h) * h⁻¹ := by group
          _ = h * τ * h⁻¹ := by rw [k]
      · right
        right
        rw [e]
        calc y * y' * (y * y') = h * (h⁻¹ * (y * y') * h * (h⁻¹ * (y * y') * h)) * h⁻¹ := by group
          _ = h * τ * h⁻¹ := by rw [k]
    · rw [List.nodup_cons, List.nodup_cons]
      refine ⟨?_, ?_, hn.filter _⟩
      · rw [List.mem_cons, List.mem_filter, decide_eq_true_eq]
        rintro (h' | ⟨-, h'⟩)
        · exact ht1 h'.symm
        · exact ht1 (by rw [← h']; simp)
      · rw [List.mem_filter, decide_eq_true_eq]
        rintro ⟨-, h'⟩
        exact ht1 (by rw [← h', ht2])
    · have hsub : (Sl.map fun y => h * y * h⁻¹).Nodup :=
        nS.map fun a b e' => by simpa using e'
      have hle := (hsub.subperm fun z hz => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact hconjS y hy).length_le
      rw [List.length_map] at hle
      simp only [List.length_cons]
      omega
  · intro t ht c hc
    rw [List.mem_filter, decide_eq_true_eq] at ht hc
    obtain ⟨htE, ht1, ht2⟩ := ht
    obtain ⟨h, hh, e⟩ := hinv t ((hE t).1 htE) ht1 ht2
    have hc' := conj_mem hh ((hE c).1 hc.1)
    have hcτ : h⁻¹ * c * h * τ = τ * (h⁻¹ * c * h) := by
      rw [← conj_back e]
      calc h⁻¹ * c * h * (h⁻¹ * t * h) = h⁻¹ * (c * t) * h := by group
        _ = h⁻¹ * (t * c) * h := by rw [hc.2]
        _ = h⁻¹ * t * h * (h⁻¹ * c * h) := by group
    have mc := (ev _ hc').2.2.2 ((comm_code h11 _ _).2 hcτ)
    rw [mem_map_code h11] at mc
    have k := (allL_map Cl _).1 k16 _ mc
    rw [orB_iff, orB_iff, orB_iff, code_one, beq_code h11, beq_code h11, code_mul h11, beq_code h11,
      anyL_map] at k
    rcases k with (k | k | k) | ⟨w, hw, k⟩
    · left
      left
      calc c = h * (h⁻¹ * c * h) * h⁻¹ := by group
        _ = 1 := by rw [k]; group
    · left
      right
      left
      rw [e]
      calc c = h * (h⁻¹ * c * h) * h⁻¹ := by group
        _ = h * τ * h⁻¹ := by rw [k]
    · left
      right
      right
      rw [e]
      calc c * c = h * (h⁻¹ * c * h * (h⁻¹ * c * h)) * h⁻¹ := by group
        _ = h * τ * h⁻¹ := by rw [k]
    · right
      have kw := (allL_map Cl _).1 k15 w hw
      rw [andB_iff, comm_code h11] at kw
      have hwG := sift_mem w kw.1
      refine ⟨h * w * h⁻¹, ?_, ?_⟩
      · rw [List.mem_filter, decide_eq_true_eq, hE]
        refine ⟨conj_mem' hh hwG, ?_⟩
        rw [e]
        calc h * w * h⁻¹ * (h * τ * h⁻¹) = h * (w * τ) * h⁻¹ := by group
          _ = h * (τ * w) * h⁻¹ := by rw [kw.2]
          _ = h * τ * h⁻¹ * (h * w * h⁻¹) := by group
      · simp only [code_inv h11, code_mul h11] at k
        rw [notB_iff, pwM16, beq_code h11] at k
        intro e'
        apply k
        have ex : (h⁻¹ * c * h)⁻¹ * (w * (h⁻¹ * c * h) * w⁻¹) =
            h⁻¹ * (c⁻¹ * (h * w * h⁻¹ * c * (h * w * h⁻¹)⁻¹)) * h := by group
        rw [ex, conj_pow', e']
        group

end CFSG.KC.LQT.M

end
