module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
import CFSG.Certificates.Kernel.LocalQTLatKSound
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import Certificates.Data.Kernel.LocalQT.M11

public section

namespace CFSG.KC.LQT.M

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

namespace GrpP

theorem h11 : (11 : ℕ) ≤ 32 := by norm_num

theorem invS (σ : Perm (Fin 11)) (x : Fin 11) : σ⁻¹ (σ x) = x := σ.symm_apply_apply x

theorem codeS (σ : Perm (Fin 11)) : CFSG.KC.LQT.S.code σ = P.code σ := rfl

theorem img_fin (σ : Perm (Fin 11)) {i : ℕ} (hi : i < 11) : img (P.code σ) i = σ ⟨i, hi⟩ :=
  img_code h11 σ ⟨i, hi⟩

theorem evalW_mem' {G : Type*} [Group G] (gs : List G) (w : List ℕ) :
    evalW gs w ∈ Subgroup.closure {g | g ∈ gs} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    rcases Nat.lt_or_ge i gs.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]
      exact Subgroup.subset_closure (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]
      exact Subgroup.one_mem _

theorem repsOK_spec {G : List ℕ} {k : ℕ} {R : List ℕ} {W : List (List ℕ)} (h : repsOK G k R W = true)
    {j : ℕ} (hj : j < 11) (hk : k ≤ j) :
    (∀ i < k, img (genAt 11 R j) i = i) ∧ img (genAt 11 R j) k = j ∧
      genAt 11 R j = evalWK 11 G (getW W j) := by
  unfold repsOK at h
  rw [allN_iff] at h
  have h1 := (impB_iff.1 (h j hj)) (Nat.ble_eq.mpr hk)
  rw [letB_eq, andB_iff, andB_iff, andB_iff, allN_iff] at h1
  obtain ⟨-, h2, h3, h4⟩ := h1
  exact ⟨fun i hi => beq_iff.1 (h2 i hi), beq_iff.1 h3, beq_iff.1 h4⟩

noncomputable def rho (gA gB : Perm (Fin 11)) (W : List (List ℕ)) (j : ℕ) : Perm (Fin 11) :=
  evalW [gA, gB] (getW W j)

variable {gA gB : Perm (Fin 11)} {CA CB : ℕ} {R1 R2 R3 R4 : List ℕ} {W1 W2 W3 W4 : List (List ℕ)}

theorem rep_code (ha : P.code gA = CA) (hb : P.code gB = CB) {k : ℕ} {R : List ℕ}
    {W : List (List ℕ)} (h : repsOK [CA, CB] k R W = true) {j : ℕ} (hj : j < 11) (hk : k ≤ j) :
    genAt 11 R j = P.code (rho gA gB W j) ∧ (∀ i < k, img (genAt 11 R j) i = i) ∧
      img (genAt 11 R j) k = j := by
  obtain ⟨h1, h2, h3⟩ := repsOK_spec h hj hk
  refine ⟨?_, h1, h2⟩
  rw [h3, ← ha, ← hb]
  exact CFSG.KC.LQT.LK.evalWK_code h11 [gA, gB] (getW W j)

theorem rho_mem (W : List (List ℕ)) (j : ℕ) :
    rho gA gB W j ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) := by
  have := evalW_mem' [gA, gB] (getW W j)
  have e : {g | g ∈ [gA, gB]} = ({gA, gB} : Set (Perm (Fin 11))) := by
    ext g
    simp
  rwa [e] at this

def InS (gA gB : Perm (Fin 11)) (W1 W2 W3 W4 : List (List ℕ)) (g : Perm (Fin 11)) : Prop :=
  ∃ a b c d, a < 11 ∧ 1 ≤ b ∧ b < 11 ∧ 2 ≤ c ∧ c < 11 ∧ 3 ≤ d ∧ d < 11 ∧
    g = rho gA gB W1 a * rho gA gB W2 b * rho gA gB W3 c * rho gA gB W4 d

structure GF (gA gB : Perm (Fin 11)) (CA CB : ℕ) (R1 R2 R3 R4 : List ℕ)
    (W1 W2 W3 W4 : List (List ℕ)) : Prop where
  r1 : repsOK [CA, CB] 0 R1 W1 = true
  r2 : repsOK [CA, CB] 1 R2 W2 = true
  r3 : repsOK [CA, CB] 2 R3 W3 = true
  r4 : repsOK [CA, CB] 3 R4 W4 = true
  one : siftM R1 R2 R3 R4 (one 11) = true
  clos : allM R1 R2 R3 R4 (fun s =>
    CFSG.KC.Ord.andB (siftM R1 R2 R3 R4 (mul 11 s CA)) (siftM R1 R2 R3 R4 (mul 11 s CB))) = true

theorem gf_of (h : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true) :
    GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4 := by
  unfold grpM at h
  rw [andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, andB_iff, andB_iff] at h
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h7, h8⟩

theorem allM_spec {f : ℕ → Bool} (h : allM R1 R2 R3 R4 f = true) {a b c d : ℕ} (ha : a < 11)
    (hb1 : 1 ≤ b) (hb : b < 11) (hc2 : 2 ≤ c) (hc : c < 11) (hd3 : 3 ≤ d) (hd : d < 11) :
    f (mul 11 (mul 11 (mul 11 (genAt 11 R1 a) (genAt 11 R2 b)) (genAt 11 R3 c)) (genAt 11 R4 d)) =
      true := by
  unfold allM at h
  rw [allN_iff] at h
  have h1 := h a ha
  unfold allMa at h1
  rw [letB_eq, allN_iff] at h1
  have h2 := (impB_iff.1 (h1 b hb)) (Nat.ble_eq.mpr hb1)
  rw [letB_eq, allN_iff] at h2
  have h3 := (impB_iff.1 (h2 c hc)) (Nat.ble_eq.mpr hc2)
  rw [letB_eq, allN_iff] at h3
  exact (impB_iff.1 (h3 d hd)) (Nat.ble_eq.mpr hd3)

theorem allM_inS (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {f : ℕ → Bool} (h : allM R1 R2 R3 R4 f = true)
    {g : Perm (Fin 11)} (hg : InS gA gB W1 W2 W3 W4 g) : f (P.code g) = true := by
  obtain ⟨a, b, c, d, ha', hb1, hb', hc2, hc', hd3, hd', rfl⟩ := hg
  have := allM_spec h ha' hb1 hb' hc2 hc' hd3 hd'
  rwa [(rep_code ha hb hG.r1 ha' (Nat.zero_le _)).1, (rep_code ha hb hG.r2 hb' hb1).1,
    (rep_code ha hb hG.r3 hc' hc2).1, (rep_code ha hb hG.r4 hd' hd3).1, code_mul h11,
    code_mul h11, code_mul h11] at this

theorem fin_val_ne {σ : Perm (Fin 11)} {i j : ℕ} (hi : i < 11) (hj : j < 11) (hij : i ≠ j) :
    (σ ⟨i, hi⟩ : ℕ) ≠ σ ⟨j, hj⟩ := fun e => hij (by
  have := σ.injective (Fin.ext e)
  simpa using this)

theorem siftM_spec (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {g : Perm (Fin 11)}
    (h : siftM R1 R2 R3 R4 (P.code g) = true) : InS gA gB W1 W2 W3 W4 g := by
  unfold siftM at h
  rw [letB_eq, letB_eq, letB_eq] at h
  have hga : img (P.code g) 0 < 11 := by rw [img_fin g (by norm_num)]; exact (g _).isLt
  generalize hav : img (P.code g) 0 = a at h hga
  obtain ⟨e1, -, f1⟩ := rep_code ha hb hG.r1 hga (Nat.zero_le _)
  rw [e1, code_inv h11, code_mul h11] at h
  set h1 := (rho gA gB W1 a)⁻¹ * g with hh1
  have h10 : ∀ (h0 : 0 < 11), (h1 ⟨0, h0⟩ : ℕ) = 0 := by
    intro h0
    have g0 : (g ⟨0, h0⟩ : ℕ) = a := by rw [← hav, img_fin g h0]
    have r0 : (rho gA gB W1 a ⟨0, h0⟩ : ℕ) = a := by rw [← img_fin _ h0, ← e1]; exact f1
    have : g ⟨0, h0⟩ = rho gA gB W1 a ⟨0, h0⟩ := Fin.ext (g0.trans r0.symm)
    rw [hh1, Perm.mul_apply, this, invS]
  have hgb : img (P.code h1) 1 < 11 := by rw [img_fin h1 (by norm_num)]; exact (h1 _).isLt
  have hgb1 : 1 ≤ img (P.code h1) 1 := by
    rw [img_fin h1 (by norm_num)]
    have := fin_val_ne (σ := h1) (i := 1) (j := 0) (by norm_num) (by norm_num) (by norm_num)
    rw [h10 (by norm_num)] at this
    omega
  generalize hbv : img (P.code h1) 1 = b at h hgb hgb1
  obtain ⟨e2, z2, f2⟩ := rep_code ha hb hG.r2 hgb hgb1
  rw [e2, code_inv h11, code_mul h11] at h
  set h2 := (rho gA gB W2 b)⁻¹ * h1 with hh2
  have r20 : ∀ (h0 : 0 < 11), rho gA gB W2 b ⟨0, h0⟩ = ⟨0, h0⟩ := fun h0 => Fin.ext (by
    rw [← img_fin _ h0, ← e2]; exact z2 0 (by norm_num))
  have h2fix : ∀ i (hi : i < 2), (h2 ⟨i, by omega⟩ : ℕ) = i := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · have e0 : h1 ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := Fin.ext (h10 (by norm_num))
      rw [hh2, Perm.mul_apply, e0, ← r20 (by norm_num), invS]
    · have b1 : h1 ⟨1, by norm_num⟩ = rho gA gB W2 b ⟨1, by norm_num⟩ := Fin.ext (by
        rw [← img_fin (rho gA gB W2 b) (by norm_num), ← e2, f2, ← hbv, img_fin h1 (by norm_num)])
      rw [hh2, Perm.mul_apply, b1, invS]
  have hgc : img (P.code h2) 2 < 11 := by rw [img_fin h2 (by norm_num)]; exact (h2 _).isLt
  have hgc2 : 2 ≤ img (P.code h2) 2 := by
    rw [img_fin h2 (by norm_num)]
    have a0 := fin_val_ne (σ := h2) (i := 2) (j := 0) (by norm_num) (by norm_num) (by norm_num)
    have a1 := fin_val_ne (σ := h2) (i := 2) (j := 1) (by norm_num) (by norm_num) (by norm_num)
    rw [h2fix 0 (by norm_num)] at a0
    rw [h2fix 1 (by norm_num)] at a1
    omega
  generalize hcv : img (P.code h2) 2 = c at h hgc hgc2
  obtain ⟨e3, z3, f3⟩ := rep_code ha hb hG.r3 hgc hgc2
  rw [e3, code_inv h11, code_mul h11] at h
  set h3 := (rho gA gB W3 c)⁻¹ * h2 with hh3
  have h3fix : ∀ i (hi : i < 3), (h3 ⟨i, by omega⟩ : ℕ) = i := by
    intro i hi
    rcases (by omega : i < 2 ∨ i = 2) with hi2 | rfl
    · have r3 : rho gA gB W3 c ⟨i, by omega⟩ = h2 ⟨i, by omega⟩ := Fin.ext (by
        rw [← img_fin (rho gA gB W3 c) (by omega), ← e3, z3 i (by omega), h2fix i hi2])
      rw [hh3, Perm.mul_apply, ← r3, invS]
    · have c2 : h2 ⟨2, by norm_num⟩ = rho gA gB W3 c ⟨2, by norm_num⟩ := Fin.ext (by
        rw [← img_fin (rho gA gB W3 c) (by norm_num), ← e3, f3, ← hcv, img_fin h2 (by norm_num)])
      rw [hh3, Perm.mul_apply, c2, invS]
  have hgd : img (P.code h3) 3 < 11 := by rw [img_fin h3 (by norm_num)]; exact (h3 _).isLt
  have hgd3 : 3 ≤ img (P.code h3) 3 := by
    rw [img_fin h3 (by norm_num)]
    have a0 := fin_val_ne (σ := h3) (i := 3) (j := 0) (by norm_num) (by norm_num) (by norm_num)
    have a1 := fin_val_ne (σ := h3) (i := 3) (j := 1) (by norm_num) (by norm_num) (by norm_num)
    have a2 := fin_val_ne (σ := h3) (i := 3) (j := 2) (by norm_num) (by norm_num) (by norm_num)
    rw [h3fix 0 (by norm_num)] at a0
    rw [h3fix 1 (by norm_num)] at a1
    rw [h3fix 2 (by norm_num)] at a2
    omega
  generalize hdv : img (P.code h3) 3 = d at h hgd hgd3
  obtain ⟨e4, -, -⟩ := rep_code ha hb hG.r4 hgd hgd3
  rw [e4, code_inv h11, code_mul h11, code_one, beq_code h11] at h
  have hgd' : h3 = rho gA gB W4 d := by
    have := congrArg (rho gA gB W4 d * ·) h
    simpa using this
  refine ⟨a, b, c, d, hga, hgb1, hgb, hgc2, hgc, hgd3, hgd, ?_⟩
  rw [← hgd', hh3, hh2, hh1]
  group

theorem pow_mem_S (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {x y : Perm (Fin 11)}
    (hy : y = gA ∨ y = gB) : ∀ k, InS gA gB W1 W2 W3 W4 x → InS gA gB W1 W2 W3 W4 (x * y ^ k)
  | 0, hx => by simpa using hx
  | k + 1, hx => by
    have ih := pow_mem_S ha hb hG hy k hx
    have h := allM_inS ha hb hG hG.clos ih
    rw [andB_iff] at h
    rw [pow_succ, ← mul_assoc]
    rcases hy with rfl | rfl
    · rw [← ha, code_mul h11] at h
      exact siftM_spec ha hb hG h.1
    · rw [← hb, code_mul h11] at h
      exact siftM_spec ha hb hG h.2

theorem inS_iff (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) (g : Perm (Fin 11)) :
    InS gA gB W1 W2 W3 W4 g ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))) := by
  constructor
  · rintro ⟨a, b, c, d, -, -, -, -, -, -, -, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (rho_mem _ _) (rho_mem _ _))
      (rho_mem _ _)) (rho_mem _ _)
  · intro hg
    refine Subgroup.closure_induction_right (p := fun x _ => InS gA gB W1 W2 W3 W4 x) ?_
      (fun x _ y hy hx => ?_) (fun x _ y hy hx => ?_) hg
    · refine siftM_spec ha hb hG ?_
      rw [← code_one]
      exact hG.one
    · have hy' : y = gA ∨ y = gB := by simpa using hy
      simpa using pow_mem_S ha hb hG hy' 1 hx
    · have hy' : y = gA ∨ y = gB := by simpa using hy
      have e : y⁻¹ = y ^ (orderOf y - 1) := by
        rw [eq_comm, ← mul_left_cancel_iff (a := y), mul_inv_cancel, ← pow_succ',
          Nat.sub_add_cancel (orderOf_pos y), pow_orderOf_eq_one]
      rw [e]
      exact pow_mem_S ha hb hG hy' _ hx

theorem allM_closure (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true) {f : ℕ → Bool}
    (h : allM R1 R2 R3 R4 f = true) {g : Perm (Fin 11)}
    (hg' : g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11)))) : f (P.code g) = true :=
  have hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4 := gf_of hg
  allM_inS ha hb hG h ((inS_iff ha hb hG g).2 hg')

theorem mem_codes {L : List (Perm (Fin 11))} {x : Perm (Fin 11)} :
    P.code x ∈ L.map P.code ↔ x ∈ L := by
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    rwa [code_inj h11 e] at hy
  · exact fun h => List.mem_map.2 ⟨x, h, rfl⟩

theorem img_lt32 (s i : ℕ) : img s i < 32 := by
  unfold img
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem img_mul (s t : ℕ) {i : ℕ} (hi : i < 11) : img (mul 11 s t) i = img s (img t i) := by
  unfold mul
  rw [img_eq, ofFn_eq, E_digit (fun j _ => img_lt32 _ _) hi]

theorem img_one' {i : ℕ} (hi : i < 11) : img (one 11) i = i := by
  unfold one
  rw [img_eq, ofFn_eq, E_digit (fun j hj => by omega) hi]

theorem img_code_ge (σ : Perm (Fin 11)) {v : ℕ} (hv : 11 ≤ v) : img (P.code σ) v = 0 := by
  rw [img_eq, code_eq, Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (E_lt (vals_lt h11 σ))
    (Nat.pow_le_pow_right (by norm_num) hv)), Nat.zero_mod]

theorem mul_congr_r (s : ℕ) {x x' : ℕ} (h : ∀ i < 11, img x i = img x' i) :
    mul 11 s x = mul 11 s x' := by
  unfold mul
  rw [ofFn_eq, ofFn_eq]
  exact E_congr fun i hi => by rw [h i hi]

theorem siftM_congr {x x' : ℕ} (h : ∀ i < 11, img x i = img x' i) :
    siftM R1 R2 R3 R4 x = siftM R1 R2 R3 R4 x' := by
  unfold siftM
  rw [h 0 (by norm_num), mul_congr_r _ h]

theorem digits_inj {A B C D t : ℕ}
    (h : mul 11 D (mul 11 C (mul 11 B (mul 11 A t))) = one 11) :
    ∀ i < 11, ∀ j < 11, img t i = img t j → i = j := by
  intro i hi j hj e
  have hi' := congrArg (fun s => img s i) h
  have hj' := congrArg (fun s => img s j) h
  simp only [img_mul _ _ hi, img_mul _ _ hj, img_one' hi, img_one' hj] at hi' hj'
  rw [← hi', ← hj', e]

theorem sift_inj {y : ℕ} (h : siftM R1 R2 R3 R4 y = true) :
    ∀ i < 11, ∀ j < 11, img y i = img y j → i = j := by
  unfold siftM at h
  rw [letB_eq, letB_eq, letB_eq, beq_iff] at h
  exact digits_inj h

theorem witness_of (ha : P.code gA = CA) (hb : P.code gB = CB)
    (hG : GF gA gB CA CB R1 R2 R3 R4 W1 W2 W3 W4) {u : Perm (Fin 11)} {y : ℕ}
    (hs : siftM R1 R2 R3 R4 y = true) (he : mul 11 y CA = mul 11 (P.code u) y) :
    ∃ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))), g * gA = u * g := by
  have hlt : ∀ i (hi : i < 11), img y i < 11 := by
    intro i hi
    have e1 := congrArg (fun s => img s (gA⁻¹ ⟨i, hi⟩)) he
    simp only [img_mul _ _ (gA⁻¹ ⟨i, hi⟩).isLt] at e1
    rw [← ha, img_fin gA (gA⁻¹ ⟨i, hi⟩).isLt] at e1
    have e2 : gA ⟨((gA⁻¹ ⟨i, hi⟩ : Fin 11) : ℕ), (gA⁻¹ ⟨i, hi⟩).isLt⟩ = ⟨i, hi⟩ := by
      simp
    rw [e2] at e1
    simp only at e1
    rw [e1]
    by_cases hv : img y (gA⁻¹ ⟨i, hi⟩) < 11
    · rw [img_fin u hv]
      exact (u _).isLt
    · rw [img_code_ge u (by omega)]
      norm_num
  let φ : Fin 11 → Fin 11 := fun i => ⟨img y i, hlt i i.isLt⟩
  have hinj : Function.Injective φ := fun i j e =>
    Fin.ext (sift_inj hs i i.isLt j j.isLt (congrArg Fin.val e))
  let g : Perm (Fin 11) := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 hinj)
  have hg : ∀ i (hi : i < 11), img (P.code g) i = img y i := fun i hi => by
    rw [img_fin g hi]
    rfl
  have hsg : siftM R1 R2 R3 R4 (P.code g) = true := by
    rw [siftM_congr hg]
    exact hs
  refine ⟨g, (inS_iff ha hb hG g).1 (siftM_spec ha hb hG hsg), ?_⟩
  ext i
  have e1 := congrArg (fun s => img s i) he
  simp only [img_mul _ _ i.isLt] at e1
  rw [← ha, img_fin gA i.isLt] at e1
  change (φ (gA i) : ℕ) = (u (φ i) : ℕ)
  change img y (gA i) = (u ⟨img y i, _⟩ : ℕ)
  rw [e1, img_fin u]

theorem iffB_iff' {p q : Bool} : CFSG.KC.LQT.S.iffB p q = true ↔ (p = true ↔ q = true) := by
  cases p <;> cases q <;> simp [CFSG.KC.LQT.S.iffB, CFSG.KC.Ord.notB]

end GrpP

open GrpP in
theorem s4154_proved (gA gB sa sb : Perm (Fin 11)) (P0 E : List (Perm (Fin 11)))
    (hE : ∀ g, g ∈ E ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))))
    {CA CB SA SB : ℕ} {LP R1 R2 R3 R4 : List ℕ} {W1 W2 W3 W4 : List (List ℕ)}
    (ha : CFSG.KC.LQT.S.code gA = CA) (hb : CFSG.KC.LQT.S.code gB = CB)
    (hsa : CFSG.KC.LQT.S.code sa = SA) (hsb : CFSG.KC.LQT.S.code sb = SB)
    (hp : P0.map CFSG.KC.LQT.S.code = LP) (hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true)
    (hk : c4154 R1 R2 R3 R4 LP SA SB = true) :
    let I := P0.filter fun x => decide (x ≠ 1 ∧ x * x = 1)
    (∀ g ∈ E, g * sa * g⁻¹ ∈ P0 → g * sb * g⁻¹ ∈ P0 → g ∈ P0)
    ∧ (∀ g ∈ E, ∀ t ∈ I, ∀ s ∈ I, g * t = t * g → g * s = s * g → t ≠ s → t * s = s * t →
          g = 1 ∨ g = t ∨ g = s ∨ g = t * s) := by
  intro I
  rw [codeS] at ha hb hsa hsb
  have hp' : P0.map P.code = LP := hp
  have key := fun g (hgE : g ∈ E) => andB_iff.1 (allM_closure ha hb hg hk ((hE g).1 hgE))
  have hinv : ∀ t ∈ I, P.code t ∈ invsL LP := by
    intro t ht
    simp only [I, List.mem_filter, decide_eq_true_eq] at ht
    unfold invsL
    rw [CFSG.KC.LQT.S.mem_filtL, ← hp', mem_codes, andB_iff, notB_iff, code_one, beq_code h11,
      code_mul h11, beq_code h11]
    exact ⟨ht.1, ht.2.1, ht.2.2⟩
  refine ⟨fun g hgE h1 h2 => ?_, fun g hgE t ht s hs h1 h2 h3 h4 => ?_⟩
  · have hn := (key g hgE).1
    unfold normK at hn
    rw [impB_iff, impB_iff, CFSG.KC.LQT.S.memL_iff, CFSG.KC.LQT.S.memL_iff,
      CFSG.KC.LQT.S.memL_iff, ← hsa, ← hsb, conj_code h11, conj_code h11, ← hp', mem_codes,
      mem_codes, mem_codes] at hn
    exact hn h1 h2
  · have hc := (key g hgE).2
    unfold centK at hc
    rw [allL_iff] at hc
    have hc := hc _ (hinv t ht)
    rw [allL_iff] at hc
    have hc := hc _ (hinv s hs)
    rw [impB_iff, impB_iff, impB_iff, impB_iff, comm_code h11, comm_code h11, comm_code h11,
      notB_iff, beq_code h11, orB_iff, orB_iff, orB_iff, code_one, beq_code h11, beq_code h11,
      beq_code h11, code_mul h11, beq_code h11] at hc
    exact hc h1 h2 h3 h4


open GrpP in
theorem s4144_proved (gA gB : Perm (Fin 11)) (Tl E : List (Perm (Fin 11)))
    (hE : ∀ g, g ∈ E ↔ g ∈ Subgroup.closure ({gA, gB} : Set (Perm (Fin 11))))
    {CA CB : ℕ} {LT WI R1 R2 R3 R4 : List ℕ} {W1 W2 W3 W4 : List (List ℕ)}
    (ha : CFSG.KC.LQT.S.code gA = CA) (hb : CFSG.KC.LQT.S.code gB = CB)
    (ht : Tl.map CFSG.KC.LQT.S.code = LT)
    (hg : grpM CA CB R1 R2 R3 R4 W1 W2 W3 W4 = true)
    (hk : c4144 R1 R2 R3 R4 CA LT WI = true) :
    (∀ g ∈ E, (g * gA = gA * g ∧ g ^ 3 = 1) ↔ g ∈ Tl)
    ∧ (∀ g ∈ E, g * gA = gA * g → (∀ t ∈ Tl, t * g = g * t) → g = 1 ∨ g = gA)
    ∧ (∀ g ∈ E, (∀ t ∈ Tl, g * t = t * g) → g = 1 ∨ g = gA)
    ∧ (∀ u ∈ E, u ≠ 1 → u * u = 1 → ∃ g ∈ E, g * gA = u * g) := by
  rw [codeS] at ha hb
  have ht' : Tl.map P.code = LT := ht
  have key := fun g (hgE : g ∈ E) => allM_closure ha hb hg hk ((hE g).1 hgE)
  have hall : ∀ (p : ℕ → ℕ → Bool) (g : Perm (Fin 11)),
      allL LT (fun t => p t (P.code g)) = true ↔ ∀ t ∈ Tl, p (P.code t) (P.code g) = true := by
    intro p g
    rw [allL_iff, ← ht', List.forall_mem_map]
  have hor : ∀ g : Perm (Fin 11), CFSG.KC.Ord.orB (Nat.beq (P.code g) (one 11)) (Nat.beq (P.code g) CA) = true ↔
      g = 1 ∨ g = gA := by
    intro g
    rw [orB_iff, code_one, beq_code h11, ← ha, beq_code h11]
  refine ⟨fun g hgE => ?_, fun g hgE h1 h2 => ?_, fun g hgE h1 => ?_, fun u huE h1 h2 => ?_⟩
  · have k := key g hgE
    unfold f4144 at k
    rw [andB_iff] at k
    have k1 := k.1
    rw [iffB_iff', andB_iff, ← ha, comm_code h11, code_pow h11, code_one, beq_code h11,
      CFSG.KC.LQT.S.memL_iff, ← ht', mem_codes] at k1
    exact k1
  · have k := key g hgE
    unfold f4144 at k
    rw [andB_iff, andB_iff] at k
    have k2 := k.2.1
    have h2' : allL LT (fun t => comm 11 t (P.code g)) = true :=
      (hall (fun t x => comm 11 t x) g).2 fun t ht => (comm_code h11 t g).2 (h2 t ht)
    have hc : comm 11 (P.code g) CA = true := by
      rw [← ha]
      exact (comm_code h11 g gA).2 h1
    rw [impB_iff, impB_iff] at k2
    exact (hor g).1 (k2 hc h2')
  · have k := key g hgE
    unfold f4144 at k
    rw [andB_iff, andB_iff, andB_iff] at k
    have k3 := k.2.2.1
    have h1' : allL LT (fun t => comm 11 (P.code g) t) = true :=
      (hall (fun t x => comm 11 x t) g).2 fun t ht => (comm_code h11 g t).2 (h1 t ht)
    rw [impB_iff] at k3
    exact (hor g).1 (k3 h1')
  · have k := key u huE
    unfold f4144 at k
    rw [andB_iff, andB_iff, andB_iff] at k
    have k4 := k.2.2.2
    rw [impB_iff, impB_iff, notB_iff, code_one, beq_code h11, code_mul h11, beq_code h11,
      anyL_iff] at k4
    obtain ⟨w, -, hw⟩ := k4 h1 h2
    rw [andB_iff, andB_iff] at hw
    obtain ⟨-, hs, he⟩ := hw
    obtain ⟨g, hgc, hgg⟩ := witness_of ha hb (gf_of hg) hs (beq_iff.1 he)
    exact ⟨g, (hE g).2 hgc, hgg⟩


end CFSG.KC.LQT.M

end
