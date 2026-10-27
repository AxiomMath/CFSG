module

public import CFSG.Certificates.Kernel.U38ProjGenSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38GenSound

public section

namespace CFSG.KC.U38PG

open CFSG.KC.Loop CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.U38
open scoped Matrix

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem allL_eq_true {α : Type} {f : α → Bool} {L : List α} :
    allL f L = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => exact iff_of_true rfl (fun x hx => absurd hx List.not_mem_nil)
  | cons a L ih =>
    change andB (f a) (allL f L) = true ↔ _
    rw [andB_eq_true, ih, List.forall_mem_cons]

theorem forceL_eq (L : List Nat) (k : List Nat → Bool) : forceL L k = k L := by
  induction L generalizing k with
  | nil => rfl
  | cons a L ih =>
    change strictB a (fun a' => forceL L (fun L' => k (a' :: L'))) = k (a :: L)
    rw [strictB_eq, ih]

theorem beq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem getL_eq (L : List Nat) (k : Nat) : getL L k = L.getD k 0 := by
  induction L generalizing k with
  | nil =>
    change 0 = _
    simp
  | cons a L ih =>
    cases k with
    | zero =>
      change a = _
      simp
    | succ k =>
      change getL L k = _
      rw [ih]
      simp

theorem gensP_eq (d : GenData) : gensP d = d.gens.toList.map packA := by
  unfold gensP
  generalize d.gens.toList = l
  induction l with
  | nil => rfl
  | cons A l ih => exact congrArg (packA A :: ·) ih

theorem conjL_eq (G : List Nat) : conjL G = G.map conjTrP := by
  induction G with
  | nil => rfl
  | cons g G ih => exact congrArg (conjTrP g :: ·) ih

theorem wordsP_eq (G GI : List Nat) (ws : List (List Nat)) : wordsP G GI ws = ws.map (wordP G GI) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => exact congrArg (wordP G GI w :: ·) ih

@[expose] noncomputable def pkL (L : List GF64) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun a _ ih => Nat.add (GF64.toNat a) (Nat.shiftLeft ih 6)) L

theorem g6_cons {x : Nat} (hx : x < 64) (y i : Nat) :
    g6 (x + Nat.shiftLeft y 6) (i + 1) = g6 y i ∧ g6 (x + Nat.shiftLeft y 6) 0 = x := by
  rw [g6_eq, g6_eq, g6_eq, shl_eq]
  constructor
  · have e : 2 ^ (6 * (i + 1)) = 64 * 2 ^ (6 * i) := by rw [Nat.mul_succ, pow_add]; ring
    have e2 : (x + y * 2 ^ 6) / 64 = y := by norm_num; omega
    rw [e, ← Nat.div_div_eq_div_mul, e2]
  · norm_num
    omega

theorem g6_pkL (L : List GF64) (i : Nat) : g6 (pkL L) i = GF64.toNat (L.getD i 0) := by
  induction L generalizing i with
  | nil =>
    change g6 0 i = _
    rw [List.getD_nil, g6_eq, Nat.zero_div]
    rfl
  | cons a L ih =>
    have hs : pkL (a :: L) = GF64.toNat a + Nat.shiftLeft (pkL L) 6 := rfl
    cases i with
    | zero =>
      rw [hs, (g6_cons (GF64.toNat_lt a) _ 0).2]
      simp
    | succ i =>
      rw [hs, (g6_cons (GF64.toNat_lt a) _ i).1, ih]
      simp

theorem decP_packA (A : Array GF64) : decP (packA A) = toMat3 A := by
  refine Matrix.ext fun i j => ?_
  have h : packA A = pkL A.toList := rfl
  have hl : ∀ n, A.toList.getD n 0 = A.getD n 0 := fun n => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [decP, toMat3, Matrix.of_apply, h, g6_pkL, hl, GF64.ofNat'_toNat]

theorem decP_IDP : decP IDP = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem g6_pack {p q r : Nat} (hp : p < 64) (hq : q < 64) (hr : r < 64) :
    g6 (p + 64 * q + 4096 * r) 0 = p ∧ g6 (p + 64 * q + 4096 * r) 1 = q ∧
      g6 (p + 64 * q + 4096 * r) 2 = r := by
  simp only [g6_eq]
  norm_num
  omega

theorem decV_packV {a : Array ℕ} (h : validV a = true) : decV (packV a) = vecOf a := by
  simp only [validV, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨-, h0⟩, h1⟩, h2⟩ := h
  have e : packV a = a.getD 0 0 + 64 * a.getD 1 0 + 4096 * a.getD 2 0 := by
    change a.getD 0 0 + (64 * a.getD 1 0 + 4096 * a.getD 2 0) = _
    ring
  obtain ⟨g0, g1, g2⟩ := g6_pack h0 h1 h2
  rw [← e] at g0 g1 g2
  funext j
  fin_cases j <;> simp [decV, vecOf, g0, g1, g2]

theorem g6_land (v : Nat) {i : Nat} (hi : i < 3) : g6 (Nat.land v 262143) i = g6 v i := by
  have h : Nat.land v 262143 = v % 2 ^ 18 := Nat.and_two_pow_sub_one_eq_mod v 18
  rw [h, g6_eq, g6_eq]
  interval_cases i <;> norm_num <;> omega

theorem decV_land (v : Nat) : decV (Nat.land v 262143) = decV v := by
  funext j
  fin_cases j
  · exact congrArg GF64.ofNat' (g6_land v (by norm_num))
  · exact congrArg GF64.ofNat' (g6_land v (by norm_num))
  · exact congrArg GF64.ofNat' (g6_land v (by norm_num))

theorem getL_gensP (d : GenData) (k : Nat) : getL (gensP d) k = packA (d.gens.getD k #[]) := by
  rw [getL_eq, gensP_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  cases d.gens.toList[k]? <;> rfl

theorem length_gensP (d : GenData) : (gensP d).length = d.gens.size := by
  simp [gensP_eq]

theorem getL_conjL {G : List Nat} {k : Nat} (hk : k < G.length) :
    getL (conjL G) k = conjTrP (getL G k) := by
  rw [getL_eq, getL_eq, conjL_eq, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem decP_letP (d : GenData) {l : Nat} (hl : l / 2 < d.gens.size) :
    decP (letP (gensP d) (conjL (gensP d)) l) = toMat3 (letterArr3 d.gens l) := by
  unfold letP letterArr3
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · have e : Nat.beq (Nat.mod l 2) 0 = true := beq_true h
    rw [e, if_pos h]
    change decP (getL (gensP d) (l / 2)) = _
    rw [getL_gensP, decP_packA]
  · have e : Nat.beq (Nat.mod l 2) 0 = false := beq_false (a := l % 2) (by omega)
    rw [e, if_neg (by omega)]
    change decP (getL (conjL (gensP d)) (l / 2)) = _
    rw [getL_conjL (by rw [length_gensP]; exact hl), decP_conjTrP, getL_gensP, decP_packA,
      toMat3_conjTrArr3]

theorem decP_wordP (d : GenData) {w : List Nat} (hw : ∀ l ∈ w, l / 2 < d.gens.size) :
    decP (wordP (gensP d) (conjL (gensP d)) w) = toMat3 (wordArr3 d.gens w) := by
  induction w with
  | nil =>
    change decP IDP = toMat3 oneArr3
    rw [toMat3_oneArr3, decP_IDP]
  | cons l w ih =>
    change decP (strictN (wordP (gensP d) (conjL (gensP d)) w)
        fun A => mulP (letP (gensP d) (conjL (gensP d)) l) A) =
      toMat3 (mulArr3 (letterArr3 d.gens l) (wordArr3 d.gens w))
    rw [strictN_eq, decP_mulP, toMat3_mulArr3, decP_letP d (hw l List.mem_cons_self),
      ih (fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))]

@[expose] noncomputable def lc (x : RowVec) : GF64 :=
  if x 0 ≠ 0 then x 0 else if x 1 ≠ 0 then x 1 else x 2

@[expose] noncomputable def keyN (x : RowVec) : Nat :=
  if x 0 ≠ 0 then 64 * GF64.toNat (x 1 / x 0) + GF64.toNat (x 2 / x 0)
  else if x 1 ≠ 0 then 4096 + GF64.toNat (x 2 / x 1) else 4160

@[expose] noncomputable def smulV (c : GF64) (x : RowVec) : RowVec := fun i => c * x i

theorem ofNat'_zero_iff_fin : ∀ a : Fin 64, GF64.ofNat' a.val = 0 ↔ a.val = 0 := by
  decide +kernel

theorem ofNat'_eq_zero {a : Nat} (ha : a < 64) : GF64.ofNat' a = 0 ↔ a = 0 :=
  ofNat'_zero_iff_fin ⟨a, ha⟩

theorem toNat_ofNat'_lt {a : Nat} (ha : a < 64) : GF64.toNat (GF64.ofNat' a) = a :=
  GF64.toNat_ofNat' ⟨a, ha⟩

theorem toNat_inj {a b : GF64} (h : GF64.toNat a = GF64.toNat b) : a = b := by
  rw [← GF64.ofNat'_toNat a, ← GF64.ofNat'_toNat b, h]

theorem lead_lt (w : Nat) : lead w < 64 := by
  unfold lead
  exact nIf_lt (nIf_lt (g6_lt _ _) (g6_lt _ _)) (g6_lt _ _)

theorem ginv_lt (a : Nat) : ginv a < 64 := g6_lt _ _

theorem lead_spec (w : Nat) : GF64.ofNat' (lead w) = lc (decV w) := by
  have z0 := ofNat'_eq_zero (g6_lt w 0)
  have z1 := ofNat'_eq_zero (g6_lt w 1)
  have e : lc (decV w) = if GF64.ofNat' (g6 w 0) ≠ 0 then GF64.ofNat' (g6 w 0) else
      if GF64.ofNat' (g6 w 1) ≠ 0 then GF64.ofNat' (g6 w 1) else GF64.ofNat' (g6 w 2) := rfl
  rw [e]
  unfold lead
  by_cases h0 : g6 w 0 = 0
  · rw [beq_true h0, if_neg (by rw [not_not, z0]; exact h0)]
    by_cases h1 : g6 w 1 = 0
    · rw [beq_true h1, if_neg (by rw [not_not, z1]; exact h1)]
    · rw [beq_false h1, if_pos (by rw [ne_eq, z1]; exact h1)]
  · rw [beq_false h0, if_pos (by rw [ne_eq, z0]; exact h0)]

theorem lc_ne_of_lead {w : Nat} (h : lead w ≠ 0) : lc (decV w) ≠ 0 := by
  rw [← lead_spec]
  intro h0
  exact h ((ofNat'_eq_zero (lead_lt w)).1 h0)

theorem gm_inv {a b : Nat} (ha : a < 64) (ha0 : a ≠ 0) (hb : b < 64) :
    gm (ginv a) b = GF64.toNat (GF64.ofNat' b / GF64.ofNat' a) := by
  rw [div_eq_inv_mul, ← ginv_spec ha ha0, ← gm_spec (ginv_lt a) hb, toNat_ofNat'_lt (gm_lt _ _)]

theorem keyOf_spec (w : Nat) : keyOf w = keyN (decV w) := by
  have z0 := ofNat'_eq_zero (g6_lt w 0)
  have z1 := ofNat'_eq_zero (g6_lt w 1)
  have e : keyN (decV w) = if GF64.ofNat' (g6 w 0) ≠ 0 then
      64 * GF64.toNat (GF64.ofNat' (g6 w 1) / GF64.ofNat' (g6 w 0)) +
        GF64.toNat (GF64.ofNat' (g6 w 2) / GF64.ofNat' (g6 w 0))
      else if GF64.ofNat' (g6 w 1) ≠ 0 then
        4096 + GF64.toNat (GF64.ofNat' (g6 w 2) / GF64.ofNat' (g6 w 1))
      else 4160 := rfl
  rw [e]
  unfold keyOf
  simp only [strictN_eq]
  by_cases h0 : g6 w 0 = 0
  · rw [beq_true h0, if_neg (by rw [not_not, z0]; exact h0)]
    by_cases h1 : g6 w 1 = 0
    · rw [beq_true h1, if_neg (by rw [not_not, z1]; exact h1)]
    · rw [beq_false h1, if_pos (by rw [ne_eq, z1]; exact h1)]
      dsimp only
      rw [gm_inv (g6_lt _ _) h1 (g6_lt _ _)]
      rfl
  · rw [beq_false h0, if_pos (by rw [ne_eq, z0]; exact h0)]
    dsimp only
    rw [gm_inv (g6_lt _ _) h0 (g6_lt _ _), gm_inv (g6_lt _ _) h0 (g6_lt _ _)]
    rfl

theorem smulV_apply (c : GF64) (x : RowVec) (i : Fin 3) : smulV c x i = c * x i := rfl

theorem keyN_smul {c : GF64} (hc : c ≠ 0) (x : RowVec) : keyN (smulV c x) = keyN x := by
  simp only [keyN, smulV_apply, ne_eq, mul_eq_zero, hc, false_or, mul_div_mul_left _ _ hc]

theorem lc_smul {c : GF64} (hc : c ≠ 0) (x : RowVec) : lc (smulV c x) = c * lc x := by
  simp only [lc, smulV_apply, ne_eq, mul_eq_zero, hc, false_or]
  split_ifs <;> rfl

theorem keyN_lt {x : RowVec} (h : x 0 ≠ 0) : keyN x < 4096 := by
  have := GF64.toNat_lt (x 1 / x 0)
  have := GF64.toNat_lt (x 2 / x 0)
  simp only [keyN, ne_eq, h, not_false_eq_true, if_true]
  omega

theorem keyN_ge {x : RowVec} (h : x 0 = 0) : 4096 ≤ keyN x := by
  simp only [keyN, h, ne_eq, not_true_eq_false, if_false]
  split_ifs <;> omega

theorem keyN_lt' {x : RowVec} (h : x 0 = 0) (h1 : x 1 ≠ 0) : keyN x < 4160 := by
  have := GF64.toNat_lt (x 2 / x 1)
  simp only [keyN, h, h1, ne_eq, not_true_eq_false, not_false_eq_true, if_false, if_true]
  omega

theorem keyN_eq {x : RowVec} (h : x 0 = 0) (h1 : x 1 = 0) : keyN x = 4160 := by
  simp [keyN, h, h1]

theorem div_eq_of_toNat {a b c e : GF64} (h : GF64.toNat (a / b) = GF64.toNat (c / e)) :
    a / b = c / e := toNat_inj h

theorem mul_div_eq {a b c e : GF64} (hb : b ≠ 0) (he : e ≠ 0) (h : a / b = c / e) :
    a = b * e⁻¹ * c := by
  calc a = b * (a / b) := by field_simp
    _ = b * (c / e) := by rw [h]
    _ = b * e⁻¹ * c := by ring

theorem eq_smul_of_keyN_eq {x y : RowVec} (hx : lc x ≠ 0) (hy : lc y ≠ 0) (h : keyN x = keyN y) :
    x = smulV (lc x * (lc y)⁻¹) y := by
  by_cases x0 : x 0 = 0 <;> by_cases y0 : y 0 = 0
  · by_cases x1 : x 1 = 0 <;> by_cases y1 : y 1 = 0
    · have hlx : lc x = x 2 := by simp [lc, x0, x1]
      have hly : lc y = y 2 := by simp [lc, y0, y1]
      rw [hlx] at hx ⊢
      rw [hly] at hy ⊢
      funext i
      fin_cases i
      · simp [smulV_apply, x0, y0]
      · simp [smulV_apply, x1, y1]
      · change x 2 = x 2 * (y 2)⁻¹ * y 2
        field_simp
    · have := keyN_lt' y0 y1
      rw [keyN_eq x0 x1] at h
      omega
    · have := keyN_lt' x0 x1
      rw [keyN_eq y0 y1] at h
      omega
    · have hlx : lc x = x 1 := by simp [lc, x0, x1]
      have hly : lc y = y 1 := by simp [lc, y0, y1]
      have h2 : GF64.toNat (x 2 / x 1) = GF64.toNat (y 2 / y 1) := by
        simp only [keyN, x0, y0, x1, y1, ne_eq, not_true_eq_false, not_false_eq_true, if_false,
          if_true] at h
        omega
      have e2 := mul_div_eq x1 y1 (div_eq_of_toNat h2)
      rw [hlx, hly]
      funext i
      fin_cases i
      · simp [smulV_apply, x0, y0]
      · change x 1 = x 1 * (y 1)⁻¹ * y 1
        field_simp
      · exact e2
  · have := keyN_lt y0
    have := keyN_ge x0
    omega
  · have := keyN_lt x0
    have := keyN_ge y0
    omega
  · have hlx : lc x = x 0 := by simp [lc, x0]
    have hly : lc y = y 0 := by simp [lc, y0]
    have hb := GF64.toNat_lt (x 2 / x 0)
    have hb' := GF64.toNat_lt (y 2 / y 0)
    have ha := GF64.toNat_lt (x 1 / x 0)
    have ha' := GF64.toNat_lt (y 1 / y 0)
    simp only [keyN, x0, y0, ne_eq, not_false_eq_true, if_true] at h
    have h1 : GF64.toNat (x 1 / x 0) = GF64.toNat (y 1 / y 0) := by omega
    have h2 : GF64.toNat (x 2 / x 0) = GF64.toNat (y 2 / y 0) := by omega
    have e1 := mul_div_eq x0 y0 (div_eq_of_toNat h1)
    have e2 := mul_div_eq x0 y0 (div_eq_of_toNat h2)
    rw [hlx, hly]
    funext i
    fin_cases i
    · change x 0 = x 0 * (y 0)⁻¹ * y 0
      field_simp
    · exact e1
    · exact e2

theorem smulV_smulV (a b : GF64) (x : RowVec) : smulV a (smulV b x) = smulV (a * b) x := by
  funext i
  simp only [smulV_apply, mul_assoc]

theorem smulV_one (x : RowVec) : smulV 1 x = x := by
  funext i
  simp only [smulV_apply, one_mul]

theorem smul_smulV (g : GL (Fin 3) GF64) (c : GF64) (x : RowVec) :
    g • smulV c x = smulV c (g • x) := by
  rw [smul_rowVec, smul_rowVec]
  funext j
  simp only [smulV, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  ring

@[expose] noncomputable def scal (K : Subgroup (GL (Fin 3) GF64)) (x : RowVec) :
    Subgroup GF64ˣ where
  carrier := {u | ∃ k ∈ K, k • x = smulV (u : GF64) x}
  one_mem' := ⟨1, K.one_mem, by rw [one_smul, Units.val_one, smulV_one]⟩
  mul_mem' := by
    intro u u' hu hu'
    obtain ⟨k, hk, hkx⟩ := hu
    obtain ⟨k', hk', hkx'⟩ := hu'
    refine Set.mem_setOf.mpr ⟨k * k', K.mul_mem hk hk', ?_⟩
    rw [mul_smul, hkx', smul_smulV, hkx, smulV_smulV, Units.val_mul, mul_comm]
  inv_mem' := by
    intro u hu
    obtain ⟨k, hk, hkx⟩ := hu
    refine Set.mem_setOf.mpr ⟨k⁻¹, K.inv_mem hk, ?_⟩
    have e : x = smulV (u : GF64) (k⁻¹ • x) := by rw [← smul_smulV, ← hkx, inv_smul_smul]
    calc k⁻¹ • x = smulV (((u⁻¹ * u : GF64ˣ)) : GF64) (k⁻¹ • x) := by
          rw [inv_mul_cancel, Units.val_one, smulV_one]
      _ = smulV ((u⁻¹ : GF64ˣ) : GF64) (smulV (u : GF64) (k⁻¹ • x)) := by
          rw [smulV_smulV, Units.val_mul]
      _ = smulV ((u⁻¹ : GF64ˣ) : GF64) x := by rw [← e]

theorem mem_scal {K : Subgroup (GL (Fin 3) GF64)} {x : RowVec} {u : GF64ˣ} :
    u ∈ scal K x ↔ ∃ k ∈ K, k • x = smulV (u : GF64) x := Iff.rfl

theorem pow63_fin : ∀ a : Fin 64, a.val ≠ 0 → GF64.ofNat' a.val ^ 63 = 1 := by
  decide +kernel

theorem pow63 {μ : GF64} (hμ : μ ≠ 0) : μ ^ 63 = 1 := by
  have h0 : GF64.toNat μ ≠ 0 := by
    intro h
    apply hμ
    rw [← GF64.ofNat'_toNat μ, h]
    rfl
  have := pow63_fin ⟨GF64.toNat μ, GF64.toNat_lt μ⟩ h0
  rwa [GF64.ofNat'_toNat] at this

theorem dvd63_nine : ∀ n < 64, n ∣ 63 → ¬ n ∣ 21 → 9 ∣ n := by decide

theorem dvd63_seven : ∀ n < 64, n ∣ 63 → ¬ n ∣ 9 → 7 ∣ n := by decide

theorem dvd_orderOf {μ : GF64} (hμ : μ ≠ 0) {e p : Nat} (he : μ ^ e ≠ 1)
    (hd : ∀ n < 64, n ∣ 63 → ¬ n ∣ e → p ∣ n) : p ∣ orderOf (Units.mk0 μ hμ) := by
  have h63 : Units.mk0 μ hμ ^ 63 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val,
    Units.val_mk0, pow63 hμ, Units.val_one])
  have hdv := orderOf_dvd_of_pow_eq_one h63
  refine hd _ (by have := Nat.le_of_dvd (by norm_num) hdv; omega) hdv ?_
  intro hde
  apply he
  have := congrArg Units.val (orderOf_dvd_iff_pow_eq_one.1 hde)
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at this

theorem le_card_of_flags {M : Subgroup GF64ˣ} {μ₁ μ₂ : GF64} (h₁ : μ₁ ≠ 0) (h₂ : μ₂ ≠ 0)
    (m₁ : Units.mk0 μ₁ h₁ ∈ M) (m₂ : Units.mk0 μ₂ h₂ ∈ M) (e₁ : μ₁ ^ 21 ≠ 1) (e₂ : μ₂ ^ 9 ≠ 1) :
    63 ≤ Nat.card M := by
  have d9 := (dvd_orderOf h₁ e₁ dvd63_nine).trans (Subgroup.orderOf_dvd_natCard M m₁)
  have d7 := (dvd_orderOf h₂ e₂ dvd63_seven).trans (Subgroup.orderOf_dvd_natCard M m₂)
  have d63 : 9 * 7 ∣ Nat.card M := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d9 d7
  exact Nat.le_of_dvd Nat.card_pos d63

inductive Reach (ms : List Nat) (v : Nat) : Nat → Prop
  | base : Reach ms v v
  | step {y m : Nat} : Reach ms v y → m ∈ ms → Reach ms v (vmP y m)

section SearchState

set_option exponentiation.threshold 25100

theorem ps_land (x n : Nat) : Nat.land x (2 ^ n - 1) = x % 2 ^ n :=
  Nat.and_two_pow_sub_one_eq_mod x n

theorem ps_shr (x n : Nat) : Nat.shiftRight x n = x / 2 ^ n :=
  Nat.shiftRight_eq_div_pow x n

theorem ps_land18 (x : Nat) : Nat.land x 262143 = x % 2 ^ 18 := ps_land x 18

theorem ps_land19 (x : Nat) : Nat.land x 524287 = x % 2 ^ 19 := ps_land x 19

theorem ps_p25045 : (2 : Nat) ^ 25045 = 2 ^ 64 * (4 * (8192 * 2 ^ 24966)) := by
  have h4 : (4 : Nat) = 2 ^ 2 := rfl
  have h13 : (8192 : Nat) = 2 ^ 13 := rfl
  rw [h4, h13, ← pow_add, ← pow_add, ← pow_add]

@[expose] noncomputable def psE (s f c t K : Nat) : Nat :=
  s + 2 ^ 64 * (f + 4 * (c + 8192 * (t + 2 ^ 24966 * K)))

theorem psE_split (s f c t K : Nat) : psE s f c t K = psE s f c t 0 + 2 ^ 25045 * K := by
  unfold psE
  rw [ps_p25045]
  generalize (2 : Nat) ^ 24966 = P
  generalize (2 : Nat) ^ 64 = B
  ring

theorem psE_lt {s f c t : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192)
    (ht : t < 2 ^ 24966) : psE s f c t 0 < 2 ^ 25045 := by
  unfold psE
  rw [ps_p25045, mul_zero, add_zero]
  generalize (2 : Nat) ^ 24966 = P at ht ⊢
  generalize (2 : Nat) ^ 64 = B at hs ⊢
  have h1 : f + 4 * (c + 8192 * t) + 1 ≤ 4 * (8192 * P) := by omega
  have h2 := Nat.mul_le_mul_left B h1
  nlinarith

theorem psE_mod {s f c t K : Nat} (hs : s < 2 ^ 64) : psE s f c t K % 2 ^ 64 = s := by
  unfold psE
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]

theorem psE_div {s f c t K : Nat} (hs : s < 2 ^ 64) :
    psE s f c t K / 2 ^ 64 = f + 4 * (c + 8192 * (t + 2 ^ 24966 * K)) := by
  unfold psE
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hs, zero_add]

theorem psE_flg {s f c t K : Nat} (hs : s < 2 ^ 64) (hf : f < 4) :
    Nat.land (Nat.shiftRight (psE s f c t K) 64) 3 = f := by
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := rfl
  rw [h3, ps_land, ps_shr, psE_div hs]
  generalize c + 8192 * (t + 2 ^ 24966 * K) = X
  have h4 : (2 : Nat) ^ 2 = 4 := rfl
  rw [h4]
  omega

theorem psE_cnt {s f c t K : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192) :
    Nat.land (Nat.shiftRight (psE s f c t K) 66) 8191 = c := by
  have h3 : (8191 : Nat) = 2 ^ 13 - 1 := rfl
  have h66 : (2 : Nat) ^ 66 = 2 ^ 64 * 4 := by norm_num
  rw [h3, ps_land, ps_shr, h66, ← Nat.div_div_eq_div_mul, psE_div hs]
  generalize t + 2 ^ 24966 * K = Y
  have h4 : (2 : Nat) ^ 13 = 8192 := rfl
  rw [h4]
  omega

theorem psE_tab {s f c t K k : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192)
    (hk : k ≤ 4160) :
    Nat.land (Nat.shiftRight (psE s f c t K) (Nat.add 79 (Nat.mul 6 k))) 63 = g6 t k := by
  have h3 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  rw [h3, ps_land, ps_shr]
  have e : (2 : Nat) ^ (Nat.add 79 (Nat.mul 6 k)) = 2 ^ 64 * 4 * 8192 * 2 ^ (6 * k) := by
    have e0 : Nat.add 79 (Nat.mul 6 k) = 79 + 6 * k := rfl
    rw [e0, pow_add 2 79 (6 * k)]
    norm_num
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, psE_div hs]
  have e2 : (f + 4 * (c + 8192 * (t + 2 ^ 24966 * K))) / 4 / 8192 = t + 2 ^ 24966 * K := by
    generalize t + 2 ^ 24966 * K = Y
    omega
  rw [e2]
  have e3 : (2 : Nat) ^ 24966 = 2 ^ (6 * k) * (2 ^ 6 * 2 ^ (24960 - 6 * k)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h64 : (2 : Nat) ^ 6 = 64 := rfl
  rw [e3, mul_assoc, Nat.add_mul_div_left _ _ (by positivity), mul_assoc, h64,
    Nat.add_mul_mod_self_left, g6_eq]

theorem psE_shr {s f c t K : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192)
    (ht : t < 2 ^ 24966) : Nat.shiftRight (psE s f c t K) 25045 = K := by
  rw [ps_shr, psE_split, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (psE_lt hs hf hc ht), zero_add]

theorem ps_LOWM : LOWM = 2 ^ 25045 - 1 := by
  unfold LOWM
  rw [shl_eq, one_mul]
  exact Nat.sub_eq

theorem psE_low {s f c t K : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192)
    (ht : t < 2 ^ 24966) : Nat.land (psE s f c t K) LOWM = psE s f c t 0 := by
  rw [ps_LOWM, ps_land, psE_split s f c t K, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (psE_lt hs hf hc ht)]

theorem psE_lor {s f c t K : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c < 8192)
    (ht : t < 2 ^ 24966) :
    Nat.lor (psE s f c t 0) (Nat.shiftLeft K 25045) = psE s f c t K := by
  rw [lor_shl (psE_lt hs hf hc ht), psE_split s f c t K, mul_comm]

theorem ps_M64 : M64 = 2 ^ 64 - 1 := rfl

theorem psE_resalt {s f c t K x : Nat} (hs : s < 2 ^ 64) :
    resalt (psE s f c t K) x = psE ((s * 6364136223846793005 + x) % 2 ^ 64) f c t K := by
  unfold resalt
  rw [strictN_eq]
  have h1 : Nat.land (psE s f c t K) M64 = s := by rw [ps_M64, ps_land, psE_mod hs]
  rw [h1, ps_M64, ps_land]
  change psE s f c t K - s + (s * 6364136223846793005 + x) % 2 ^ 64 = _
  unfold psE
  omega

theorem psE_or {s f c t K g : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hg : g < 4) :
    Nat.lor (psE s f c t K) (Nat.shiftLeft g 64) = psE s (Nat.lor f g) c t K := by
  have hf' : f < 2 ^ 2 := hf
  have hfg : Nat.lor f g < 2 ^ 2 := Nat.or_lt_two_pow hf hg
  have e1 : ∀ f', f' < 2 ^ 2 → psE s f' c t K = Nat.lor s (Nat.shiftLeft
      (Nat.lor f' (Nat.shiftLeft (c + 8192 * (t + 2 ^ 24966 * K)) 2)) 64) := by
    intro f' h'
    rw [lor_shl h', lor_shl hs]
    unfold psE
    generalize (2 : Nat) ^ 24966 = P
    generalize (2 : Nat) ^ 64 = B
    ring
  rw [e1 f hf', e1 _ hfg]
  generalize c + 8192 * (t + 2 ^ 24966 * K) = X
  change (s ||| (f ||| X <<< 2) <<< 64) ||| g <<< 64 = s ||| ((f ||| g) ||| X <<< 2) <<< 64
  rw [Nat.or_assoc s, ← Nat.shiftLeft_or_distrib, Nat.or_assoc f (X <<< 2) g,
    Nat.or_assoc f g (X <<< 2), Nat.or_comm (X <<< 2) g]

theorem ps_g6_ins {t a k : Nat} (ha : a < 64) (h0 : g6 t k = 0) (j : Nat) :
    g6 (t + a * 2 ^ (6 * k)) j = if j = k then a else g6 t j := by
  rw [g6_eq] at h0
  rw [g6_eq, g6_eq]
  have hP : 0 < 2 ^ (6 * k) := by positivity
  have h64 : (64 : Nat) = 2 ^ 6 := rfl
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · rw [if_neg hjk.ne]
    have e : (2 : Nat) ^ (6 * k) = 2 ^ (6 * j) * (64 * 2 ^ (6 * (k - j) - 6)) := by
      rw [h64, ← pow_add, ← pow_add]
      congr 1
      omega
    have e' : a * (2 ^ (6 * j) * (64 * 2 ^ (6 * (k - j) - 6))) =
        2 ^ (6 * j) * (64 * (a * 2 ^ (6 * (k - j) - 6))) := by ring
    rw [e, e', Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · rw [if_pos rfl, Nat.add_mul_div_right _ _ hP]
    generalize t / 2 ^ (6 * j) = X at h0 ⊢
    omega
  · rw [if_neg hjk.ne']
    have e : (2 : Nat) ^ (6 * j) = 2 ^ (6 * k) * (64 * 2 ^ (6 * (j - k) - 6)) := by
      rw [h64, ← pow_add, ← pow_add]
      congr 1
      omega
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hP]
    generalize t / 2 ^ (6 * k) = X at h0 ⊢
    have h1 : (X + a) / 64 = X / 64 := by omega
    rw [h1]

theorem ps_tab_lt {t a k : Nat} (ha : a < 64) (h0 : g6 t k = 0) (hk : k ≤ 4160)
    (ht : t < 2 ^ 24966) : t + a * 2 ^ (6 * k) < 2 ^ 24966 := by
  rw [g6_eq] at h0
  have h64 : (64 : Nat) = 2 ^ 6 := rfl
  have e : (2 : Nat) ^ 24966 = 2 ^ (6 * k) * (64 * 2 ^ (24960 - 6 * k)) := by
    rw [h64, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [e] at ht ⊢
  have hP : 0 < 2 ^ (6 * k) := by positivity
  have hd := Nat.div_add_mod t (2 ^ (6 * k))
  have hm := Nat.mod_lt t hP
  have hq : t / 2 ^ (6 * k) < 64 * 2 ^ (24960 - 6 * k) := by
    rw [Nat.div_lt_iff_lt_mul hP]
    linarith
  generalize t / 2 ^ (6 * k) = X at h0 hd hq
  generalize t % 2 ^ (6 * k) = r at hd hm
  generalize 2 ^ (6 * k) = P at hP hd hm ht ⊢
  generalize 2 ^ (24960 - 6 * k) = R at hq ht ⊢
  have h1 : X + a + 1 ≤ 64 * R := by omega
  have h2 := Nat.mul_le_mul_left P h1
  nlinarith

@[expose] def psStk (L : List Nat) (K : Nat) : Prop :=
  ∀ j, K / 2 ^ (19 * j) % 2 ^ 19 = 0 ∨ ∃ y ∈ L, K / 2 ^ (19 * j) % 2 ^ 19 = y + 2 ^ 18

theorem psStk_pop {L : List Nat} {K : Nat} (h : psStk L K) : psStk L (K / 2 ^ 19) := by
  intro j
  have e : K / 2 ^ 19 / 2 ^ (19 * j) = K / 2 ^ (19 * (j + 1)) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    ring
  rw [e]
  exact h (j + 1)

theorem psStk_push {L : List Nat} {K y : Nat} (h : psStk L K) (hy : y < 2 ^ 18) :
    psStk (y :: L) (y + 2 ^ 18 + K * 2 ^ 19) := by
  have hy' : y + 2 ^ 18 < 2 ^ 19 := by
    norm_num at hy ⊢
    omega
  intro j
  cases j with
  | zero =>
    right
    refine ⟨y, List.mem_cons_self, ?_⟩
    rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy']
  | succ j =>
    have e : (y + 2 ^ 18 + K * 2 ^ 19) / 2 ^ (19 * (j + 1)) = K / 2 ^ (19 * j) := by
      have e0 : 19 * (j + 1) = 19 + 19 * j := by ring
      rw [e0, pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hy', zero_add]
    rw [e]
    exact (h j).imp id fun ⟨z, hz, e⟩ => ⟨z, List.mem_cons_of_mem _ hz, e⟩

abbrev psFl (ms L : List Nat) (b : Nat) : Prop :=
  ∃ y ∈ L, ∃ m ∈ ms, ∃ y' ∈ L, keyOf (vmP y m) = keyOf y' ∧ lead (vmP y m) ≠ 0 ∧
    Nat.testBit (flagsOf (gm (lead (vmP y m)) (ginv (lead y')))) b = true

abbrev psC (ms : List Nat) (v0 : Nat) (L : List Nat) (s f t K : Nat) : Prop :=
  s < 2 ^ 64 ∧ f < 4 ∧ t < 2 ^ 24966 ∧ (L.map keyOf).Nodup ∧
    (∀ y ∈ L, lead y ≠ 0 ∧ y < 2 ^ 18 ∧ Reach ms v0 y ∧ g6 t (keyOf y) = lead y) ∧
    (∀ k < 4161, g6 t k ≠ 0 → ∃ y ∈ L, keyOf y = k) ∧
    (∀ b, Nat.testBit f b = true → psFl ms L b) ∧ psStk L K

abbrev psI (ms : List Nat) (v0 S : Nat) (L : List Nat) : Prop :=
  ∃ s f t K, S = psE s f L.length t K ∧ psC ms v0 L s f t K

theorem ps_keyOf_le (w : Nat) : keyOf w ≤ 4160 := by
  unfold keyOf
  simp only [strictN_eq]
  have := gm_lt (ginv (g6 w 1)) (g6 w 2)
  have := gm_lt (ginv (g6 w 0)) (g6 w 1)
  have := gm_lt (ginv (g6 w 0)) (g6 w 2)
  cases Nat.beq (g6 w 0) 0 <;> cases Nat.beq (g6 w 1) 0 <;> simp only [Nat.add_eq, Nat.mul_eq] <;>
    omega

theorem ps_lead_land (w : Nat) : lead (Nat.land w 262143) = lead w := by
  unfold lead
  rw [g6_land w (by norm_num : 0 < 3), g6_land w (by norm_num : 1 < 3),
    g6_land w (by norm_num : 2 < 3)]

theorem ps_keyOf_land (w : Nat) : keyOf (Nat.land w 262143) = keyOf w := by
  unfold keyOf
  rw [g6_land w (by norm_num : 0 < 3), g6_land w (by norm_num : 1 < 3),
    g6_land w (by norm_num : 2 < 3)]

theorem ps_vmP_lt (y m : Nat) : vmP y m < 2 ^ 18 := by
  unfold vmP
  simp only [strictN_eq]
  rw [pack3_eq (dot3_lt _ _ _ _ _ _) (dot3_lt _ _ _ _ _ _)]
  have h1 := dot3_lt (g6 y 0) (g6 y 1) (g6 y 2) (g6 m 0) (g6 m 3) (g6 m 6)
  have h2 := dot3_lt (g6 y 0) (g6 y 1) (g6 y 2) (g6 m 1) (g6 m 4) (g6 m 7)
  have h3 := dot3_lt (g6 y 0) (g6 y 1) (g6 y 2) (g6 m 2) (g6 m 5) (g6 m 8)
  change _ < 262144
  omega

theorem ps_flagsOf_lt (mu : Nat) : flagsOf mu < 4 := by
  unfold flagsOf
  rw [strictN_eq]
  exact Nat.or_lt_two_pow (n := 2) (nIf_lt (by norm_num) (by norm_num))
    (nIf_lt (by norm_num) (by norm_num))

theorem ps_len {L : List Nat} (h : (L.map keyOf).Nodup) : L.length ≤ 4161 := by
  have hs : L.map keyOf ⊆ List.range 4161 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (Nat.lt_succ_of_le (ps_keyOf_le y))
  have := (h.subperm hs).length_le
  rwa [List.length_map, List.length_range] at this

theorem ps_entry (w : Nat) :
    Nat.lor (Nat.land w 262143) 262144 = Nat.land w 262143 + 2 ^ 18 := by
  have h := lor_shl (x := Nat.land w 262143) (i := 18)
    (by rw [ps_land18]; exact Nat.mod_lt _ (by positivity)) 1
  rw [one_mul] at h
  exact h

theorem ps_insS {s f c t K w k a : Nat} (hs : s < 2 ^ 64) (hf : f < 4) (hc : c + 1 < 8192)
    (ht : t + a * 2 ^ (6 * k) < 2 ^ 24966) :
    insS (psE s f c t K) w k a =
      psE s f (c + 1) (t + a * 2 ^ (6 * k)) (Nat.land w 262143 + 2 ^ 18 + K * 2 ^ 19) := by
  have e1 : Nat.add (Nat.add (psE s f c t K) (Nat.shiftLeft a (Nat.add 79 (Nat.mul 6 k))))
      (Nat.shiftLeft 1 66) = psE s f (c + 1) (t + a * 2 ^ (6 * k)) K := by
    rw [shl_eq, shl_eq]
    change psE s f c t K + a * 2 ^ (79 + 6 * k) + 1 * 2 ^ 66 = _
    unfold psE
    have h79 : (2 : Nat) ^ 79 = 2 ^ 64 * 4 * 8192 := by norm_num
    have h66 : (2 : Nat) ^ 66 = 2 ^ 64 * 4 := by norm_num
    rw [pow_add 2 79 (6 * k), h79, h66]
    generalize (2 : Nat) ^ 24966 = P
    generalize (2 : Nat) ^ 64 = B
    ring
  have he : Nat.land w 262143 + 2 ^ 18 < 2 ^ 19 := by
    have := Nat.mod_lt w (by positivity : 0 < 2 ^ 18)
    rw [ps_land18]
    norm_num at this ⊢
    omega
  have ht' : t < 2 ^ 24966 := lt_of_le_of_lt (Nat.le_add_right _ _) ht
  unfold insS
  rw [strictN_eq, e1]
  rw [psE_low hs hf hc ht, psE_shr hs hf hc ht, ps_entry]
  have hc' : Nat.lor (Nat.shiftLeft K 19) (Nat.land w 262143 + 2 ^ 18) =
      Nat.lor (Nat.land w 262143 + 2 ^ 18) (Nat.shiftLeft K 19) := Nat.lor_comm _ _
  rw [hc', lor_shl he, psE_lor hs hf hc ht]

theorem psI_resalt {ms : List Nat} {v0 S x : Nat} {L : List Nat} (h : psI ms v0 S L) :
    psI ms v0 (resalt S x) L := by
  obtain ⟨s, f, t, K, hS, hC⟩ := h
  subst hS
  exact ⟨_, f, t, K, psE_resalt hC.1, Nat.mod_lt _ (by positivity), hC.2⟩

theorem ps_ins {ms : List Nat} {v0 s f t K w : Nat} {L : List Nat} (hC : psC ms v0 L s f t K)
    (hw : lead w ≠ 0) (h0 : g6 t (keyOf w) = 0) (hR : Reach ms v0 (Nat.land w 262143)) :
    psI ms v0 (insS (psE s f L.length t K) w (keyOf w) (lead w)) (Nat.land w 262143 :: L) := by
  obtain ⟨hs, hf, ht, hnd, hL, htab, hfl, hstk⟩ := hC
  have hk := ps_keyOf_le w
  have hlen := ps_len hnd
  have ha := lead_lt w
  have htl := ps_tab_lt ha h0 hk ht
  rw [ps_insS hs hf (by omega) htl]
  have hyl := ps_lead_land w
  have hyk := ps_keyOf_land w
  have hy18 : Nat.land w 262143 < 2 ^ 18 := by
    rw [ps_land18]
    exact Nat.mod_lt _ (by positivity)
  generalize Nat.land w 262143 = y at hyl hyk hy18 hR ⊢
  have hne : ∀ z ∈ L, keyOf z ≠ keyOf w := fun z hz e =>
    (hL z hz).1 (by rw [← (hL z hz).2.2.2, e, h0])
  refine ⟨s, f, t + lead w * 2 ^ (6 * keyOf w), y + 2 ^ 18 + K * 2 ^ 19, rfl, hs, hf, htl, ?_,
    ?_, ?_, ?_, psStk_push hstk hy18⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hnd⟩
    obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
    exact hne z hz (e.trans hyk)
  · intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · refine ⟨by rw [hyl]; exact hw, hy18, hR, ?_⟩
      rw [ps_g6_ins ha h0, hyk, if_pos rfl, hyl]
    · obtain ⟨a1, a2, a3, a4⟩ := hL z hz
      exact ⟨a1, a2, a3, by rw [ps_g6_ins ha h0, if_neg (hne z hz), a4]⟩
  · intro j hj hj0
    rw [ps_g6_ins ha h0] at hj0
    by_cases e : j = keyOf w
    · exact ⟨y, List.mem_cons_self, hyk.trans e.symm⟩
    · rw [if_neg e] at hj0
      obtain ⟨z, hz, e'⟩ := htab j hj hj0
      exact ⟨z, List.mem_cons_of_mem _ hz, e'⟩
  · intro b hb
    obtain ⟨y1, h1, m, hm, y2, h2, rest⟩ := hfl b hb
    exact ⟨y1, List.mem_cons_of_mem _ h1, m, hm, y2, List.mem_cons_of_mem _ h2, rest⟩

theorem ps_stepM {ms : List Nat} {v0 S y m : Nat} {L : List Nat} (h : psI ms v0 S L)
    (hy : y ∈ L) (hm : m ∈ ms) : ∃ L', psI ms v0 (stepM S y m) L' ∧ L ⊆ L' := by
  obtain ⟨s, f, t, K, hS, hC⟩ := h
  subst hS
  have hlen := ps_len hC.2.2.2.1
  unfold stepM
  simp only [strictN_eq]
  cases hc : Nat.beq (lead (vmP y m)) 0
  · have hw : lead (vmP y m) ≠ 0 := Nat.ne_of_beq_eq_false hc
    dsimp only
    rw [psE_tab hC.1 hC.2.1 (by omega) (ps_keyOf_le _)]
    cases ht0 : Nat.beq (g6 t (keyOf (vmP y m))) 0
    · have ht0' := Nat.ne_of_beq_eq_false ht0
      dsimp only
      obtain ⟨y', hy', hk'⟩ := hC.2.2.2.2.2.1 _ (Nat.lt_succ_of_le (ps_keyOf_le _)) ht0'
      have hl' : g6 t (keyOf (vmP y m)) = lead y' := by
        rw [← hk']
        exact (hC.2.2.2.2.1 y' hy').2.2.2
      have hg := ps_flagsOf_lt (gm (lead (vmP y m)) (ginv (g6 t (keyOf (vmP y m)))))
      obtain ⟨hs, hf, ht, hnd, hL, htab, hfl, hstk⟩ := hC
      refine ⟨L, psI_resalt ⟨s, Nat.lor f _, t, K, psE_or hs hf hg, hs,
        Nat.or_lt_two_pow (n := 2) hf hg, ht, hnd, hL, htab, fun b hb => ?_, hstk⟩, fun _ h => h⟩
      change (f ||| _).testBit b = true at hb
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · exact hfl b hb
      · rw [hl'] at hb
        exact ⟨y, hy, m, hm, y', hy', hk'.symm, hw, hb⟩
    · have ht0' := Nat.eq_of_beq_eq_true ht0
      dsimp only
      have hR : Reach ms v0 (Nat.land (vmP y m) 262143) := by
        rw [ps_land18, Nat.mod_eq_of_lt (ps_vmP_lt y m)]
        exact Reach.step (hC.2.2.2.2.1 y hy).2.2.1 hm
      exact ⟨_, psI_resalt (ps_ins hC hw ht0' hR), fun _ h => List.mem_cons_of_mem _ h⟩
  · dsimp only
    exact ⟨L, ⟨s, f, t, K, rfl, hC⟩, fun _ h => h⟩

theorem ps_inner {ms : List Nat} {v0 y : Nat} : ∀ ms' : List Nat, (∀ m ∈ ms', m ∈ ms) →
    ∀ S L, psI ms v0 S L → y ∈ L → ∃ L', psI ms v0 (innerL y ms' S) L' := by
  intro ms'
  induction ms' with
  | nil => exact fun _ S L h _ => ⟨L, h⟩
  | cons m ms' ih =>
    intro hms S L h hy
    obtain ⟨L1, h1, hsub⟩ := ps_stepM h hy (hms m List.mem_cons_self)
    have e : innerL y (m :: ms') S = innerL y ms' (stepM S y m) := by
      change strictN (stepM S y m) (innerL y ms') = _
      rw [strictN_eq]
    rw [e]
    exact ih (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm')) _ L1 h1 (hsub hy)

theorem ps_pop {ms : List Nat} {v0 S : Nat} {L : List Nat} (h : psI ms v0 S L) :
    ∃ L', psI ms v0 (popStep ms S) L' := by
  obtain ⟨s, f, t, K, hS, hC⟩ := h
  subst hS
  have hlen := ps_len hC.2.2.2.1
  have hc : L.length < 8192 := by omega
  unfold popStep
  simp only [strictN_eq]
  rw [psE_shr hC.1 hC.2.1 hc hC.2.2.1, ps_land19]
  cases hb : Nat.beq (K % 2 ^ 19) 0
  · have hb' := Nat.ne_of_beq_eq_false hb
    dsimp only
    have hj0 := hC.2.2.2.2.2.2.2 0
    rw [Nat.mul_zero, pow_zero, Nat.div_one] at hj0
    obtain ⟨y, hy, he⟩ := hj0.resolve_left hb'
    have hy18 := (hC.2.2.2.2.1 y hy).2.1
    have hey : Nat.land (K % 2 ^ 19) 262143 = y := by
      rw [ps_land18, he, Nat.add_mod_right, Nat.mod_eq_of_lt hy18]
    rw [psE_low hC.1 hC.2.1 hc hC.2.2.1, ps_shr K 19, psE_lor hC.1 hC.2.1 hc hC.2.2.1, hey]
    obtain ⟨hs, hf, ht, hnd, hL, htab, hfl, hstk⟩ := hC
    exact ps_inner ms (fun _ h => h) _ L
      ⟨s, f, t, K / 2 ^ 19, rfl, hs, hf, ht, hnd, hL, htab, hfl, psStk_pop hstk⟩ hy
  · dsimp only
    exact ⟨L, s, f, t, K, rfl, hC⟩

theorem ps_run (ms : List Nat) {v0 S : Nat} (h : ∃ L, psI ms v0 S L) :
    ∃ L, psI ms v0 (runS ms S) L := by
  have inner : ∀ n S', (∃ L, psI ms v0 S' L) → ∃ L, psI ms v0
      (Nat.rec (motive := fun _ => Nat) S' (fun _ ih2 => strictN ih2 (popStep ms)) n) L := by
    intro n
    induction n with
    | zero => exact fun S' h => h
    | succ n ih =>
      intro S' h
      obtain ⟨L, hL⟩ := ih S' h
      change ∃ L, psI ms v0 (strictN (Nat.rec (motive := fun _ => Nat) S'
        (fun _ ih2 => strictN ih2 (popStep ms)) n) (popStep ms)) L
      rw [strictN_eq]
      exact ps_pop hL
  have outer : ∀ n, ∃ L, psI ms v0 (Nat.rec (motive := fun _ => Nat) S (fun _ ih =>
      strictN ih fun S' => Nat.rec (motive := fun _ => Nat) S'
        (fun _ ih2 => strictN ih2 (popStep ms)) 32) n) L := by
    intro n
    induction n with
    | zero => exact h
    | succ n ih =>
      change ∃ L, psI ms v0 (strictN (Nat.rec (motive := fun _ => Nat) S (fun _ ih =>
        strictN ih fun S' => Nat.rec (motive := fun _ => Nat) S'
          (fun _ ih2 => strictN ih2 (popStep ms)) 32) n) fun S' =>
            Nat.rec (motive := fun _ => Nat) S' (fun _ ih2 => strictN ih2 (popStep ms)) 32) L
      rw [strictN_eq]
      exact inner 32 _ ih
  exact outer 32

theorem ps_init (ms : List Nat) (v : Nat) : ∃ L, psI ms (Nat.land v 262143) (initS v) L := by
  have hS : SALT < 2 ^ 64 := by
    unfold SALT
    norm_num
  have e0 : SALT = psE SALT 0 0 0 0 := by
    unfold psE
    simp
  have hz : ∀ k, g6 0 k = 0 := fun k => by
    rw [g6_eq]
    simp
  have hC0 : psC ms (Nat.land v 262143) [] SALT 0 0 0 :=
    ⟨hS, by norm_num, by positivity, List.nodup_nil, fun y hy => absurd hy List.not_mem_nil,
      fun k _ hk => absurd (hz k) hk, fun b hb => by simp at hb, fun j => Or.inl (by simp)⟩
  unfold initS
  simp only [strictN_eq]
  cases hc : Nat.beq (lead v) 0
  · dsimp only
    have hw := Nat.ne_of_beq_eq_false hc
    have h1 := ps_ins hC0 hw (hz _) Reach.base
    rw [List.length_nil, ← e0] at h1
    exact ⟨_, h1⟩
  · dsimp only
    exact ⟨[], SALT, 0, 0, 0, e0, hC0⟩

end SearchState

theorem searchP_sound (ms : List Nat) (v : Nat) :
    ∃ L : List Nat, L.length = cntOf (searchP ms v) ∧ (L.map keyOf).Nodup ∧
      (∀ y ∈ L, lead y ≠ 0 ∧ Reach ms (Nat.land v 262143) y) ∧
      (∀ b, Nat.testBit (flgOf (searchP ms v)) b = true → ∃ y ∈ L, ∃ m ∈ ms, ∃ y' ∈ L,
        keyOf (vmP y m) = keyOf y' ∧ lead (vmP y m) ≠ 0 ∧
        Nat.testBit (flagsOf (gm (lead (vmP y m)) (ginv (lead y')))) b = true) := by
  obtain ⟨L, s, f, t, K, hS, hs, hf, ht, hnd, hL, -, hfl, -⟩ := ps_run ms (ps_init ms v)
  have hlen := ps_len hnd
  refine ⟨L, ?_, hnd, fun y hy => ⟨(hL y hy).1, (hL y hy).2.2.1⟩, fun b hb => ?_⟩
  · unfold cntOf searchP
    rw [hS, psE_cnt hs hf (by omega)]
  · unfold flgOf searchP at hb
    rw [hS, psE_flg hs hf] at hb
    exact hfl b hb

theorem reach_dec {ms : List Nat} {v y : Nat} (hR : Reach ms v y) {K : Subgroup (GL (Fin 3) GF64)}
    (hm : ∀ m ∈ ms, ∃ g ∈ K, ∀ z : RowVec, Matrix.vecMul z (decP m) = g • z) :
    ∃ h ∈ K, decV y = h • decV v := by
  induction hR with
  | base => exact ⟨1, K.one_mem, (one_smul _ _).symm⟩
  | step _ hmem ih =>
    obtain ⟨h, hK, hy⟩ := ih
    obtain ⟨g, gK, hg⟩ := hm _ hmem
    exact ⟨g * h, K.mul_mem gK hK, by rw [decV_vmP, hg, hy, mul_smul]⟩

theorem projGenK_facts {d : GenData} (h : projGenK d = true) :
    (∀ A ∈ d.gens.toList, isSUArr A = true) ∧ validV d.v0 = true ∧
    (∀ w ∈ d.words, ∀ l ∈ w, l / 2 < d.gens.size) ∧
    (∀ u ∈ wordsP (gensP d) (conjL (gensP d)) d.words, vmP (packV d.v0) u = packV d.v0) ∧
    cntOf (searchP (gensP d) (packV d.v0)) = 513 ∧ flgOf (searchP (gensP d) (packV d.v0)) = 3 ∧
    cntOf (searchP (wordsP (gensP d) (conjL (gensP d)) d.words)
      (startP (gensP d) (packV d.v0))) = 512 := by
  unfold projGenK searchK at h
  simp only [andB_eq_true, forceL_eq, strictB_eq, allL_eq_true] at h
  obtain ⟨h1, h2, h3, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, fun w hw l hl => ?_, fun u hu => Nat.eq_of_beq_eq_true (h5 u hu),
    Nat.eq_of_beq_eq_true h6, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8⟩
  have := h3 w hw l hl
  simp only [Nat.blt_eq] at this
  exact this

theorem closure_genSet_eq_top_of_card {d : GenData}
    (hG : ∀ k < d.gens.size, isSUArr (d.gens.getD k #[]) = true)
    (hcard : 16547328 ≤ Nat.card (Hc d)) : Subgroup.closure (genSet d) = ⊤ := by
  have hHcSU : Hc d ≤ SU := by
    rw [Hc, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact SU.inv_mem (GLof_mem (hG k hk))
  have hHcEq : Hc d = SU := Subgroup.eq_of_le_of_card_ge hHcSU (by rw [card_SU]; exact hcard)
  have hmap : (Subgroup.closure (genSet d)).map SU.subtype = Hc d := by
    rw [MonoidHom.map_closure]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨g, ⟨k, hk, hgk⟩, rfl⟩
      have : (g : GL (Fin 3) GF64) = Mg d k :=
        Units.ext (by rw [hgk]; exact (coe_GLof (hG k hk)).symm)
      rw [Subgroup.coe_subtype, this]
      exact Mg_mem_Hc d hk
    · rw [Hc, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      refine (Subgroup.closure (SU.subtype '' genSet d)).inv_mem (Subgroup.subset_closure ?_)
      refine ⟨⟨Mg d k, GLof_mem (hG k hk)⟩, ⟨k, hk, ?_⟩, rfl⟩
      exact coe_GLof (hG k hk)
  rw [eq_top_iff]
  intro g _
  have hg : (g : GL (Fin 3) GF64) ∈ (Subgroup.closure (genSet d)).map SU.subtype := by
    rw [hmap, hHcEq]
    exact g.2
  obtain ⟨x, hx, hxg⟩ := hg
  have : x = g := Subtype.ext hxg
  rw [← this]
  exact hx

theorem mem_gensP {d : GenData} {m : Nat} (hm : m ∈ gensP d) :
    ∃ k < d.gens.size, m = packA (d.gens.getD k #[]) := by
  rw [← length_gensP]
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  refine ⟨k, hk, ?_⟩
  rw [← getL_gensP, getL_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem closure_genSet_eq_top_of_projGenK {d : GenData} (h : projGenK d = true) :
    Subgroup.closure (genSet d) = ⊤ := by
  obtain ⟨hA, hv0, hw, hfix, hc1, hf1, hc2⟩ := projGenK_facts h
  have hG : ∀ k < d.gens.size, isSUArr (d.gens.getD k #[]) = true := by
    intro k hk
    apply hA
    have e : d.gens.getD k #[] = d.gens[k] := by simp [Array.getD_eq_getD_getElem?, hk]
    rw [e]
    exact Array.getElem_mem_toList hk
  refine closure_genSet_eq_top_of_card hG ?_
  set x : RowVec := vecOf d.v0 with hxdef
  have hx : decV (packV d.v0) = x := decV_packV hv0
  have hm1 : ∀ m ∈ gensP d, ∃ g ∈ Hc d, ∀ z : RowVec, Matrix.vecMul z (decP m) = g • z := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_gensP hm
    refine ⟨(Mg d k)⁻¹, Subgroup.subset_closure ⟨k, hk, rfl⟩, fun z => ?_⟩
    rw [smul_rowVec, inv_inv, Mg, coe_GLof (hG k hk), decP_packA]
  have hmU : ∀ m ∈ wordsP (gensP d) (conjL (gensP d)) d.words,
      ∃ g ∈ Hc d ⊓ MulAction.stabilizer (GL (Fin 3) GF64) x,
        ∀ z : RowVec, Matrix.vecMul z (decP m) = g • z := by
    intro m hm
    have hm' := hm
    rw [wordsP_eq] at hm'
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hm'
    have hsu := isSUArr_wordArr3 hG (hw w hwm)
    have hact : ∀ z : RowVec, Matrix.vecMul z (decP (wordP (gensP d) (conjL (gensP d)) w)) =
        (GLof (wordArr3 d.gens w))⁻¹ • z := by
      intro z
      rw [smul_rowVec, inv_inv, coe_GLof hsu, decP_wordP d (hw w hwm)]
    refine ⟨(GLof (wordArr3 d.gens w))⁻¹, Subgroup.mem_inf.2 ⟨(Hc d).inv_mem
      (GLof_word_mem d hG (hw w hwm)), ?_⟩, hact⟩
    rw [MulAction.mem_stabilizer_iff, ← hact, ← hx, ← decV_vmP, hfix _ hm]
  obtain ⟨L1, hl1, hn1, hy1, hfl1⟩ := searchP_sound (gensP d) (packV d.v0)
  have hr1 : ∀ y ∈ L1, lc (decV y) ≠ 0 ∧ ∃ h ∈ Hc d, decV y = h • x := by
    intro y hy
    obtain ⟨hl, hR⟩ := hy1 y hy
    refine ⟨lc_ne_of_lead hl, ?_⟩
    obtain ⟨g, hg, e⟩ := reach_dec hR hm1
    exact ⟨g, hg, by rw [e, decV_land, hx]⟩
  have hflag : ∀ b, Nat.testBit (flgOf (searchP (gensP d) (packV d.v0))) b = true →
      ∃ c < 64, ∃ hc : GF64.ofNat' c ≠ 0, c ≠ 0 ∧ Nat.testBit (flagsOf c) b = true ∧
        Units.mk0 _ hc ∈ scal (Hc d) x := by
    intro b hb
    obtain ⟨y, hy, m, hm, y', hy', hk, hl, hbit⟩ := hfl1 b hb
    obtain ⟨hly, h, hh, eh⟩ := hr1 y hy
    obtain ⟨hly', h', hh', eh'⟩ := hr1 y' hy'
    obtain ⟨g, hg, eg⟩ := hm1 m hm
    have ht0 : lead y' ≠ 0 := (hy1 y' hy').1
    have hμ : GF64.ofNat' (gm (lead (vmP y m)) (ginv (lead y'))) =
        lc (decV (vmP y m)) * (lc (decV y'))⁻¹ := by
      rw [gm_spec (lead_lt _) (ginv_lt _), ginv_spec (lead_lt _) ht0, lead_spec, lead_spec]
    have hne : GF64.ofNat' (gm (lead (vmP y m)) (ginv (lead y'))) ≠ 0 := by
      rw [hμ]
      exact mul_ne_zero (lc_ne_of_lead hl) (inv_ne_zero hly')
    refine ⟨_, gm_lt _ _, hne, fun h0 => hne (by rw [h0]; rfl), hbit, ?_⟩
    have hnorm := eq_smul_of_keyN_eq (lc_ne_of_lead hl) hly'
      (by rw [← keyOf_spec, ← keyOf_spec, hk])
    rw [← hμ] at hnorm
    refine ⟨h'⁻¹ * (g * h), (Hc d).mul_mem ((Hc d).inv_mem hh') ((Hc d).mul_mem hg hh), ?_⟩
    rw [Units.val_mk0, mul_smul, mul_smul, ← eh, ← eg, ← decV_vmP, hnorm, eh', smul_smulV,
      inv_smul_smul]
  have hf3 : flgOf (searchP (gensP d) (packV d.v0)) = 3 := hf1
  obtain ⟨c1, c1lt, c1ne, c1z, hb1, hm1'⟩ := hflag 0 (by rw [hf3]; rfl)
  obtain ⟨c2, c2lt, c2ne, c2z, hb2, hm2'⟩ := hflag 1 (by rw [hf3]; rfl)
  have hM : 63 ≤ Nat.card (scal (Hc d) x) :=
    le_card_of_flags c1ne c2ne hm1' hm2' ((flags_spec_fin ⟨c1, c1lt⟩ c1z).1 hb1)
      ((flags_spec_fin ⟨c2, c2lt⟩ c2z).2 hb2)
  have hkeyinj : ∀ (L : List Nat), (L.map keyOf).Nodup → ∀ i j : Fin L.length,
      keyOf (L.get i) = keyOf (L.get j) → i = j := by
    intro L hn i j hij
    have hn' := List.Nodup.of_map keyOf hn
    refine (List.Nodup.get_inj_iff hn').1 ?_
    have hi : i.val < (L.map keyOf).length := by simp
    have hj : j.val < (L.map keyOf).length := by simp
    have := (List.Nodup.getElem_inj_iff hn (hi := hi) (hj := hj)).1 (by simpa using hij)
    exact congrArg L.get (Fin.ext this)
  have horb : 63 * 513 ≤ (MulAction.orbit (Hc d) x).ncard := by
    let f : scal (Hc d) x × Fin L1.length → MulAction.orbit (Hc d) x := fun p =>
      ⟨smulV ((p.1 : GF64ˣ) : GF64) (decV (L1.get p.2)), by
        obtain ⟨k, hk, ek⟩ := mem_scal.1 p.1.2
        obtain ⟨-, h, hh, eh⟩ := hr1 _ (List.get_mem L1 p.2)
        refine MulAction.mem_orbit_iff.2 ⟨⟨h * k, (Hc d).mul_mem hh hk⟩, ?_⟩
        change (h * k) • x = _
        rw [mul_smul, ek, smul_smulV, ← eh]⟩
    have hf : Function.Injective f := by
      rintro ⟨u, i⟩ ⟨u', j⟩ he
      have he' : smulV ((u : GF64ˣ) : GF64) (decV (L1.get i)) =
          smulV ((u' : GF64ˣ) : GF64) (decV (L1.get j)) := congrArg Subtype.val he
      have hkey : keyOf (L1.get i) = keyOf (L1.get j) := by
        rw [keyOf_spec, keyOf_spec, ← keyN_smul (u : GF64ˣ).ne_zero (decV (L1.get i)), he',
          keyN_smul (u' : GF64ˣ).ne_zero]
      have hij := hkeyinj L1 hn1 i j hkey
      subst hij
      have hl := (hr1 _ (List.get_mem L1 i)).1
      have hc := congrArg lc he'
      rw [lc_smul (u : GF64ˣ).ne_zero, lc_smul (u' : GF64ˣ).ne_zero] at hc
      have huu : ((u : GF64ˣ) : GF64) = ((u' : GF64ˣ) : GF64) := mul_right_cancel₀ hl hc
      exact Prod.ext (Subtype.ext (Units.ext huu)) rfl
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin L1.length), Fintype.card_fin, hl1, hc1,
      Nat.card_coe_set_eq] at this
    exact (Nat.mul_le_mul_right 513 hM).trans this
  obtain ⟨L2, hl2, hn2, hy2, -⟩ := searchP_sound (wordsP (gensP d) (conjL (gensP d)) d.words)
    (startP (gensP d) (packV d.v0))
  have hr2 : ∀ i : Fin L2.length, ∃ h ∈ Hc d ⊓ MulAction.stabilizer (GL (Fin 3) GF64) x,
      decV (L2.get i) = h • decV (Nat.land (startP (gensP d) (packV d.v0)) 262143) :=
    fun i => reach_dec (hy2 _ (List.get_mem L2 i)).2 hmU
  choose f hfK hfe using hr2
  have hstab : 512 ≤ Nat.card (MulAction.stabilizer (Hc d) x) := by
    let F : Fin L2.length → MulAction.stabilizer (Hc d) x := fun i =>
      ⟨⟨f i, (Subgroup.mem_inf.1 (hfK i)).1⟩, by
        rw [MulAction.mem_stabilizer_iff]
        exact (Subgroup.mem_inf.1 (hfK i)).2⟩
    have hF : Function.Injective F := by
      intro i j hij
      have e : f i = f j := congrArg (fun s : MulAction.stabilizer (Hc d) x =>
        ((s : Hc d) : GL (Fin 3) GF64)) hij
      apply hkeyinj L2 hn2 i j
      rw [keyOf_spec, keyOf_spec, hfe, hfe, e]
    have := Nat.card_le_card_of_injective F hF
    rwa [Nat.card_eq_fintype_card (α := Fin L2.length), Fintype.card_fin, hl2, hc2] at this
  have hcard : Nat.card (Hc d) =
      (MulAction.orbit (Hc d) x).ncard * Nat.card (MulAction.stabilizer (Hc d) x) := by
    rw [← Subgroup.index_mul_card (MulAction.stabilizer (Hc d) x), MulAction.index_stabilizer]
  rw [hcard]
  calc 16547328 = (63 * 513) * 512 := by norm_num
    _ ≤ _ := Nat.mul_le_mul horb hstab

end CFSG.KC.U38PG
