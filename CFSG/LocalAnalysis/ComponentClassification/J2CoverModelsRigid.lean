module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsOuter

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

structure TwistData (R : Type*) [Group R] where
  τ : R ≃* R
  z : R
  ε : ZMod 2
  τ_τ : ∀ x, τ (τ x) = x
  τ_z : τ z = z
  z_mul : ∀ x, z * x = x * z
  z_z : z * z = 1

@[ext] structure TwistExt {R : Type*} [Group R] (D : TwistData R) where
  x : R
  e : ZMod 2

namespace TwistExt

variable {R : Type*} [Group R] (D : TwistData R)

@[expose] def tauPow (e : ZMod 2) (y : R) : R := if e = 0 then y else D.τ y

@[expose] def zPow (k : ZMod 2) : R := if k = 0 then 1 else D.z

theorem zmod_two_cases (e : ZMod 2) : e = 0 ∨ e = 1 := by
  fin_cases e
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem tauPow_zero (y : R) : tauPow D 0 y = y := by simp [tauPow]

theorem tauPow_one (y : R) : tauPow D 1 y = D.τ y := by simp [tauPow]

theorem zPow_zero : zPow D 0 = 1 := by simp [zPow]

theorem zPow_one : zPow D 1 = D.z := by simp [zPow]

theorem tauPow_mul (e : ZMod 2) (a b : R) : tauPow D e (a * b) = tauPow D e a * tauPow D e b := by
  rcases zmod_two_cases e with rfl | rfl
  · simp only [tauPow_zero]
  · simp only [tauPow_one, map_mul]

theorem tauPow_one_elt (e : ZMod 2) : tauPow D e 1 = 1 := by
  rcases zmod_two_cases e with rfl | rfl
  · rw [tauPow_zero]
  · rw [tauPow_one, map_one]

theorem tauPow_inv (e : ZMod 2) (a : R) : tauPow D e a⁻¹ = (tauPow D e a)⁻¹ := by
  rcases zmod_two_cases e with rfl | rfl
  · simp only [tauPow_zero]
  · simp only [tauPow_one, map_inv]

theorem tauPow_add (e d : ZMod 2) (y : R) : tauPow D (e + d) y = tauPow D e (tauPow D d y) := by
  rcases zmod_two_cases e with rfl | rfl <;> rcases zmod_two_cases d with rfl | rfl
  · simp only [add_zero, tauPow_zero]
  · simp only [zero_add, tauPow_zero]
  · simp only [add_zero, tauPow_zero]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, tauPow_zero, tauPow_one, tauPow_one, D.τ_τ]

theorem tauPow_zPow (e k : ZMod 2) : tauPow D e (zPow D k) = zPow D k := by
  rcases zmod_two_cases e with rfl | rfl <;> rcases zmod_two_cases k with rfl | rfl
  · rw [tauPow_zero]
  · rw [tauPow_zero]
  · rw [tauPow_one, zPow_zero, map_one]
  · rw [tauPow_one, zPow_one, D.τ_z]

theorem zPow_mul_comm (k : ZMod 2) (a : R) : zPow D k * a = a * zPow D k := by
  rcases zmod_two_cases k with rfl | rfl
  · rw [zPow_zero, one_mul, mul_one]
  · rw [zPow_one, D.z_mul]

theorem zPow_add (k l : ZMod 2) : zPow D (k + l) = zPow D k * zPow D l := by
  rcases zmod_two_cases k with rfl | rfl <;> rcases zmod_two_cases l with rfl | rfl
  · rw [add_zero, zPow_zero, one_mul]
  · rw [zero_add, zPow_zero, one_mul]
  · rw [add_zero, zPow_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, zPow_zero, zPow_one, D.z_z]

theorem zPow_mul_self (k : ZMod 2) : zPow D k * zPow D k = 1 := by
  rw [← zPow_add, show k + k = 0 by grind, zPow_zero]

variable {D}

instance : Mul (TwistExt D) :=
  ⟨fun p q => ⟨p.x * tauPow D p.e q.x * zPow D (D.ε * p.e * q.e), p.e + q.e⟩⟩

instance : One (TwistExt D) := ⟨⟨1, 0⟩⟩

instance : Inv (TwistExt D) := ⟨fun p => ⟨tauPow D p.e (p.x⁻¹ * zPow D (D.ε * p.e * p.e)), p.e⟩⟩

theorem mul_x (p q : TwistExt D) : (p * q).x = p.x * tauPow D p.e q.x * zPow D (D.ε * p.e * q.e) :=
  rfl

theorem mul_e (p q : TwistExt D) : (p * q).e = p.e + q.e := rfl

theorem one_x : (1 : TwistExt D).x = 1 := rfl

theorem one_e : (1 : TwistExt D).e = 0 := rfl

theorem inv_x (p : TwistExt D) : p⁻¹.x = tauPow D p.e (p.x⁻¹ * zPow D (D.ε * p.e * p.e)) := rfl

theorem inv_e (p : TwistExt D) : p⁻¹.e = p.e := rfl

instance : Group (TwistExt D) where
  mul_assoc p q r := by
    refine TwistExt.ext ?_ ?_
    · rw [mul_x, mul_x, mul_x, mul_x, mul_e, mul_e, tauPow_mul, tauPow_mul, tauPow_zPow,
        tauPow_add]
      have h1 : p.x * tauPow D p.e q.x * zPow D (D.ε * p.e * q.e) *
          tauPow D p.e (tauPow D q.e r.x) * zPow D (D.ε * (p.e + q.e) * r.e) =
          p.x * tauPow D p.e q.x * tauPow D p.e (tauPow D q.e r.x) *
            (zPow D (D.ε * p.e * q.e) * zPow D (D.ε * (p.e + q.e) * r.e)) := by
        rw [mul_assoc (p.x * tauPow D p.e q.x), zPow_mul_comm, ← mul_assoc, mul_assoc]
      have h2 : p.x * (tauPow D p.e q.x * tauPow D p.e (tauPow D q.e r.x) *
          zPow D (D.ε * q.e * r.e)) * zPow D (D.ε * p.e * (q.e + r.e)) =
          p.x * tauPow D p.e q.x * tauPow D p.e (tauPow D q.e r.x) *
            (zPow D (D.ε * q.e * r.e) * zPow D (D.ε * p.e * (q.e + r.e))) := by
        simp only [mul_assoc]
      rw [h1, h2, ← zPow_add, ← zPow_add]
      congr 2
      ring
    · rw [mul_e, mul_e, mul_e, mul_e, add_assoc]
  one_mul p := by
    refine TwistExt.ext ?_ ?_
    · rw [mul_x, one_x, one_e, one_mul, tauPow_zero, mul_zero, zero_mul, zPow_zero, mul_one]
    · rw [mul_e, one_e, zero_add]
  mul_one p := by
    refine TwistExt.ext ?_ ?_
    · rw [mul_x, one_x, one_e, mul_zero, zPow_zero, mul_one, tauPow_one_elt, mul_one]
    · rw [mul_e, one_e, add_zero]
  inv_mul_cancel p := by
    refine TwistExt.ext ?_ ?_
    · rw [mul_x, inv_x, inv_e, one_x, tauPow_mul, tauPow_zPow,
        mul_assoc (tauPow D p.e p.x⁻¹), zPow_mul_comm, ← mul_assoc, ← tauPow_mul, inv_mul_cancel,
        tauPow_one_elt, one_mul, zPow_mul_self]
    · rw [mul_e, inv_e, one_e]
      grind

theorem card_twistExt [Finite R] : Nat.card (TwistExt D) = Nat.card R * 2 := by
  have e : TwistExt D ≃ R × ZMod 2 := ⟨fun p => (p.x, p.e), fun q => ⟨q.1, q.2⟩, fun _ => rfl,
    fun _ => rfl⟩
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]

end TwistExt

@[expose] noncomputable def rootPair {G : Type*} [Group G] (w : G) : ℕ × ℕ :=
  (Nat.card {x : G // x ^ 2 = w}, Nat.card {x : G // x ^ 4 = w})

theorem rootPair_map {G : Type*} [Group G] (φ : G ≃* G) (w : G) : rootPair (φ w) = rootPair w := by
  have h : ∀ n : ℕ, Nat.card {x : G // x ^ n = φ w} = Nat.card {x : G // x ^ n = w} := fun n =>
    (Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun x => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow,
        EmbeddingLike.apply_eq_iff_eq])).symm
  rw [rootPair, rootPair, h 2, h 4]

theorem aut_fix_of_rootPair {G : Type*} [Group G] (φ : G ≃* G) (z : G)
    (hz : z ∈ Subgroup.center G) (hz1 : z ≠ 1) (zs : List G)
    (hc : ∀ w ∈ Subgroup.center G, w = 1 ∨ w ∈ zs)
    (hd : ∀ w ∈ zs, rootPair w = rootPair z → w = z) : φ z = z := by
  have hφz : φ z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨h, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hz h]
  rcases hc _ hφz with h | h
  · exact absurd (φ.injective (h.trans (map_one φ).symm)) hz1
  · exact hd _ h (rootPair_map φ z)

structure Coding (G : Type*) [Group G] (n : ℕ) (mul : ℕ → ℕ → ℕ) where
  enc : G ≃ Fin n
  enc_mul : ∀ x y, (enc (x * y) : ℕ) = mul (enc x) (enc y)

namespace Coding

variable {G : Type*} [Group G] {n : ℕ} {mul : ℕ → ℕ → ℕ} (C : Coding G n mul)

theorem mem_center_iff (x : G) :
    x ∈ Subgroup.center G ↔ allLt n (fun c => mul (C.enc x) c == mul c (C.enc x)) = true := by
  rw [Subgroup.mem_center_iff, allLt_iff]
  constructor
  · intro h c hc
    have := h (C.enc.symm ⟨c, hc⟩)
    rw [beq_iff_eq]
    have h1 := C.enc_mul x (C.enc.symm ⟨c, hc⟩)
    have h2 := C.enc_mul (C.enc.symm ⟨c, hc⟩) x
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, this]
  · intro h y
    have := h (C.enc y) (C.enc y).isLt
    rw [beq_iff_eq, ← C.enc_mul, ← C.enc_mul] at this
    exact (C.enc.injective (Fin.ext this)).symm

theorem card_pow_eq (w : G) (k : ℕ) (f : ℕ → ℕ)
    (hf : ∀ x : G, (C.enc (x ^ k) : ℕ) = f (C.enc x)) :
    Nat.card {x : G // x ^ k = w} = countFold n fun c => f c == C.enc w := by
  have e : {x : G // x ^ k = w} ≃ {c : Fin n // f c = C.enc w} :=
    Equiv.subtypeEquiv C.enc fun x => by
      rw [← hf, ← Fin.ext_iff]
      exact C.enc.injective.eq_iff.symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    countFold_eq]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : f c = C.enc w
  · rw [ite_eq_left hc, ite_eq_left (by rw [beq_iff_eq]; exact hc)]
  · rw [ite_eq_right hc, ite_eq_right (by rw [beq_iff_eq]; exact hc)]

end Coding


theorem card_center_of_codes {G : Type*} [Group G] {n : ℕ} {mul : ℕ → ℕ → ℕ} (C : Coding G n mul)
    (hn : 133 ≤ n) (h : ∀ x : G, x ∈ Subgroup.center G ↔ (C.enc x : ℕ) ∈ [0, 4, 128, 132]) :
    Nat.card (Subgroup.center G) = 4 := by
  have e : Subgroup.center G ≃ {c : Fin n // (c : ℕ) ∈ [0, 4, 128, 132]} :=
    Equiv.subtypeEquiv C.enc fun x => h x
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun c : Fin n => (c : ℕ) ∈ [0, 4, 128, 132]) =
      {⟨0, by omega⟩, ⟨4, by omega⟩, ⟨128, by omega⟩, ⟨132, by omega⟩} := by
    ext c
    simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  rw [this, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_pair (by simp [Fin.ext_iff])]

theorem zmod_two_val_lt (e : ZMod 2) : e.val < 2 := ZMod.val_lt e

@[expose] noncomputable def codeR (x : Rf) : ℕ := idx x.g + 128 * x.e.val

theorem codeR_lt (x : Rf) : codeR x < 256 := by
  have := idx_lt x.g
  have := zmod_two_val_lt x.e
  rw [codeR]
  omega

theorem codeR_mod (x : Rf) : codeR x % 128 = idx x.g := by
  have := idx_lt x.g
  rw [codeR]
  omega

theorem codeR_div (x : Rf) : codeR x / 128 = x.e.val := by
  have := idx_lt x.g
  rw [codeR]
  omega

theorem val_ite (b : Bool) : ((if b then 1 else 0 : ZMod 2)).val = if b then 1 else 0 := by
  cases b <;> rfl

theorem val_add_two (a b : ZMod 2) : (a + b).val = (a.val + b.val) % 2 := ZMod.val_add a b

theorem codeR_mul (x y : Rf) : codeR (x * y) = mulR (codeR x) (codeR y) := by
  obtain ⟨hm1, hm2⟩ := mulIdx_spec (a := idx x.g) (idx_lt y.g)
  rw [elt_idx, elt_idx] at hm2
  have hg : idx (x * y).g = mulIdx (idx x.g) (idx y.g) := by
    rw [CocExt.mul_g, ← hm2, idx_elt hm1]
  have he : (x * y).e.val = (x.e.val + y.e.val +
      (if bitAt fRows (idx x.g) (idx y.g) then 1 else 0)) % 2 := by
    rw [CocExt.mul_e, fNorm_toFun, fCoc, tbl, val_add_two, val_add_two, val_ite]
    omega
  rw [mulR, codeR_mod, codeR_mod, codeR_div, codeR_div, mulTab_get (idx_lt _) (idx_lt _), codeR,
    hg, he]

@[expose] noncomputable def decodeR (c : ℕ) : Rf := ⟨((c / 128 : ℕ) : ZMod 2), elt (c % 128)⟩

theorem decodeR_codeR (x : Rf) : decodeR (codeR x) = x := by
  refine CocExt.ext ?_ ?_
  · rw [decodeR, codeR_div, ZMod.natCast_zmod_val]
  · rw [decodeR, codeR_mod, elt_idx]

theorem codeR_decodeR {c : ℕ} (hc : c < 256) : codeR (decodeR c) = c := by
  have h1 : c % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have h2 : ((c / 128 : ℕ) : ZMod 2).val = c / 128 := by
    rw [ZMod.val_natCast]
    omega
  rw [codeR, decodeR]
  simp only
  rw [idx_elt h1, h2]
  omega

@[expose] noncomputable def codingR : Coding Rf 256 mulR where
  enc := ⟨fun x => ⟨codeR x, codeR_lt x⟩, fun c => decodeR c, decodeR_codeR,
    fun c => Fin.ext (codeR_decodeR c.isLt)⟩
  enc_mul := codeR_mul

theorem codingR_enc (x : Rf) : (codingR.enc x : ℕ) = codeR x := rfl

theorem codeR_tauR (x : Rf) : codeR (tauR x) = tauC (codeR x) := by
  have hb : idx (tauR x).g = betaTab[idx x.g]! := by
    rw [tauR_g, betaTab_get (idx_lt _)]
    conv_lhs => rw [← elt_idx x.g, betaS_elt (idx_lt _)]
    exact idx_elt (betaIdx_lt (idx_lt _))
  have he : (tauR x).e.val = (x.e.val + (if lamBit (idx x.g) then 1 else 0)) % 2 := by
    rw [tauR_e, val_add_two, lamCoch, mk1, val_ite]
    rfl
  rw [tauC, codeR_mod, codeR_div, codeR, hb, he]

@[expose] noncomputable def zR : Rf := ⟨0, elt 4⟩

theorem codeR_one : codeR 1 = 0 := by
  rw [codeR, CocExt.one_g, CocExt.one_e, ← elt_zero, idx_elt (by norm_num)]
  rfl

theorem codeR_zR : codeR zR = 4 := by
  rw [codeR, zR]
  simp only
  rw [idx_elt (by norm_num)]
  rfl

theorem codeR_central : codeR CocExt.central = 128 := by
  rw [codeR, CocExt.central]
  simp only
  rw [← elt_zero, idx_elt (by norm_num)]
  rfl

theorem zR_mul_central : zR * CocExt.central = ⟨1, elt 4⟩ := by
  refine CocExt.ext ?_ ?_
  · rw [CocExt.mul_e, zR, CocExt.central]
    simp only
    rw [fNorm_toFun, isNormCocycle_fCoc.2.1, zero_add, add_zero]
  · rw [CocExt.mul_g, zR, CocExt.central]
    simp only
    rw [mul_one]

theorem codeR_zR_central : codeR (zR * CocExt.central) = 132 := by
  rw [zR_mul_central, codeR]
  simp only
  rw [idx_elt (by norm_num)]
  rfl

theorem groupCheck_parts :
    centerOK 256 mulR = true ∧ rootCounts 256 mulR = [(0, 0), (48, 0), (40, 96)] ∧
    centerOK 512 (mulT 0) = true ∧ rootCounts 512 (mulT 0) = [(0, 0), (48, 64), (56, 160)] ∧
    centerOK 512 (mulT 1) = true ∧
      rootCounts 512 (mulT 1) = [(16, 0), (96, 64), (40, 160)] := by
  have h := groupCheck_eq
  simp only [groupCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem mem_center_of_centerOK {G : Type*} [Group G] {n : ℕ} {mul : ℕ → ℕ → ℕ}
    (C : Coding G n mul) (h : centerOK n mul = true) (x : G) :
    x ∈ Subgroup.center G ↔ (C.enc x : ℕ) ∈ [0, 4, 128, 132] := by
  rw [C.mem_center_iff]
  have := allLt_spec h (C.enc x).isLt
  rw [beq_iff_eq] at this
  rw [this]
  simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

theorem rootPair_of_codes {G : Type*} [Group G] {n : ℕ} {mul : ℕ → ℕ → ℕ} (C : Coding G n mul)
    (w : G) : rootPair w = (sqCount n mul (C.enc w), fourthCount n mul (C.enc w)) := by
  rw [rootPair, C.card_pow_eq w 2 (fun c => mul c c) (fun x => by rw [pow_two, C.enc_mul]),
    C.card_pow_eq w 4 (fun c => mul (mul c c) (mul c c)) (fun x => by
      rw [show x ^ 4 = x ^ 2 * x ^ 2 by group, C.enc_mul, pow_two, C.enc_mul])]
  rfl

theorem mem_center_Rf (x : Rf) :
    x ∈ Subgroup.center Rf ↔ x = 1 ∨ x = zR ∨ x = CocExt.central ∨ x = zR * CocExt.central := by
  rw [mem_center_of_centerOK codingR groupCheck_parts.1, codingR_enc]
  have hinj : ∀ y : Rf, codeR x = codeR y ↔ x = y := fun y =>
    ⟨fun h => by rw [← decodeR_codeR x, h, decodeR_codeR], fun h => by rw [h]⟩
  rw [← hinj 1, ← hinj zR, ← hinj CocExt.central, ← hinj (zR * CocExt.central), codeR_one, codeR_zR,
    codeR_central, codeR_zR_central]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem rootPair_Rf : rootPair zR = (0, 0) ∧ rootPair (CocExt.central : Rf) = (48, 0) ∧
    rootPair (zR * CocExt.central) = (40, 96) := by
  have h := groupCheck_parts.2.1
  rw [rootCounts] at h
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at h
  rw [rootPair_of_codes codingR, rootPair_of_codes codingR, rootPair_of_codes codingR,
    codingR_enc, codingR_enc, codingR_enc, codeR_zR, codeR_central, codeR_zR_central]
  exact ⟨Prod.ext h.1.1 h.1.2, Prod.ext h.2.1.1 h.2.1.2, Prod.ext h.2.2.1 h.2.2.2⟩


@[expose] noncomputable def tData (ε : ZMod 2) : TwistData Rf where
  τ := tauR
  z := CocExt.central
  ε := ε
  τ_τ := tauR_tauR
  τ_z := tauR_central
  z_mul := CocExt.central_mul
  z_z := CocExt.central_mul_central

abbrev Teps (ε : ZMod 2) : Type := TwistExt (tData ε)

abbrev T0 : Type := Teps 0

abbrev T1 : Type := Teps 1

@[expose] noncomputable def codeT {ε : ZMod 2} (p : Teps ε) : ℕ := codeR p.x + 256 * p.e.val

theorem codeT_mod {ε : ZMod 2} (p : Teps ε) : codeT p % 256 = codeR p.x := by
  have := codeR_lt p.x
  rw [codeT]
  omega

theorem codeT_div {ε : ZMod 2} (p : Teps ε) : codeT p / 256 = p.e.val := by
  have := codeR_lt p.x
  rw [codeT]
  omega

theorem codeT_lt {ε : ZMod 2} (p : Teps ε) : codeT p < 512 := by
  have := codeR_lt p.x
  have := zmod_two_val_lt p.e
  rw [codeT]
  omega

theorem codeR_tauPow {ε : ZMod 2} (e : ZMod 2) (y : Rf) :
    codeR (TwistExt.tauPow (tData ε) e y) =
      if e.val = 1 then tauC (codeR y) else codeR y := by
  rcases TwistExt.zmod_two_cases e with rfl | rfl
  · rw [TwistExt.tauPow_zero, ite_eq_right (by decide)]
  · rw [TwistExt.tauPow_one, ite_eq_left (by decide)]
    exact codeR_tauR y

theorem codeR_mul_zPow {ε : ZMod 2} (k : ZMod 2) (r : Rf) :
    codeR (r * TwistExt.zPow (tData ε) k) = if k = 1 then mulR (codeR r) 128 else codeR r := by
  rcases TwistExt.zmod_two_cases k with rfl | rfl
  · rw [TwistExt.zPow_zero, mul_one, ite_eq_right (by decide)]
  · rw [TwistExt.zPow_one, ite_eq_left rfl, codeR_mul,
      show (tData ε).z = CocExt.central from rfl, codeR_central]

theorem codeT_mul {ε : ZMod 2} (p q : Teps ε) : codeT (p * q) = mulT ε.val (codeT p) (codeT q) := by
  rw [mulT, codeT_mod, codeT_mod, codeT_div, codeT_div, codeT, TwistExt.mul_x, TwistExt.mul_e,
    codeR_mul_zPow, codeR_mul, codeR_tauPow, val_add_two]
  have hε : (tData ε).ε = ε := rfl
  have hc : (ε * p.e * q.e = 1) = (ε.val = 1 ∧ p.e.val = 1 ∧ q.e.val = 1) := by
    rcases TwistExt.zmod_two_cases ε with rfl | rfl <;>
      rcases TwistExt.zmod_two_cases p.e with h1 | h1 <;>
      rcases TwistExt.zmod_two_cases q.e with h2 | h2 <;> rw [h1, h2] <;> decide
  rw [hε]
  simp only [hc]

@[expose] noncomputable def decodeT (ε : ZMod 2) (c : ℕ) : Teps ε :=
  ⟨decodeR (c % 256), ((c / 256 : ℕ) : ZMod 2)⟩

@[expose] noncomputable def codingT (ε : ZMod 2) : Coding (Teps ε) 512 (mulT ε.val) where
  enc := ⟨fun p => ⟨codeT p, codeT_lt p⟩, fun c => decodeT ε c, fun p => by
      refine TwistExt.ext ?_ ?_
      · change decodeR (codeT p % 256) = p.x
        rw [codeT_mod, decodeR_codeR]
      · change ((codeT p / 256 : ℕ) : ZMod 2) = p.e
        rw [codeT_div, ZMod.natCast_zmod_val],
    fun c => by
      apply Fin.ext
      change codeR (decodeR (c % 256)) + 256 * ((c / 256 : ℕ) : ZMod 2).val = c
      have h1 : (c : ℕ) % 256 < 256 := Nat.mod_lt _ (by norm_num)
      have h2 : ((c / 256 : ℕ) : ZMod 2).val = c / 256 := by
        rw [ZMod.val_natCast]
        have := c.isLt
        omega
      rw [codeR_decodeR h1, h2]
      omega⟩
  enc_mul := codeT_mul

theorem codingT_enc (ε : ZMod 2) (p : Teps ε) : ((codingT ε).enc p : ℕ) = codeT p := rfl

@[expose] noncomputable def zT (ε : ZMod 2) : Teps ε := ⟨zR, 0⟩

@[expose] noncomputable def tT (ε : ZMod 2) : Teps ε := ⟨CocExt.central, 0⟩

theorem zT_mul_tT (ε : ZMod 2) : zT ε * tT ε = ⟨zR * CocExt.central, 0⟩ := by
  refine TwistExt.ext ?_ ?_
  · rw [TwistExt.mul_x, zT, tT]
    simp only
    rw [TwistExt.tauPow_zero, mul_zero, TwistExt.zPow_zero, mul_one]
  · rw [TwistExt.mul_e, zT, tT]
    simp only
    rw [add_zero]

theorem codeT_one (ε : ZMod 2) : codeT (1 : Teps ε) = 0 := by
  rw [codeT, TwistExt.one_x, TwistExt.one_e, codeR_one]
  rfl

theorem codeT_zT (ε : ZMod 2) : codeT (zT ε) = 4 := by
  rw [codeT, zT]
  simp only
  rw [codeR_zR]
  rfl

theorem codeT_tT (ε : ZMod 2) : codeT (tT ε) = 128 := by
  rw [codeT, tT]
  simp only
  rw [codeR_central]
  rfl

theorem codeT_zT_tT (ε : ZMod 2) : codeT (zT ε * tT ε) = 132 := by
  rw [zT_mul_tT, codeT]
  simp only
  rw [codeR_zR_central]
  rfl

theorem mem_center_T {ε : ZMod 2} (hε : centerOK 512 (mulT ε.val) = true) (p : Teps ε) :
    p ∈ Subgroup.center (Teps ε) ↔ p = 1 ∨ p = zT ε ∨ p = tT ε ∨ p = zT ε * tT ε := by
  rw [mem_center_of_centerOK (codingT ε) hε, codingT_enc]
  have hinj : ∀ q : Teps ε, codeT p = codeT q ↔ p = q := fun q =>
    ⟨fun h => (codingT ε).enc.injective (Fin.ext h), fun h => by rw [h]⟩
  rw [← hinj 1, ← hinj (zT ε), ← hinj (tT ε), ← hinj (zT ε * tT ε), codeT_one, codeT_zT,
    codeT_tT, codeT_zT_tT]
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem mem_center_T0 (p : T0) :
    p ∈ Subgroup.center T0 ↔ p = 1 ∨ p = zT 0 ∨ p = tT 0 ∨ p = zT 0 * tT 0 :=
  mem_center_T (by rw [show (0 : ZMod 2).val = 0 from rfl]; exact groupCheck_parts.2.2.1) p

theorem mem_center_T1 (p : T1) :
    p ∈ Subgroup.center T1 ↔ p = 1 ∨ p = zT 1 ∨ p = tT 1 ∨ p = zT 1 * tT 1 :=
  mem_center_T (by rw [show (1 : ZMod 2).val = 1 from rfl]; exact groupCheck_parts.2.2.2.2.1) p

theorem rootPair_T {ε : ZMod 2} {l : List (ℕ × ℕ)} (h : rootCounts 512 (mulT ε.val) = l) :
    [rootPair (zT ε), rootPair (tT ε), rootPair (zT ε * tT ε)] = l := by
  rw [← h, rootCounts, rootPair_of_codes (codingT ε), rootPair_of_codes (codingT ε),
    rootPair_of_codes (codingT ε), codingT_enc, codingT_enc, codingT_enc, codeT_zT, codeT_tT,
    codeT_zT_tT]
  rfl

theorem rootPair_T0 : rootPair (zT 0) = (0, 0) ∧ rootPair (tT 0) = (48, 64) ∧
    rootPair (zT 0 * tT 0) = (56, 160) := by
  have := rootPair_T (ε := 0) (l := [(0, 0), (48, 64), (56, 160)])
    (by rw [show (0 : ZMod 2).val = 0 from rfl]; exact groupCheck_parts.2.2.2.1)
  simp only [List.cons.injEq, and_true] at this
  exact this

theorem rootPair_T1 : rootPair (zT 1) = (16, 0) ∧ rootPair (tT 1) = (96, 64) ∧
    rootPair (zT 1 * tT 1) = (40, 160) := by
  have := rootPair_T (ε := 1) (l := [(16, 0), (96, 64), (40, 160)])
    (by rw [show (1 : ZMod 2).val = 1 from rfl]; exact groupCheck_parts.2.2.2.2.2)
  simp only [List.cons.injEq, and_true] at this
  exact this

theorem aut_fix_center_of_rootPairs {G : Type*} [Group G] (z₁ z₂ z₃ : G)
    (hc : ∀ x, x ∈ Subgroup.center G ↔ x = 1 ∨ x = z₁ ∨ x = z₂ ∨ x = z₃)
    (h1 : z₁ ≠ 1) (h2 : z₂ ≠ 1) (h3 : z₃ ≠ 1) (h12 : rootPair z₁ ≠ rootPair z₂)
    (h13 : rootPair z₁ ≠ rootPair z₃) (h23 : rootPair z₂ ≠ rootPair z₃) (φ : G ≃* G) :
    ∀ x ∈ Subgroup.center G, φ x = x := by
  have hc' : ∀ w ∈ Subgroup.center G, w = 1 ∨ w ∈ [z₁, z₂, z₃] := fun w hw => by
    rcases (hc w).1 hw with h | h | h | h <;> simp [h]
  have mem : ∀ z, (z = z₁ ∨ z = z₂ ∨ z = z₃) → z ∈ Subgroup.center G := fun z hz =>
    (hc z).2 (Or.inr hz)
  intro x hx
  rcases (hc x).1 hx with rfl | rfl | rfl | rfl
  · exact map_one φ
  · refine aut_fix_of_rootPair φ _ (mem _ (Or.inl rfl)) h1 _ hc' fun w hw hp => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · rfl
    · exact absurd hp.symm h12
    · exact absurd hp.symm h13
  · refine aut_fix_of_rootPair φ _ (mem _ (Or.inr (Or.inl rfl))) h2 _ hc' fun w hw hp => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd hp h12
    · rfl
    · exact absurd hp.symm h23
  · refine aut_fix_of_rootPair φ _ (mem _ (Or.inr (Or.inr rfl))) h3 _ hc' fun w hw hp => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd hp h13
    · exact absurd hp h23
    · rfl

theorem codeR_ne {x y : Rf} (h : codeR x ≠ codeR y) : x ≠ y := fun e => h (by rw [e])

theorem codeT_ne {ε : ZMod 2} {p q : Teps ε} (h : codeT p ≠ codeT q) : p ≠ q :=
  fun e => h (by rw [e])

theorem aut_fix_center_Rf (φ : Rf ≃* Rf) : ∀ x ∈ Subgroup.center Rf, φ x = x := by
  obtain ⟨r1, r2, r3⟩ := rootPair_Rf
  refine aut_fix_center_of_rootPairs zR CocExt.central (zR * CocExt.central) mem_center_Rf
    (codeR_ne (by rw [codeR_zR, codeR_one]; decide))
    (codeR_ne (by rw [codeR_central, codeR_one]; decide))
    (codeR_ne (by rw [codeR_zR_central, codeR_one]; decide))
    (by rw [r1, r2]; decide) (by rw [r1, r3]; decide) (by rw [r2, r3]; decide) φ

theorem aut_fix_center_T0 (φ : T0 ≃* T0) : ∀ x ∈ Subgroup.center T0, φ x = x := by
  obtain ⟨r1, r2, r3⟩ := rootPair_T0
  refine aut_fix_center_of_rootPairs (zT 0) (tT 0) (zT 0 * tT 0) mem_center_T0
    (codeT_ne (by rw [codeT_zT, codeT_one]; decide))
    (codeT_ne (by rw [codeT_tT, codeT_one]; decide))
    (codeT_ne (by rw [codeT_zT_tT, codeT_one]; decide))
    (by rw [r1, r2]; decide) (by rw [r1, r3]; decide) (by rw [r2, r3]; decide) φ

theorem aut_fix_center_T1 (φ : T1 ≃* T1) : ∀ x ∈ Subgroup.center T1, φ x = x := by
  obtain ⟨r1, r2, r3⟩ := rootPair_T1
  refine aut_fix_center_of_rootPairs (zT 1) (tT 1) (zT 1 * tT 1) mem_center_T1
    (codeT_ne (by rw [codeT_zT, codeT_one]; decide))
    (codeT_ne (by rw [codeT_tT, codeT_one]; decide))
    (codeT_ne (by rw [codeT_zT_tT, codeT_one]; decide))
    (by rw [r1, r2]; decide) (by rw [r1, r3]; decide) (by rw [r2, r3]; decide) φ


theorem card_Rf : Nat.card Rf = 256 := by
  rw [CocExt.card_cocExt, card_S]

instance : Finite Rf := Nat.finite_of_card_ne_zero (by rw [card_Rf]; norm_num)

theorem card_Teps (ε : ZMod 2) : Nat.card (Teps ε) = 512 := by
  rw [TwistExt.card_twistExt, card_Rf]

theorem elt_four_mul_self : elt 4 * elt 4 = 1 := by
  rw [← (mulIdx_spec (a := 4) (by norm_num)).2, show mulIdx 4 4 = 0 by decide +kernel, elt_zero]

theorem orderOf_elt_four : orderOf (elt 4) = 2 :=
  orderOf_eq_prime (by rw [pow_two, elt_four_mul_self])
    (fun h => absurd (elt_injective (by norm_num) (by norm_num) (h.trans elt_zero.symm))
      (by norm_num))

theorem fCoc_elt_four : fCoc (elt 4) (elt 4) = 0 := by
  rcases fCoc_diag (elt 4) orderOf_elt_four with h | h
  · exact h.2
  · rw [fixCount_elt_four] at h
    exact absurd h.1 (by norm_num)

theorem zR_mul_self : zR * zR = 1 := by
  refine CocExt.ext ?_ ?_
  · rw [CocExt.mul_e, zR, fNorm_toFun, fCoc_elt_four, CocExt.one_e]
    rfl
  · rw [CocExt.mul_g, zR, elt_four_mul_self, CocExt.one_g]

theorem zR_central_sq : zR * CocExt.central * (zR * CocExt.central) = 1 := by
  calc zR * CocExt.central * (zR * CocExt.central)
      = zR * (CocExt.central * zR) * CocExt.central := by group
    _ = zR * (zR * CocExt.central) * CocExt.central := by rw [CocExt.central_mul zR]
    _ = (zR * zR) * (CocExt.central * CocExt.central) := by group
    _ = 1 := by rw [zR_mul_self, CocExt.central_mul_central, one_mul]

theorem center_Rf_sq : ∀ x ∈ Subgroup.center Rf, x ^ 2 = 1 := by
  intro x hx
  rw [pow_two]
  rcases (mem_center_Rf x).1 hx with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact zR_mul_self
  · exact CocExt.central_mul_central
  · exact zR_central_sq

theorem card_center_Rf : Nat.card (Subgroup.center Rf) = 4 :=
  card_center_of_codes codingR (by norm_num) (mem_center_of_centerOK codingR groupCheck_parts.1)

theorem TwistExt_mk_zero_sq {ε : ZMod 2} (x : Rf) :
    ((⟨x, 0⟩ : Teps ε) * ⟨x, 0⟩ : Teps ε) = ⟨x * x, 0⟩ := by
  refine TwistExt.ext ?_ ?_
  · rw [TwistExt.mul_x, TwistExt.tauPow_zero, mul_zero, TwistExt.zPow_zero, mul_one]
  · rw [TwistExt.mul_e, add_zero]

theorem center_T_sq {ε : ZMod 2} (hε : centerOK 512 (mulT ε.val) = true) :
    ∀ p ∈ Subgroup.center (Teps ε), p ^ 2 = 1 := by
  have hz : ∀ x : Rf, x * x = 1 → (⟨x, 0⟩ : Teps ε) ^ 2 = 1 := fun x hx => by
    rw [pow_two, TwistExt_mk_zero_sq, hx]
    rfl
  intro p hp
  rcases (mem_center_T hε p).1 hp with rfl | rfl | rfl | rfl
  · exact one_pow 2
  · exact hz _ zR_mul_self
  · exact hz _ CocExt.central_mul_central
  · rw [zT_mul_tT]
    exact hz _ zR_central_sq

theorem centerOK_T0 : centerOK 512 (mulT (0 : ZMod 2).val) = true := by
  rw [show (0 : ZMod 2).val = 0 from rfl]
  exact groupCheck_parts.2.2.1

theorem centerOK_T1 : centerOK 512 (mulT (1 : ZMod 2).val) = true := by
  rw [show (1 : ZMod 2).val = 1 from rfl]
  exact groupCheck_parts.2.2.2.2.1

theorem card_center_T0 : Nat.card (Subgroup.center T0) = 4 :=
  card_center_of_codes (codingT 0) (by norm_num) (mem_center_of_centerOK (codingT 0) centerOK_T0)

theorem card_center_T1 : Nat.card (Subgroup.center T1) = 4 :=
  card_center_of_codes (codingT 1) (by norm_num) (mem_center_of_centerOK (codingT 1) centerOK_T1)

theorem center_T0_sq : ∀ p ∈ Subgroup.center T0, p ^ 2 = 1 := center_T_sq centerOK_T0

theorem center_T1_sq : ∀ p ∈ Subgroup.center T1, p ^ 2 = 1 := center_T_sq centerOK_T1

end CFSG.ComponentClassification.J2Cover.Models
