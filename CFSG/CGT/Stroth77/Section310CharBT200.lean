module

public import CFSG.CGT.Stroth77.Section310CharBC
public import CFSG.CGT.Stroth77.Section47Core
public import CFSG.CGT.Stroth77.Stroth34Defs

public section

namespace CFSG.CGT.Stroth77

open Stroth47Core

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
  {dD : StrothWeakTypeData D (.t200 m)}

theorem StrothWeakTypeData.a_pow_two_pow_n {τ : StrothTypeIndex} (dD : StrothWeakTypeData D τ) :
    (dD.a : G) ^ 2 ^ τ.n = 1 := by
  rw [dD.a_eq, ← dD.ofTorus_nsmul]
  have h : (2 ^ τ.n) • (Torus.a : Torus τ.k) = 0 := by
    rw [show (Torus.a : Torus τ.k) = gen τ.k 1 from rfl, show τ.n = τ.k 1 from rfl,
      ← addOrderOf_gen τ.k 1]
    exact addOrderOf_nsmul_eq_zero _
  rw [h, dD.ofTorus_zero]

theorem StrothWeakTypeData.b_pow_two_pow_n {τ : StrothTypeIndex} (dD : StrothWeakTypeData D τ) :
    (dD.b : G) ^ 2 ^ τ.n = 1 := by
  rw [dD.b_eq, ← dD.ofTorus_nsmul]
  have h : (2 ^ τ.n) • (Torus.b : Torus τ.k) = 0 := by
    rw [show (Torus.b : Torus τ.k) = gen τ.k 2 from rfl, ← τ.k_two, ← addOrderOf_gen τ.k 2]
    exact addOrderOf_nsmul_eq_zero _
  rw [h, dD.ofTorus_zero]

namespace Stroth310T200

theorem two_le_k (hm : 2 ≤ m) (i : Fin 3) : 2 ≤ (StrothTypeIndex.t200 m).k i := by
  fin_cases i
  · exact hm
  · show 2 ≤ m + 2; omega
  · show 2 ≤ m + 2; omega

theorem card_D (dD : StrothWeakTypeData D (.t200 m)) : Nat.card D = 2 ^ (3 * m + 4) := by
  rw [dD.card]
  change 2 ^ (m + (m + 2) + (m + 2)) = 2 ^ (3 * m + 4)
  ring_nf

theorem φuv_om_ne (hm : 1 ≤ m) :
    (StrothTypeIndex.t200 m).action.φuv (om200 m ![1, 0, 0]) ≠ om200 m ![1, 0, 0] := by
  rw [t200_φuv_om hm]
  intro h
  have h1 := (om200_eq_iff hm _ _).mp h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
  norm_num [Int.ModEq] at h1

theorem uv_not_mem (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) :
    ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w :=
  dD.not_forall_commute_uv_of_torus (by rw [two_nsmul]; exact om200_add_self hm _) (φuv_om_ne hm)

theorem c_pow_mem (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) :
    (dD.c : G) ^ 2 ^ (m - 1) ∈ omegaIn 1 D := by
  rw [dD.t200_c_pow]
  exact mem_omegaIn_one_of_mul_self (dD.ofTorus_mem _)
    (by rw [← dD.ofTorus_add, om200_add_self hm, dD.ofTorus_zero])

theorem c_pow_not_commute (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) :
    ¬ (dD.c : G) ^ 2 ^ (m - 1) * dD.uv = dD.uv * (dD.c : G) ^ 2 ^ (m - 1) := by
  rw [dD.t200_c_pow, dD.uv_mul_ofTorus]
  intro h
  exact φuv_om_ne hm (dD.ofTorus_inj (mul_right_cancel h).symm)

theorem a₁_b₁ (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) :
    (dD.a : G) ^ 2 ^ (m + 1) ≠ 1 ∧ (dD.b : G) ^ 2 ^ (m + 1) ≠ 1 ∧
      (dD.a : G) ^ 2 ^ (m + 1) ≠ (dD.b : G) ^ 2 ^ (m + 1) := by
  rw [dD.t200_a_pow, dD.t200_b_pow, Ne, Ne, Ne, dD.ofTorus_eq_one_iff, dD.ofTorus_eq_one_iff,
    dD.ofTorus_inj.eq_iff, ← om200_zero (m := m)]
  refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · have h1 := (om200_eq_iff hm _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
    norm_num [Int.ModEq] at h1
  · have h1 := (om200_eq_iff hm _ _).mp h0 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply] at h1
    norm_num [Int.ModEq] at h1
  · have h1 := (om200_eq_iff hm _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    norm_num [Int.ModEq] at h1

theorem hA (h : F.IsD D dD) (hm : 2 ≤ m) :
    ∀ g ∈ Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G),
      D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D →
      ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine h.hA_of_torus (two_le_k hm) (uv_not_mem dD hm1) (v₁ := om200 (m' + 1) ![0, 1, 0])
    (v₂ := om200 (m' + 1) ![0, 0, 1]) (z := Torus.ofInt _ ![0, 2 ^ m', 0]) ?_
    (om200_add_self hm1 _) ?_ ?_ ?_ ?_
  · rw [← natCast_zsmul, ← Torus.ofInt_zsmul, om200]
    congr 1
    funext i
    fin_cases i <;> simp [StrothTypeIndex.k, Type200.k] <;> ring
  · intro h0
    have h1 := (om200_eq_iff hm1 _ _).mp h0 1
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h1
    norm_num [Int.ModEq] at h1
  · rw [t200_φu_om]
    congr 1
  · rw [t200_φuv_om hm1]
    refine (om200_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide
  · rw [t200_φt_om hm1]
    refine (om200_eq_iff hm1 _ _).mpr fun i => ?_
    fin_cases i <;> simp [Int.ModEq] <;> decide

theorem bound_i (dD : StrothWeakTypeData D (.t200 m)) (hm : 2 ≤ m) {e : G}
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (hc : e⁻¹ * (dD.c : G) * e = dD.c)
    (ha : e⁻¹ * (dD.a : G) * e = dD.a * (dD.a : G) ^ 2 ^ (m + 1))
    (hb : e⁻¹ * (dD.b : G) * e = dD.b * (dD.b : G) ^ 2 ^ (m + 1)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxC : x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨hA1, hB1, hAB⟩ := a₁_b₁ dD hm1
  have hb4 := dD.bound_comm (card_D dD) (c_pow_not_commute dD hm1) heN hc (pow_mem dD.a.2 _)
    (pow_mem dD.b.2 _) ha hb hA1 hB1 hAB hxN
    (Subgroup.mem_centralizer_iff.mp hxC _ (c_pow_mem dD hm1))
  have hpos : 0 < Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) := Nat.card_pos
  have h4m : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : 16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) ≤ Nat.card D :=
    le_trans (by nlinarith) hb4
  omega

theorem card_le_eight_of_inv (dD : StrothWeakTypeData D (.t200 m)) (hm : 1 ≤ m) {e : G}
    {j t : ℕ} (hj : j = 2 ^ (m + 1) * t) (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ j)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ j) (y : G) :
    Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) ≤ 8 := by
  have hle : D ⊓ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      omegaIn 1 D := by
    intro z hz
    exact mem_omegaIn_one_of_mul_self hz.1.1 (dD.mul_self_eq_one_of_inv_shape
      (by change 3 ≤ m + 2; omega) (j := j) (t := t) (by rw [hj]; rfl) hc ha hb hz.1.1
      (Subgroup.mem_centralizer_singleton_iff.mp hz.2))
  have h8 : Nat.card (omegaIn 1 D) = 8 := natCard_omegaIn_one_of_pos dD.e (t200_one_le_k hm)
  exact (Subgroup.card_le_of_le hle).trans h8.le


theorem f_sq_conj (hm : 2 ≤ m) {f x : G} (hx : x ^ 2 ^ (m + 2) = 1)
    (hfx : f⁻¹ * x * f = x * x ^ 2 ^ m) : (f * f)⁻¹ * x * (f * f) = x * x ^ 2 ^ (m + 1) := by
  have hcp : ∀ (y : G) (k : ℕ), f⁻¹ * y ^ k * f = (f⁻¹ * y * f) ^ k := fun y k => by
    have h1 := conj_pow (a := f⁻¹) (b := y) (i := k)
    rw [inv_inv] at h1
    exact h1.symm
  have hN2 : x ^ (2 ^ m * 2 ^ m) = 1 := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    rw [show 2 ^ (m' + 2) * 2 ^ (m' + 2) = 2 ^ (m' + 2 + 2) * 2 ^ m' by ring, pow_mul, hx,
      one_pow]
  calc (f * f)⁻¹ * x * (f * f) = f⁻¹ * (x * x ^ 2 ^ m) * f := by rw [← hfx]; group
    _ = (f⁻¹ * x * f) * (f⁻¹ * x ^ 2 ^ m * f) := by group
    _ = (x * x ^ 2 ^ m) * (x * x ^ 2 ^ m) ^ 2 ^ m := by rw [hcp, hfx]
    _ = x ^ (2 ^ m * 2 ^ m) * x ^ (2 * 2 ^ m + 1) := by
      have e : x * x ^ 2 ^ m = x ^ (2 ^ m + 1) := (pow_succ' x (2 ^ m)).symm
      rw [e, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    _ = x * x ^ 2 ^ (m + 1) := by
      rw [hN2, one_mul, pow_succ', pow_succ' 2 m]

theorem sixteen_mul_card_x (dD : StrothWeakTypeData D (.t200 m)) {f : G}
    (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (ha : f⁻¹ * (dD.a : G) * f = dD.a * (dD.a : G) ^ 2 ^ m)
    (hb : f⁻¹ * (dD.b : G) * f = dD.b * (dD.b : G) ^ 2 ^ m) :
    16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G)) ≤ Nat.card D := by
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm' : ∀ (g : G) (q : ℕ), g * g ^ q * g⁻¹ = g ^ q := fun g q => by
    rw [(Commute.self_pow g q).eq, mul_inv_cancel_right]
  refine sixteen_mul_card_inf_centralizer_le hcommD hfN dD.a.2 dD.b.2
    (by rw [ha, hcomm']) (by rw [hb, hcomm']) ?_
  intro i l i' l' hil
  have e1 : ∀ p q : ℕ, ((dD.a : G) ^ 2 ^ m) ^ p * ((dD.b : G) ^ 2 ^ m) ^ q =
      dD.ofTorus (Torus.ofInt _ ![0, ((2 ^ m * p : ℕ) : ℤ), ((2 ^ m * q : ℕ) : ℤ)]) := by
    intro p q
    rw [dD.ofTorus_ofInt]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, zpow_zero, one_mul, zpow_natCast, ← pow_mul]
  rw [e1, e1, dD.ofTorus_inj.eq_iff, Torus.ofInt_eq_ofInt_iff] at hil
  have h1 := (hil 1).dvd
  have h2 := (hil 2).dvd
  simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h1 h2
  have hk1 : (StrothTypeIndex.t200 m).k 1 = m + 2 := rfl
  have hk2 : (StrothTypeIndex.t200 m).k 2 = m + 2 := rfl
  rw [hk1] at h1
  rw [hk2] at h2
  push_cast at h1 h2
  have hcancel : ∀ p p' : ℕ, (2 : ℤ) ^ (m + 2) ∣ 2 ^ m * (p' : ℤ) - 2 ^ m * p →
      (4 : ℤ) ∣ (p' : ℤ) - p := fun p p' hd => by
    rw [← mul_sub, pow_add] at hd
    exact (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ m ≠ 0)).mp
      (by norm_num at hd ⊢; exact hd)
  have hi := hcancel _ _ h1
  have hl := hcancel _ _ h2
  have hi4 := i.isLt
  have hi4' := i'.isLt
  have hl4 := l.isLt
  have hl4' := l'.isLt
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> omega

theorem bound_x (dD : StrothWeakTypeData D (.t200 m)) (hm : 2 ≤ m) {f : G}
    (hfN : f ∈ Subgroup.normalizer (D : Set G)) (hc : f⁻¹ * (dD.c : G) * f = dD.c)
    (ha : f⁻¹ * (dD.a : G) * f = dD.a * (dD.a : G) ^ 2 ^ m)
    (hb : f⁻¹ * (dD.b : G) * f = dD.b * (dD.b : G) ^ 2 ^ m) {x : G}
    (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxC : x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    16 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({f} : Set G)) < Nat.card D := by
  have hm1 : 1 ≤ m := by omega
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h16 := sixteen_mul_card_x dD hfN ha hb
  have hbN : dD.uv * x ∈ Subgroup.normalizer (D : Set G) := mul_mem dD.uv_mem hxN
  have hcH : (dD.c : G) ∈ D ⊓ Subgroup.centralizer ({f} : Set G) := by
    refine ⟨dD.c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (dD.c : G) * f = f * (f⁻¹ * (dD.c : G) * f) := by group
      _ = f * dD.c := by rw [hc]
  have h2m := two_pow_mul_card_inf_centralizer_le hcommD (card_D dD) inf_le_left hbN hcH
    (not_commute_mul_of_commute (c_pow_not_commute dD hm1)
      (Subgroup.mem_centralizer_iff.mp hxC _ (c_pow_mem dD hm1)))
  rw [inf_right_comm D]
  have hpos : 0 < Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G) ⊓
      Subgroup.centralizer ({dD.uv * x} : Set G)) := Nat.card_pos
  have h2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have : 16 * (2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({f} : Set G) ⊓
      Subgroup.centralizer ({dD.uv * x} : Set G))) ≤ Nat.card D :=
    le_trans (Nat.mul_le_mul_left 16 ((Nat.mul_le_mul_right _ h2).trans h2m)) h16
  omega

end Stroth310T200

open Stroth310T200

theorem StrothFrame.IsD.mem_normalizer_omegaIn_t200 (h : F.IsD D dD) (hm : 2 ≤ m)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) →
        (StrothTypeIndex.t200 m).m = (StrothTypeIndex.t200 m).n)
    (h34 : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e ∧
        (Rel34i dD e (2 ^ (m + 1)) ∨
          Rel34inv dD e 0 1 2 ∨ Rel34inv dD e 0 1 1 ∨ Rel34inv dD e 0 1 3 ∨
          Rel34inv dD e (2 ^ (m + 1)) 1 2 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 1 ∨
          Rel34inv dD e (2 ^ (m + 1)) ((dD.c : G) ^ 2 ^ (m - 1)) 3)) ∨
      (∃ e ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.closure {e, f} ∧
        Rel34i dD e (2 ^ (m + 1)) ∧ (Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3) ∧
        f⁻¹ * e * f = e⁻¹ * (dD.c : G) ^ 2 ^ (m - 1)) ∨
      (2 ≤ m ∧ ∃ f ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
        (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers f ∧
        (Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 1 ∨ Rel34x dD f (2 ^ m) (2 ^ (m - 1)) 3)))
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hm1 : 1 ≤ m := by omega
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDs := Stroth310T200.card_D dD
  have h1024 : 2 ^ 10 ≤ 2 ^ (3 * m + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hRN : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      x ∈ Subgroup.normalizer (D : Set G) := fun x hx => (Subgroup.mem_inf.mp hx).1.2
  have hRC : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := fun x hx =>
    (Subgroup.mem_inf.mp hx).2
  have hc2D : (dD.c : G) ^ 2 ^ (m - 1) ∈ D := pow_mem dD.c.2 _
  have hinv8 : ∀ {e : G} {j : ℕ} {s : G} {p : ℕ}, (j = 0 ∨ j = 2 ^ (m + 1)) →
      Rel34inv dD e j s p → ∀ y : G,
      Nat.card ↥(D ⊓ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({e} : Set G))
        ≤ 8 := by
    intro e j s p hj hrel y
    rcases hj with rfl | rfl
    · exact Stroth310T200.card_le_eight_of_inv dD hm1 (t := 0) (by ring) hrel.c_conj hrel.a_conj
        hrel.b_conj y
    · exact Stroth310T200.card_le_eight_of_inv dD hm1 (t := 1) (by ring) hrel.c_conj hrel.a_conj
        hrel.b_conj y
  refine h.mem_normalizer_omegaIn_of_cases (by change m ≠ m + 2; omega) (t200_one_le_k hm1)
    (Stroth310T200.uv_not_mem dD hm1) h226 (Stroth310T200.hA h hm) ?_ hgN
  rcases h34 with hRD | ⟨e, heR, hRe, hshape⟩ | ⟨e, heR, f, hfR, hRef, he, hf, hfe⟩ |
    ⟨-, f, hfR, hRf, hf⟩
  · intro x _ Q hQR hQD _
    exact absurd (hRD ▸ hQR) hQD
  ·
    have heN := hRN e heR
    rcases hshape with he | he | he | he | he | he | he
    · refine h.hB_of_zpowers hRe heN (he.e_sq ▸ inv_mem dD.c.2) ?_
        (Stroth310T200.bound_i dD hm heN he.c_conj he.a_conj he.b_conj (hRN e heR) (hRC e heR))
      simpa using Stroth310T200.bound_i dD hm heN he.c_conj he.a_conj he.b_conj (x := 1) (one_mem _)
        (one_mem _)
    all_goals
      refine h.hB_of_zpowers hRe heN ?_ ?_ ?_
      · rw [he.e_sq]
        first | exact one_mem D | exact hc2D
      all_goals
        first
        | (have := hinv8 (Or.inl rfl) he (y := dD.uv); omega)
        | (have := hinv8 (Or.inr rfl) he (y := dD.uv); omega)
        | (have := hinv8 (Or.inl rfl) he (y := dD.uv * e); omega)
        | (have := hinv8 (Or.inr rfl) he (y := dD.uv * e); omega)
  ·
    have heN := hRN e heR
    have hfN := hRN f hfR
    have hf' : Rel34inv dD f 0 1 1 ∨ Rel34inv dD f 0 1 3 := hf
    have hff : f * f = 1 := by rcases hf with hf | hf <;> exact hf.e_sq
    have hfc : f⁻¹ * (dD.c : G) * f = (dD.c : G)⁻¹ := by rcases hf with hf | hf <;> exact hf.c_conj
    have hfa : f⁻¹ * (dD.a : G) * f = (dD.a : G)⁻¹ * (dD.a : G) ^ 0 := by
      rcases hf with hf | hf <;> exact hf.a_conj
    have hfb : f⁻¹ * (dD.b : G) * f = (dD.b : G)⁻¹ * (dD.b : G) ^ 0 := by
      rcases hf with hf | hf <;> exact hf.b_conj
    have hRrs : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) =
          (D ⊔ Subgroup.zpowers e) ⊔ Subgroup.zpowers f := by
      rw [hRef, sup_assoc, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        ← Subgroup.closure_union, Set.insert_eq]
    have hsN : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers e : Subgroup G) : Set G) :=
      mem_normalizer_sup_zpowers hfN (by
        rw [hfe]
        exact mul_mem (Subgroup.mem_sup_right (inv_mem (Subgroup.mem_zpowers e)))
          (Subgroup.mem_sup_left hc2D))
    refine h.hB_of_tower hRrs heN (he.e_sq ▸ inv_mem dD.c.2) hsN
      (by rw [hff]; exact one_mem _)
      (fun x hx => Stroth310T200.bound_i dD hm heN he.c_conj he.a_conj he.b_conj (hRN x hx)
        (hRC x hx)) ?_
    intro x hx y hyR hyD'
    rw [hRrs] at hyR
    have hfy := (mem_or_inv_mul_mem_of_mem_sup_zpowers hsN (by rw [hff]; exact one_mem _)
      hyR).resolve_left hyD'
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers heN (he.e_sq ▸ inv_mem dD.c.2) hfy with
      hd | hd
    ·
      have e1 : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G) = D ⊓ Subgroup.centralizer ({f} : Set G) ⊓
            Subgroup.centralizer ({dD.uv * x} : Set G) := by
        rw [inf_right_comm D, show y = f * (f⁻¹ * y) by group,
          inf_centralizer_mul_of_mem hcommD hd]
      rw [e1, inf_right_comm D]
      have := Stroth310T200.card_le_eight_of_inv dD hm1 (j := 0) (t := 0) (by ring) hfc hfa hfb
        (dD.uv * x)
      omega
    ·
      have hy' : y = f * e * (e⁻¹ * (f⁻¹ * y)) := by group
      have hfec : (f * e)⁻¹ * (dD.c : G) * (f * e) = (dD.c : G)⁻¹ := by
        calc (f * e)⁻¹ * (dD.c : G) * (f * e) = e⁻¹ * (f⁻¹ * (dD.c : G) * f) * e := by group
          _ = (e⁻¹ * (dD.c : G) * e)⁻¹ := by rw [hfc]; group
          _ = (dD.c : G)⁻¹ := by rw [he.c_conj]
      have hNN : (dD.a : G) ^ 2 ^ (m + 1) * (dD.a : G) ^ 2 ^ (m + 1) = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        exact dD.a_pow_two_pow_n
      have hNNb : (dD.b : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        exact dD.b_pow_two_pow_n
      have hfea : (f * e)⁻¹ * (dD.a : G) * (f * e) =
          (dD.a : G)⁻¹ * (dD.a : G) ^ (2 ^ (m + 1) * 1) := by
        calc (f * e)⁻¹ * (dD.a : G) * (f * e) = e⁻¹ * (f⁻¹ * (dD.a : G) * f) * e := by group
          _ = (e⁻¹ * (dD.a : G) * e)⁻¹ := by rw [hfa, pow_zero, mul_one]; group
          _ = (dD.a : G)⁻¹ * (dD.a : G) ^ (2 ^ (m + 1) * 1) := by
            rw [he.a_conj, mul_one, mul_inv_rev, inv_eq_of_mul_eq_one_right hNN,
              (Commute.self_pow (dD.a : G) _).inv_left.eq]
      have hfeb : (f * e)⁻¹ * (dD.b : G) * (f * e) =
          (dD.b : G)⁻¹ * (dD.b : G) ^ (2 ^ (m + 1) * 1) := by
        calc (f * e)⁻¹ * (dD.b : G) * (f * e) = e⁻¹ * (f⁻¹ * (dD.b : G) * f) * e := by group
          _ = (e⁻¹ * (dD.b : G) * e)⁻¹ := by rw [hfb, pow_zero, mul_one]; group
          _ = (dD.b : G)⁻¹ * (dD.b : G) ^ (2 ^ (m + 1) * 1) := by
            rw [he.b_conj, mul_one, mul_inv_rev, inv_eq_of_mul_eq_one_right hNNb,
              (Commute.self_pow (dD.b : G) _).inv_left.eq]
      have e1 : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G) = D ⊓ Subgroup.centralizer ({f * e} : Set G) ⊓
            Subgroup.centralizer ({dD.uv * x} : Set G) := by
        rw [inf_right_comm D, hy', inf_centralizer_mul_of_mem hcommD hd]
      rw [e1, inf_right_comm D]
      have := Stroth310T200.card_le_eight_of_inv dD hm1 (j := 2 ^ (m + 1) * 1) (t := 1) rfl hfec
        hfea hfeb (dD.uv * x)
      omega
  ·
    have hfN := hRN f hfR
    have hfc : f⁻¹ * (dD.c : G) * f = dD.c := by rcases hf with hf | hf <;> exact hf.1.c_conj
    have hfa : f⁻¹ * (dD.a : G) * f = dD.a * (dD.a : G) ^ 2 ^ m := by
      rcases hf with hf | hf <;> exact hf.1.a_conj
    have hfb : f⁻¹ * (dD.b : G) * f = dD.b * (dD.b : G) ^ 2 ^ m := by
      rcases hf with hf | hf <;> exact hf.1.b_conj
    have hf4 : f * f * (f * f) ∈ D := by
      rcases hf with hf | hf <;> rw [hf.2] <;> exact mul_mem (inv_mem (pow_mem dD.c.2 _))
        (pow_mem dD.c.2 _)
    have hRrs : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) =
          (D ⊔ Subgroup.zpowers (f * f)) ⊔ Subgroup.zpowers f := by
      rw [hRf, sup_assoc, sup_eq_right.mpr ((Subgroup.zpowers_le).mpr
        (mul_mem (Subgroup.mem_zpowers f) (Subgroup.mem_zpowers f)))]
    have hrN : f * f ∈ Subgroup.normalizer (D : Set G) := mul_mem hfN hfN
    have hsN : f ∈ Subgroup.normalizer ((D ⊔ Subgroup.zpowers (f * f) : Subgroup G) : Set G) :=
      mem_normalizer_sup_zpowers hfN (by
        rw [show f⁻¹ * (f * f) * f = f * f by group]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hs2 : f * f ∈ D ⊔ Subgroup.zpowers (f * f) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hffc : (f * f)⁻¹ * (dD.c : G) * (f * f) = dD.c := by
      calc (f * f)⁻¹ * (dD.c : G) * (f * f) = f⁻¹ * (f⁻¹ * (dD.c : G) * f) * f := by group
        _ = dD.c := by rw [hfc, hfc]
    have hffa := Stroth310T200.f_sq_conj hm (by exact dD.a_pow_two_pow_n) hfa
    have hffb := Stroth310T200.f_sq_conj hm (by exact dD.b_pow_two_pow_n) hfb
    refine h.hB_of_tower hRrs hrN hf4 hsN hs2
      (fun x hx => Stroth310T200.bound_i dD hm hrN hffc hffa hffb (hRN x hx) (hRC x hx)) ?_
    intro x hx y hyR hyD'
    rw [hRrs] at hyR
    have hfy := (mem_or_inv_mul_mem_of_mem_sup_zpowers hsN hs2 hyR).resolve_left hyD'
    have hCf : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G) = D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({f} : Set G) := by
      rcases mem_or_inv_mul_mem_of_mem_sup_zpowers hrN hf4 hfy with hd | hd
      · rw [inf_right_comm D, show y = f * (f⁻¹ * y) by group,
          inf_centralizer_mul_of_mem hcommD hd, inf_right_comm D]
      ·
        have hy' : y = f⁻¹ * (f * f * (f * f)) * ((f * f)⁻¹ * (f⁻¹ * y)) := by group
        rw [inf_right_comm D, hy', inf_centralizer_mul_of_mem hcommD hd,
          inf_centralizer_mul_of_mem hcommD hf4, inf_right_comm D]
        congr 1
        ext z
        simp only [Subgroup.mem_centralizer_singleton_iff]
        constructor
        · intro h1
          calc z * f = f * (f⁻¹ * z) * f := by group
            _ = f * (z * f⁻¹) * f := by rw [h1]
            _ = f * z := by group
        · intro h1
          calc z * f⁻¹ = f⁻¹ * (f * z) * f⁻¹ := by group
            _ = f⁻¹ * (z * f) * f⁻¹ := by rw [h1]
            _ = f⁻¹ * z := by group
    rw [hCf]
    exact Stroth310T200.bound_x dD hm hfN hfc hfa hfb (hRN x hx) (hRC x hx)

end CFSG.CGT.Stroth77
