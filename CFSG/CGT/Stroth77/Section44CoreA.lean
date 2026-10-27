module

public import CFSG.CGT.Stroth77.Section44Core

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core

namespace Stroth44Core

variable {m : ℕ}

@[expose] def om201 (m : ℕ) (ε : Fin 3 → ℤ) : Torus (StrothTypeIndex.t201 m).k :=
  Torus.ofInt _ (fun i => ε i * 2 ^ ((StrothTypeIndex.t201 m).k i - 1))

theorem t201_one_le_k (hm : 1 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t201 m).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type201.k] <;> omega

theorem om201_eq_iff (hm : 1 ≤ m) (ε ε' : Fin 3 → ℤ) :
    om201 m ε = om201 m ε' ↔ ∀ i, ε i ≡ ε' i [ZMOD 2] :=
  ofInt_mul_two_pow_pred_eq_iff (t201_one_le_k hm) ε ε'

theorem om201_apply (ε : Fin 3 → ℤ) :
    om201 m ε = Torus.ofInt _ ![ε 0 * 2 ^ (m - 1), ε 1 * 2 ^ (m + 1), ε 2 * 2 ^ (m + 1)] := by
  rw [om201]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem t201_φuv_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φuv (om201 m ε) = om201 m ![ε 0, ε 0 + ε 1, ε 0 + ε 2] := by
  rw [om201_apply, om201_apply, t201_φuv, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨2 * ε 0 - 2 * ε 1 - 2 * ε 2, by ring⟩,
    ⟨ε 0 - ε 2 - 6 * 2 ^ k * ε 2 - 8 * (2 ^ k) ^ 2 * ε 2, by ring⟩,
    ⟨ε 0 - ε 1 - 2 * 2 ^ k * ε 1, by ring⟩⟩

theorem t201_φt_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φt (om201 m ε) = om201 m ![ε 0, ε 0 + ε 1, ε 2] := by
  rw [om201_apply, om201_apply, t201_φt, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨2 * ε 2 + 8 * 2 ^ k * ε 2, by ring⟩,
    ⟨ε 1 + ε 2 + 2 * 2 ^ k * ε 2 - 2 * 2 ^ k * ε 1, by ring⟩, ⟨ε 2 + 2 * 2 ^ k * ε 2, by ring⟩⟩

theorem t201_φu_om (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φu (om201 m ε) = om201 m ![ε 0, ε 2, ε 1] := by
  rw [om201_apply, om201_apply, t201_φu]
  congr 1


theorem t201_φρ_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    (StrothTypeIndex.t201 m).action.φρ (om201 m ε) = om201 m ![ε 0, ε 2, ε 1 + ε 2] := by
  rw [om201_apply, om201_apply, t201_φρ, t201_ofInt_eq_iff]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨⟨2 * ε 2, by ring⟩, ⟨ε 2, by ring⟩, ⟨ε 2, by ring⟩⟩

theorem om201_add (ε ε' : Fin 3 → ℤ) : om201 m ε + om201 m ε' = om201 m (ε + ε') := by
  rw [om201, om201, om201, ← Torus.ofInt_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem t201_d8Act_z (hm : 1 ≤ m) (i j l : Bool) :
    (StrothTypeIndex.t201 m).action.d8Act i j l (om201 m ![0, 1, 1]) = om201 m ![0, 1, 1] := by
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t201_φuv_om hm, t201_φt_om hm, t201_φu_om] <;>
    rw [om201_eq_iff hm] <;> decide

theorem t201_d8Act_conj (hm : 1 ≤ m) (i j l : Bool) (h : (i, j, l) ≠ (false, false, false)) :
    ∃ q : Torus (StrothTypeIndex.t201 m).k,
      (StrothTypeIndex.t201 m).action.d8Act i j l q = q + om201 m ![0, 1, 1] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  rw [om201_apply]
  cases i <;> cases j <;> cases l
  · exact absurd rfl h
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨0, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φt, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨1 + 4 * 2 ^ k, by ring⟩, ⟨1 + 2 ^ k, by ring⟩, ⟨1 + 2 ^ k, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φt, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨0, by ring⟩, ⟨1 - 2 * 2 ^ k, by ring⟩, ⟨1, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 2 ^ (k + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨-2, by ring⟩, ⟨-3 * 2 ^ k - 4 * (2 ^ k) ^ 2, by ring⟩, ⟨-(2 ^ k), by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 2 ^ (k + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨-2, by ring⟩, ⟨-3 * 2 ^ k - 4 * (2 ^ k) ^ 2, by ring⟩, ⟨-(2 ^ k), by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 2 ^ (k + 1), 0], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φt, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨1 - 4 * 2 ^ k, by ring⟩, ⟨1 - 2 ^ k, by ring⟩, ⟨1 - 2 ^ k - 4 * (2 ^ k) ^ 2, by ring⟩⟩
  · refine ⟨Torus.ofInt _ ![0, 0, 2 ^ (k + 1 + 1)], ?_⟩
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply]
    rw [t201_φu, t201_φt, t201_φuv, ← Torus.ofInt_add, t201_ofInt_eq_iff]
    simp only [Pi.add_apply, Nat.add_sub_cancel, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    refine ⟨⟨2 - 8 * 2 ^ k, by ring⟩, ⟨1 - 2 * 2 ^ k, by ring⟩,
      ⟨2 - 2 * 2 ^ k - 8 * (2 ^ k) ^ 2, by ring⟩⟩

section Group

variable {G : Type*} [Group G] {D : Subgroup G} (dD : StrothWeakTypeData D (.t201 m))

open StrothWeakTypeData

theorem c_pow_om : (dD.c : G) ^ 2 ^ (m - 1) = dD.ofTorus (om201 m ![1, 0, 0]) := by
  rw [c_pow_eq, om201_apply]
  congr 2
  funext i
  fin_cases i <;> simp

theorem z_om : (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) =
    dD.ofTorus (om201 m ![0, 1, 1]) := by
  rw [za_eq, zb_eq, ofTorus_ofInt_mul, om201_apply]
  congr 2
  funext i
  fin_cases i <;> simp

theorem t201_eq_om_of_mul_self (hm : 1 ≤ m) {y : G} (hy : y ∈ D) (h2 : y * y = 1) :
    ∃ ε : Fin 3 → ℤ, (∀ i, ε i = 0 ∨ ε i = 1) ∧ y = dD.ofTorus (om201 m ε) := by
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hy
  rw [ofTorus_mul_self, ofTorus_eq_one_iff] at h2
  obtain ⟨ε, hε, rfl⟩ := (Torus.two_zsmul_eq_zero_iff (t201_one_le_k hm) v).mp
    (by rw [two_zsmul]; exact h2)
  exact ⟨ε, hε, rfl⟩

theorem ofTorus_conj_nf {v q w : Torus (StrothTypeIndex.t201 m).k} {i j l : Bool}
    (hq : (StrothTypeIndex.t201 m).action.d8Act i j l q = q + w)
    (hw : (StrothTypeIndex.t201 m).action.d8Act i j l w = w) :
    (dD.ofTorus q)⁻¹ * (dD.ofTorus v * dD.d8 i j l) * dD.ofTorus q =
      dD.ofTorus v * dD.d8 i j l * dD.ofTorus w := by
  rw [← dD.ofTorus_neg, mul_assoc, mul_assoc, dD.d8_mul_ofTorus, mul_assoc (dD.ofTorus v),
    dD.d8_mul_ofTorus, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← dD.ofTorus_add, ← dD.ofTorus_add,
    ← dD.ofTorus_add, hq, hw]
  congr 2
  rw [add_comm (-q) v, add_assoc, neg_add_cancel_left]

theorem t201_hC2c (hm : 1 ≤ m) : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
    y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) =
      (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) * y := by
  intro y hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  rw [z_om]
  exact (dD.nf_commute_iff _ _ _ _ _).2 (t201_d8Act_z hm i j l)

theorem t201_hC2 (hm : 1 ≤ m) : ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}, y * y = 1 →
    y ≠ 1 → y ≠ (dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1) →
    ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u},
      q⁻¹ * y * q = y * ((dD.a : G) ^ 2 ^ (m + 1) * (dD.b : G) ^ 2 ^ (m + 1)) := by
  intro y hy hy2 hy1 hyz
  rw [z_om] at hyz ⊢
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hy
  by_cases hw : (i, j, l) = (false, false, false)
  ·
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl, rfl⟩ := hw
    rw [dD.d8_fff, mul_one] at hy2 hy1 hyz ⊢
    obtain ⟨ε, hε, hεeq⟩ := t201_eq_om_of_mul_self dD hm (dD.ofTorus_mem v) hy2
    obtain rfl := dD.ofTorus_inj hεeq
    have hεv : ε = ![ε 0, ε 1, ε 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hεv] at hy1 hyz ⊢
    have huv : dD.uv ∈ D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hu : dD.u ∈ D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    rw [← dD.ofTorus_add, om201_add]
    rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;>
      rw [h0, h1, h2] at hy1 hyz ⊢
    · exact absurd (by rw [show (![0, 0, 0] : Fin 3 → ℤ) = 0 by funext i; fin_cases i <;> rfl,
        om201, show (fun i => (0 : Fin 3 → ℤ) i * 2 ^ ((StrothTypeIndex.t201 m).k i - 1)) = 0 by
          funext i; simp, Torus.ofInt_zero, dD.ofTorus_zero]) hy1
    · refine ⟨dD.u, hu, ?_⟩
      rw [dD.conj_ofTorus dD.u_mem dD.u_conj, t201_φu_om, dD.ofTorus_inj.eq_iff, om201_eq_iff hm]
      decide
    · refine ⟨dD.u, hu, ?_⟩
      rw [dD.conj_ofTorus dD.u_mem dD.u_conj, t201_φu_om, dD.ofTorus_inj.eq_iff, om201_eq_iff hm]
      decide
    · exact absurd rfl hyz
    all_goals
      refine ⟨dD.uv, huv, ?_⟩
      rw [dD.conj_ofTorus dD.uv_mem dD.uv_conj, t201_φuv_om hm, dD.ofTorus_inj.eq_iff,
        om201_eq_iff hm]
      decide
  ·
    obtain ⟨q, hq⟩ := t201_d8Act_conj hm i j l hw
    exact ⟨dD.ofTorus q, Subgroup.mem_sup_left (dD.ofTorus_mem q),
      ofTorus_conj_nf dD hq (t201_d8Act_z hm i j l)⟩

theorem t201_comm_c₁ (hm : 1 ≤ m) {v : Torus (StrothTypeIndex.t201 m).k} {i j l : Bool}
    (h : dD.ofTorus v * dD.d8 i j l * (dD.c : G) ^ 2 ^ (m - 1) =
      (dD.c : G) ^ 2 ^ (m - 1) * (dD.ofTorus v * dD.d8 i j l)) : i = false ∧ j = false := by
  rw [c_pow_om, nf_commute_iff] at h
  cases i <;> cases j <;> cases l <;>
    simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, t201_φuv_om hm, t201_φt_om hm, t201_φu_om, om201_eq_iff hm] at h <;>
    first
    | exact ⟨rfl, rfl⟩
    | exact absurd h (by decide)

theorem t201_mem_CSc₁ (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) :
    ∃ (v : Torus (StrothTypeIndex.t201 m).k) (l : Bool),
      y = dD.ofTorus v * dD.d8 false false l := by
  obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨v, i, j, l, rfl⟩ := dD.mem_sup_iff.mp hyS
  rw [Subgroup.mem_centralizer_iff] at hyC
  have hc := hyC _ (Set.mem_singleton _)
  obtain ⟨rfl, rfl⟩ := t201_comm_c₁ dD hm hc.symm
  exact ⟨v, l, rfl⟩

theorem t201_mem_CSc₁_of_not_mem (hm : 1 ≤ m) {y : G}
    (hy : y ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)}) (hyD : y ∉ D) :
    ∃ v : Torus (StrothTypeIndex.t201 m).k, y = dD.ofTorus v * dD.d8 false false true := by
  obtain ⟨v, l, rfl⟩ := t201_mem_CSc₁ dD hm hy
  cases l
  · exact absurd (by rw [dD.d8_fff, mul_one]; exact dD.ofTorus_mem v) hyD
  · exact ⟨v, rfl⟩

theorem t201_h7 (hm : 1 ≤ m) :
    ∀ E : Subgroup G, E ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → (∀ y ∈ E, y * y = 1) →
        Nat.card E ≠ 16 := by
  intro E hE hinv hcard
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have h1 := inv_eq_of_mul_eq_one_right (hinv a ha)
    have h2 := inv_eq_of_mul_eq_one_right (hinv b hb)
    have h3 := inv_eq_of_mul_eq_one_right (hinv _ (mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := h3.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [h1, h2]
  have hD1 : ∀ e ∈ E, e ∈ D → ∃ a b c : Bool,
      e = dD.ofTorus (om201 m ![(a.toNat : ℤ), b.toNat, c.toNat]) := by
    intro e he heD
    obtain ⟨ε, hε, rfl⟩ := t201_eq_om_of_mul_self dD hm heD (hinv e he)
    refine ⟨decide (ε 0 = 1), decide (ε 1 = 1), decide (ε 2 = 1), ?_⟩
    congr 2
    funext i
    fin_cases i <;> simp [bool_toNat_cast_eq (hε _)]
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by simp [Nat.card_eq_fintype_card]
  by_cases hD : ∃ e₀ ∈ E, e₀ ∉ D
  · obtain ⟨e₀, he₀, he₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := t201_mem_CSc₁_of_not_mem dD hm (hE he₀) he₀D
    have hfix : ∀ d ∈ E, d ∈ D → ∃ a b : Bool,
        d = dD.ofTorus (om201 m ![(a.toNat : ℤ), b.toNat, b.toNat]) := by
      intro d hd hdD
      obtain ⟨a, b, c, rfl⟩ := hD1 d hd hdD
      have hc := hcomm _ hd _ he₀
      rw [hv₀] at hc
      have hω := (dD.nf_commute_iff v₀ _ false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply, t201_φu_om, om201_eq_iff hm] at hω
      have h1 := hω 1
      have hbc : c = b := by
        revert h1
        cases a <;> cases b <;> cases c <;> decide
      exact ⟨a, b, by rw [hbc]⟩
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om201 m ![(w.2.1.toNat : ℤ), w.2.2.toNat, w.2.2.toNat]) *
        (if w.1 then e₀ else 1)
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨a, b, hd⟩ := hfix e he heD
        exact ⟨(false, a, b), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := t201_mem_CSc₁_of_not_mem dD hm (hE he) heD
        have hmem : e * e₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨a, b, hd⟩ := hfix (e * e₀⁻¹) (mul_mem he (inv_mem he₀)) hmem
        refine ⟨(true, a, b), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    let f : Bool × Bool × Bool → G := fun w =>
      dD.ofTorus (om201 m ![(w.1.toNat : ℤ), w.2.1.toNat, w.2.2.toNat])
    have hcov : ∀ e ∈ E, ∃ w, f w = e := by
      intro e he
      obtain ⟨a, b, c, hd⟩ := hD1 e he (hD e he)
      exact ⟨(a, b, c), hd.symm⟩
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, h8] at hle
    omega

theorem t201_h9 (hm : 1 ≤ m) :
    ∀ X : Subgroup G, X ≤ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u}) ⊓
      Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)} → IsMulCommutative X →
        Nat.card X = Nat.card D → X = D := by
  intro X hX hab hcard
  have hDcard : Nat.card D = 2 ^ (m + (m + 2) + (m + 2)) := dD.card
  by_cases hD : ∃ x₀ ∈ X, x₀ ∉ D
  · exfalso
    obtain ⟨x₀, hx₀, hx₀D⟩ := hD
    obtain ⟨v₀, hv₀⟩ := t201_mem_CSc₁_of_not_mem dD hm (hX hx₀) hx₀D
    have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    haveI : NeZero (2 ^ m) := ⟨by positivity⟩
    haveI : NeZero (2 ^ (m + 2)) := ⟨by positivity⟩
    have hfix : ∀ d ∈ X, d ∈ D → ∃ (p : ZMod (2 ^ m)) (q : ZMod (2 ^ (m + 2))),
        d = dD.ofTorus (Torus.ofInt _ ![(p.val : ℤ), (q.val : ℤ), (q.val : ℤ)]) := by
      intro d hd hdD
      obtain ⟨v, rfl⟩ := dD.exists_ofTorus hdD
      have hc := hcomm _ hd _ hx₀
      rw [hv₀] at hc
      have hfv := (dD.nf_commute_iff v₀ v false false true).mp hc.symm
      simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
        AddMonoidHom.id_apply] at hfv
      obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
      rw [t201_φu, t201_ofInt_eq_iff] at hfv
      obtain ⟨-, h1, -⟩ := hfv
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      refine ⟨((x 0 : ℤ) : ZMod (2 ^ m)), ((x 1 : ℤ) : ZMod (2 ^ (m + 2))), ?_⟩
      congr 1
      rw [t201_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, ZMod.val_intCast]
      have hm' : ((2 ^ m : ℕ) : ℤ) = 2 ^ m := by push_cast; rfl
      have hm'' : ((2 ^ (m + 2) : ℕ) : ℤ) = 2 ^ (m + 2) := by push_cast; rfl
      rw [hm', hm'']
      refine ⟨⟨-(x 0 / 2 ^ m), by rw [Int.emod_def]; ring⟩, ⟨-(x 1 / 2 ^ (m + 2)), by
        rw [Int.emod_def]; ring⟩, ?_⟩
      obtain ⟨c, hc⟩ := h1
      exact ⟨c - x 1 / 2 ^ (m + 2), by rw [Int.emod_def]; linear_combination hc⟩
    let f : Bool × ZMod (2 ^ m) × ZMod (2 ^ (m + 2)) → G := fun w =>
      dD.ofTorus (Torus.ofInt _ ![(w.2.1.val : ℤ), (w.2.2.val : ℤ), (w.2.2.val : ℤ)]) *
        (if w.1 then x₀ else 1)
    have hcov : ∀ e ∈ X, ∃ w, f w = e := by
      intro e he
      by_cases heD : e ∈ D
      · obtain ⟨p, q, hd⟩ := hfix e he heD
        exact ⟨(false, p, q), by simp [f, hd]⟩
      · obtain ⟨v, hv⟩ := t201_mem_CSc₁_of_not_mem dD hm (hX he) heD
        have hmem : e * x₀⁻¹ ∈ D := by
          rw [hv, hv₀]
          exact dD.nf_u_mul_inv_mem v₀ v
        obtain ⟨p, q, hd⟩ := hfix (e * x₀⁻¹) (mul_mem he (inv_mem hx₀)) hmem
        refine ⟨(true, p, q), ?_⟩
        simp only [f, if_true]
        rw [← hd, inv_mul_cancel_right]
    have hle := Stroth42Core.natCard_le_of_subset_range f hcov
    rw [hcard, hDcard, Nat.card_prod, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hle
    have h2 : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    rw [h2, show 2 * (2 ^ m * 2 ^ (m + 2)) = 2 ^ (m + m + 3) by ring] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · simp only [not_exists, not_and, not_not] at hD
    haveI : Finite D := Nat.finite_of_card_ne_zero (by rw [hDcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge (fun x hx => hD x hx) hcard.ge

end Group

end Stroth44Core

end CFSG.CGT.Stroth77
