module

public import CFSG.CGT.Stroth77.Section47CoreI
public import CFSG.CGT.Stroth77.Section47Harada

public section

namespace CFSG.CGT.Stroth77

open Matrix Stroth42Core Stroth34T200 Stroth47Core

namespace StrothWeakTypeData

section General

variable {G : Type*} [Group G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)

theorem not_mem_sup_of_conj {g : G} {φ : Torus τ.k →+ Torus τ.k}
    (hg : ∀ v, g⁻¹ * dD.ofTorus v * g = dD.ofTorus (φ v))
    (hφ : ∀ i j l, (∀ v, φ v = τ.action.d8Act i j l v) → False) :
    g ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} := by
  intro h
  obtain ⟨w, a, b, c, hw⟩ := dD.mem_sup_iff.mp h
  apply hφ (xor a (c && b)) b c
  intro v
  apply dD.ofTorus_inj
  rw [← hg, hw]
  have h1 : (dD.d8 a b c)⁻¹ * dD.ofTorus v =
      dD.ofTorus (τ.action.d8Act (xor a (c && b)) b c v) * (dD.d8 a b c)⁻¹ := by
    rw [dD.d8_inv, dD.d8_mul_ofTorus]
  have h2 : (dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w = dD.ofTorus v := by
    rw [← dD.ofTorus_neg, ← dD.ofTorus_add, ← dD.ofTorus_add, add_comm (-w) v, add_assoc,
      neg_add_cancel, add_zero]
  calc (dD.ofTorus w * dD.d8 a b c)⁻¹ * dD.ofTorus v * (dD.ofTorus w * dD.d8 a b c)
      = (dD.d8 a b c)⁻¹ * ((dD.ofTorus w)⁻¹ * dD.ofTorus v * dD.ofTorus w) * dD.d8 a b c := by
        group
    _ = (dD.d8 a b c)⁻¹ * dD.ofTorus v * dD.d8 a b c := by rw [h2]
    _ = dD.ofTorus (τ.action.d8Act (xor a (c && b)) b c v) * (dD.d8 a b c)⁻¹ * dD.d8 a b c := by
        rw [h1]
    _ = _ := by group

end General

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {f : G} {p : ℕ}

theorem t200x_cab_pow (p : ℕ) :
    ((dD.c : G) * dD.a * dD.b) ^ p = dD.ofTorus (Torus.ofInt _ ![(p : ℤ), p, p]) := by
  rw [dD.c_eq, dD.a_eq, dD.b_eq, ← dD.ofTorus_add, ← dD.ofTorus_add, ← dD.ofTorus_nsmul,
    c_eq_ofInt, a_eq_ofInt, b_eq_ofInt, t200_add_vec, t200_add_vec, ← natCast_zsmul,
    t200_zsmul_vec]
  norm_num

theorem t200x_a_pow_inv (p : ℕ) :
    ((dD.a : G) ^ p)⁻¹ = dD.ofTorus (Torus.ofInt _ ![0, -(p : ℤ), 0]) := by
  rw [dD.a_eq, ← dD.ofTorus_nsmul, ← dD.ofTorus_neg, a_eq_ofInt, ← natCast_zsmul,
    t200_zsmul_vec, t200_neg_vec]
  norm_num

theorem t200x_conj_ofTorus {M : ℕ} (hrel : Rel34x dD f (2 ^ m) M p)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    f⁻¹ * dD.ofTorus v * f = dD.ofTorus (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m] v) :=
  dD.conj_ofTorus_of_gens
    (by rw [hrel.1.c_conj, torusDiag_gen, ofTorus_zsmul, ← c_eq]; simp)
    (by
      rw [hrel.1.a_conj, torusDiag_gen, ofTorus_zsmul, ← a_eq,
        show (![1, 1 + 2 ^ m, 1 + 2 ^ m] : Fin 3 → ℤ) 1 = 1 + 2 ^ m from rfl,
        _root_.zpow_add, zpow_one,
        show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl, zpow_natCast])
    (by
      rw [hrel.1.b_conj, torusDiag_gen, ofTorus_zsmul, ← b_eq,
        show (![1, 1 + 2 ^ m, 1 + 2 ^ m] : Fin 3 → ℤ) 2 = 1 + 2 ^ m from rfl,
        _root_.zpow_add, zpow_one,
        show ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]) v

theorem t200x_e_conj_uv {M : ℕ} (hrel : Rel34x dD f (2 ^ m) M p) :
    (f * f)⁻¹ * dD.uv * (f * f) =
      dD.ofTorus (Torus.ofInt _ ![2 * (p : ℤ), (2 + 2 ^ m) * p, (2 + 2 ^ m) * p]) * dD.uv := by
  calc (f * f)⁻¹ * dD.uv * (f * f) = f⁻¹ * (f⁻¹ * dD.uv * f) * f := by group
    _ = f⁻¹ * (((dD.c : G) * dD.a * dD.b) ^ p * dD.uv) * f := by rw [hrel.1.uv_conj]
    _ = f⁻¹ * ((dD.c : G) * dD.a * dD.b) ^ p * f * (f⁻¹ * dD.uv * f) := by group
    _ = dD.ofTorus (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m] (Torus.ofInt _ ![(p : ℤ), p, p])) *
        (dD.ofTorus (Torus.ofInt _ ![(p : ℤ), p, p]) * dD.uv) := by
      rw [hrel.1.uv_conj, dD.t200x_cab_pow, dD.t200x_conj_ofTorus hrel]
    _ = _ := by
      rw [← mul_assoc, ← dD.ofTorus_add, torusDiag_ofInt, ← Torus.ofInt_add]
      congr 3
      funext i
      fin_cases i <;> simp <;> ring

theorem t200x_e_conj_t {M : ℕ} (hrel : Rel34x dD f (2 ^ m) M p) :
    (f * f)⁻¹ * dD.t * (f * f) =
      dD.ofTorus (Torus.ofInt _ ![0, -((2 + 2 ^ m) * (p : ℤ)), 0]) * dD.t := by
  calc (f * f)⁻¹ * dD.t * (f * f) = f⁻¹ * (f⁻¹ * dD.t * f) * f := by group
    _ = f⁻¹ * (((dD.a : G) ^ p)⁻¹ * dD.t) * f := by rw [hrel.1.t_conj]
    _ = f⁻¹ * ((dD.a : G) ^ p)⁻¹ * f * (f⁻¹ * dD.t * f) := by group
    _ = dD.ofTorus (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m] (Torus.ofInt _ ![0, -(p : ℤ), 0])) *
        (dD.ofTorus (Torus.ofInt _ ![0, -(p : ℤ), 0]) * dD.t) := by
      rw [hrel.1.t_conj, dD.t200x_a_pow_inv, dD.t200x_conj_ofTorus hrel]
    _ = _ := by
      rw [← mul_assoc, ← dD.ofTorus_add, torusDiag_ofInt, ← Torus.ofInt_add]
      congr 3
      funext i
      fin_cases i <;> simp <;> ring

theorem t200x_e_mul_self (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    f * f * (f * f) = dD.ofTorus (Torus.ofInt _ ![2 ^ (m - 1) - (p : ℤ), 0, 0]) := by
  rw [hrel.2, t200_ofTorus_ofInt3, zpow_zero, zpow_zero, mul_one, mul_one, ← zpow_natCast,
    ← zpow_natCast, ← _root_.zpow_neg, ← _root_.zpow_add]
  congr 1
  push_cast
  ring

@[expose] def t200xEAction (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) : dD.EAction (f * f) where
  φe := (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m]).comp (torusDiag _ ![1, 1 + 2 ^ m, 1 + 2 ^ m])
  wuv := Torus.ofInt _ ![2 * (p : ℤ), (2 + 2 ^ m) * p, (2 + 2 ^ m) * p]
  wt := Torus.ofInt _ ![0, -((2 + 2 ^ m) * (p : ℤ)), 0]
  ve := Torus.ofInt _ ![2 ^ (m - 1) - (p : ℤ), 0, 0]
  conj_ofTorus v := by
    rw [show (f * f)⁻¹ * dD.ofTorus v * (f * f) = f⁻¹ * (f⁻¹ * dD.ofTorus v * f) * f by group,
      dD.t200x_conj_ofTorus hrel, dD.t200x_conj_ofTorus hrel]
    rfl
  conj_uv := dD.t200x_e_conj_uv hrel
  conj_t := dD.t200x_e_conj_t hrel
  conj_u := by
    rw [show (f * f)⁻¹ * dD.u * (f * f) = f⁻¹ * (f⁻¹ * dD.u * f) * f by group, hrel.1.u_conj,
      hrel.1.u_conj]
  mul_self := dD.t200x_e_mul_self hrel

theorem t200xEAction_φe_apply (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) (x : Fin 3 → ℤ) :
    (dD.t200xEAction hrel).φe (Torus.ofInt _ x) =
      Torus.ofInt _
        ![x 0, (1 + 2 ^ m) * ((1 + 2 ^ m) * x 1), (1 + 2 ^ m) * ((1 + 2 ^ m) * x 2)] := by
  show torusDiag _ _ (torusDiag _ _ _) = _
  rw [torusDiag_ofInt, torusDiag_ofInt]
  congr 1
  funext i
  fin_cases i <;> simp

theorem t200xEAction_ve (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    (dD.t200xEAction hrel).ve = Torus.ofInt _ ![2 ^ (m - 1) - (p : ℤ), 0, 0] := rfl

theorem t200xEAction_wuv (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    (dD.t200xEAction hrel).wuv =
      Torus.ofInt _ ![2 * (p : ℤ), (2 + 2 ^ m) * p, (2 + 2 ^ m) * p] := rfl

theorem t200xEAction_wt (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    (dD.t200xEAction hrel).wt = Torus.ofInt _ ![0, -((2 + 2 ^ m) * (p : ℤ)), 0] := rfl

end StrothWeakTypeData

namespace Stroth47Core

variable {m : ℕ}

theorem t200x_φf_om (hm : 1 ≤ m) (ε : Fin 3 → ℤ) :
    torusDiag (StrothTypeIndex.t200 m).k ![1, 1 + 2 ^ m, 1 + 2 ^ m] (om200 m ε) = om200 m ε := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [om200_succ, torusDiag_ofInt, t200_ofInt_eq_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨⟨0, by ring⟩, ⟨-(2 ^ m' * ε 1), by ring⟩, ⟨-(2 ^ m' * ε 2), by ring⟩⟩

theorem t200x_not_word (hm : 1 ≤ m) (i j l : Bool)
    (h : ∀ v, torusDiag (StrothTypeIndex.t200 m).k ![1, 1 + 2 ^ m, 1 + 2 ^ m] v =
      (StrothTypeIndex.t200 m).action.d8Act i j l v) : False := by
  have hc := h (om200 m ![1, 0, 0])
  have ha := h (om200 m ![0, 1, 0])
  rw [t200x_φf_om hm] at hc ha
  obtain ⟨rfl, rfl, rfl⟩ := t200_faithful_om hm i j l hc.symm ha.symm
  have h1 := h (Torus.ofInt _ ![0, 1, 0])
  rw [torusDiag_ofInt] at h1
  simp only [SigmaFourAction.d8Act, Bool.false_eq_true, ↓reduceIte, AddMonoidHom.comp_apply,
    AddMonoidHom.id_apply, t200_ofInt_eq_iff] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1
  obtain ⟨-, ⟨k, hk⟩, -⟩ := h1
  have h2 : (2 : ℤ) ^ m * (-1) = 2 ^ m * (4 * k) := by linear_combination hk
  have h3 := mul_left_cancel₀ (pow_ne_zero m (two_ne_zero : (2 : ℤ) ≠ 0)) h2
  omega

end Stroth47Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t200 m)) {f : G} {p : ℕ}

open Stroth47Core

theorem t200x_not_mem (hm : 1 ≤ m) (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    f ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) := by
  have hS₁ : f ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} :=
    dD.not_mem_sup_of_conj (dD.t200x_conj_ofTorus hrel) fun i j l h =>
      t200x_not_word hm i j l h
  intro hf
  obtain ⟨v, i, j, l, k, hk⟩ := (dD.t200xEAction hrel).mem_sup_zpowers_iff.mp hf
  cases k
  · simp only [bpow, Bool.false_eq_true, ↓reduceIte, mul_one] at hk
    exact hS₁ (hk ▸ dD.nf_mem v i j l)
  · simp only [bpow, ↓reduceIte] at hk
    have hinv : f⁻¹ = dD.ofTorus v * dD.d8 i j l := by
      calc f⁻¹ = f * (f * f)⁻¹ := by group
        _ = dD.ofTorus v * dD.d8 i j l := by
          nth_rewrite 1 [hk]; group
    have h1 := Subgroup.inv_mem _ (hinv ▸ dD.nf_mem v i j l)
    rw [inv_inv] at h1
    exact hS₁ h1

theorem t200x_U_eq (e : G) :
    D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e =
      D ⊔ Subgroup.closure ({dD.uv, dD.t, dD.u} ∪ {e}) := by
  rw [sup_assoc, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]

theorem t200x_U_le_normalizer {e : G} (he : e ∈ Subgroup.normalizer (D : Set G)) :
    D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e ≤
      Subgroup.normalizer (D : Set G) :=
  sup_le (sup_le Subgroup.le_normalizer dD.closure_le_normalizer) ((Subgroup.zpowers_le).2 he)

theorem t200x_conj_mul_inv_mem (hfN : f ∈ Subgroup.normalizer (D : Set G)) {M : ℕ}
    (hrel : Rel34x dD f (2 ^ m) M p) :
    ∀ x ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f),
      f⁻¹ * x * f * x⁻¹ ∈ D := by
  refine Stroth47.conj_mul_inv_mem hfN (dD.t200x_U_le_normalizer (mul_mem hfN hfN))
    (dD.t200x_U_eq _) ?_
  intro x hx
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with (rfl | rfl | rfl) | rfl
  · rw [hrel.1.uv_conj, mul_inv_cancel_right]
    exact D.pow_mem (D.mul_mem (D.mul_mem dD.c.2 dD.a.2) dD.b.2) _
  · rw [hrel.1.t_conj, mul_inv_cancel_right]
    exact D.inv_mem (D.pow_mem dD.a.2 _)
  · rw [hrel.1.u_conj, mul_inv_cancel]
    exact one_mem _
  · rw [show f⁻¹ * (f * f) * f * (f * f)⁻¹ = 1 by group]
    exact one_mem _

theorem t200x_mem_normalizer (hfN : f ∈ Subgroup.normalizer (D : Set G)) {M : ℕ}
    (hrel : Rel34x dD f (2 ^ m) M p) :
    f ∈ Subgroup.normalizer
      ((D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) : Subgroup G) :
        Set G) := by
  set U := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) with hU
  have hDU : D ≤ U := le_sup_left.trans le_sup_left
  have heU : f * f ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hconj : ∀ x ∈ U, f⁻¹ * x * f ∈ U := fun x hx => by
    have := U.mul_mem (hDU (dD.t200x_conj_mul_inv_mem hfN hrel x hx)) hx
    rwa [inv_mul_cancel_right] at this
  rw [Subgroup.mem_normalizer_iff'']
  intro y
  refine ⟨fun hy => hconj y hy, fun hy => ?_⟩
  have h1 : f * f * (f⁻¹ * y * f) * (f * f)⁻¹ ∈ U :=
    U.mul_mem (U.mul_mem heU hy) (U.inv_mem heU)
  have h2 := hconj _ h1
  rwa [show f⁻¹ * (f * f * (f⁻¹ * y * f) * (f * f)⁻¹) * f = y by group] at h2

theorem t200x_mul_self_of_not_mem (hfN : f ∈ Subgroup.normalizer (D : Set G))
    (hrel : Rel34x dD f (2 ^ m) (2 ^ (m - 1)) p) :
    ∀ y ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) ⊔
        Subgroup.zpowers f,
      y ∉ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) →
      ∃ (v : Torus (StrothTypeIndex.t200 m).k) (i : Bool),
        y * y = dD.ofTorus v * dD.d8 i false false * (f * f) := by
  set U := D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers (f * f) with hU
  have hUN : U ≤ Subgroup.normalizer (D : Set G) := dD.t200x_U_le_normalizer (mul_mem hfN hfN)
  have heU : f * f ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hfU := dD.t200x_mem_normalizer hfN hrel
  intro y hy hyU
  obtain ⟨w, hw, k, rfl⟩ := (Stroth47.mem_sup_zpowers_iff_of_mul_self_mem hfU heU).mp hy
  cases k
  · exact absurd (by simpa [bpow] using hw) hyU
  simp only [bpow, ↓reduceIte]
  have hd' : f * w * f⁻¹ * w⁻¹ ∈ D := by
    have hx : f * w * f⁻¹ ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp hfU w).mp hw
      exact this
    have := D.inv_mem (dD.t200x_conj_mul_inv_mem hfN hrel _ hx)
    rwa [show (f⁻¹ * (f * w * f⁻¹) * f * (f * w * f⁻¹)⁻¹)⁻¹ = f * w * f⁻¹ * w⁻¹ by group] at this
  obtain ⟨v₁, hv₁⟩ := dD.exists_ofTorus hd'
  have hwd : w * dD.ofTorus v₁ * w⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hUN hw) _).mp (dD.ofTorus_mem v₁)
  obtain ⟨v₂, hv₂⟩ := dD.exists_ofTorus hwd
  have hsq : w * f * (w * f) = w * dD.ofTorus v₁ * w⁻¹ * (w * w) * (f * f) := by
    have : f * w = dD.ofTorus v₁ * w * f := by
      rw [← hv₁]; group
    calc w * f * (w * f) = w * (f * w) * f := by group
      _ = w * (dD.ofTorus v₁ * w * f) * f := by rw [this]
      _ = _ := by group
  rcases (dD.t200xEAction hrel).mul_self_mem_or w hw with h2 | h2
  · obtain ⟨v₃, hv₃⟩ := dD.exists_ofTorus h2
    refine ⟨v₂ + v₃, false, ?_⟩
    rw [hsq, hv₂, hv₃, d8_fff, mul_one, dD.ofTorus_add]
  · obtain ⟨v₃, hv₃⟩ := dD.exists_ofTorus h2
    refine ⟨v₂ + v₃, true, ?_⟩
    have hww : w * w = dD.ofTorus v₃ * dD.uv := by
      rw [← hv₃, mul_assoc, dD.uv_sq, mul_one]
    rw [hsq, hv₂, hww, d8_tff, dD.ofTorus_add]
    group

end StrothWeakTypeData

end CFSG.CGT.Stroth77
