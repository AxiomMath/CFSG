module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Torus
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Pairing

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped commutatorElement

section Norm

variable {F : Type} [Field F] {b c : F}

theorem exists_planeNorm_eq [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) (r : F) : ∃ a : Fin 2 → F, planeNorm b c a = r := by
  classical
  have := Fintype.ofFinite F
  set D : F := c - b ^ 2 / 4 with hD
  have hD0 : D ≠ 0 := by
    intro h
    apply hirr (-(b / 2))
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have : (-(b / 2)) ^ 2 + b * (-(b / 2)) + c = D := by
      rw [hD]
      field_simp
      ring
    rw [this, h]
  open Polynomial in
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f := (X ^ 2 - C r : F[X])) (g := (C D * X ^ 2 : F[X]))
    (by exact degree_X_pow_sub_C (by norm_num) r)
    (by exact degree_C_mul_X_pow 2 hD0)
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd)
  refine ⟨![x - b / 2 * y, y], ?_⟩
  simp at hxy
  simp only [planeNorm, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  rw [hD] at hxy
  field_simp at hxy ⊢
  linear_combination hxy

end Norm

section Decomposition

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem commute_AB_C {x y : spinGroup (quadMinus 3 F b c)}
    (hx : x ∈ (qA b c).range ⊔ (qB hirr).range) (hy : y ∈ (qC b c).range) : x * y = y * x := by
  have : (qA b c).range ⊔ (qB hirr).range ≤ Subgroup.centralizer ({y} : Set _) := sup_le
    (fun a ha => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_qA_qC hirr ha hy)
    (fun a ha => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_qB_qC hirr ha hy)
  exact Subgroup.mem_centralizer_singleton_iff.1 (this hx)

theorem mem_Qsub_iff {g : spinGroup (quadMinus 3 F b c)} :
    g ∈ Qsub hirr ↔ ∃ (x : F) (w : Fin 2 → F) (y : F),
      g = qA b c (.ofAdd x) * qB hirr (.ofAdd w) * qC b c (.ofAdd y) := by
  constructor
  · intro hg
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_normalizes (Q := (qA b c).range ⊔ (qB hirr).range)
      (A := (qC b c).range) (fun a ha q hq => by
        have := commute_AB_C hirr hq ha
        rw [← this, mul_inv_cancel_right]
        exact hq)).1 hg
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := (mem_sup_iff_of_normalizes (Q := (qA b c).range)
      (A := (qB hirr).range) (fun a ha q hq => by
        have := commute_qA_qB hirr hq ha
        rw [← this, mul_inv_cancel_right]
        exact hq)).1 hu
    obtain ⟨x, rfl⟩ := hu₁
    obtain ⟨w, rfl⟩ := hu₂
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x.toAdd, w.toAdd, y.toAdd, rfl⟩
  · rintro ⟨x, w, y, rfl⟩
    exact (Qsub hirr).mul_mem ((Qsub hirr).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨.ofAdd x, rfl⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨.ofAdd w, rfl⟩)))
      (Subgroup.mem_sup_right ⟨.ofAdd y, rfl⟩)

theorem qABC_mul (x₁ x₂ y₁ y₂ : F) (w₁ w₂ : Fin 2 → F) :
    (qA b c (.ofAdd x₁) * qB hirr (.ofAdd w₁) * qC b c (.ofAdd y₁)) *
        (qA b c (.ofAdd x₂) * qB hirr (.ofAdd w₂) * qC b c (.ofAdd y₂)) =
      qA b c (.ofAdd (x₁ + x₂)) * qB hirr (.ofAdd (w₁ + w₂)) * qC b c (.ofAdd (y₁ + y₂)) := by
  have h1 : qC b c (.ofAdd y₁) * qA b c (.ofAdd x₂) = qA b c (.ofAdd x₂) * qC b c (.ofAdd y₁) :=
    (commute_qA_qC hirr ⟨_, rfl⟩ ⟨_, rfl⟩).symm
  have h2 : qC b c (.ofAdd y₁) * qB hirr (.ofAdd w₂) = qB hirr (.ofAdd w₂) * qC b c (.ofAdd y₁) :=
    (commute_qB_qC hirr ⟨_, rfl⟩ ⟨_, rfl⟩).symm
  have h3 : qB hirr (.ofAdd w₁) * qA b c (.ofAdd x₂) = qA b c (.ofAdd x₂) * qB hirr (.ofAdd w₁) :=
    (commute_qA_qB hirr ⟨_, rfl⟩ ⟨_, rfl⟩).symm
  rw [ofAdd_add, ofAdd_add, ofAdd_add, map_mul, map_mul, map_mul]
  calc qA b c (.ofAdd x₁) * qB hirr (.ofAdd w₁) * qC b c (.ofAdd y₁) *
        (qA b c (.ofAdd x₂) * qB hirr (.ofAdd w₂) * qC b c (.ofAdd y₂))
      = qA b c (.ofAdd x₁) * qB hirr (.ofAdd w₁) * (qC b c (.ofAdd y₁) * qA b c (.ofAdd x₂)) *
        qB hirr (.ofAdd w₂) * qC b c (.ofAdd y₂) := by group
    _ = qA b c (.ofAdd x₁) * (qB hirr (.ofAdd w₁) * qA b c (.ofAdd x₂)) * qC b c (.ofAdd y₁) *
        qB hirr (.ofAdd w₂) * qC b c (.ofAdd y₂) := by rw [h1]; group
    _ = qA b c (.ofAdd x₁) * qA b c (.ofAdd x₂) * qB hirr (.ofAdd w₁) *
        (qC b c (.ofAdd y₁) * qB hirr (.ofAdd w₂)) * qC b c (.ofAdd y₂) := by rw [h3]; group
    _ = _ := by rw [h2]; group

end Decomposition

section Rho

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

variable (b c) in
@[expose] noncomputable def rhoA (x : F) : spinGroup (quadMinus 3 F b c) := qA b c (.ofAdd x)

variable (b c) in
@[expose] noncomputable def rhoC (x : F) : spinGroup (quadMinus 3 F b c) := qC b c (.ofAdd x)

@[expose] noncomputable def rhoB (w : Fin 2 → F) : spinGroup (quadMinus 3 F b c) :=
  qB hirr (.ofAdd w)

@[expose] noncomputable def rhoN (w : Fin 2 → F) : spinGroup (quadMinus 3 F b c) :=
  nN hirr (.ofAdd w)

theorem rhoA_add (x y : F) : rhoA b c (x + y) = rhoA b c x * rhoA b c y := by
  simp [rhoA, ofAdd_add]

theorem rhoC_add (x y : F) : rhoC b c (x + y) = rhoC b c x * rhoC b c y := by
  simp [rhoC, ofAdd_add]

theorem rhoB_add (w w' : Fin 2 → F) : rhoB hirr (w + w') = rhoB hirr w * rhoB hirr w' := by
  simp [rhoB, ofAdd_add]

theorem rhoN_add (w w' : Fin 2 → F) : rhoN hirr (w + w') = rhoN hirr w * rhoN hirr w' := by
  simp [rhoN, ofAdd_add]

theorem rhoA_comm (x y : F) : rhoA b c x * rhoA b c y = rhoA b c y * rhoA b c x :=
  commute_of_mem_range (qA b c) ⟨_, rfl⟩ ⟨_, rfl⟩

theorem rhoC_comm (x y : F) : rhoC b c x * rhoC b c y = rhoC b c y * rhoC b c x :=
  commute_of_mem_range (qC b c) ⟨_, rfl⟩ ⟨_, rfl⟩

theorem rhoB_comm (w w' : Fin 2 → F) : rhoB hirr w * rhoB hirr w' = rhoB hirr w' * rhoB hirr w :=
  commute_of_mem_range (qB hirr) ⟨_, rfl⟩ ⟨_, rfl⟩

theorem rhoN_comm (w w' : Fin 2 → F) : rhoN hirr w * rhoN hirr w' = rhoN hirr w' * rhoN hirr w :=
  commute_of_mem_range (nN hirr) ⟨_, rfl⟩ ⟨_, rfl⟩

theorem rhoA_rhoB (x : F) (w : Fin 2 → F) : rhoA b c x * rhoB hirr w = rhoB hirr w * rhoA b c x :=
  commute_qA_qB hirr ⟨_, rfl⟩ ⟨_, rfl⟩

include hirr in
theorem rhoA_rhoC (x y : F) : rhoA b c x * rhoC b c y = rhoC b c y * rhoA b c x :=
  commute_qA_qC hirr ⟨_, rfl⟩ ⟨_, rfl⟩

theorem rhoB_rhoC (w : Fin 2 → F) (y : F) : rhoB hirr w * rhoC b c y = rhoC b c y * rhoB hirr w :=
  commute_qB_qC hirr ⟨_, rfl⟩ ⟨_, rfl⟩

theorem planeNorm_ne_zero_of_ne {a : Fin 2 → F} {r : F} (hr : r ≠ 0) (h : planeNorm b c a = r) :
    a ≠ 0 := by
  rintro rfl
  rw [planeNorm_zero] at h
  exact hr h.symm

end Rho

section Pairings

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {E : Type*} [Group E] {π : E →* spinGroup (quadMinus 3 F b c)}
  (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)
  (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)

include hirr hcen hπ h2 hodd h5 in
theorem pair_AA (x y : F) {a b' : E} (ha : π a = rhoA b c x) (hb : π b' = rhoA b c y) :
    ⁅a, b'⁆ = 1 := by
  refine pair_eq_one_of_scalar hcen hπ (rhoA b c) rhoA_add rhoA_comm (exists_good_scalar h5) ?_
    x y ha hb
  intro r hr
  obtain ⟨a', ha'⟩ := exists_planeNorm_eq hirr h2 hodd r⁻¹
  have ha0 : a' ≠ 0 := planeNorm_ne_zero_of_ne (inv_ne_zero hr) ha'
  obtain ⟨g, hg⟩ := hπ (sT hirr a')
  refine ⟨g, fun v => ?_⟩
  rw [hg]
  change sT hirr a' * qA b c (.ofAdd v) * (sT hirr a')⁻¹ = qA b c (.ofAdd (r • v))
  rw [sT_conj_qA hirr ha0, ha', inv_inv, smul_eq_mul]

include hirr hcen hπ h2 hodd h5 in
theorem pair_CC (x y : F) {a b' : E} (ha : π a = rhoC b c x) (hb : π b' = rhoC b c y) :
    ⁅a, b'⁆ = 1 := by
  refine pair_eq_one_of_scalar hcen hπ (rhoC b c) rhoC_add rhoC_comm (exists_good_scalar h5) ?_
    x y ha hb
  intro r hr
  obtain ⟨a', ha'⟩ := exists_planeNorm_eq hirr h2 hodd r
  have ha0 : a' ≠ 0 := planeNorm_ne_zero_of_ne hr ha'
  obtain ⟨g, hg⟩ := hπ (sT hirr a')
  refine ⟨g, fun v => ?_⟩
  rw [hg]
  change sT hirr a' * qC b c (.ofAdd v) * (sT hirr a')⁻¹ = qC b c (.ofAdd (r • v))
  rw [sT_conj_qC hirr ha0, ha', smul_eq_mul]

include hirr hcen hπ h5 in
theorem pair_BB (w w' : Fin 2 → F) {a b' : E} (ha : π a = rhoB hirr w) (hb : π b' = rhoB hirr w') :
    ⁅a, b'⁆ = 1 := by
  refine pair_eq_one_of_scalar hcen hπ (rhoB hirr) (rhoB_add hirr) (rhoB_comm hirr)
    (exists_good_scalar h5) ?_ w w' ha hb
  intro r hr
  obtain ⟨g, hg⟩ := hπ (dT b c (Units.mk0 r hr))
  refine ⟨g, fun v => ?_⟩
  rw [hg]
  exact dT_conj_qB hirr (Units.mk0 r hr) v

include hirr hcen hπ h5 in
theorem pair_NN (w w' : Fin 2 → F) {a b' : E} (ha : π a = rhoN hirr w) (hb : π b' = rhoN hirr w') :
    ⁅a, b'⁆ = 1 := by
  refine pair_eq_one_of_scalar hcen hπ (rhoN hirr) (rhoN_add hirr) (rhoN_comm hirr)
    (exists_good_scalar h5) ?_ w w' ha hb
  intro r hr
  obtain ⟨g, hg⟩ := hπ (dT b c (Units.mk0 r hr)⁻¹)
  refine ⟨g, fun v => ?_⟩
  rw [hg]
  have := dT_conj_nN hirr (Units.mk0 r hr)⁻¹ v
  rw [inv_inv] at this
  exact this

include h5 in
theorem exists_sq_ne_one : ∃ t : Fˣ, (t : F) ^ 2 ≠ 1 := by
  obtain ⟨t, ht⟩ := CFSG.ClassicalInvolution.ModelFacts.OddCover.exists_unit_sq_ne_one h5
  exact ⟨t, fun h => ht (Units.ext (by simpa using h))⟩

include hirr hcen hπ h5 in
theorem pair_AB (x : F) (w : Fin 2 → F) {a b' : E} (ha : π a = rhoA b c x)
    (hb : π b' = rhoB hirr w) : ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  obtain ⟨g, hg⟩ := hπ (sT hirr ((t : F) • planeOne))
  refine pair_eq_one_of_scale_left hcen hπ (rhoA b c) (rhoB hirr) rhoA_add
    (fun x w => rhoA_rhoB hirr x w) (α := ((t : F) ^ 2)⁻¹) (fun h => ht (by simpa using h))
    (g := g) (fun v => ?_) (fun v => ?_) x w ha hb
  · rw [hg]
    exact sT_smul_conj_qA hirr ht0 v
  · rw [hg]
    exact sT_smul_conj_qB hirr ht0 v

include hirr hcen hπ h5 in
theorem pair_BA (w : Fin 2 → F) (x : F) {a b' : E} (ha : π a = rhoB hirr w)
    (hb : π b' = rhoA b c x) : ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  obtain ⟨g, hg⟩ := hπ (sT hirr ((t : F) • planeOne))
  refine pair_eq_one_of_scale_right hcen hπ (rhoB hirr) (rhoA b c) rhoA_add
    (fun w x => (rhoA_rhoB hirr x w).symm) (β := ((t : F) ^ 2)⁻¹)
    (fun h => ht (by simpa using h)) (g := g) (fun v => ?_) (fun v => ?_) w x ha hb
  · rw [hg]
    exact sT_smul_conj_qB hirr ht0 v
  · rw [hg]
    exact sT_smul_conj_qA hirr ht0 v

include hirr hcen hπ h5 in
theorem pair_AC (x y : F) {a b' : E} (ha : π a = rhoA b c x) (hb : π b' = rhoC b c y) :
    ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  obtain ⟨g, hg⟩ := hπ (dT b c t)
  refine pair_eq_one_of_scale_left hcen hπ (rhoA b c) (rhoC b c) rhoA_add
    (fun x y => rhoA_rhoC hirr x y) (α := (t : F) ^ 2) ht (g := g) (fun v => ?_) (fun v => ?_)
    x y ha hb
  · rw [hg]
    exact dT_conj_qA t v
  · rw [hg]
    exact dT_conj_qC t v

include hirr hcen hπ h5 in
theorem pair_CA (y x : F) {a b' : E} (ha : π a = rhoC b c y) (hb : π b' = rhoA b c x) :
    ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  obtain ⟨g, hg⟩ := hπ (dT b c t)
  refine pair_eq_one_of_scale_right hcen hπ (rhoC b c) (rhoA b c) rhoA_add
    (fun y x => (rhoA_rhoC hirr x y).symm) (β := (t : F) ^ 2) ht (g := g) (fun v => ?_)
    (fun v => ?_) y x ha hb
  · rw [hg]
    exact dT_conj_qC t v
  · rw [hg]
    exact dT_conj_qA t v

include hirr hcen hπ h5 in
theorem pair_BC (w : Fin 2 → F) (y : F) {a b' : E} (ha : π a = rhoB hirr w)
    (hb : π b' = rhoC b c y) : ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  have ht1 : (t : F) ≠ 1 := fun h => ht (by rw [h]; norm_num)
  obtain ⟨g, hg⟩ := hπ (dT b c t)
  refine pair_eq_one_of_scale_left hcen hπ (rhoB hirr) (rhoC b c) (rhoB_add hirr)
    (fun w y => rhoB_rhoC hirr w y) (α := (t : F)) ht1 (g := g) (fun v => ?_) (fun v => ?_)
    w y ha hb
  · rw [hg]
    exact dT_conj_qB hirr t v
  · rw [hg]
    exact dT_conj_qC t v

include hirr hcen hπ h5 in
theorem pair_CB (y : F) (w : Fin 2 → F) {a b' : E} (ha : π a = rhoC b c y)
    (hb : π b' = rhoB hirr w) : ⁅a, b'⁆ = 1 := by
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  have ht1 : (t : F) ≠ 1 := fun h => ht (by rw [h]; norm_num)
  obtain ⟨g, hg⟩ := hπ (dT b c t)
  refine pair_eq_one_of_scale_right hcen hπ (rhoC b c) (rhoB hirr) (rhoB_add hirr)
    (fun y w => (rhoB_rhoC hirr w y).symm) (β := (t : F)) ht1 (g := g) (fun v => ?_)
    (fun v => ?_) y w ha hb
  · rw [hg]
    exact dT_conj_qC t v
  · rw [hg]
    exact dT_conj_qB hirr t v

include hirr hcen hπ h2 hodd h5 in
theorem commute_lifts {x x' : F} {w w' : Fin 2 → F} {y y' : F} {a₁ a₂ a₃ b₁ b₂ b₃ : E}
    (ha₁ : π a₁ = rhoA b c x) (ha₂ : π a₂ = rhoB hirr w) (ha₃ : π a₃ = rhoC b c y)
    (hb₁ : π b₁ = rhoA b c x') (hb₂ : π b₂ = rhoB hirr w') (hb₃ : π b₃ = rhoC b c y') :
    Commute (a₁ * a₂ * a₃) (b₁ * b₂ * b₃) := by
  have c11 : Commute a₁ b₁ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_AA hirr hcen hπ h2 hodd h5 x x' ha₁ hb₁)
  have c12 : Commute a₁ b₂ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_AB hirr hcen hπ h5 x w' ha₁ hb₂)
  have c13 : Commute a₁ b₃ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_AC hirr hcen hπ h5 x y' ha₁ hb₃)
  have c21 : Commute a₂ b₁ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_BA hirr hcen hπ h5 w x' ha₂ hb₁)
  have c22 : Commute a₂ b₂ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_BB hirr hcen hπ h5 w w' ha₂ hb₂)
  have c23 : Commute a₂ b₃ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_BC hirr hcen hπ h5 w y' ha₂ hb₃)
  have c31 : Commute a₃ b₁ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_CA hirr hcen hπ h5 y x' ha₃ hb₁)
  have c32 : Commute a₃ b₂ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_CB hirr hcen hπ h5 y w' ha₃ hb₂)
  have c33 : Commute a₃ b₃ := commutatorElement_eq_one_iff_mul_comm.1
    (pair_CC hirr hcen hπ h2 hodd h5 y y' ha₃ hb₃)
  exact (((c11.mul_right c12).mul_right c13).mul_left ((c21.mul_right c22).mul_right c23)).mul_left
    ((c31.mul_right c32).mul_right c33)

end Pairings

section Hat

variable {F : Type} [Field F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {E : Type*} [Group E] (π : E →* spinGroup (quadMinus 3 F b c))

@[expose] noncomputable def Qhat6 : Subgroup E := (Qsub hirr).comap π

@[expose] noncomputable def Ahat6 : Subgroup E := (Nsub hirr).comap π

variable {π}

theorem mem_Qhat6 {g : E} : g ∈ Qhat6 hirr π ↔ π g ∈ Qsub hirr := Iff.rfl

theorem mem_Ahat6 {g : E} : g ∈ Ahat6 hirr π ↔ π g ∈ Nsub hirr := Iff.rfl

theorem ker_le_Qhat6 : π.ker ≤ Qhat6 hirr π := fun c hc => by
  rw [mem_Qhat6, MonoidHom.mem_ker.1 hc]
  exact (Qsub hirr).one_mem

theorem Ahat6_conj_Qhat6 {a q : E} (ha : a ∈ Ahat6 hirr π) (hq : q ∈ Qhat6 hirr π) :
    a * q * a⁻¹ ∈ Qhat6 hirr π := by
  rw [mem_Qhat6, map_mul, map_mul, map_inv]
  exact Nsub_conj_Qsub hirr ha hq

theorem Uhat6_eq (hπ : Function.Surjective π) :
    (Qsub hirr ⊔ Nsub hirr).comap π = Qhat6 hirr π ⊔ Ahat6 hirr π := by
  refine le_antisymm ?_ (sup_le (Subgroup.comap_mono le_sup_left) (Subgroup.comap_mono le_sup_right))
  intro g hg
  obtain ⟨q, hq, n, hn, hqn⟩ := (mem_sup_iff_of_normalizes (Q := Qsub hirr) (A := Nsub hirr)
    (fun a ha q hq => Nsub_conj_Qsub hirr ha hq)).1 hg
  obtain ⟨s, hs⟩ := hπ n
  have hsA : s ∈ Ahat6 hirr π := by
    rw [mem_Ahat6, hs]
    exact hn
  have hgs : g * s⁻¹ ∈ Qhat6 hirr π := by
    rw [mem_Qhat6, map_mul, map_inv, hs, hqn, mul_inv_cancel_right]
    exact hq
  have : g = (g * s⁻¹) * s := by group
  rw [this]
  exact Subgroup.mul_mem_sup hgs hsA

theorem exists_decomp (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π) {g : E}
    (hg : g ∈ Qhat6 hirr π) :
    ∃ (x : F) (w : Fin 2 → F) (y : F) (a₁ a₂ a₃ z : E), π a₁ = rhoA b c x ∧ π a₂ = rhoB hirr w ∧
      π a₃ = rhoC b c y ∧ z ∈ Subgroup.center E ∧ g = a₁ * a₂ * a₃ * z := by
  obtain ⟨x, w, y, hxwy⟩ := (mem_Qsub_iff hirr).1 hg
  obtain ⟨a₁, ha₁⟩ := hπ (rhoA b c x)
  obtain ⟨a₂, ha₂⟩ := hπ (rhoB hirr w)
  obtain ⟨a₃, ha₃⟩ := hπ (rhoC b c y)
  refine ⟨x, w, y, a₁, a₂, a₃, (a₁ * a₂ * a₃)⁻¹ * g, ha₁, ha₂, ha₃, hcen ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, ha₁, ha₂, ha₃, hxwy]
  exact inv_mul_cancel _

section Kappa

variable (b c) in
@[expose] noncomputable def tri (x : F) (w : Fin 2 → F) (y : F) : spinGroup (quadMinus 3 F b c) :=
  qA b c (.ofAdd x) * qB hirr (.ofAdd w) * qC b c (.ofAdd y)

theorem tri_mul (x₁ x₂ y₁ y₂ : F) (w₁ w₂ : Fin 2 → F) :
    tri b c hirr x₁ w₁ y₁ * tri b c hirr x₂ w₂ y₂ =
      tri b c hirr (x₁ + x₂) (w₁ + w₂) (y₁ + y₂) :=
  qABC_mul hirr x₁ x₂ y₁ y₂ w₁ w₂

theorem tri_zero : tri b c hirr 0 0 0 = 1 := by
  simp [tri]

theorem mem_Qsub_iff_tri {g : spinGroup (quadMinus 3 F b c)} :
    g ∈ Qsub hirr ↔ ∃ x w y, g = tri b c hirr x w y := mem_Qsub_iff hirr

theorem zT_conj_tri (t : Fˣ) (x : F) (w : Fin 2 → F) (y : F) :
    zT hirr t * tri b c hirr x w y * (zT hirr t)⁻¹ =
      tri b c hirr ((t : F) ^ 2 * x) ((t : F) ^ 2 • w) ((t : F) ^ 2 * y) := by
  have e : zT hirr t * tri b c hirr x w y * (zT hirr t)⁻¹ =
      (zT hirr t * qA b c (.ofAdd x) * (zT hirr t)⁻¹) *
        (zT hirr t * qB hirr (.ofAdd w) * (zT hirr t)⁻¹) *
        (zT hirr t * qC b c (.ofAdd y) * (zT hirr t)⁻¹) := by
    rw [tri]
    group
  rw [e, zT_conj_qA, zT_conj_qB, zT_conj_qC]
  rfl

theorem zT_conj_tri_pow (t : Fˣ) (i : ℕ) (x : F) (w : Fin 2 → F) (y : F) :
    (zT hirr t) ^ i * tri b c hirr x w y * ((zT hirr t) ^ i)⁻¹ =
      tri b c hirr (((t : F) ^ 2) ^ i * x) (((t : F) ^ 2) ^ i • w) (((t : F) ^ 2) ^ i * y) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : (zT hirr t) ^ (i + 1) * tri b c hirr x w y * ((zT hirr t) ^ (i + 1))⁻¹ =
        zT hirr t * ((zT hirr t) ^ i * tri b c hirr x w y * ((zT hirr t) ^ i)⁻¹) *
          (zT hirr t)⁻¹ := by
      rw [pow_succ']
      group
    rw [e, ih, zT_conj_tri]
    simp only [pow_succ', mul_assoc, smul_smul]

theorem zT_inv_conj_tri (t : Fˣ) (x : F) (w : Fin 2 → F) (y : F) :
    (zT hirr t)⁻¹ * tri b c hirr x w y * zT hirr t =
      tri b c hirr (((t : F) ^ 2)⁻¹ * x) (((t : F) ^ 2)⁻¹ • w) (((t : F) ^ 2)⁻¹ * y) := by
  have h0 : (t : F) ^ 2 ≠ 0 := pow_ne_zero 2 t.ne_zero
  have h := zT_conj_tri hirr t (((t : F) ^ 2)⁻¹ * x) (((t : F) ^ 2)⁻¹ • w) (((t : F) ^ 2)⁻¹ * y)
  rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul, smul_smul, mul_inv_cancel₀ h0, one_smul,
    ← mul_assoc, mul_inv_cancel₀ h0, one_mul] at h
  rw [← h]
  group

end Kappa

section HatComm

variable [Finite F] (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)
  (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)

include hirr hcen hπ h2 hodd h5 in
theorem Qhat6_comm : ∀ a ∈ Qhat6 hirr π, ∀ a' ∈ Qhat6 hirr π, a * a' = a' * a := by
  intro a ha a' ha'
  obtain ⟨x, w, y, a₁, a₂, a₃, z, ha₁, ha₂, ha₃, hz, rfl⟩ := exists_decomp hirr hcen hπ ha
  obtain ⟨x', w', y', b₁, b₂, b₃, z', hb₁, hb₂, hb₃, hz', rfl⟩ := exists_decomp hirr hcen hπ ha'
  have hc := commute_lifts hirr hcen hπ h2 hodd h5 ha₁ ha₂ ha₃ hb₁ hb₂ hb₃
  have h1 : Commute (a₁ * a₂ * a₃) (b₁ * b₂ * b₃ * z') :=
    hc.mul_right (Subgroup.mem_center_iff.1 hz' _)
  exact (h1.mul_left (Subgroup.mem_center_iff.1 hz _).symm)

include hirr hcen hπ h5 in
theorem Ahat6_comm : ∀ a ∈ Ahat6 hirr π, ∀ a' ∈ Ahat6 hirr π, a * a' = a' * a := by
  intro a ha a' ha'
  obtain ⟨u, hu⟩ := (mem_Ahat6 hirr).1 ha
  obtain ⟨u', hu'⟩ := (mem_Ahat6 hirr).1 ha'
  exact commutatorElement_eq_one_iff_mul_comm.1
    (pair_NN hirr hcen hπ h5 u.toAdd u'.toAdd hu.symm hu'.symm)

include hirr hcen hπ h2 hodd h5 in
theorem exists_kappa6 [Finite E] {p f : ℕ} [hp : Fact p.Prime] (hF : Nat.card F = p ^ f)
    (hf : 1 ≤ f) (hker : IsPGroup p π.ker) :
    ∃ κ : E → E, (∀ y ∈ Qhat6 hirr π, κ y ∈ π.ker) ∧
      (∀ y ∈ Qhat6 hirr π, ∀ y' ∈ Qhat6 hirr π, κ (y * y') = κ y * κ y') ∧
      (∀ c' ∈ π.ker, κ c' = c') ∧
      ∀ g ∈ Ahat6 hirr π, ∀ y ∈ Qhat6 hirr π, κ (g * y * g⁻¹) = κ y := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨t, ht⟩ := exists_sq_ne_one h5
  set ν : F := (t : F) ^ 2 with hν
  have hν0 : ν ≠ 0 := pow_ne_zero 2 t.ne_zero
  have hν1 : ν ≠ 1 := ht
  obtain ⟨z, hz⟩ := hπ (zT hirr t)
  set m := Nat.card F - 1 with hm
  have hmK : Nat.Coprime m (Nat.card π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
    rw [hk]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_))
    intro hdvd
    have hpq : p ∣ Nat.card F := by rw [hF]; exact dvd_pow_self p (by omega)
    have := Nat.dvd_sub hpq hdvd
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hconjpow : ∀ (i : ℕ) (y : E) (x' : F) (w' : Fin 2 → F) (y' : F),
      π y = tri b c hirr x' w' y' →
      π (z ^ i * y * (z ^ i)⁻¹) = tri b c hirr (ν ^ i * x') (ν ^ i • w') (ν ^ i * y') := by
    intro i y x' w' y' hy
    rw [map_mul, map_mul, map_inv, map_pow, hz, hy]
    exact zT_conj_tri_pow hirr t i x' w' y'
  have hnorm : ∀ (n : ℕ) (y : E) (x' : F) (w' : Fin 2 → F) (y' : F), π y = tri b c hirr x' w' y' →
      π (normSum z y n) = tri b c hirr ((∑ i ∈ Finset.range n, ν ^ i) * x')
        ((∑ i ∈ Finset.range n, ν ^ i) • w') ((∑ i ∈ Finset.range n, ν ^ i) * y') := by
    intro n y x' w' y' hy
    induction n with
    | zero => simp [tri_zero]
    | succ n ih =>
      rw [normSum_succ, map_mul, ih, hconjpow n y x' w' y' hy, tri_mul, Finset.sum_range_succ]
      simp only [add_mul, add_smul]
  have hgeom : ∑ i ∈ Finset.range m, ν ^ i = 0 := by
    have h1 := geom_sum_mul ν m
    have h2' : ν ^ m = 1 := by
      rw [hm, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one ν hν0
    rw [h2', sub_self] at h1
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hν1)
  have hN : ∀ y ∈ Qhat6 hirr π, normSum z y m ∈ π.ker := by
    intro y hy
    obtain ⟨x', w', y', hxy⟩ := (mem_Qsub_iff_tri hirr).1 hy
    rw [MonoidHom.mem_ker, hnorm m y x' w' y' hxy, hgeom, zero_mul, zero_smul, zero_mul, tri_zero]
  have hzY : ∀ y ∈ Qhat6 hirr π, z * y * z⁻¹ ∈ Qhat6 hirr π := by
    intro y hy
    obtain ⟨x', w', y', hxy⟩ := (mem_Qsub_iff_tri hirr).1 hy
    rw [mem_Qhat6, map_mul, map_mul, map_inv, hz, hxy, zT_conj_tri]
    exact (mem_Qsub_iff_tri hirr).2 ⟨_, _, _, rfl⟩
  have hzY' : ∀ y ∈ Qhat6 hirr π, z⁻¹ * y * z ∈ Qhat6 hirr π := by
    intro y hy
    obtain ⟨x', w', y', hxy⟩ := (mem_Qsub_iff_tri hirr).1 hy
    rw [mem_Qhat6, map_mul, map_mul, map_inv, hz, hxy, zT_inv_conj_tri]
    exact (mem_Qsub_iff_tri hirr).2 ⟨_, _, _, rfl⟩
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_retraction_fun (Y := Qhat6 hirr π)
    (K := π.ker) (ker_le_Qhat6 hirr) hcen (Qhat6_comm hirr hcen hπ h2 hodd h5) hzY hzY' hmK hN
  refine ⟨κ, hκK, hκmul, hκid, fun g hg y hy => ?_⟩
  refine hκinv g (fun y hy => Ahat6_conj_Qhat6 hirr hg hy) (fun y _ => ?_) y hy
  refine conj_conj_comm_of_comm_mem_center (comm_mem_center_of_commute_map hcen ?_) y
  obtain ⟨u, hu⟩ := (mem_Ahat6 hirr).1 hg
  change π g * π z = π z * π g
  rw [← hu, hz]
  have h3 := zT_conj_nN hirr t u.toAdd
  rw [ofAdd_toAdd] at h3
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

end HatComm

section Main

variable [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = p ^ f) (hf : 1 ≤ f) (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
  (h5 : 5 ≤ Nat.card F)

omit [CharP F p] in
include hirr hF hf h2 hodd h5 in
theorem spinMinus6_commutator_inf_ker_eq_bot [Finite E] (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hker : IsPGroup p π.ker) :
    ⁅(Qsub hirr ⊔ Nsub hirr).comap π, (Qsub hirr ⊔ Nsub hirr).comap π⁆ ⊓ π.ker = ⊥ := by
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_kappa6 hirr hcen hπ h2 hodd h5 hF hf hker
  rw [Uhat6_eq hirr hπ]
  exact commutator_sup_inf_eq_bot_of_sieg (C := π.ker) (Q := Qhat6 hirr π) (A := Ahat6 hirr π)
    (Ahat6_comm hirr hcen hπ h5) (fun a ha q hq => Ahat6_conj_Qhat6 hirr ha hq) hκmul hκid
    (fun y hy => hcen (hκK y hy)) hκinv

include hirr hF hf h2 hodd h5 in
theorem spinMinus6_ker_eq_bot_of_isPGroup [Finite E] [Group.IsPerfect E]
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hker : IsPGroup p π.ker) :
    π.ker = ⊥ :=
  ker_eq_bot_of_commutator_inf_eq_bot π hπ hcen hker (isPGroup_Usub hirr)
    (not_dvd_index_Usub hirr hF hf h2)
    (spinMinus6_commutator_inf_ker_eq_bot hirr hF hf h2 hodd h5 hπ hcen hker)

end Main

end Hat

end CFSG.ClassicalInvolution.WeakCT
