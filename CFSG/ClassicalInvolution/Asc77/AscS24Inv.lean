module

public import CFSG.ClassicalInvolution.Asc77.AscT7XMem

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

section FrameFacts

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G} (D : T7X.Frame24 p f Ω W)

@[expose] def dEl (c : ℕ) : G := D.eEl c * (D.x₂ ^ D.m)⁻¹

omit [Finite G] in
theorem dEl_mem (c : ℕ) : dEl D c ∈ W :=
  W.mul_mem (D.eEl_mem c) (W.inv_mem (W.pow_mem D.x₂_mem _))

omit [Finite G] in
theorem eEl_eq_dEl_mul (c : ℕ) : D.eEl c = dEl D c * D.x₂ ^ D.m := by
  unfold dEl
  group

omit [Finite G] in
theorem bEl_mem : D.x₁ ^ D.m ∈ D.F.ρ.R :=
  D.F.ρ.R.pow_mem (D.h₁ ▸ Subgroup.mem_zpowers D.x₁ : D.x₁ ∈ D.F.ρ.R ⊓ W).1 _

omit [Finite G] in
theorem bEl'_mem : D.x₂ ^ D.m ∈ D.F.ρ'.R :=
  D.F.ρ'.R.pow_mem (D.h₂ ▸ Subgroup.mem_zpowers D.x₂ : D.x₂ ∈ D.F.ρ'.R ⊓ W).1 _

omit [Finite G] in
theorem orderOf_bEl : orderOf (D.x₁ ^ D.m) = 4 := by
  rw [orderOf_pow_of_dvd (Nat.pos_iff_ne_zero.mp D.hm) ⟨4, by rw [D.o₁]; ring⟩, D.o₁]
  exact Nat.mul_div_cancel _ D.hm

omit [Finite G] in
theorem orderOf_bEl' : orderOf (D.x₂ ^ D.m) = 4 := by
  rw [orderOf_pow_of_dvd (Nat.pos_iff_ne_zero.mp D.hm) ⟨4, by rw [D.o₂]; ring⟩, D.o₂]
  exact Nat.mul_div_cancel _ D.hm

omit [Finite G] in
theorem bEl_sq : D.x₁ ^ D.m * D.x₁ ^ D.m = D.F.z := by
  rw [← pow_add, show D.m + D.m = 2 * D.m by ring, D.z₁]

omit [Finite G] in
theorem bEl'_sq : D.x₂ ^ D.m * D.x₂ ^ D.m = D.F.z := by
  rw [← pow_add, show D.m + D.m = 2 * D.m by ring, D.z₂]

omit [Finite G] in
theorem z_mem : D.F.z ∈ W := D.z₁ ▸ W.pow_mem D.x₁_mem _

omit [Finite G] in
theorem z_sq : D.F.z * D.F.z = 1 := D.F.hz.sq

omit [Finite G] in
theorem bEl_inv : (D.x₁ ^ D.m)⁻¹ = D.x₁ ^ D.m * D.F.z := by
  rw [← bEl_sq D, ← mul_assoc]
  have h4 : D.x₁ ^ D.m * D.x₁ ^ D.m * D.x₁ ^ D.m * D.x₁ ^ D.m = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, show D.m + D.m + D.m + D.m = 4 * D.m by ring, D.pow₁]
  exact (eq_inv_of_mul_eq_one_left h4).symm

omit [Finite G] in
theorem bEl'_inv : (D.x₂ ^ D.m)⁻¹ = D.x₂ ^ D.m * D.F.z := by
  rw [← bEl'_sq D, ← mul_assoc]
  have h4 : D.x₂ ^ D.m * D.x₂ ^ D.m * D.x₂ ^ D.m * D.x₂ ^ D.m = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, show D.m + D.m + D.m + D.m = 4 * D.m by ring, D.pow₂]
  exact (eq_inv_of_mul_eq_one_left h4).symm

omit [Finite G] in
theorem conj_r_bEl : D.F.ρ.r * D.x₁ ^ D.m * D.F.ρ.r⁻¹ = D.x₁ ^ D.m * D.F.z := by
  rw [← conj_pow, D.r₁, inv_pow, bEl_inv]

omit [Finite G] in
theorem conj_r_bEl' : D.F.ρ.r * D.x₂ ^ D.m * D.F.ρ.r⁻¹ = D.x₂ ^ D.m := by
  rw [← conj_pow, D.r₂]

omit [Finite G] in
theorem conj_t_bEl : D.F.ρ'.r * D.x₁ ^ D.m * D.F.ρ'.r⁻¹ = D.x₁ ^ D.m := by
  rw [← conj_pow, D.t₁]

omit [Finite G] in
theorem conj_t_bEl' : D.F.ρ'.r * D.x₂ ^ D.m * D.F.ρ'.r⁻¹ = D.x₂ ^ D.m * D.F.z := by
  rw [← conj_pow, D.t₂, inv_pow, bEl'_inv]

omit [Finite G] in
theorem conj_r_z : D.F.ρ.r * D.F.z * D.F.ρ.r⁻¹ = D.F.z :=
  D.F.hz.conj_eq (conjSub_eq_self_of_mem (D.F.ρ.hRK.1 D.F.ρ.hr))

omit [Finite G] in
theorem conj_t_z : D.F.ρ'.r * D.F.z * D.F.ρ'.r⁻¹ = D.F.z :=
  D.F.hz'.conj_eq (conjSub_eq_self_of_mem (D.F.ρ'.hRK.1 D.F.ρ'.hr))

theorem conj_s_z : D.F.ρ₃.r * D.F.z * D.F.ρ₃.r⁻¹ = D.F.j * D.F.z :=
  D.c.conj_involution D.F.ρ₃ D.F.ρ D.F.hne₁.symm D.F.hn₁' D.F.hj D.F.hz

theorem dEl_t {c : ℕ} (hc : 2 * c = D.m) : D.F.ρ'.r * dEl D c * D.F.ρ'.r⁻¹ = dEl D c := by
  have h1 := D.eEl_t_eq hc
  have h2 := conj_t_bEl' D
  have hzc : D.F.z * (D.x₂ ^ D.m)⁻¹ = (D.x₂ ^ D.m)⁻¹ * D.F.z :=
    (Thompson.commutes_of_mem_WSet D.c.hp D.c.hq D.c.hΩ D.c.hW _ (z_mem D) _
      (W.inv_mem (W.pow_mem D.x₂_mem _)))
  unfold dEl
  calc D.F.ρ'.r * (D.eEl c * (D.x₂ ^ D.m)⁻¹) * D.F.ρ'.r⁻¹
      = (D.F.ρ'.r * D.eEl c * D.F.ρ'.r⁻¹) * (D.F.ρ'.r * D.x₂ ^ D.m * D.F.ρ'.r⁻¹)⁻¹ := by group
    _ = D.eEl c * D.F.z * (D.F.z⁻¹ * (D.x₂ ^ D.m)⁻¹) := by rw [h1, h2]; group
    _ = D.eEl c * (D.x₂ ^ D.m)⁻¹ := by group

theorem dEl_cent_R' {c : ℕ} (hc : 2 * c = D.m) :
    D.F.ρ'.R ≤ Subgroup.centralizer ({dEl D c} : Set G) :=
  T7X.rep_le_centralizer D.c D.F.ρ' (dEl_mem D c) (dEl_t D hc)

theorem dEl_sq {c : ℕ} (hc : 2 * c = D.m)
    (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) : dEl D c * dEl D c = D.F.z := by
  have he := D.eEl_sq hc hZ
  have hcomm : D.eEl c * (D.x₂ ^ D.m)⁻¹ = (D.x₂ ^ D.m)⁻¹ * D.eEl c :=
    Thompson.commutes_of_mem_WSet D.c.hp D.c.hq D.c.hΩ D.c.hW _ (D.eEl_mem c) _
      (W.inv_mem (W.pow_mem D.x₂_mem _))
  have hb := bEl'_sq D
  unfold dEl
  calc D.eEl c * (D.x₂ ^ D.m)⁻¹ * (D.eEl c * (D.x₂ ^ D.m)⁻¹)
      = D.eEl c * ((D.x₂ ^ D.m)⁻¹ * D.eEl c) * (D.x₂ ^ D.m)⁻¹ := by group
    _ = D.eEl c * (D.eEl c * (D.x₂ ^ D.m)⁻¹) * (D.x₂ ^ D.m)⁻¹ := by rw [← hcomm]
    _ = (D.eEl c * D.eEl c) * (D.x₂ ^ D.m * D.x₂ ^ D.m)⁻¹ := by group
    _ = D.F.z := by rw [he, hb, one_mul, inv_eq_of_mul_eq_one_left (z_sq D)]

end FrameFacts

end CFSG.ClassicalInvolution.Asc77.S24
