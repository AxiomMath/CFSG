module

public import CFSG.CGT.M24S.Extraspecial
public import CFSG.CGT.M24S.NSDefs

public section

namespace CFSG.CGT.M24S.NSSecond

open Matrix GL4

variable {G : Type} [Group G]

theorem card_sup_le_of_le_normalizer {N K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (N ⊔ K : Subgroup G) ≤ Nat.card N * Nat.card K := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_mul_of_right_le_normalizer_left N K h]
  exact Set.natCard_mul_le

theorem mem_normalizer_of_map_le [Finite G] {N : Subgroup G} {x : G}
    (h : N.map (MulAut.conj x).toMonoidHom ≤ N) : x ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

theorem le_normalizer_of_commute {N K : Subgroup G} (h : ∀ a ∈ N, ∀ b ∈ K, a * b = b * a) :
    K ≤ Subgroup.normalizer (N : Set G) :=
  le_trans (fun b hb => Subgroup.mem_centralizer_iff.2 fun a ha => h a ha b hb)
    (Subgroup.centralizer_le_normalizer _)

theorem card_zpowers_le_two {a : G} (ha : a * a = 1) : Nat.card (Subgroup.zpowers a) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one two_pos (by rw [pow_two, ha])

theorem card_dihedral_le {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 4 = 1) :
    Nat.card (Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a : Subgroup G) ≤ 8 := by
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hconj : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    calc a * (a * b) * a⁻¹ = (a * a) * b * a⁻¹ := by group
      _ = b⁻¹ * a⁻¹ := by rw [ha, one_mul, hbi]
      _ = (a * b)⁻¹ := (mul_inv_rev a b).symm
  have hn : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Subgroup.zpowers (a * b) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * (a * b) * a⁻¹) = _
    rw [hconj, Subgroup.zpowers_inv]
  calc _ ≤ Nat.card (Subgroup.zpowers (a * b)) * Nat.card (Subgroup.zpowers a) :=
        card_sup_le_of_le_normalizer hn
    _ ≤ 4 * 2 := Nat.mul_le_mul (by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) hab) (card_zpowers_le_two ha)

@[expose] def tauA : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1,0,0,0; 0,1,1,0; 0,0,1,0; 0,0,0,1]

@[expose] def tauB : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1,0,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1]

@[expose] def tauC : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1,0,0,0; 0,1,0,1; 0,0,1,0; 0,0,0,1]

@[expose] def dihedralMat (p : Fin 4 × Fin 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  (tauA * tauB) ^ (p.1 : ℕ) * tauA ^ (p.2 : ℕ)

@[expose] def LiftData (τ : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  τ *ᵥ e0 = e0 ∧ (∀ v : Fin 4 → ZMod 2, (v + τ *ᵥ v = 0 ∨ v + τ *ᵥ v = e0) → v + τ *ᵥ v = 0) ∧
    ∃ M : Matrix (Fin 4) (Fin 4) (ZMod 2), M * M = 1 ∧ M * mk4 ![0, 0, 1] 1 = τ * M

theorem liftData_tauA : LiftData tauA :=
  ⟨by decide, by decide, !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0], by decide, by decide⟩

theorem liftData_tauB : LiftData tauB :=
  ⟨by decide, by decide, !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1], by decide, by decide⟩

theorem liftData_tauC : LiftData tauC :=
  ⟨by decide, by decide, !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1], by decide, by decide⟩

theorem tauA_mul_self : tauA * tauA = 1 := by decide

theorem tauB_mul_self : tauB * tauB = 1 := by decide

theorem tauA_mul_tauB_sq : tauA * tauB * (tauA * tauB) = tauC := by decide

theorem blk_dihedralMat_injective :
    ∀ p q : Fin 4 × Fin 2, blk (dihedralMat p) = blk (dihedralMat q) → p = q := by
  decide

theorem det_eq_one_of_mul_self' {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : M * M = 1) :
    M.det = 1 :=
  zmod_two_eq_one_of_mul_self _ (by rw [← det_mul, h, det_one])

variable {T H : Subgroup G} {z : G} (c : NatCoord T H z)

theorem vec_inv {s : G} (hs : s ∈ T) : c.vec s⁻¹ = c.vec s := by
  have h := c.vec_mul (T.inv_mem hs) hs
  rw [inv_mul_cancel, c.vec_one] at h
  have h2 := congrArg (· + c.vec s) h
  simp only [zero_add, add_assoc, vec_add_self, add_zero] at h2
  exact h2.symm

theorem mulVec_eq_of_blk_eq_one {g : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hg : g *ᵥ e0 = e0)
    (hb : blk g = 1) (v : Fin 4 → ZMod 2) : g *ᵥ v = v + (top g ⬝ᵥ tail v) • e0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [mulVec_apply_zero g hg]
    simp
  · have h := congrFun (tail_mulVec g hg v) j
    rw [hb, one_mulVec] at h
    change (g *ᵥ v) j.succ = v j.succ + (top g ⬝ᵥ tail v) • e0 j.succ
    rw [show e0 j.succ = 0 from Pi.single_eq_of_ne (Fin.succ_ne_zero j) 1, smul_zero, add_zero]
    exact h

theorem top_mul_of_mem_E {x y : G} (hx : x ∈ c.E) (hy : y ∈ c.E) :
    top (c.mat (x * y)) = top (c.mat x) + top (c.mat y) := by
  rw [c.mat_mul (c.mem_H_of_mem_E hx) (c.mem_H_of_mem_E hy),
    top_mul _ _ (c.mulVec_e0_of_mem_E hx), c.blk_of_mem_E hy, vecMul_one, add_comm]

theorem top_inv_of_mem_E {x : G} (hx : x ∈ c.E) : top (c.mat x⁻¹) = top (c.mat x) := by
  have h := top_mul_of_mem_E c (c.E.inv_mem hx) hx
  rw [inv_mul_cancel, c.mat_one, top_one] at h
  have h2 := congrArg (· + top (c.mat x)) h
  simp only [zero_add, add_assoc, vec_add_self, add_zero] at h2
  exact h2.symm

theorem mem_T_of_top_eq_zero {x : G} (hx : x ∈ c.E) (h : top (c.mat x) = 0) : x ∈ T := by
  rw [← c.mat_eq_one_iff (c.mem_H_of_mem_E hx), c.mat_eq_mk4_of_mem_E hx, h, mk4_zero_one]

theorem vec_commutator {y s : G} (hy : y ∈ c.E) (hs : s ∈ T) :
    y⁻¹ * s * y * s⁻¹ ∈ T ∧
      c.vec (y⁻¹ * s * y * s⁻¹) = (top (c.mat y) ⬝ᵥ tail (c.vec s)) • e0 := by
  have hyi : y⁻¹ ∈ c.E := c.E.inv_mem hy
  have h1 : y⁻¹ * s * y ∈ T := by
    have := c.conj_mem (c.mem_H_of_mem_E hyi) hs
    rwa [inv_inv] at this
  refine ⟨T.mul_mem h1 (T.inv_mem hs), ?_⟩
  have h2 : c.vec (y⁻¹ * s * y) = c.mat y⁻¹ *ᵥ c.vec s := by
    have := c.vec_conj (c.mem_H_of_mem_E hyi) hs
    rwa [inv_inv] at this
  rw [c.vec_mul h1 (T.inv_mem hs), h2, vec_inv c hs,
    mulVec_eq_of_blk_eq_one (c.mulVec_e0_of_mem_E hyi) (c.blk_of_mem_E hyi),
    top_inv_of_mem_E c hy, add_comm (c.vec s), add_assoc, vec_add_self, add_zero]

theorem conj_eq_of_dotProduct_eq_zero {y s : G} (hy : y ∈ c.E) (hs : s ∈ T)
    (h : top (c.mat y) ⬝ᵥ tail (c.vec s) = 0) : s * y * s⁻¹ = y := by
  obtain ⟨hm, hv⟩ := vec_commutator c hy hs
  rw [h, zero_smul] at hv
  have h1 : y⁻¹ * s * y * s⁻¹ = 1 := c.eq_of_vec_eq hm T.one_mem (hv.trans c.vec_one.symm)
  calc s * y * s⁻¹ = y * (y⁻¹ * s * y * s⁻¹) := by group
    _ = y := by rw [h1, mul_one]

theorem conj_eq_of_dotProduct_eq_one {y s : G} (hy : y ∈ c.E) (hs : s ∈ T)
    (h : top (c.mat y) ⬝ᵥ tail (c.vec s) = 1) : s * y * s⁻¹ = y * z := by
  obtain ⟨hm, hv⟩ := vec_commutator c hy hs
  rw [h, one_smul] at hv
  have h1 : y⁻¹ * s * y * s⁻¹ = z := c.eq_of_vec_eq hm c.mem (hv.trans c.vec_z.symm)
  calc s * y * s⁻¹ = y * (y⁻¹ * s * y * s⁻¹) := by group
    _ = y * z := by rw [h1]

theorem tail_e0 : tail e0 = 0 := by decide

theorem tail_cons_zero (u : Fin 3 → ZMod 2) : tail (Fin.cons 0 u : Fin 4 → ZMod 2) = u :=
  funext fun i => Fin.cons_succ (α := fun _ => ZMod 2) 0 u i

theorem mem_E_of_centreTransvecting {w : G}
    (hw : w ∈ H ⊓ Subgroup.centralizer ({z} : Set G)) (hc : CentreTransvecting T z w) :
    w ∈ c.E := by
  have he := (c.mem_centralizer_iff hw.1).1 hw.2
  refine (c.mem_E_iff).2 ⟨hw.1, he, eq_one_of_forall_mulVec_eq fun u => ?_⟩
  obtain ⟨s, hs, hsv⟩ := c.exists_vec_eq (Fin.cons 0 u)
  have key : tail (c.mat w *ᵥ c.vec s) = tail (c.vec s) := by
    rw [← c.vec_conj hw.1 hs]
    rcases hc s hs with h | h
    · have : w * s * w⁻¹ = s := by
        calc w * s * w⁻¹ = w * s * w⁻¹ * s⁻¹ * s := by group
          _ = s := by rw [h, one_mul]
      rw [this]
    · have : w * s * w⁻¹ = z * s := by
        calc w * s * w⁻¹ = w * s * w⁻¹ * s⁻¹ * s := by group
          _ = z * s := by rw [h]
      rw [this, c.vec_mul c.mem hs, c.vec_z, tail_add, tail_e0, zero_add]
  rwa [tail_mulVec _ he, hsv, tail_cons_zero] at key

include c in
theorem card_zpowers_z : Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime c.z_sq c.z_ne_one

theorem exists_mem_top_eq {W : Subgroup G} (hWE : W ≤ c.E) (hW16 : Nat.card W = 16)
    (hWT : W ⊓ T = Subgroup.zpowers z) (x : Fin 3 → ZMod 2) :
    ∃ w ∈ W, top (c.mat w) = x := by
  let f : W →* Multiplicative (Fin 3 → ZMod 2) := c.τ.comp (Subgroup.inclusion hWE)
  have hker : f.ker = T.subgroupOf W := by
    ext w
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker,
      show f w = c.τ (Subgroup.inclusion hWE w) from rfl, ← MonoidHom.mem_ker, c.ker_τ,
      Subgroup.mem_subgroupOf]
    rfl
  have hk : Nat.card f.ker = 2 := by
    rw [hker, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, hWT,
      card_zpowers_z c]
  have hr : Nat.card f.range = 8 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hk, hW16] at h1
    omega
  have htop : f.range = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hr, NatCoord.card_vec]
    norm_num
  obtain ⟨w, hw⟩ := (MonoidHom.range_eq_top.1 htop) (Multiplicative.ofAdd x)
  refine ⟨w, w.2, Multiplicative.ofAdd.injective ?_⟩
  rw [← hw]
  exact (c.τ_apply (Subgroup.inclusion hWE w)).symm

end CFSG.CGT.M24S.NSSecond
