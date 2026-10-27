module

public import CFSG.CGT.Stroth77.Section225FrameRTwo

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem commutator_pow_four (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) :
    (⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ : D) ^ 4 = 1 := by
  have hwD : x * y * x⁻¹ * y⁻¹ ∈ D := commutator_mem_D dD hk hcent hx hy
  have hy2 : y * y ∈ D := mul_self_mem_of_mem_R dD hk hcent hy
  set w := x * y * x⁻¹ * y⁻¹ with hw
  have hyw : y * w * y⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hy) w).mp hwD
  set a := y * w * y⁻¹ with ha
  have hc : a * w = w * a := comm_of_mem dD hyw hwD
  have h1 : a * w⁻¹ ∈ omegaIn 1 D := commutator_mem_omegaIn_one dD hy hwD
  have h2 : w * a ∈ omegaIn 1 D := by
    have e1 : x * (y * y) * x⁻¹ * (y * y)⁻¹ = w * a := by simp only [hw, ha]; group
    rw [← e1]
    exact commutator_mem_omegaIn_one dD hx hy2
  have key : w * w = (a * w⁻¹)⁻¹ * (w * a) := by
    calc w * w = w * (a⁻¹ * (a * w)) := by group
      _ = w * (a⁻¹ * (w * a)) := by rw [hc]
      _ = (a * w⁻¹)⁻¹ * (w * a) := by group
  have hww : w * w ∈ omegaIn 1 D := by
    rw [key]
    exact mul_mem (inv_mem h1) h2
  have h4 := ((mem_omegaIn_iff_of_comm (fun a ha b hb => comm_of_mem dD ha hb)).mp hww).2
  have h4' : (w * w) ^ 2 = 1 := by simpa using h4
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  calc w ^ 4 = (w * w) ^ 2 := by rw [← pow_two, ← pow_mul]
    _ = 1 := h4'

theorem barD_commutator_one_two (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) :
    barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ 1 = 0 ∧
      barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ 2 = 0 := by
  have hk0 := hk 0
  have hkk := familyTwo_k hfam
  have hk3 : 3 ≤ τ.k 1 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  exact barD_of_pow_four hk hk3 hk3' (commutator_pow_four (dD := dD) hk hcent hx hy)

theorem two_pow_pred_mul_eq_halfHom {n : ℕ} (hn : 1 ≤ n) (v : ZMod (2 ^ n)) :
    (2 : ZMod (2 ^ n)) ^ (n - 1) * v = halfHom n (ZMod.cast v) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective v
  rw [ZMod.cast_intCast (dvd_pow_self 2 (by omega)), halfHom_eq_intCast]
  obtain ⟨t, ht⟩ := two_dvd_sub_val_of_intCast_eq (rfl : ((z : ℤ) : ZMod 2) = (z : ZMod 2))
  have h2n : (2 : ℤ) ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have e : (2 : ℤ) ^ (n - 1) * (((z : ZMod 2).val : ℕ) : ℤ) = 2 ^ (n - 1) * z - 2 ^ n * t := by
    rw [h2n]
    linear_combination (-(2 : ℤ) ^ (n - 1)) * ht
  rw [e]
  push_cast
  have h0 : (2 : ZMod (2 ^ n)) ^ n = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ n)
  rw [h0]
  ring

section WithS

variable (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
  (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {s : G} (hs : s ∈ 𝓡[S, D])
  (hd : devMat dD hk s hs = devD) (hs2 : s * s = (dD.c : G))

include hfam hcent hd

theorem conj_commutator_s_eq {x : G} (hx : x ∈ 𝓡[S, D]) :
    s * (x * s * x⁻¹ * s⁻¹) * s⁻¹ = x * s * x⁻¹ * s⁻¹ := by
  obtain ⟨h1, h2⟩ := barD_commutator_one_two (dD := dD) hfam hk hcent hx hs
  obtain ⟨-, h00, -, -, h10, h20⟩ := devD_block
  refine conj_eq_of_devMat_col (w := ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩)
    hk hs (fun i => ?_) h1 h2
  rw [hd]
  fin_cases i
  · exact h00
  · exact h10
  · exact h20

include hs2

theorem torusHalf_devMat_mulVec_c {x : G} (hx : x ∈ 𝓡[S, D]) :
    torusHalf τ.k (devMat dD hk x hx *ᵥ ![1, 0, 0]) =
      (2 : ℤ) • dD.e (Additive.ofMul
        (⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ : D)) := by
  have hsw := conj_commutator_s_eq hfam hk hcent hs hd hx
  set w : D := ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩
  have hxc : (⟨x * (dD.c : G) * x⁻¹ * (dD.c : G)⁻¹,
      omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx dD.c.2)⟩ : D) = w * w := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, w]
    rw [← hs2]
    calc x * (s * s) * x⁻¹ * (s * s)⁻¹ =
          (x * s * x⁻¹ * s⁻¹) * (s * (x * s * x⁻¹ * s⁻¹) * s⁻¹) := by group
      _ = (x * s * x⁻¹ * s⁻¹) * (x * s * x⁻¹ * s⁻¹) := by rw [hsw]
  have h := devMat_val_eq (dD := dD) hk x hx dD.c
  rw [barD_c, hxc] at h
  rw [← h, ofMul_mul, map_add, two_zsmul]

theorem devMat_mulVec_c_add_barD {x : G} (hx : x ∈ 𝓡[S, D]) :
    devMat dD hk x hx *ᵥ
        (![1, 0, 0] + barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩) =
      devD *ᵥ sqBar dD hk hcent x hx := by
  have h3 := torusHalf_devMat_mulVec_c hfam hk hcent hs hd hs2 hx
  have hx2 := mul_self_mem_of_mem_R dD hk hcent hx
  set w : D := ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩
  have hid : (⟨s * (x * x) * s⁻¹ * (x * x)⁻¹,
      omegaIn_le 1 D (commutator_mem_omegaIn_one dD hs hx2)⟩ : D) =
      w⁻¹ * w⁻¹ * (⟨x * (w : G) * x⁻¹ * (w : G)⁻¹,
        omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx w.2)⟩ : D)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, w]
    group
  have h1 := devMat_val_eq (dD := dD) hk s hs ⟨x * x, hx2⟩
  have h2 := devMat_val_eq (dD := dD) hk x hx w
  rw [hd, hid] at h1
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg] at h1
  rw [h2] at h1
  have hneg : ∀ ε, -torusHalf τ.k ε = torusHalf τ.k ε := fun ε => by
    rw [← map_neg]
    congr 1
    funext i
    exact CharTwo.neg_eq (ε i)
  have e1 : -dD.e (Additive.ofMul w) + -dD.e (Additive.ofMul w) =
      (2 : ℤ) • dD.e (Additive.ofMul w) := by
    rw [← neg_add, ← two_zsmul, ← h3, hneg]
  apply torusHalf_injective τ.k (one_le_of_two_le hk)
  rw [Matrix.mulVec_add, map_add, h3,
    show sqBar dD hk hcent x hx = barD dD hk ⟨x * x, hx2⟩ from rfl, ← h1, e1, hneg]

theorem barD_commutator_zero_eq (hm2 : τ.m = 2) {x : G} (hx : x ∈ 𝓡[S, D]) :
    barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ 0 =
      devMat dD hk x hx 0 0 := by
  have h := congrFun (torusHalf_devMat_mulVec_c hfam hk hcent hs hd hs2 hx) 0
  have hk0 : τ.k 0 = 2 := by rw [familyTwo_k hfam]; simp [hm2]
  have hmv : (devMat dD hk x hx *ᵥ ![1, 0, 0]) 0 = devMat dD hk x hx 0 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [torusHalf_apply, hmv, Pi.smul_apply, zsmul_eq_mul, Int.cast_ofNat] at h
  have h2 := two_pow_pred_mul_eq_halfHom (one_le_of_two_le hk 0)
    (dD.e (Additive.ofMul (⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ : D)) 0)
  rw [show τ.k 0 - 1 = 1 by omega, pow_one] at h2
  exact (halfHom_injective (one_le_of_two_le hk 0) (h.trans h2)).symm

theorem devMat_mulVec_c_eq {x : G} (hx : x ∈ 𝓡[S, D])
    (h : 3 ≤ τ.m ∨ devMat dD hk x hx 0 0 = 0) :
    devMat dD hk x hx *ᵥ ![1, 0, 0] = devD *ᵥ sqBar dD hk hcent x hx := by
  have hw : barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ = 0 := by
    obtain ⟨h1, h2⟩ := barD_commutator_one_two (dD := dD) hfam hk hcent hx hs
    have h0 : barD dD hk ⟨x * s * x⁻¹ * s⁻¹, commutator_mem_D dD hk hcent hx hs⟩ 0 = 0 := by
      have hk0 := hk 0
      rw [familyTwo_k hfam] at hk0
      simp at hk0
      rcases Nat.lt_or_ge τ.m 3 with hlt | hge
      · have hm2 : τ.m = 2 := by omega
        rw [barD_commutator_zero_eq hfam hk hcent hs hd hs2 hm2 hx]
        rcases h with h | h
        · omega
        · exact h
      · refine barD_eq_zero_of_pow (dD := dD) hk (j := 2)
          (commutator_pow_four (dD := dD) hk hcent hx hs) ?_
        rw [familyTwo_k hfam]
        simp
        omega
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have := devMat_mulVec_c_add_barD hfam hk hcent hs hd hs2 hx
  rwa [hw, add_zero] at this

end WithS

end DeviationGeneric

end CFSG.CGT.Stroth77
