module

public import CFSG.CGT.Stroth77.DeviationGenericFamilyTwo
public import CFSG.CGT.Stroth77.Section224FrameFin
public import CFSG.CGT.Stroth77.Section225FrameSquare

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

section Generators

variable (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
include hfam

theorem devMat_conj_uv_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.uv⁻¹ * x * dD.uv ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actUvOne (devMat dD hk x hx) :=
  eq_actUvOne_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.uv_mem dD.uv_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).1)
    (fun ε => (familyOne_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).1)
    (fun d _ => conj_commutator x _ d))

theorem devMat_conj_t_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.t⁻¹ * x * dD.t ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actTOne (devMat dD hk x hx) :=
  eq_actTOne_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.t_mem dD.t_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).2.1)
    (fun ε => (familyOne_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.1)
    (fun d _ => conj_commutator x _ d))

theorem devMat_conj_u_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.u⁻¹ * x * dD.u ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actU (devMat dD hk x hx) :=
  eq_actU_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.u_mem dD.u_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).2.2.1)
    (fun ε => (familyOne_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.2.1)
    (fun d _ => conj_commutator x _ d))

variable (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)

theorem sqBar_conj_uv_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.uv⁻¹ * x * dD.uv ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = sqBar dD hk hcent x hx := by
  rw [sqBar_conj hk hcent hx dD.uv_mem hy dD.uv_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).1), Matrix.one_mulVec]

theorem sqBar_conj_t_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.t⁻¹ * x * dD.t ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = sqBar dD hk hcent x hx := by
  rw [sqBar_conj hk hcent hx dD.t_mem hy dD.t_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).2.1), Matrix.one_mulVec]

theorem sqBar_conj_u_familyOne {x : G} (hx : x ∈ 𝓡[S, D])
    (hy : dD.u⁻¹ * x * dD.u ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = barU *ᵥ sqBar dD hk hcent x hx :=
  sqBar_conj hk hcent hx dD.u_mem hy dD.u_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).2.2.1)

end Generators

theorem devMat_proj_rho_familyOne (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hS : Local.Setting S D) {x : G} (hx : x ∈ 𝓡[S, D]) (hy : hS.proj dD.ρ x ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actRhoOne (devMat dD hk x hx) := by
  refine eq_actRhoOne_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.ρ_mem dD.ρ_conj
    (fun v => (familyOne_torusBar hfam (one_le_of_two_le hk) v).2.2.2)
    (fun ε => (familyOne_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.2.2) ?_)
  intro d hd
  have hd' : dD.ρ⁻¹ * d * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem d).mp hd
  have h1 := proj_conj_D_left hS dD.ρ_mem (R_le_setting_R dD hk hS hx) hd'
  calc hS.proj dD.ρ x * (dD.ρ⁻¹ * d * dD.ρ) * (hS.proj dD.ρ x)⁻¹ * (dD.ρ⁻¹ * d * dD.ρ)⁻¹ =
      ((dD.ρ⁻¹ * x * dD.ρ) * (dD.ρ⁻¹ * d * dD.ρ) * (dD.ρ⁻¹ * x * dD.ρ)⁻¹) *
        (dD.ρ⁻¹ * d * dD.ρ)⁻¹ := by rw [h1]
    _ = dD.ρ⁻¹ * (x * d * x⁻¹ * d⁻¹) * dD.ρ := by group

theorem proj_rho_mul_self (hk : ∀ i, 2 ≤ τ.k i) (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    (hS : Local.Setting S D) {x : G} (hx : x ∈ 𝓡[S, D]) :
    hS.proj dD.ρ x * hS.proj dD.ρ x = dD.ρ⁻¹ * (x * x) * dD.ρ := by
  have hxR := R_le_setting_R dD hk hS hx
  rw [← hS.proj_mul dD.ρ_mem hxR hxR]
  apply hS.proj_eq_of_mem
  exact hS.D_le_R ((Subgroup.mem_normalizer_iff''.mp dD.ρ_mem _).mp
    (mul_self_mem_of_mem_R dD hk hcent hx))

theorem sqBar_proj_rho_familyOne (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) (hS : Local.Setting S D) {x : G}
    (hx : x ∈ 𝓡[S, D]) (hy : hS.proj dD.ρ x ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = barRhoOne *ᵥ sqBar dD hk hcent x hx := by
  have h : (⟨hS.proj dD.ρ x * hS.proj dD.ρ x, mul_self_mem_of_mem_R dD hk hcent hy⟩ : D) =
      conjBy dD.ρ_mem ⟨x * x, mul_self_mem_of_mem_R dD hk hcent hx⟩ :=
    Subtype.ext (by simp only [conjBy]; exact proj_rho_mul_self hk hcent hS hx)
  rw [sqBar, h, barD, dD.ρ_conj, (familyOne_torusBar hfam (one_le_of_two_le hk) _).2.2.2]
  rfl

theorem mem_centralizer_omegaIn_iff_familyOne (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    {x : G} (hx : x ∈ 𝓡[S, D]) :
    x ∈ Subgroup.centralizer ((omegaIn (τ.n - 1) D : Subgroup G) : Set G) ↔
      ∀ i, devMat dD hk x hx i 0 = 0 := by
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  have hn : τ.n - 1 = τ.m := by omega
  have hkk := familyOne_k hfam
  constructor
  · intro hc
    have hcΩ : (dD.c : G) ∈ omegaIn (τ.n - 1) D := by
      refine mem_omegaIn_of_pow_eq_one dD.c.2 ?_
      rw [hn, ← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, dD.orderOf_c]
    have hcx := Subgroup.mem_centralizer_iff.mp hc _ hcΩ
    have h := devMat_val_eq (dD := dD) hk x hx dD.c
    have h0 : (⟨x * (dD.c : G) * x⁻¹ * (dD.c : G)⁻¹, omegaIn_le 1 D
        (commutator_mem_omegaIn_one dD hx dD.c.2)⟩ : D) = 1 := Subtype.ext (by
      simp only [Subgroup.coe_one]
      rw [← hcx]; group)
    rw [h0, ofMul_one, map_zero, barD_c] at h
    have h' := torusHalf_injective τ.k (one_le_of_two_le hk) (h.symm.trans (map_zero _).symm)
    intro i
    have := congrFun h' i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  · intro hcol
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hwD, hw2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hw
    have hw' : (⟨w, hwD⟩ : D) ^ (2 ^ τ.m) = 1 := Subtype.ext (by rw [← hn]; simpa using hw2)
    have h1 : barD dD hk ⟨w, hwD⟩ 1 = 0 := barD_eq_zero_of_pow hk hw' (by rw [hkk]; simp)
    have h2 : barD dD hk ⟨w, hwD⟩ 2 = 0 := barD_eq_zero_of_pow hk hw' (by rw [hkk]; simp)
    have := conj_eq_of_devMat_col hk hx hcol h1 h2
    calc w * x = (x * w * x⁻¹) * x := by rw [this]
      _ = x * w := by group

theorem barD_commutator_one_two_familyOne (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D]) :
    barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ 1 = 0 ∧
      barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ 2 = 0 := by
  have hk0 := hk 0
  have hkk := familyOne_k hfam
  have hk3 : 3 ≤ τ.k 1 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  have hk3' : 3 ≤ τ.k 2 := by rw [hkk] at hk0 ⊢; simp at hk0 ⊢; omega
  exact barD_of_pow_four hk hk3 hk3' (commutator_pow_four (dD := dD) hk hcent hx hy)

theorem torusHalf_mulVec_zero_of_row_zero (f : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (hf : f 0 0 = 0 ∧ f 0 1 = 0 ∧ f 0 2 = 0) (v : Fin 3 → ZMod 2) :
    torusHalf τ.k (f *ᵥ v) 0 = 0 := by
  obtain ⟨h1, h2, h3⟩ := hf
  rw [torusHalf_apply]
  have : (f *ᵥ v) 0 = 0 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2, h3]
  rw [this, halfHom_zero]

theorem barD_commutator_zero_familyOne (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D])
    (hfx : devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0)
    (hfy : devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0) :
    barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ 0 = 0 := by
  have hwD : x * y * x⁻¹ * y⁻¹ ∈ D := commutator_mem_D dD hk hcent hx hy
  have hy2 : y * y ∈ D := mul_self_mem_of_mem_R dD hk hcent hy
  set w : D := ⟨x * y * x⁻¹ * y⁻¹, hwD⟩ with hw
  have hid : w * w = (⟨y * (w : G) * y⁻¹ * (w : G)⁻¹, omegaIn_le 1 D
      (commutator_mem_omegaIn_one dD hy w.2)⟩ : D)⁻¹ *
      ⟨x * (y * y) * x⁻¹ * (y * y)⁻¹, omegaIn_le 1 D (commutator_mem_omegaIn_one dD hx hy2)⟩ := by
    apply Subtype.ext
    have hc : (y * (w : G) * y⁻¹) * (w : G) = (w : G) * (y * (w : G) * y⁻¹) :=
      comm_of_mem dD ((Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_mem_R hy) _).mp hwD) hwD
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (w : G) * w = (w : G) * ((y * (w : G) * y⁻¹)⁻¹ * ((y * (w : G) * y⁻¹) * w)) := by group
      _ = (w : G) * ((y * (w : G) * y⁻¹)⁻¹ * ((w : G) * (y * (w : G) * y⁻¹))) := by rw [hc]
      _ = (y * (w : G) * y⁻¹ * (w : G)⁻¹)⁻¹ * (x * (y * y) * x⁻¹ * (y * y)⁻¹) := by
          simp only [hw]; group
  have h1 := devMat_val_eq (dD := dD) hk y hy w
  have h2 := devMat_val_eq (dD := dD) hk x hx ⟨y * y, hy2⟩
  have he : (2 : ℕ) * dD.e (Additive.ofMul w) 0 = 0 := by
    have h3 := congrArg (fun v : Torus τ.k => v 0) (congrArg dD.e (congrArg Additive.ofMul hid))
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg, Pi.add_apply, Pi.neg_apply] at h3
    rw [h1, h2, torusHalf_mulVec_zero_of_row_zero _ hfy, torusHalf_mulVec_zero_of_row_zero _ hfx,
      neg_zero, add_zero] at h3
    rw [← h3]
    push_cast
    ring
  obtain ⟨z, hz⟩ := exists_two_mul_of_two_mul_eq_zero (hk 0) he
  rw [barD, torusBar_apply, ← hz]
  push_cast
  rw [ZMod.cast_mul (dvd_pow_self 2 (by have := hk 0; omega)),
    show ((2 : ZMod (2 ^ τ.k 0)).cast : ZMod 2) = 0 from by
      rw [show (2 : ZMod (2 ^ τ.k 0)) = ((2 : ℕ) : ZMod (2 ^ τ.k 0)) by norm_cast,
        ZMod.cast_natCast (dvd_pow_self 2 (by have := hk 0; omega))]
      decide, zero_mul]

theorem sqBar_mul_of_row_zero (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D) {x y : G} (hx : x ∈ 𝓡[S, D])
    (hy : y ∈ 𝓡[S, D])
    (hfx : devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0)
    (hfy : devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0) :
    sqBar dD hk hcent (x * y) (mul_mem hx hy) =
      sqBar dD hk hcent x hx + sqBar dD hk hcent y hy := by
  rw [sqBar_mul hk hcent hx hy]
  have h0 := barD_commutator_zero_familyOne hk hcent hx hy hfx hfy
  obtain ⟨h1, h2⟩ := barD_commutator_one_two_familyOne (dD := dD) hfam hk hcent hx hy
  have hz : barD dD hk ⟨x * y * x⁻¹ * y⁻¹, commutator_mem_D dD hk hcent hx hy⟩ = 0 := by
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  rw [hz, add_zero]

end DeviationGeneric

end CFSG.CGT.Stroth77
