module

public import CFSG.CGT.Stroth77.DeviationGenericAniso
public import CFSG.CGT.Stroth77.Section225FrameFin
public import CFSG.CGT.Stroth77.Section226Bridge
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

omit [Finite G] in
theorem conj_mem_R {l x : G} (hlS : l ∈ S) (hlN : l ∈ Subgroup.normalizer (D : Set G))
    (hx : x ∈ 𝓡[S, D]) : l⁻¹ * x * l ∈ 𝓡[S, D] := by
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hlS)
    (mem_S_of_mem_R hx)) hlS, mul_mem (mul_mem (inv_mem hlN) (mem_normalizer_of_mem_R hx)) hlN⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have hle : l * e * l⁻¹ ∈ mhoOne D :=
    CFSG.GroupTheory.HuppertProduct.conj_mem_mho
      (fun s hs => (Subgroup.mem_normalizer_iff.mp hlN s).mp hs) he
  have hc := Subgroup.mem_centralizer_iff.mp (mem_centralizer_of_mem_R hx) _ hle
  calc e * (l⁻¹ * x * l) = l⁻¹ * ((l * e * l⁻¹) * x) * l := by group
    _ = l⁻¹ * (x * (l * e * l⁻¹)) * l := by rw [hc]
    _ = l⁻¹ * x * l * e := by group

omit [Finite G] in
theorem conj_commutator (x l d : G) :
    (l⁻¹ * x * l) * (l⁻¹ * d * l) * (l⁻¹ * x * l)⁻¹ * (l⁻¹ * d * l)⁻¹ =
      l⁻¹ * (x * d * x⁻¹ * d⁻¹) * l := by
  group

section Generators

variable (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
include hfam

theorem devMat_conj_uv {x : G} (hx : x ∈ 𝓡[S, D]) (hy : dD.uv⁻¹ * x * dD.uv ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actUv (devMat dD hk x hx) :=
  eq_actUv_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.uv_mem dD.uv_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).1)
    (fun ε => (familyTwo_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).1)
    (fun d _ => conj_commutator x _ d))

theorem devMat_conj_t {x : G} (hx : x ∈ 𝓡[S, D]) (hy : dD.t⁻¹ * x * dD.t ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actT (devMat dD hk x hx) :=
  eq_actT_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.t_mem dD.t_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).2.1)
    (fun ε => (familyTwo_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.1)
    (fun d _ => conj_commutator x _ d))

theorem devMat_conj_u {x : G} (hx : x ∈ 𝓡[S, D]) (hy : dD.u⁻¹ * x * dD.u ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actU (devMat dD hk x hx) :=
  eq_actU_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.u_mem dD.u_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).2.2.1)
    (fun ε => (familyTwo_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.2.1)
    (fun d _ => conj_commutator x _ d))

variable (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)

theorem sqBar_conj_uv {x : G} (hx : x ∈ 𝓡[S, D]) (hy : dD.uv⁻¹ * x * dD.uv ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = barUv *ᵥ sqBar dD hk hcent x hx :=
  sqBar_conj hk hcent hx dD.uv_mem hy dD.uv_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).1)

theorem sqBar_conj_t {x : G} (hx : x ∈ 𝓡[S, D]) (hy : dD.t⁻¹ * x * dD.t ∈ 𝓡[S, D]) :
    sqBar dD hk hcent _ hy = barT *ᵥ sqBar dD hk hcent x hx :=
  sqBar_conj hk hcent hx dD.t_mem hy dD.t_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).2.1)

end Generators

theorem R_le_setting_R (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i)
    (hS : Local.Setting S D) : 𝓡[S, D] ≤ hS.R := fun _ hx =>
  Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
    Subgroup.centralizer_le (omegaIn_one_le_mhoOne dD hk) (mem_centralizer_of_mem_R hx)⟩

theorem proj_mem_R (dD : StrothWeakTypeData D τ) (hk : ∀ i, 2 ≤ τ.k i) (hS : Local.Setting S D)
    {x : G} (hx : x ∈ 𝓡[S, D]) : hS.proj dD.ρ x ∈ 𝓡[S, D] :=
  Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp
      (hS.proj_mem dD.ρ_mem (R_le_setting_R dD hk hS hx))).1,
    hS.proj_mem_centralizer_mhoOne dD.ρ_mem (R_le_setting_R dD hk hS hx)
      (mem_centralizer_of_mem_R hx)⟩

theorem proj_conj_D_left (hS : Local.Setting S D) {g r : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ hS.R) {d : G} (hd : d ∈ D) :
    hS.proj g r * d * (hS.proj g r)⁻¹ = (g⁻¹ * r * g) * d * (g⁻¹ * r * g)⁻¹ := by
  set p := hS.proj g r
  set z := g⁻¹ * r * g
  have hp : p ∈ Subgroup.normalizer (D : Set G) := hS.R_le_normalizer (hS.proj_mem hg hr)
  have he : p * d * p⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hp d).mp hd
  have h := hS.proj_conj_D hg hr he
  have h1 : p⁻¹ * (p * d * p⁻¹) * p = d := by group
  rw [h1] at h
  calc p * d * p⁻¹ = z * (z⁻¹ * (p * d * p⁻¹) * z) * z⁻¹ := by group
    _ = z * d * z⁻¹ := by rw [← h]

theorem devMat_proj_rho (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i) (hS : Local.Setting S D)
    {x : G} (hx : x ∈ 𝓡[S, D]) (hy : hS.proj dD.ρ x ∈ 𝓡[S, D]) :
    devMat dD hk _ hy = actRho (devMat dD hk x hx) := by
  refine eq_actRho_of_mul _ _ (devMat_mul_eq_of_conj hk hx hy dD.ρ_mem dD.ρ_conj
    (fun v => (familyTwo_torusBar hfam (one_le_of_two_le hk) v).2.2.2)
    (fun ε => (familyTwo_torusHalf hfam (le_trans (by norm_num) (hk 0)) ε).2.2.2) ?_)
  intro d hd
  have hd' : dD.ρ⁻¹ * d * dD.ρ ∈ D := (Subgroup.mem_normalizer_iff''.mp dD.ρ_mem d).mp hd
  have h1 := proj_conj_D_left hS dD.ρ_mem (R_le_setting_R dD hk hS hx) hd'
  calc hS.proj dD.ρ x * (dD.ρ⁻¹ * d * dD.ρ) * (hS.proj dD.ρ x)⁻¹ * (dD.ρ⁻¹ * d * dD.ρ)⁻¹ =
      ((dD.ρ⁻¹ * x * dD.ρ) * (dD.ρ⁻¹ * d * dD.ρ) * (dD.ρ⁻¹ * x * dD.ρ)⁻¹) *
        (dD.ρ⁻¹ * d * dD.ρ)⁻¹ := by rw [h1]
    _ = dD.ρ⁻¹ * (x * d * x⁻¹ * d⁻¹) * dD.ρ := by group

theorem mem_centralizer_omegaIn_iff (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i) {x : G}
    (hx : x ∈ 𝓡[S, D]) :
    x ∈ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ↔
      ∀ i, devMat dD hk x hx i 0 = 0 := by
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb => comm_of_mem dD ha hb
  have hn : τ.n - 2 = τ.m := by omega
  have hkk := familyTwo_k hfam
  constructor
  · intro hc
    have hcΩ : (dD.c : G) ∈ omegaIn (τ.n - 2) D := by
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

end DeviationGeneric

end CFSG.CGT.Stroth77
