module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesSp6
public import CFSG.LieType.Steinberg.CentralExt.SpTorus

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance f4PilotMainGraphTorusLeviNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Param

variable {K : Type} [Field K]

@[expose] def c3TorusParam (t : Fin 3 → Kˣ) : Fin (Tag.rank .F4) → Kˣ :=
  ![(t 0 * t 1 * t 2)⁻¹, t 2 * t 2, t 1 * (t 2)⁻¹, t 0 * (t 1)⁻¹]

theorem c3TorusParam_apply_zero (t : Fin 3 → Kˣ) : c3TorusParam t 0 = (t 0 * t 1 * t 2)⁻¹ :=
  rfl

theorem c3TorusParam_apply_one (t : Fin 3 → Kˣ) : c3TorusParam t 1 = t 2 * t 2 :=
  rfl

theorem c3TorusParam_apply_two (t : Fin 3 → Kˣ) : c3TorusParam t 2 = t 1 * (t 2)⁻¹ :=
  rfl

theorem c3TorusParam_apply_three (t : Fin 3 → Kˣ) : c3TorusParam t 3 = t 0 * (t 1)⁻¹ :=
  rfl

theorem c3Torus_toStd_eq (γ : Fin 3 → ℤ) : toStd 3 γ = ![γ 0, γ 1 - γ 0, 2 * γ 2 - γ 1] := by
  funext a
  fin_cases a <;> simp [toStd]

theorem rootChar_c3TorusParam_c3ToF4 (t : Fin 3 → Kˣ) (γ : Fin 3 → ℤ) :
    rootChar (c3TorusParam t) (c3ToF4 γ) = CentralExt.SpTorus.chi (toStd 3 γ) t := by
  rw [c3Torus_toStd_eq]
  change (∏ i : Fin 4, c3TorusParam t i ^ c3ToF4 γ i) = ∏ a : Fin 3, t a ^ _
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, c3ToF4_apply]
  simp only [c3TorusParam, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

theorem c3Torus_sp6ParamA_apply (a : Kˣ) : sp6ParamA K a = ![a, 1, 1] := by
  funext i
  fin_cases i <;> simp [sp6ParamA]

theorem c3Torus_sp6ParamM2_apply (a b : Kˣ) : sp6ParamM2 K (a, b) = ![a, b, 1] := by
  funext i
  fin_cases i <;> simp [sp6ParamM2]

theorem c3Torus_sp6ParamM3_apply (a b : Kˣ) : sp6ParamM3 K (a, b) = ![a, b, b] := by
  funext i
  fin_cases i <;> simp [sp6ParamM3]

end Param

section Action


variable {K : Type} [Field K]

theorem c3Torus_rootDiagUnit_eq_torusElt (t : Fin 3 → Kˣ) :
    rootDiagUnit .F4 (c3TorusParam t) =
      torusElt .F4 K 1 (t 0 * t 1 * t 2) * torusElt .F4 K 2 (t 0 * t 1) *
        torusElt .F4 K 3 (t 0) := by
  simp only [torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  obtain ⟨-, -, -, -, a10, a11, a12, a13, a20, a21, a22, a23, a30, a31, a32, a33⟩ :=
    f4Cartan_values
  funext i
  apply Additive.ofMul.injective
  rcases fin_F4_cases i with rfl | rfl | rfl | rfl
  · simp only [Pi.mul_apply, a10, a20, a30, c3TorusParam_apply_zero, ofMul_mul, ofMul_zpow,
      ofMul_inv]
    module
  · simp only [Pi.mul_apply, a11, a21, a31, c3TorusParam_apply_one, ofMul_mul, ofMul_zpow]
    module
  · simp only [Pi.mul_apply, a12, a22, a32, c3TorusParam_apply_two, ofMul_mul, ofMul_zpow,
      ofMul_inv]
    module
  · simp only [Pi.mul_apply, a13, a23, a33, c3TorusParam_apply_three, ofMul_mul, ofMul_zpow,
      ofMul_inv]
    module


theorem c3Torus_rootDiagUnit_mem_map_C3Levi (t : Fin 3 → Kˣ) :
    rootDiagUnit .F4 (c3TorusParam t) ∈ (C3Levi K).map (adjointGroup .F4 K).subtype := by
  rw [c3Torus_rootDiagUnit_eq_torusElt]
  exact mul_mem (mul_mem (torusElt_mem_neighbourLevi (N := .X) (by decide) _)
    (torusElt_mem_neighbourLevi (N := .X) (by decide) _))
    (torusElt_mem_neighbourLevi (N := .X) (by decide) _)

theorem c3Torus_exists_mem_C3Levi (t : Fin 3 → Kˣ) :
    ∃ d : C3Levi K, ((d : adjointGroup .F4 K) : ModGL .F4 K) =
      rootDiagUnit .F4 (c3TorusParam t) := by
  obtain ⟨d, hd, he⟩ := c3Torus_rootDiagUnit_mem_map_C3Levi (K := K) t
  exact ⟨⟨d, hd⟩, he⟩

theorem c3Torus_rootDiagUnit_conj_f4Par (b : Fin (Tag.rank .F4) → Kˣ)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (c : K) :
    rootDiagUnit .F4 b * ((Adjoint.f4Par K γ c : adjointGroup .F4 K) : ModGL .F4 K) *
        (rootDiagUnit .F4 b)⁻¹ =
      ((Adjoint.f4Par K γ ((rootChar b γ : K) * c) : adjointGroup .F4 K) : ModGL .F4 K) := by
  rw [coe_f4Par_eq_pinnedX hγ, coe_f4Par_eq_pinnedX hγ, rootDiagUnit_conj_pinnedX b hγ]
  congr 1
  ring

end Action

theorem c3Torus_sp6Diag_conj_x {K : Type} [Field K] {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (t : Fin 3 → Kˣ) (c : K) :
    sp6Diag K t * Sp.x 3 K γ c * (sp6Diag K t)⁻¹ =
      Sp.x 3 K γ ((CentralExt.SpTorus.chi (toStd 3 γ) t : K) * c) :=
  CentralExt.SpTorus.tor_conj_x hγ t c

section Main


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem c3LeviHom_sp6Diag_conj_f4Par (t : Fin 3 → Kˣ) {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : K) :
    c3LeviHom K (sp6Diag K t) * Adjoint.f4Par K (c3ToF4 γ) c * (c3LeviHom K (sp6Diag K t))⁻¹ =
      Adjoint.f4Par K (c3ToF4 γ) ((rootChar (c3TorusParam t) (c3ToF4 γ) : K) * c) := by
  rw [← c3LeviHom_x γ c, show c3LeviHom K (sp6Diag K t) * c3LeviHom K (Sp.x 3 K γ c) *
      (c3LeviHom K (sp6Diag K t))⁻¹ =
      c3LeviHom K (sp6Diag K t * Sp.x 3 K γ c * (sp6Diag K t)⁻¹) by simp only [map_mul, map_inv],
    c3Torus_sp6Diag_conj_x hγ, c3LeviHom_x, rootChar_c3TorusParam_c3ToF4]

theorem coe_c3LeviEquiv_sp6Diag (t : Fin 3 → Kˣ) :
    (((c3LeviEquiv K (sp6Diag K t) : C3Levi K) : adjointGroup .F4 K) : ModGL .F4 K) =
      rootDiagUnit .F4 (c3TorusParam t) := by
  obtain ⟨d, hd⟩ := c3Torus_exists_mem_C3Levi (K := K) t
  have hle : C3Levi K ≤ centralizer
      {(c3LeviHom K (sp6Diag K t))⁻¹ * (d : adjointGroup .F4 K)} := by
    refine C3Levi_eq_closure.le.trans ((closure_le _).2 ?_)
    rintro _ ⟨γ', hγ', c, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := exists_c3ToF4_eq_of_mem_c3LeviRoots hγ'
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h1 := c3LeviHom_sp6Diag_conj_f4Par t hγ c
    have h2 : (d : adjointGroup .F4 K) * Adjoint.f4Par K (c3ToF4 γ) c *
        (d : adjointGroup .F4 K)⁻¹ =
          Adjoint.f4Par K (c3ToF4 γ) ((rootChar (c3TorusParam t) (c3ToF4 γ) : K) * c) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hd]
      exact c3Torus_rootDiagUnit_conj_f4Par _ (isRoot_c3ToF4 hγ) c
    set g := c3LeviHom K (sp6Diag K t)
    set y := Adjoint.f4Par K (c3ToF4 γ) c
    calc y * (g⁻¹ * d) = g⁻¹ * (g * y * g⁻¹) * d := by group
      _ = g⁻¹ * (d * y * (d : adjointGroup .F4 K)⁻¹) * d := by rw [h1, h2]
      _ = g⁻¹ * d * y := by group
  have hc : (c3LeviEquiv K (sp6Diag K t))⁻¹ * d ∈ center (C3Levi K) := by
    rw [mem_center_iff]
    intro z
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_c3LeviEquiv] using
      mem_centralizer_singleton_iff.1 (hle z.2)
  rw [center_C3Levi_eq_bot, mem_bot, inv_mul_eq_one] at hc
  rw [hc, hd]

theorem c3Torus_mem_inf_of_param {J : Finset (Fin (Tag.rank .F4))} (t : Fin 3 → Kˣ)
    (ht : ∀ j ∈ J, c3TorusParam t j = 1) :
    ((c3LeviEquiv K (sp6Diag K t) : C3Levi K) : adjointGroup .F4 K) ∈
      (leviTorus K J).subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K := by
  refine Subgroup.mem_inf.2 ⟨?_, (c3LeviEquiv K (sp6Diag K t)).2⟩
  rw [mem_subgroupOf, coe_c3LeviEquiv_sp6Diag]
  exact rootDiagUnit_mem_leviTorus ht

theorem c3Torus_eq_c3LeviEquiv_of_param {x : C3Levi K} {b : Fin (Tag.rank .F4) → Kˣ}
    (hx : ((x : adjointGroup .F4 K) : ModGL .F4 K) = rootDiagUnit .F4 b) (t : Fin 3 → Kˣ)
    (h1 : c3TorusParam t 1 = b 1) (h2 : c3TorusParam t 2 = b 2)
    (h3 : c3TorusParam t 3 = b 3) :
    x = c3LeviEquiv K (sp6Diag K t) := by
  have hy : (((x * (c3LeviEquiv K (sp6Diag K t))⁻¹ : C3Levi K) : adjointGroup .F4 K) :
      ModGL .F4 K) ∈ leviTorus K {1, 2, 3} := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, coe_c3LeviEquiv_sp6Diag, rootDiagUnit_inv, ← rootDiagUnit_mul]
    refine rootDiagUnit_mem_leviTorus fun j hj => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · rw [Pi.mul_apply, Pi.inv_apply, h1, mul_inv_cancel]
    · rw [Pi.mul_apply, Pi.inv_apply, h2, mul_inv_cancel]
    · rw [Pi.mul_apply, Pi.inv_apply, h3, mul_inv_cancel]
  have hc : x * (c3LeviEquiv K (sp6Diag K t))⁻¹ ∈ center (C3Levi K) := by
    rw [mem_center_iff]
    intro z
    have hz := levi_le_centralizer_torus (K := K) AmalgamNeighbour.X
      ⟨(z : adjointGroup .F4 K), z.2, rfl⟩
    change _ ∈ centralizer (torusLineR K : Set (ModGL .F4 K)) at hz
    rw [torusLineR_eq_leviTorus] at hz
    have e := mem_centralizer_iff.1 hz _ hy
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e ⊢
    exact e.symm
  rwa [center_C3Levi_eq_bot, mem_bot, mul_inv_eq_one] at hc

theorem map_c3LeviEquiv_sp6TorusA :
    ((sp6TorusA (⊤ : Subgroup Kˣ)).map (c3LeviEquiv K).toMonoidHom).map (C3Levi K).subtype =
      (leviTorus K {1, 2}).subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨a, -, rfl⟩, rfl⟩, rfl⟩
    refine c3Torus_mem_inf_of_param (sp6ParamA K a) fun j hj => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · rw [c3TorusParam_apply_one, c3Torus_sp6ParamA_apply]
      simp
    · rw [c3TorusParam_apply_two, c3Torus_sp6ParamA_apply]
      simp
  · intro x hx
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 (mem_subgroupOf.1 hxT)
    have e := c3Torus_eq_c3LeviEquiv_of_param (x := ⟨x, hxD⟩) hbx.symm (sp6ParamA K (b 3))
      (by rw [c3TorusParam_apply_one, c3Torus_sp6ParamA_apply, hb 1 (by simp)]; simp)
      (by rw [c3TorusParam_apply_two, c3Torus_sp6ParamA_apply, hb 2 (by simp)]; simp)
      (by rw [c3TorusParam_apply_three, c3Torus_sp6ParamA_apply]; simp)
    exact ⟨⟨x, hxD⟩, ⟨_, ⟨b 3, mem_top _, rfl⟩, e.symm⟩, rfl⟩

theorem map_c3LeviEquiv_sp6TorusM2 :
    ((sp6TorusM2 (⊤ : Subgroup Kˣ)).map (c3LeviEquiv K).toMonoidHom).map (C3Levi K).subtype =
      (leviTorus K {1}).subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨⟨a, a'⟩, -, rfl⟩, rfl⟩, rfl⟩
    refine c3Torus_mem_inf_of_param (sp6ParamM2 K (a, a')) fun j hj => ?_
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [c3TorusParam_apply_one, c3Torus_sp6ParamM2_apply]
    simp
  · intro x hx
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 (mem_subgroupOf.1 hxT)
    have e := c3Torus_eq_c3LeviEquiv_of_param (x := ⟨x, hxD⟩) hbx.symm
      (sp6ParamM2 K (b 3 * b 2, b 2))
      (by rw [c3TorusParam_apply_one, c3Torus_sp6ParamM2_apply, hb 1 (by simp)]; simp)
      (by rw [c3TorusParam_apply_two, c3Torus_sp6ParamM2_apply]; simp)
      (by rw [c3TorusParam_apply_three, c3Torus_sp6ParamM2_apply]; simp)
    exact ⟨⟨x, hxD⟩, ⟨_, ⟨(b 3 * b 2, b 2), Subgroup.mem_prod.2 ⟨mem_top _, mem_top _⟩, rfl⟩,
      e.symm⟩, rfl⟩

theorem map_c3LeviEquiv_sp6TorusM3 :
    ((sp6TorusM3 (⊤ : Subgroup Kˣ)).map (c3LeviEquiv K).toMonoidHom).map (C3Levi K).subtype =
      (leviTorus K {2}).subgroupOf (adjointGroup .F4 K) ⊓ C3Levi K := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨_, ⟨⟨a, a'⟩, -, rfl⟩, rfl⟩, rfl⟩
    refine c3Torus_mem_inf_of_param (sp6ParamM3 K (a, a')) fun j hj => ?_
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [c3TorusParam_apply_two, c3Torus_sp6ParamM3_apply]
    simp
  · intro x hx
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hb, hbx⟩ := mem_leviTorus.1 (mem_subgroupOf.1 hxT)
    obtain ⟨s, hs⟩ := exists_sq_eq_of_ringChar_eq_two (ringChar.eq K 2) (b 1)
    have e := c3Torus_eq_c3LeviEquiv_of_param (x := ⟨x, hxD⟩) hbx.symm
      (sp6ParamM3 K (b 3 * s, s))
      (by rw [c3TorusParam_apply_one, c3Torus_sp6ParamM3_apply, ← hs, sq]; simp)
      (by rw [c3TorusParam_apply_two, c3Torus_sp6ParamM3_apply, hb 2 (by simp)]; simp)
      (by rw [c3TorusParam_apply_three, c3Torus_sp6ParamM3_apply]; simp)
    exact ⟨⟨x, hxD⟩, ⟨_, ⟨(b 3 * s, s), Subgroup.mem_prod.2 ⟨mem_top _, mem_top _⟩, rfl⟩,
      e.symm⟩, rfl⟩

end Main

end CFSG.SeitzReduction.F4Pilot
