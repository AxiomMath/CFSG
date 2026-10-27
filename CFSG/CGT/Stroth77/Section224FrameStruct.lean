module

public import CFSG.CGT.Stroth77.Section224FrameAniso

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace StrothFrame.IsD

open DeviationGeneric Stroth225Frame Stroth224Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

private theorem u_mem_S'' (h : F.IsD D dD) : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S

theorem sqBar_inv (hk : ∀ i, 2 ≤ τ.k i) (hcent : (F.S : Subgroup G) ⊓
    Subgroup.centralizer (D : Set G) = D) {x : G} (hx : x ∈ 𝓡[(F.S : Subgroup G), D]) :
    sqBar dD hk hcent x⁻¹ (inv_mem hx) = sqBar dD hk hcent x hx := by
  have h : (⟨x⁻¹ * x⁻¹, mul_self_mem_of_mem_R dD hk hcent (inv_mem hx)⟩ : D) =
      (⟨x * x, mul_self_mem_of_mem_R dD hk hcent hx⟩ : D)⁻¹ :=
    Subtype.ext (by simp only [Subgroup.coe_inv]; group)
  rw [sqBar, sqBar, h, barD_inv]

theorem cond_of_flat_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    {y : G} (hy : y ∈ 𝓡[(F.S : Subgroup G), D])
    (hf : devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0) :
    Cond (devMat dD hk y hy) (sqBar dD hk h.cent y hy) := by
  refine ⟨devMat_mulVec_sqBar hk h.cent hy, ⟨fun hq => ?_, fun h0 => ?_⟩⟩
  · exact (devMat_eq_zero_iff hk h.cent hy).mpr
      (h.mem_of_sqBar_eq_zero_familyOne hfam hk hy hf hq)
  · have hyD := (devMat_eq_zero_iff hk h.cent hy).mp h0
    rw [sqBar, show (⟨y * y, mul_self_mem_of_mem_R dD hk h.cent hy⟩ : D) =
      ⟨y, hyD⟩ * ⟨y, hyD⟩ from rfl, barD_mul, barD_add_self]

theorem struct_of_flat_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hS : Local.Setting (F.S : Subgroup G) D) {x : G} (hx : x ∈ 𝓡[(F.S : Subgroup G), D])
    (hf : devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0) :
    (devMat dD hk x hx 1 2 = 0 ∧ devMat dD hk x hx 2 1 = 0 ∧
        devMat dD hk x hx 1 1 = devMat dD hk x hx 2 2) ∧
      sqBar dD hk h.cent x hx =
        ![devMat dD hk x hx 1 1, devMat dD hk x hx 1 0, devMat dD hk x hx 2 0] := by
  have hρx := proj_mem_R dD hk hS hx
  have huS := u_mem_S'' h
  have hux := conj_mem_R huS dD.u_mem hx
  have huρx := conj_mem_R huS dD.u_mem hρx
  have hfρ : devMat dD hk _ hρx = actRhoOne (devMat dD hk x hx) :=
    devMat_proj_rho_familyOne hfam hk hS hx hρx
  have hfu : devMat dD hk _ hux = actU (devMat dD hk x hx) :=
    devMat_conj_u_familyOne hfam hk hx hux
  have hfuρ : devMat dD hk _ huρx = actU (actRhoOne (devMat dD hk x hx)) := by
    rw [devMat_conj_u_familyOne hfam hk hρx huρx, hfρ]
  have hqρ := sqBar_proj_rho_familyOne hfam hk h.cent hS hx hρx
  have hqu := sqBar_conj_u_familyOne hfam hk h.cent hx hux
  have hquρ : sqBar dD hk h.cent _ huρx = barU *ᵥ (barRhoOne *ᵥ sqBar dD hk h.cent x hx) := by
    rw [sqBar_conj_u_familyOne hfam hk h.cent hρx huρx, hqρ]
  obtain ⟨hrρ, hru⟩ := row_zero_actRhoOne_actU (devMat dD hk x hx) hf
  have hruρ := (row_zero_actRhoOne_actU (actRhoOne (devMat dD hk x hx)) hrρ).2
  have hfρ' : devMat dD hk _ hρx 0 0 = 0 ∧ devMat dD hk _ hρx 0 1 = 0 ∧
      devMat dD hk _ hρx 0 2 = 0 := by rw [hfρ]; exact hrρ
  have hfu' : devMat dD hk _ hux 0 0 = 0 ∧ devMat dD hk _ hux 0 1 = 0 ∧
      devMat dD hk _ hux 0 2 = 0 := by rw [hfu]; exact hru
  have hfuρ' : devMat dD hk _ huρx 0 0 = 0 ∧ devMat dD hk _ huρx 0 1 = 0 ∧
      devMat dD hk _ huρx 0 2 = 0 := by rw [hfuρ]; exact hruρ
  have hsum : ∀ {y : G} (hy : y ∈ 𝓡[(F.S : Subgroup G), D]) (g : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (p : Fin 3 → ZMod 2),
      (devMat dD hk y hy 0 0 = 0 ∧ devMat dD hk y hy 0 1 = 0 ∧ devMat dD hk y hy 0 2 = 0) →
      devMat dD hk y hy = g → sqBar dD hk h.cent y hy = p →
      Cond (devMat dD hk x hx + g) (sqBar dD hk h.cent x hx + p) := by
    intro y hy g p hfy hg hp
    have hxy := mul_mem hx hy
    have hd : devMat dD hk _ hxy = devMat dD hk x hx + g := by rw [devMat_mul hk hx hy, hg]
    have hq : sqBar dD hk h.cent _ hxy = sqBar dD hk h.cent x hx + p := by
      rw [sqBar_mul_of_row_zero hfam hk h.cent hx hy hf hfy, hp]
    have hfxy : devMat dD hk _ hxy 0 0 = 0 ∧ devMat dD hk _ hxy 0 1 = 0 ∧
        devMat dD hk _ hxy 0 2 = 0 := by
      rw [devMat_mul hk hx hy]
      simp only [Matrix.add_apply, hf.1, hf.2.1, hf.2.2, hfy.1, hfy.2.1, hfy.2.2, add_zero,
        and_self]
    have := cond_of_flat_familyOne h hfam hk hxy hfxy
    rwa [hd, hq] at this
  exact struct_fin (devMat dD hk x hx) (sqBar dD hk h.cent x hx) hf
    (cond_of_flat_familyOne h hfam hk hx hf)
    (hsum hρx _ _ hfρ' hfρ hqρ) (hsum hux _ _ hfu' hfu hqu) (hsum huρx _ _ hfuρ' hfuρ hquρ)

theorem flat_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hS : Local.Setting (F.S : Subgroup G) D) {x : G} (hx : x ∈ 𝓡[(F.S : Subgroup G), D]) :
    devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0 := by
  have huvx := conj_mem_R h.uv_mem_S dD.uv_mem hx
  have hy := mul_mem (inv_mem hx) huvx
  have hdev : devMat dD hk _ hy = devMat dD hk x hx + actUvOne (devMat dD hk x hx) := by
    rw [devMat_mul hk (inv_mem hx) huvx, devMat_inv hk h.cent hx,
      devMat_conj_uv_familyOne hfam hk hx huvx]
  have hq : sqBar dD hk h.cent _ hy 1 = 0 ∧ sqBar dD hk h.cent _ hy 2 = 0 := by
    have h1 := sqBar_mul (dD := dD) hk h.cent (inv_mem hx) huvx
    rw [sqBar_inv hk h.cent hx, sqBar_conj_uv_familyOne hfam hk h.cent hx huvx] at h1
    obtain ⟨c1, c2⟩ := barD_commutator_one_two_familyOne (dD := dD) hfam hk h.cent
      (inv_mem hx) huvx
    have hqq : ∀ i, (sqBar dD hk h.cent x hx + sqBar dD hk h.cent x hx) i = 0 := fun i =>
      CharTwo.add_self_eq_zero _
    refine ⟨?_, ?_⟩
    · rw [h1, Pi.add_apply, hqq 1, zero_add]; exact c1
    · rw [h1, Pi.add_apply, hqq 2, zero_add]; exact c2
  have hfy : devMat dD hk _ hy 0 0 = 0 ∧ devMat dD hk _ hy 0 1 = 0 ∧
      devMat dD hk _ hy 0 2 = 0 := by
    have key : ∀ g : Matrix (Fin 3) (Fin 3) (ZMod 2),
        (g + actUvOne g) 0 0 = 0 ∧ (g + actUvOne g) 0 1 = 0 ∧ (g + actUvOne g) 0 2 = 0 := by
      intro g
      have key' : ∀ a b c d e i j k l : ZMod 2,
          (!![a, b, c; d, e, i; j, k, l] + actUvOne !![a, b, c; d, e, i; j, k, l]) 0 0 = 0 ∧
          (!![a, b, c; d, e, i; j, k, l] + actUvOne !![a, b, c; d, e, i; j, k, l]) 0 1 = 0 ∧
          (!![a, b, c; d, e, i; j, k, l] + actUvOne !![a, b, c; d, e, i; j, k, l]) 0 2 = 0 := by
        decide
      rw [Matrix.eta_fin_three g]
      exact key' _ _ _ _ _ _ _ _ _
    rw [hdev]
    exact key _
  obtain ⟨hb, hs⟩ := struct_of_flat_familyOne h hfam hk hS hy hfy
  rw [hdev] at hb hs
  have hc1 : (devMat dD hk x hx + actUvOne (devMat dD hk x hx)) 1 0 = 0 := by
    have := congrFun hs 1
    rw [← hq.1, this]; rfl
  have hc2 : (devMat dD hk x hx + actUvOne (devMat dD hk x hx)) 2 0 = 0 := by
    have := congrFun hs 2
    rw [← hq.2, this]; rfl
  exact row_zero_of_add_actUvOne _ hb ⟨hc1, hc2⟩

theorem struct_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n) (hk : ∀ i, 2 ≤ τ.k i)
    (hS : Local.Setting (F.S : Subgroup G) D) {x : G} (hx : x ∈ 𝓡[(F.S : Subgroup G), D]) :
    (devMat dD hk x hx 0 0 = 0 ∧ devMat dD hk x hx 0 1 = 0 ∧ devMat dD hk x hx 0 2 = 0) ∧
      (devMat dD hk x hx 1 2 = 0 ∧ devMat dD hk x hx 2 1 = 0 ∧
        devMat dD hk x hx 1 1 = devMat dD hk x hx 2 2) ∧
      sqBar dD hk h.cent x hx =
        ![devMat dD hk x hx 1 1, devMat dD hk x hx 1 0, devMat dD hk x hx 2 0] :=
  ⟨flat_familyOne h hfam hk hS hx, struct_of_flat_familyOne h hfam hk hS hx
    (flat_familyOne h hfam hk hS hx)⟩

theorem mem_of_sqBar_eq_zero_of_mem_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n)
    (hk : ∀ i, 2 ≤ τ.k i) (hS : Local.Setting (F.S : Subgroup G) D) {x : G}
    (hx : x ∈ 𝓡[(F.S : Subgroup G), D]) (hq : sqBar dD hk h.cent x hx = 0) : x ∈ D :=
  h.mem_of_sqBar_eq_zero_familyOne hfam hk hx (flat_familyOne h hfam hk hS hx) hq

theorem mem_omegaIn_one_of_mul_self_familyOne (h : F.IsD D dD) (hfam : τ.m + 1 = τ.n)
    (hk : ∀ i, 2 ≤ τ.k i) (hS : Local.Setting (F.S : Subgroup G) D) {z : G}
    (hz : z ∈ 𝓡[(F.S : Subgroup G), D]) (hz2 : z * z = 1) : z ∈ omegaIn 1 D := by
  have hq : sqBar dD hk h.cent z hz = 0 := by
    rw [sqBar, show (⟨z * z, mul_self_mem_of_mem_R dD hk h.cent hz⟩ : D) = 1 from
      Subtype.ext hz2, barD_one]
  exact mem_omegaIn_one_of_mul_self (h.mem_of_sqBar_eq_zero_of_mem_familyOne hfam hk hS hz hq) hz2

end StrothFrame.IsD

end CFSG.CGT.Stroth77
