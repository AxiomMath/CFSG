module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2GL
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASetting
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk9
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Act
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

omit [CFSG.GH74.QTGen4.Finite4 G] in

private theorem conjAct_val (A : Subgroup G) {q : G} (hq : q ∈ Subgroup.normalizer (A : Set G))
    (a : ↥A) : ((conjAct A ⟨q, hq⟩ a : ↥A) : G) = q * a * q⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe A (Subgroup.inclusion le_rfl ⟨q, hq⟩) a

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem autOn_eq_top_F4 (s : F8Setup T V L H γ γ' g)
    (hmγ : mIdx (F8.Uγ V H (g : G)) (F8.Dγ V (fsuV1 T V) H (g : G)) = 1)
    (hmH : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (g : G)) = 1) :
    autOn (Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G))
      ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊤ := by
  classical
  have := C.fact_F4
  have hMod := stmtL32NModule_of_inputs_F4 C.h1332 C.h1334
  have : IsMulCommutative ↥V := (hMod G T L V C.S.hyp.hyp C.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 C.S.hyp (stmt13_3_2_two_of_F4 C.h1332) hMod C.h1222
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 hV2
  obtain ⟨z, a, c, hz, hz1, ha, haV, hc, hcV⟩ := S14.exists_basis_F4
  obtain ⟨e₁, e₂, b, D⟩ := C.good_of_setup_F4 s (by omega) (by omega)
  have hA := C.isElemAbelian_A_F4 s
  set A := ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ with hAdef
  set N := Subgroup.normalizer (A : Set G) with hNdef
  obtain ⟨v, hvz⟩ : ∃ v : ↥A, (v : G) = z := ⟨⟨z, D.V₁_le hz⟩, rfl⟩
  have hv1 : v ≠ 1 := fun h => hz1 (by rw [← hvz, h]; rfl)
  have hV₁ : ∀ x : ↥A, (x : G) ∈ fsuV1 T V → x = 1 ∨ x = v := by
    intro x hm
    rcases S14.eq_of_mem_V1_F4 hz hz1 hm with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans hvz.symm))

  have hT : ∀ x : ↥A, x ≠ 1 → x ≠ v →
      ∃ α ∈ autOn N A, (∀ a, α a * a⁻¹ = 1 ∨ α a * a⁻¹ = v) ∧ α x = x * v := by
    intro x hx1 hxv
    have hxV : (x : G) ∉ fsuV1 T V := fun hm => by
      rcases hV₁ x hm with h | h
      · exact hx1 h
      · exact hxv h
    obtain ⟨q, hq, hqx⟩ := C.exists_noncomm_F4 D x.2 hxV
    have hqN : q ∈ N := C.pCoreOf_le_normalizer_A_F4 D hq
    have hcV : ∀ a : ↥A, q * a * q⁻¹ * (a : G)⁻¹ ∈ fsuV1 T V := fun a =>
      C.h91_F4.commutator_mem_V₁ hq (C.A_le_UH_F4 s a.2)
    refine ⟨conjAct A ⟨q, hqN⟩, Subgroup.mem_map.mpr ⟨⟨q, hqN⟩, hqN, rfl⟩, fun a => ?_, ?_⟩
    · have hm : conjAct A ⟨q, hqN⟩ a * a⁻¹ ∈ (fsuV1 T V).subgroupOf A := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, conjAct_val]
        exact hcV a
      exact hV₁ _ hm
    · apply Subtype.ext
      rw [Subgroup.coe_mul, conjAct_val, hvz]
      rcases S14.eq_of_mem_V1_F4 hz hz1 (hcV x) with h | h
      · exfalso
        apply hqx
        calc q * x = (q * x * q⁻¹ * (x : G)⁻¹) * x * q := by group
          _ = x * q := by rw [h]; group
      · calc q * (x : G) * q⁻¹ = (q * x * q⁻¹ * (x : G)⁻¹) * x := by group
          _ = z * x := by rw [h]
          _ = x * z := F7.isElemAbelian_comm hA (D.V₁_le hz) x.2

  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨l, hl, hl3, hlz, hla, -⟩ := exists_x_cube_F4 S14 hz hz1 ha haV hc hcV
  have hl' : l ∈ l1 T L V := hl1eq ▸ hl
  have hlO : l ∉ pCoreOf 2 (l1 T L V) := fun h => by
    have h1 := (S14.pCoreOf_L1_le_F4 (hl1eq ▸ h)).2.2 a (S14.hV2.2.1 ha)
    rw [hla] at h1
    apply hcV
    rw [show c = c * a⁻¹ * a by group]
    exact mul_mem (S14.hV2.1 h1) ha
  have hlN : l ∈ N := D.l1_le hl'
  have hρ : conjAct A ⟨l, hlN⟩ ∈ autOn N A := Subgroup.mem_map.mpr ⟨⟨l, hlN⟩, hlN, rfl⟩
  have hρv : conjAct A ⟨l, hlN⟩ v = v := Subtype.ext (by rw [conjAct_val, hvz]; exact hlz)
  have hρ3 : conjAct A ⟨l, hlN⟩ ^ 3 = 1 := by
    have h1 : (⟨l, hlN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hl3)
    rw [← map_pow, h1, map_one]
  have hρf : ∀ a : ↥A, a ≠ 1 → a ≠ v →
      conjAct A ⟨l, hlN⟩ a ≠ a ∧ conjAct A ⟨l, hlN⟩ a ≠ a * v := by
    intro a ha1 hav
    have haV : (a : G) ∉ fsuV1 T V := fun hm => by
      rcases hV₁ a hm with h | h
      · exact ha1 h
      · exact hav h
    have hfix : l * a * l⁻¹ * (a : G)⁻¹ ∉ fsuV1 T V := fun hyu =>
      haV (Setting147.mem_V1_of_fix_F4 C.S C.h1222 C.h1332 C.h1334 C.hHL hl' hlO
        (C.A_le_UH_F4 s a.2) hyu)
    refine ⟨fun h => hfix ?_, fun h => hfix ?_⟩
    · have h1 := congrArg Subtype.val h
      rw [conjAct_val] at h1
      rw [h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have h1 := congrArg Subtype.val h
      rw [conjAct_val, Subgroup.coe_mul, hvz] at h1
      rw [h1, F7.isElemAbelian_comm hA a.2 (D.V₁_le hz), mul_inv_cancel_right]
      exact hz

  have hlt : F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun he => ?_
    rw [he] at hmγ
    simp [mIdx] at hmγ
  obtain ⟨δ, δ', k, y, sk, hyγ, -, hUδ, hUH, hDHk, hDδk⟩ :=
    C.h98.exists_symmetric_setup s (C.h98.not_Vγ_le_ballStab_of_lt s hlt)
  have hmγk : mIdx (F8.Uγ V H (k : G)) (F8.Dγ V (fsuV1 T V) H (k : G)) = 1 := by
    rw [hUδ, hDδk, F9.mIdx_conjSub, hmH]
  have hmHk : mIdx (conjClosure V H) (F8.DH V (fsuV1 T V) H (k : G)) = 1 := by
    rw [hDHk, ← hUH, F9.mIdx_conjSub, hmγ]
  obtain ⟨e₁', e₂', b', Dk⟩ := C.good_of_setup_F4 sk (by omega) (by omega)
  have hAk : ⁅conjClosure V H, F8.Uγ V H (k : G)⁆ = Quasithin.conjSub (y : G) A := by
    have e1 : Quasithin.conjSub (y : G) A = ⁅Quasithin.conjSub (y : G) (conjClosure V H),
        Quasithin.conjSub (y : G) (F8.Uγ V H (g : G))⁆ :=
      Subgroup.map_commutator _ _ _
    rw [e1, hUH, Subgroup.commutator_comm, hUδ]
  have hzk : (y : G) * z * (y : G)⁻¹ ∈ ⁅conjClosure V H, F8.Uγ V H (k : G)⁆ := by
    rw [hAk]
    exact Quasithin.mul_mem_conjSub (D.V₁_le hz)
  have hyg : (((y * g : ↥((L ⊔ T) ⊔ H))) : G) ∈ H := by
    have h1 : (y * g) • F8.γ₁ T L H = F8.γ₁ T L H := by rw [mul_smul, s.edge₁, hyγ]
    have := mem_stab_of_smul_eq h1
    rwa [stab_γ₁ C.h98.amalgamHypV.le₂] at this
  have hyg' : (y : G) * (g : G) ∈ H := by simpa using hyg
  have eA : Quasithin.conjSub (y : G) (F8.A₁ (fsuV1 T V) (g : G)) = fsuV1 T V := by
    rw [F8.A₁, ← Quasithin.conjSub_mul,
      F7.conjSub_eq_of_mem_normalizer (C.h98.H_normalizes_V₁ hyg')]
  have hzkV : (y : G) * z * (y : G)⁻¹ ∉ fsuV1 T V := by
    intro hm
    rw [← eA, Quasithin.mem_conjSub] at hm
    have e : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) = z := by group
    rw [e] at hm
    have h0 : z ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨hz, hm⟩
    rw [C.h98.F913_5b s, Subgroup.mem_bot] at h0
    exact hz1 h0
  obtain ⟨q, hq, hqx⟩ := C.exists_noncomm_F4 Dk hzk hzkV
  have hqN := C.pCoreOf_le_normalizer_A_F4 Dk hq
  rw [hAk] at hqN
  have hq'N : (y : G)⁻¹ * q * (y : G) ∈ N := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 : (y : G) * a * (y : G)⁻¹ ∈ Quasithin.conjSub (y : G) A := Quasithin.mul_mem_conjSub ha
    have h2 := (Subgroup.mem_normalizer_iff.mp hqN _).mp h1
    rw [Quasithin.mem_conjSub] at h2
    have e : (y : G)⁻¹ * q * (y : G) * a * ((y : G)⁻¹ * q * (y : G))⁻¹ =
        (y : G)⁻¹ * (q * ((y : G) * a * (y : G)⁻¹) * q⁻¹) * (y : G) := by group
    rw [e]
    exact h2
  have hβ : conjAct A ⟨_, hq'N⟩ ∈ autOn N A := Subgroup.mem_map.mpr ⟨⟨_, hq'N⟩, hq'N, rfl⟩
  have hβv : conjAct A ⟨_, hq'N⟩ v ≠ v := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [conjAct_val, hvz] at h1
    apply hqx
    calc q * ((y : G) * z * (y : G)⁻¹)
        = (y : G) * ((y : G)⁻¹ * q * (y : G) * z * ((y : G)⁻¹ * q * (y : G))⁻¹) *
            (y : G)⁻¹ * q := by group
      _ = (y : G) * z * (y : G)⁻¹ * q := by rw [h1]
  exact E8.eq_top_of_transitive hA D.card hv1 hT hρ hρv hρ3 hρf hβ hβv

end Ctx_F4

theorem input1476S2GL_of_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Input1476S2GL_F4 := by
  intro G _ _ T L V H S Y hY2 hYH hHY hexp hYM hHYL hHL hmin h25 γ γ' g s hmγ hmH _ _ _
  have h98 := S.hypF98_F4 (stmt13_3_2_two_of_F4 h1332) (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222
  exact Ctx_F4.autOn_eq_top_F4 ⟨S, h98, h1222, h1332, h1334, hY2, hYH, hHY, hexp, hYM, hHYL, hHL,
    hmin, h25⟩ s hmγ hmH

theorem input1476S2_holds_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h36 : A36ForSQTK) :
    Input1476S2_F4 :=
  input1476S2_of_F4 h1222 h1332 h1334 h36 (input1476S2GL_of_F4 h1222 h1332 h1334)

end CFSG.Quasithin.H13.L32A.S2

end
