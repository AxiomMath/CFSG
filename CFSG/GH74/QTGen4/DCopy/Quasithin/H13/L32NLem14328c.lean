module

public import CFSG.Quasithin.H13.L32NLem14328c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NInputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneNine

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

structure Ctx_F4 (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ : Subgroup G) (g z b l : G)
    [IsMulCommutative ↥V] : Prop where
  hyp : Hyp14310One G T L V
  lt : fsuV1 T V < centerOf (fsuU T V)
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  S : L32NSet14.Setting_F4 G T L V V₂
  z_mem : z ∈ fsuV1 T V
  z_ne : z ≠ 1
  b_mem : b ∈ V
  b_nmem : b ∉ V₂
  l_mem : l ∈ L
  l3 : l ^ 3 = 1
  l_a : l * (g⁻¹ * z * g) * l⁻¹ = g⁻¹ * z * g
  l_z : l * z * l⁻¹ = b
  l_b : l * b * l⁻¹ = z * b
  U_T : fsuU T V ≤ T
  T_U : T ≤ Subgroup.normalizer (fsuU T V : Set G)
  zI : centerOf (i128 T L V (fsuV1 T V)) =
    centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g
  I_eq : i128 T L V (fsuV1 T V) = oTwoUpper (p128 T L V) ⊔ fsuU T V

variable {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem conj_z_mem_F4 {g z : G} (S : L32NSet14.Setting_F4 G T L V V₂) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V) (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) :
    g⁻¹ * z * g ∈ V₂ ∧ g⁻¹ * z * g ∉ fsuV1 T V := by
  have hgV₂ := g_mem_normalizer hV₂ hgP
  refine ⟨?_, fun ha => ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hgV₂) z).mp
      (hV₂.2 hz)
    simpa using this
  · rcases S.eq_of_mem_V1_F4 hz hz1 ha with h1 | h1
    · apply hz1
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · apply hgN
      refine S.mem_g1_F4 hz hz1 ?_
      calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [h1]
        _ = z := by group

theorem exists_ctx_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h12810 : Lemma12_8_10_F4) {T L V : Subgroup G}
    (h : Hyp14310One G T L V) (hlt : fsuV1 T V < centerOf (fsuU T V)) :
    ∃ _ : IsMulCommutative ↥V, ∃ (V₂ : Subgroup G) (g z b l : G), Ctx_F4 G T L V V₂ g z b l := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2_F4 h1332
  have hV := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g_F4 h13322 hV (exist1282g_F4 h1222)
  have hs := h.setting1282One_F4 h13322 hV hV₂
  obtain ⟨hc, S⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  obtain ⟨z, -, b, hz, hz1, -, -, hbV, hbV₂⟩ := S.exists_basis_F4
  obtain ⟨haV₂, ha1⟩ := conj_z_mem_F4 S hV₂ hgP hgN hz hz1
  have hzV₂ : z ∈ V₂ := hV₂.2 hz
  have hzV : z ∈ V := hV₂.1.1 hzV₂
  have haV : g⁻¹ * z * g ∈ V := hV₂.1.1 haV₂
  obtain ⟨l, hlL, hl3, hla, hlz, hlb⟩ := S.exists_rot_F4 haV hzV hbV hz1
    (fun h1 => hbV₂ (h1 ▸ one_mem _)) (fun h1 => ha1 (h1 ▸ hz)) (fun h1 => hbV₂ (h1 ▸ haV₂))
    (fun h1 => hbV₂ (h1 ▸ hzV₂)) (fun h1 => hbV₂ (h1 ▸ V₂.mul_mem haV₂ hzV₂))
  obtain ⟨hUT, hTU⟩ := (hs.almostSpecial_F4 h1222 h12213).G22_three
  exact ⟨hc, V₂, g, z, b, l, ⟨h, hlt, hV₂, hs, hgP, hgN, S, hz, hz1, hbV, hbV₂, hlL, hl3, hla,
    hlz, hlb, hUT, hTU, (h12810 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.1.symm,
    L128P.i128_eq_sup_F4 h1222 h12213 hs⟩⟩

namespace Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l)
include C

theorem a_mem_F4 : g⁻¹ * z * g ∈ V₂ :=
  (conj_z_mem_F4 C.S C.plane C.gP C.gN C.z_mem C.z_ne).1

theorem a_nmem_F4 : g⁻¹ * z * g ∉ fsuV1 T V :=
  (conj_z_mem_F4 C.S C.plane C.gP C.gN C.z_mem C.z_ne).2

theorem z_V₂_F4 : z ∈ V₂ := C.plane.2 C.z_mem

theorem z_V_F4 : z ∈ V := C.plane.1.1 C.z_V₂_F4

theorem a_V_F4 : g⁻¹ * z * g ∈ V := C.plane.1.1 C.a_mem_F4

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
