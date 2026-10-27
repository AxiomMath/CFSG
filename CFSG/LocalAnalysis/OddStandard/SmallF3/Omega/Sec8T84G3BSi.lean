module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BRq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BS4

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {E E0 Y Y' V V' F F' P H : Subgroup G}

theorem sec8t84g3b_side_exists (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4)
    (S : Sec8T84G3BSide G E E0 Y Y' V V' F F' P H) {γ : G} (hγ2 : γ * γ = 1)
    (hQ : ∀ x ∈ sec8t84g_Q E E0, γ * x * γ⁻¹ ∈ sec8t84g_Q E E0)
    (hO : ∀ o ∈ oddCoreIn (sec8t84g_Q E E0), γ * o * γ⁻¹ ∈ oddCoreIn (sec8t84g_Q E E0))
    (hU : ∀ u ∈ V ⊔ F, γ * u * γ⁻¹ ∈ V ⊔ F) (hU' : ∀ u ∈ V' ⊔ F', γ * u * γ⁻¹ ∈ V' ⊔ F')
    (hC : IsElemAb2 ((V ⊔ F) ⊓ centralizer ({γ} : Set G)) 2) :
    ∃ z ∈ sec8t84g_Q E E0, z ∈ Y ∧ (∀ u ∈ V' ⊔ F', z * u = u * z) ∧
      z ∈ normalizer ((V ⊔ F : Subgroup G) : Set G) ∧
      z ^ 3 ∈ oddCoreIn (sec8t84g_Q E E0) ∧ γ * z * γ⁻¹ * z⁻¹ ∈ oddCoreIn (sec8t84g_Q E E0) ∧
      ∀ u ∈ V ⊔ F, z * u = u * z → u = 1 := by
  haveI hNn : ((oddCoreIn (normalizer (E : Set G))).subgroupOf Y).Normal := S.ydata.O_norm
  let π : ↥Y →* ↥Y ⧸ (oddCoreIn (normalizer (E : Set G))).subgroupOf Y :=
    QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ x : ↥Y, π x = 1 ↔ (x : G) ∈ oddCoreIn (normalizer (E : Set G)) :=
    fun x => QuotientGroup.eq_one_iff x
  have hS4c := sec8t84g3b_S4_ydata hP hS4 S.ydata S.P_syl S.F_le_P S.F_e16 S.F_ne
  have hNJ := sec8t84g3b_normJ_ydata hP S.ydata S.P_syl S.F_le_P S.F_e16 S.F_ne
  have hZY : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤ Y := S.Z_le_Y
  have hZQ : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤ sec8t84g_Q E E0 :=
    sec8t84g3b_Z_le (fun y hy _ _ => hy) S.U_le_Q
  have hZC : sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') ≤
      centralizer ((V' ⊔ F' : Subgroup G) : Set G) :=
    sec8t84g3b_Z_le (fun y _ hc _ => hc) (fun u hu => Subgroup.mem_centralizer_iff.mpr
      (fun u' hu' => (S.UU'_comm u hu u' hu').symm))
  let φ : ↥(sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F')) →*
      ↥Y ⧸ (oddCoreIn (normalizer (E : Set G))).subgroupOf Y := π.comp (Subgroup.inclusion hZY)
  have hrange : ∀ y, y ∈ sec8t84g3b_M ((V.subgroupOf Y).map π) ((F.subgroupOf Y).map π) ↔
      ∃ z, φ z = y := by
    intro y
    constructor
    · intro hy
      have hle : sec8t84g3b_M ((V.subgroupOf Y).map π) ((F.subgroupOf Y).map π) ≤ φ.range := by
        unfold sec8t84g3b_M twoRes
        refine (Subgroup.closure_le _).mpr ?_
        rintro g ⟨hg, hodd⟩
        obtain ⟨z, hz, hzY, hzg⟩ := sec8t84g3b_range_gen S π hπs hker rfl rfl hNJ g hg hodd
        exact ⟨⟨z, hz⟩, hzg⟩
      exact hle hy
    · rintro ⟨z, rfl⟩
      exact sec8t84g3b_phi_mem S π rfl rfl hS4c.1 z.1 z.2 (hZY z.2)
  have hUZ : V ⊔ F ≤ sec8t84g3b_Z (sec8t84g_Q E E0) (V ⊔ F) (V' ⊔ F') := le_sup_right
  obtain ⟨z, hzZ, -, hz3, hzγ, hzfix⟩ := sec8t84g3b_one_side hS4c φ hγ2
    (sec8t84g3b_Z_conj hγ2 hQ hU hU') hO hU
    (fun z => by
      rw [show φ z = π ⟨z, hZY z.2⟩ from rfl, hker, S.O_eq]
      exact ⟨fun hN => ⟨hZQ z.2, hN⟩, fun h => h.2⟩) hrange hUZ
    (fun u hu hO' => by
      rw [S.O_eq] at hO'
      have h1 : u ∈ (E ⊔ E0) ⊓ oddCoreIn (normalizer (E : Set G)) := ⟨S.U_le_W hu, hO'.2⟩
      rwa [S.W_inf, Subgroup.mem_bot] at h1)
    (fun z hz => by
      have hle : V ⊔ F ≤ (((V.subgroupOf Y).map π ⊔ (F.subgroupOf Y).map π).comap π).map
          Y.subtype := by
        refine sup_le (fun v hv => ?_) (fun f hf => ?_)
        · exact Subgroup.mem_map.mpr ⟨⟨v, S.ydata.V_le hv⟩, Subgroup.mem_comap.mpr
            (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π
              (x := ⟨v, S.ydata.V_le hv⟩) hv)), rfl⟩
        · exact Subgroup.mem_map.mpr ⟨⟨f, S.F_le_Y hf⟩, Subgroup.mem_comap.mpr
            (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem π
              (x := ⟨f, S.F_le_Y hf⟩) hf)), rfl⟩
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp (hle hz)
      have hxe : x = ⟨z.1, hZY z.2⟩ := Subtype.ext hxz
      rw [show φ z = π ⟨z.1, hZY z.2⟩ from rfl, ← hxe]
      exact Subgroup.mem_comap.mp hx)
    (fun x hx => by
      rw [← Subgroup.map_sup] at hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← Subgroup.subgroupOf_sup S.ydata.V_le S.F_le_Y] at hw
      exact ⟨⟨(w : G), hUZ hw⟩, hw, rfl⟩)
    (by rw [hC.2]; norm_num) (fun u hu => hC.1.mul_self_eq_one hu)
  have hzQ : z ∈ sec8t84g_Q E E0 := hZQ hzZ
  have hzY : z ∈ Y := hZY hzZ
  refine ⟨z, hzQ, hzY, fun u hu => (Subgroup.mem_centralizer_iff.mp (hZC hzZ) u hu).symm,
    ?_, hz3, hzγ, hzfix⟩
  exact sec8t84g3b_mem_normalizer_of_conj (sec8t84g3b_conj_sup
    (fun v hv => Subgroup.mem_sup_left (S.conj_V hzY v hv))
    (fun f hf => Subgroup.mem_sup_right (S.conj_F hzY (sec8t84g3b_Q_le_E0 hzQ) f hf)))

end CFSG.OddStandard.SmallF3.Omega
