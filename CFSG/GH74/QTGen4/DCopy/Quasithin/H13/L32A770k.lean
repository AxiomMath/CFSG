module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem exists_l1_fpf_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧
      ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2_F4 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, hxb⟩ := S14.exists_rot_F4 hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  refine ⟨x, Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1_F4 hz0 hz1 hxz⟩, 3, by decide, hx3⟩, hx3,
    fun v hv hxv => ?_⟩

  obtain ⟨z', hz', -, hgen⟩ := exists_gen_of_card_two S14.card_V1_F4
  have hxc : ∀ c ∈ fsuV1 T V, x * c * x⁻¹ = c := by
    intro c hc
    rcases hgen c hc with rfl | rfl
    · group
    · rcases hgen z hz0 with e | e
      · exact absurd e hz1
      · rw [← e]; exact hxz

  have hidx1 : (fsuV1 T V).relIndex V₂ = 2 := by
    have := Subgroup.relIndex_mul_card (fsuV1 T V) V₂
    rw [inf_eq_left.mpr hV2.1, S14.card_V1_F4, hV2.2.2.2] at this
    omega
  have hidx2 : V₂.relIndex V = 2 := by
    have := Subgroup.relIndex_mul_card V₂ V
    rw [inf_eq_left.mpr hV2.2.1, hV2.2.2.2, S14.card_V_F4] at this
    omega
  have hcomm : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p := fun p hp q hq => S14.comm_V_F4 hp hq
  have hsq : ∀ p ∈ V, p * p = 1 := fun p hp => S14.mul_self_V_F4 hp
  have hbV' : b ∈ V := hb
  by_contra hvV1
  by_cases hvV2 : v ∈ V₂
  ·
    have hac : a⁻¹ * v ∈ fsuV1 T V := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx1 (a := (⟨a, ha⟩ : ↥V₂)⁻¹)
        (b := ⟨v, hvV2⟩)
      have h1 := key.mpr ⟨fun h' => absurd (by
        have := inv_mem (Subgroup.mem_subgroupOf.mp h')
        simpa using this) haV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hvV1⟩
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have e : x * v * x⁻¹ * v⁻¹ = b * a⁻¹ := by
      calc x * v * x⁻¹ * v⁻¹ = x * (a * (a⁻¹ * v)) * x⁻¹ * (a * (a⁻¹ * v))⁻¹ := by group
        _ = (x * a * x⁻¹) * (x * (a⁻¹ * v) * x⁻¹) * (a⁻¹ * v)⁻¹ * a⁻¹ := by group
        _ = b * a⁻¹ := by rw [hxa, hxc _ hac]; group
    rw [e] at hxv
    exact hbV (by
      rw [show b = (b * a⁻¹) * a by group]
      exact mul_mem (hV2.1 hxv) ha)
  ·
    have hbw : b⁻¹ * v ∈ V₂ := by
      have key := Subgroup.mul_mem_iff_of_index_two hidx2 (a := (⟨b, hbV'⟩ : ↥V)⁻¹)
        (b := ⟨v, hv⟩)
      have h1 := key.mpr ⟨fun h' => absurd (by
        have := inv_mem (Subgroup.mem_subgroupOf.mp h')
        simpa using this) hbV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hvV2⟩
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    by_cases hw1 : b⁻¹ * v ∈ fsuV1 T V
    · have e : x * v * x⁻¹ * v⁻¹ = a := by
        calc x * v * x⁻¹ * v⁻¹ = x * (b * (b⁻¹ * v)) * x⁻¹ * (b * (b⁻¹ * v))⁻¹ := by group
          _ = (x * b * x⁻¹) * (x * (b⁻¹ * v) * x⁻¹) * (b⁻¹ * v)⁻¹ * b⁻¹ := by group
          _ = a := by rw [hxb, hxc _ hw1]; group
      rw [e] at hxv
      exact haV hxv
    ·
      have hac : a⁻¹ * (b⁻¹ * v) ∈ fsuV1 T V := by
        have key := Subgroup.mul_mem_iff_of_index_two hidx1 (a := (⟨a, ha⟩ : ↥V₂)⁻¹)
          (b := ⟨b⁻¹ * v, hbw⟩)
        have h1 := key.mpr ⟨fun h' => absurd (by
          have := inv_mem (Subgroup.mem_subgroupOf.mp h')
          simpa using this) haV, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hw1⟩
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      set c := a⁻¹ * (b⁻¹ * v) with hc
      have hcV : c ∈ V := (Subgroup.mem_inf.mp hac).1
      have hv' : v = b * a * c := by rw [hc]; group
      have e : x * v * x⁻¹ * v⁻¹ = b⁻¹ := by
        rw [hv']
        calc x * (b * a * c) * x⁻¹ * (b * a * c)⁻¹ =
            (x * b * x⁻¹) * (x * a * x⁻¹) * (x * c * x⁻¹) * c⁻¹ * a⁻¹ * b⁻¹ := by group
          _ = a * b * b * a⁻¹ * b⁻¹ := by rw [hxb, hxa, hxc _ hac]; group
          _ = a * (b * b) * a⁻¹ * b⁻¹ := by group
          _ = b⁻¹ := by rw [hsq b hbV']; group
      rw [e] at hxv
      exact hbV (by simpa using hV2.1 (inv_mem hxv))

end CFSG.Quasithin.H13.L32A
