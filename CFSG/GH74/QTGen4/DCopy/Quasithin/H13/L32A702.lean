module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem inf_V_eq_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {I : Subgroup G} (hVI : fsuV1 T V ≤ I) (hIU : I < conjClosure V H)
    (hHI : H ≤ Subgroup.normalizer (I : Set G)) : V ⊓ I = fsuV1 T V := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨x, hx, -, hxa, hxb⟩ := S14.exists_x_F4 hz hz1 ha haV hb hbV
  have hxl : x ∈ l1 T L V := hl1eq ▸ hx
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hxH : x ∈ H := hL1H hxl
  have hxI : ∀ w ∈ I, x * w * x⁻¹ ∈ I := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hHI hxH) w).mp hw
  have haV' : a ∈ V := S14.hV2.2.1 ha

  have hVI' : a ∈ I → b ∈ I → V ≤ I := by
    intro haI hbI v hv
    rcases S14.mem_V_F4 hb hbV hv with h | h
    · rcases S14.mem_V2_F4 ha haV h with h' | h'
      · exact hVI h'
      · rw [show v = a⁻¹ * (a * v) by group]
        exact mul_mem (inv_mem haI) (hVI h')
    · have hbv : b * v ∈ I := by
        rcases S14.mem_V2_F4 ha haV h with h' | h'
        · exact hVI h'
        · rw [show b * v = a⁻¹ * (a * (b * v)) by group]
          exact mul_mem (inv_mem haI) (hVI h')
      rw [show v = b⁻¹ * (b * v) by group]
      exact mul_mem (inv_mem hbI) hbv
  have hnot : ¬ V ≤ I := fun h =>
    hIU.2 (conjClosure_le fun h' hh' v hv => (Subgroup.mem_normalizer_iff.mp (hHI hh') v).mp (h hv))
  refine le_antisymm (fun w hw => ?_) (le_inf (fun v hv => (Subgroup.mem_inf.mp hv).1) hVI)
  by_contra hwV
  apply hnot
  have hwV' := hw.1
  have hwI := hw.2
  have hbb : b * b = 1 := S14.mul_self_V_F4 hb
  have haa : a * a = 1 := S14.mul_self_V_F4 haV'
  rcases S14.mem_V_F4 hb hbV hwV' with h | h
  ·
    rcases S14.mem_V2_F4 ha haV h with h' | h'
    · exact absurd h' hwV
    · have haI : a ∈ I := by
        rw [show a = a * w * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      exact hVI' haI (hxa ▸ hxI a haI)
  · rcases S14.mem_V2_F4 ha haV h with h' | h'
    ·
      have hbI : b ∈ I := by
        rw [show b = b * w * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      have habI : a * b ∈ I := hxb ▸ hxI b hbI
      have haI : a ∈ I := by
        rw [show a = a * b * b⁻¹ by group]
        exact mul_mem habI (inv_mem hbI)
      exact hVI' haI hbI
    ·
      have habI : a * b ∈ I := by
        rw [show a * b = a * (b * w) * w⁻¹ by group]
        exact mul_mem (hVI h') (inv_mem hwI)
      have hx2 : x * (a * b) * x⁻¹ = a := by
        rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group, hxa, hxb]
        calc b * (a * b) = b * a * b := by group
          _ = a * b * b := by rw [S14.comm_V_F4 hb haV']
          _ = a := by rw [mul_assoc, hbb, mul_one]
      have haI : a ∈ I := hx2 ▸ hxI _ habI
      exact hVI' haI (hxa ▸ hxI a haI)

end Setting147

end CFSG.Quasithin.H13.L32A
