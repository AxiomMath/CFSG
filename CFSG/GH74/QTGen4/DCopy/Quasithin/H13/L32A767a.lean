module

public import CFSG.Quasithin.H13.L32A767a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem exists_conj_V2_F4 (h : Hyp147 G T L V) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) {F : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card ↥F = 4) : ∃ l ∈ L, conjSub l V₂ = F := by
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14_F4 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, -, -⟩ := S14.exists_basis_F4
  have hzV2 : z ∈ V₂ := hV2.1 hz0
  have hza : z ≠ a := fun e => haV (e ▸ hz0)
  have ha1 : a ≠ 1 := fun e => haV (e ▸ one_mem _)
  obtain ⟨f₁, hf₁, f₂, hf₂, hf₁1, hf₂1, hf₁₂⟩ := exists_two_of_card_four hF4
  obtain ⟨l, hl, hlz, hla⟩ := exists_conj_eq_pair (h.hyp1281One_F4 h13322 hMod) (hV2.2.1 hzV2)
    (hV2.2.1 ha) (hFV hf₁) (hFV hf₂) hz1 ha1 hf₁1 hf₂1 hza hf₁₂
  refine ⟨l, hl, (Subgroup.eq_of_le_of_card_ge ?_ ?_)⟩
  · intro w hw
    rw [mem_conjSub] at hw
    have hv := hw
    set v := l⁻¹ * w * l with hvdef
    have hw' : w = l * v * l⁻¹ := by rw [hvdef]; group
    rw [hw']
    rcases S14.mem_V2_F4 ha haV hv with h1 | h1
    · rcases S14.eq_of_mem_V1_F4 hz0 hz1 h1 with h2 | h2
      · rw [h2]; simp
      · rw [h2, hlz]; exact hf₁
    · rcases S14.eq_of_mem_V1_F4 hz0 hz1 h1 with h2 | h2
      · rw [eq_inv_of_mul_eq_one_right h2, show l * a⁻¹ * l⁻¹ = (l * a * l⁻¹)⁻¹ by group, hla]
        exact inv_mem hf₂
      · rw [show v = a⁻¹ * z by rw [← h2]; group,
          show l * (a⁻¹ * z) * l⁻¹ = (l * a * l⁻¹)⁻¹ * (l * z * l⁻¹) by group, hla, hlz]
        exact mul_mem (inv_mem hf₂) hf₁
  · rw [hF4, conjSub, Subgroup.card_map_of_injective (MulAut.conj l).injective, hV2.2.2.2]

end CFSG.Quasithin.H13.L32A
