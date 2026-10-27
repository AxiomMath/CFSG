module

public import CFSG.LocalAnalysis.OddStandard.GH71.UFrame2
public import CFSG.LocalAnalysis.OddStandard.GH71.Unbalanced

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G} {g : G}

namespace Ctx71

theorem Su_le (h : Ctx71 G z S U u) (hgz : g * z * g⁻¹ = u) :
    S.map (MulAut.conj g).toMonoidHom ≤ Cen u := by
  rintro _ ⟨s, hs, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [mem_centralizer_singleton_iff, ← hgz]
  have hsz : s * z = z * s := mem_centralizer_singleton_iff.mp (h.S_le hs)
  calc g * s * g⁻¹ * (g * z * g⁻¹) = g * (s * z) * g⁻¹ := by group
    _ = g * (z * s) * g⁻¹ := by rw [hsz]
    _ = g * z * g⁻¹ * (g * s * g⁻¹) := by group

theorem U_le_Su (h : Ctx71 G z S U u) (hgU : g ∈ normalizer (U : Set G)) :
    U ≤ S.map (MulAut.conj g).toMonoidHom := by
  intro x hx
  refine ⟨g⁻¹ * x * g, h.U_le ?_, by simp [mul_assoc]⟩
  have := (mem_normalizer_iff.mp (inv_mem hgU) x).mp hx
  simpa [mul_assoc] using this

theorem Su_norm (h : Ctx71 G z S U u) (hgU : g ∈ normalizer (U : Set G)) :
    S.map (MulAut.conj g).toMonoidHom ≤ normalizer (U : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  exact mul_mem (mul_mem hgU (h.U_norm hs)) (inv_mem hgU)

omit [Finite G] in
theorem T₂_le_Su (hgT : g ∈ normalizer ((S ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G)) :
    S ⊓ centralizer ({u} : Set G) ≤ S.map (MulAut.conj g).toMonoidHom := by
  intro x hx
  refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
  have := (mem_normalizer_iff.mp (inv_mem hgT) x).mp hx
  simp only [inv_inv] at this
  exact this.1

theorem Su_inf (h : Ctx71 G z S U u)
    (hgT : g ∈ normalizer ((S ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G))
    (hgz : g * z * g⁻¹ = u) :
    S.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({z} : Set G) =
      S ⊓ centralizer ({u} : Set G) := by
  have hT := h.sylow_T₂
  refine hT.2.2 _ ?_ ?_ (le_inf (T₂_le_Su hgT) (inf_le_left.trans h.S_le))
  · rw [h.centralizer_U]
    exact le_inf inf_le_right (inf_le_left.trans (h.Su_le hgz))
  · exact (h.S2.map _).to_le inf_le_left

theorem frame_u (h : Ctx71 G z S U u) (hgU : g ∈ normalizer (U : Set G)) (hgz : g * z * g⁻¹ = u) :
    AhatFrame (HBar (Cen u)) (barIn (Cen u) (S.map (MulAut.conj g).toMonoidHom))
      (barIn (Cen u) U) := by
  have hSu := h.Su_le hgz
  have hSu2 : IsPGroup 2 ↥(S.map (MulAut.conj g).toMonoidHom) := h.S2.map _
  have hUu : U ≤ Cen u := (h.U_le_Su hgU).trans hSu
  have hU2 : IsPGroup 2 ↥U := h.S2.to_le h.U_le
  refine ⟨h.cover_of_involution h.orderOf_u, IVK812.isPGroup_barIn hSu2, ?_, ?_, ⟨?_, ?_⟩,
    IVK812.barIn_le_normalizer (h.Su_norm hgU)⟩
  · rw [IVK812.card_barIn_two hSu hSu2, card_map_of_injective (MulAut.conj g).injective, h.card_S]
  · exact map_mono (fun x hx => h.U_le_Su hgU hx)
  · have hU := h.U_four.1
    have hUsub : IsElementaryAbelian 2 ↥(U.subgroupOf (Cen u)) := by
      have e : ↥(U.subgroupOf (Cen u)) ≃* ↥U := subgroupOfEquivOfLe hUu
      refine { toIsMulCommutative := ⟨⟨fun a b => e.injective ?_⟩⟩, exponent_dvd_p := ?_ }
      · rw [map_mul, map_mul]
        exact hU.toIsMulCommutative.is_comm.comm _ _
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => e.injective ?_
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hU.exponent_dvd_p _
    exact isElementaryAbelian_map'' hUsub _
  · rw [IVK812.card_barIn_two hUu hU2]
    exact h.U_four.2

end Ctx71

end CFSG.OddStandard.GH71
