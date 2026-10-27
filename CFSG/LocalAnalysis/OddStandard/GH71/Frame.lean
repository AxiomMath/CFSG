module

public import CFSG.LocalAnalysis.OddStandard.GH71.Setup
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10One
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Quot
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatSpec

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_conj_mem {U : Subgroup G} {g : G}
    (h : ∀ x ∈ U, g * x * g⁻¹ ∈ U) : g ∈ normalizer (U : Set G) := by
  have hle : U.map (MulAut.conj g).toMonoidHom ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : U.map (MulAut.conj g).toMonoidHom = U :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : x = y := by
      have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      exact (mul_left_cancel (mul_right_cancel e)).symm
    rw [this]; exact hy

theorem exists_ctx71 {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S)
    (hcov : IsDoubleCoverOfAlt (CentralizerBar z) 11) : ∃ U u, Ctx71 G z S U u := by
  have hone : TypeOneCase G Kind.ly := by
    left
    have hd := hctx.data
    cases hd with
    | ly hs =>
      obtain ⟨n, -, hs⟩ := hs
      exact hs.one_class
  obtain ⟨U, hUS, hU4, hUn, hzU, hAut⟩ := exists_U_typeOne hctx hone
  have hUn' : S ≤ normalizer (U : Set G) := fun s hs => mem_normalizer_of_conj_mem (hUn s hs)
  have hex : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    by_contra hne
    push Not at hne
    have hsub : (U : Set G) ⊆ ({1, z} : Set G) := by
      intro x hx
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hne x hx h1)
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := Set.ncard_insert_le _ _ |>.trans (by simp)
    have hU4' : (U : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]; exact hU4.2
    omega
  obtain ⟨u, huU, hu1, huz⟩ := hex
  exact ⟨U, u, ⟨hctx, hcov, hUS, hU4, hUn', hzU, hAut, huU, hu1, huz⟩⟩

namespace Ctx71

variable {z : G} {S U : Subgroup G} {u : G}

theorem frame (h : Ctx71 G z S U u) :
    AhatFrame (HBar (Cen z)) (barIn (Cen z) S) (barIn (Cen z) U) := by
  have hSC : S ≤ Cen z := h.S_le
  have hUC : U ≤ Cen z := h.U_le.trans hSC
  have hU2 : IsPGroup 2 ↥U := h.S2.to_le h.U_le
  refine ⟨h.cover, IVK812.isPGroup_barIn h.S2, ?_, ?_, ⟨?_, ?_⟩,
    IVK812.barIn_le_normalizer h.U_norm⟩
  · rw [IVK812.card_barIn_two hSC h.S2, h.card_S]
  · exact map_mono (fun x hx => h.U_le hx)
  · have hU := h.U_four.1
    have hUsub : IsElementaryAbelian 2 ↥(U.subgroupOf (Cen z)) := by
      have e : ↥(U.subgroupOf (Cen z)) ≃* ↥U := subgroupOfEquivOfLe hUC
      refine { toIsMulCommutative := ⟨⟨fun a b => e.injective ?_⟩⟩, exponent_dvd_p := ?_ }
      · rw [map_mul, map_mul]
        exact hU.toIsMulCommutative.is_comm.comm _ _
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => e.injective ?_
        rw [map_pow, map_one]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hU.exponent_dvd_p _
    exact isElementaryAbelian_map'' hUsub _
  · rw [IVK812.card_barIn_two hUC hU2]
    exact h.U_four.2

theorem not_mem_center (h : Ctx71 G z S U u) {x : G} (hxU : x ∈ U) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    (QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) ⟨x, h.U_le.trans h.S_le hxU⟩ : HBar (Cen z)) ∉
      center (HBar (Cen z)) := by
  intro hc
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z))
  have hzC : z ∈ Cen z := mem_centralizer_singleton_iff.mpr rfl
  have hxC : x ∈ Cen z := h.U_le.trans h.S_le hxU
  have hcard : Nat.card (center (HBar (Cen z))) = 2 := h.cover.2.1
  have hzc : π ⟨z, hzC⟩ ∈ center (HBar (Cen z)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp g'.2)
  have hz1 : π ⟨z, hzC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨z, hzC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).mp h1
    refine not_mem_pPrimeCore_of_involution ?_ ?_ hmem
    · exact Subtype.ext (h.sq_eq_one_of_mem_U h.z_mem)
    · intro h1'; exact h.z_ne_one (congrArg Subtype.val h1')
  have hx1' : π ⟨x, hxC⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨x, hxC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).mp h1
    refine not_mem_pPrimeCore_of_involution ?_ ?_ hmem
    · exact Subtype.ext (h.sq_eq_one_of_mem_U hxU)
    · intro h1'; exact hx1 (congrArg Subtype.val h1')
  have hxz' : π ⟨x, hxC⟩ = π ⟨z, hzC⟩ := by
    by_contra hne
    have h3 : ({1, π ⟨z, hzC⟩, π ⟨x, hxC⟩} : Set (HBar (Cen z))) ⊆
        (center (HBar (Cen z)) : Set (HBar (Cen z))) := by
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact (center _).one_mem
      · exact hzc
      · exact hc
    have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
    have h5 : ({1, π ⟨z, hzC⟩, π ⟨x, hxC⟩} : Set (HBar (Cen z))).ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨1, _, _, hz1.symm, hx1'.symm, fun e => hne e.symm, rfl⟩
    have h6 : ((center (HBar (Cen z)) : Set (HBar (Cen z)))).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]; exact hcard
    omega
  have hmem : (⟨x, hxC⟩ * ⟨z, hzC⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := by
    have h1 : π (⟨x, hxC⟩ * ⟨z, hzC⟩) = 1 := by
      rw [map_mul, hxz', ← map_mul]
      have : (⟨z, hzC⟩ * ⟨z, hzC⟩ : ↥(Cen z)) = 1 := Subtype.ext (h.sq_eq_one_of_mem_U h.z_mem)
      rw [this, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  refine not_mem_pPrimeCore_of_involution ?_ ?_ hmem
  · apply Subtype.ext
    show x * z * (x * z) = 1
    have hxz2 : x * z ∈ U := U.mul_mem hxU h.z_mem
    exact h.sq_eq_one_of_mem_U hxz2
  · intro h1
    apply hxz
    have h2 : x * z = 1 := congrArg Subtype.val h1
    have hz : z * z = 1 := h.sq_eq_one_of_mem_U h.z_mem
    calc x = x * z * z := by rw [mul_assoc, hz, mul_one]
      _ = z := by rw [h2, one_mul]

end Ctx71

end CFSG.OddStandard.GH71
