module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem characteristic_map_equiv_pair {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    {D : Subgroup P} (hD : D.Characteristic) : (D.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro ψ
  have h1 := Subgroup.characteristic_iff_map_eq.mp hD ((e.trans ψ).trans e.symm)
  calc (D.map e.toMonoidHom).map ψ.toMonoidHom
      = (D.map ((e.trans ψ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
    _ = D.map e.toMonoidHom := by rw [h1]

omit [Finite G] in
theorem map_subtype_characteristic {M T : Subgroup G} (hTM : T ≤ M) {T₁' : Subgroup ↥M}
    (hle : T₁' ≤ T.subgroupOf M) (hchar : (T₁'.subgroupOf (T.subgroupOf M)).Characteristic) :
    T₁'.map M.subtype ≤ T ∧ ((T₁'.map M.subtype).subgroupOf T).Characteristic := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_subgroupOf.mp (hle hx)
  · have heq : (T₁'.map M.subtype).subgroupOf T =
        (T₁'.subgroupOf (T.subgroupOf M)).map (Subgroup.subgroupOfEquivOfLe hTM).toMonoidHom := by
      ext x
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, hyx⟩
        refine ⟨⟨y, hle hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
        apply Subtype.ext
        rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe]
        exact hyx
      · rintro ⟨z, hz, hzx⟩
        refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
        have := congrArg Subtype.val hzx
        rw [MulEquiv.coe_toMonoidHom, Subgroup.subgroupOfEquivOfLe_apply_coe] at this
        exact this
    rw [heq]
    exact characteristic_map_equiv_pair _ hchar

theorem pRank_normalizer_pair_le_one {M T : Subgroup G} (hTM : T ≤ M) {T₁' : Subgroup ↥M}
    (hle : T₁' ≤ T.subgroupOf M) (hchar : (T₁'.subgroupOf (T.subgroupOf M)).Characteristic)
    (hne : T₁' ≠ ⊥) {q : ℕ} (hq : q.Prime)
    (hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank q (Subgroup.normalizer (C : Set G)) ≤ 1) :
    CFSG.Open.pRank q (Subgroup.normalizer (T₁' : Set ↥M)) ≤ 1 := by
  obtain ⟨hCT, hCchar⟩ := map_subtype_characteristic hTM hle hchar
  have hCne : T₁'.map M.subtype ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective T₁' M.subtype_injective).mp h)
  have h1 := hC (T₁'.map M.subtype) hCne hCT hCchar
  have h2 := CFSG.SectionRank.pRank_le_map hq.one_lt M.subtype M.subtype_injective
    (Subgroup.normalizer (T₁' : Set ↥M))
  have h3 := CFSG.SectionRank.pRank_mono hq.one_lt
    (Subgroup.le_normalizer_map (H := T₁') M.subtype)
  exact h2.trans (h3.trans h1)

end CFSG.LocalAnalysis.RankThreeUC.S15
