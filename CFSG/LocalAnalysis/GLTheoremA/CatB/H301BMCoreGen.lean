module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenHyp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open

theorem extraspecial_of_overgroup {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p])
    {R Z B R0 R1 : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) (hB : IsElemAbelian p B)
    (hBR : B ≤ Subgroup.normalizer (R : Set G))
    (hCB : R ⊓ Subgroup.centralizer (B : Set G) ≤ Z)
    (hH : ∀ H : Subgroup G, H ≤ B → Nat.card H * p = Nat.card B →
      Nat.card ↥(R ⊓ Subgroup.centralizer (H : Set G)) ≤ 2 ^ (k + 1))
    (hT : ∀ T : Subgroup G, IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
      T ≤ Subgroup.centralizer (Z : Set G) → T ≤ R)
    (hR0 : timmesfeldIsExtraspecial ↥R0) (hZ0 : Z = (Subgroup.center ↥R0).map R0.subtype)
    (hBR0 : B ≤ Subgroup.normalizer (R0 : Set G)) (hR1 : IsPGroup 2 R1)
    (hBR1 : B ≤ Subgroup.normalizer (R1 : Set G)) (h01 : R0 < R1) :
    timmesfeldIsExtraspecial ↥R1 := by
  have hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r := fun z hz r hr =>
    (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr
  have hZR0 : Z ≤ R0 := by
    rw [hZ0]
    exact Subgroup.map_subtype_le _
  have hR0R : R0 ≤ R := hT R0 hR0.1 hBR0 fun r hr =>
    Subgroup.mem_centralizer_iff.2 fun z (hz : z ∈ Z) =>
      ((mem_center_map_iff.1 (hZ0 ▸ hz)).2 r hr).symm
  have hZT : Z ≤ R1 ⊓ R := le_inf (hZR0.trans h01.le) (hZR0.trans hR0R)
  have hBT : B ≤ Subgroup.normalizer ((R1 ⊓ R : Subgroup G) : Set G) :=
    (le_inf hBR1 hBR).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hrad := radical_le_of_hyperplane_bound hp2 hk hR hZ hB hBR hCB hH hZT inf_le_right hBT
  have hTe : timmesfeldIsExtraspecial ↥(R1 ⊓ R) := by
    refine ((isExtraspecial_or_card_two_iff_radical hR hZ hZT inf_le_right).2 hrad).resolve_right
      fun h2 => ((isExtraspecial_iff_radical hR hZ hZR0 hR0R).1 hR0).1 ?_
    exact (le_inf h01.le hR0R).trans (Subgroup.eq_of_le_of_card_ge hZT
      (h2.trans (card_center_map_eq_two hR hZ).symm).le).symm.le
  have hZT' : Z = (Subgroup.center ↥(R1 ⊓ R)).map (R1 ⊓ R).subtype := le_antisymm
    (fun z hz => mem_center_map_iff.2
      ⟨hZT hz, fun t ht => hZc z hz t (Subgroup.mem_inf.1 ht).2⟩)
    fun x hx => hrad x (mem_center_map_iff.1 hx).1 fun t ht =>
      ((mem_center_map_iff.1 hx).2 t ht).symm
  have hN1 : R1 ⊓ Subgroup.normalizer ((R1 ⊓ R : Subgroup G) : Set G) ≤ R1 ⊓ R :=
    le_inf inf_le_left (hT _ (hR1.to_le inf_le_left)
      ((le_inf hBR1 (hBT.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
      (inf_le_right.trans (normalizer_le_centralizer_center hTe hZT')))
  have hR1T : R1 ≤ R1 ⊓ R := by
    refine Subgroup.subgroupOf_eq_top.1 (Classical.byContradiction fun hne => ?_)
    haveI := hR1.isNilpotent
    have hlt := normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.2 hne)
    rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_left : R1 ⊓ R ≤ R1)] at hlt
    exact hlt.not_ge fun n hn => Subgroup.mem_subgroupOf.2
      (hN1 (Subgroup.mem_inf.2 ⟨n.2, Subgroup.mem_subgroupOf.1 hn⟩))
  exact (le_antisymm inf_le_left hR1T) ▸ hTe

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
