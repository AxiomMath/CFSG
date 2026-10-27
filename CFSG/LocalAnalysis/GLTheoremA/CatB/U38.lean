module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U38Heis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem lift_sylow_amb {G : Type} [Group G] [Finite G] {J : Subgroup G} {M : Type} [Group M]
    (π : ↥J →* M) (hk : ¬ 2 ∣ Nat.card π.ker) {Tb : Subgroup M} (hTr : Tb ≤ π.range)
    (hT : SylowAmb Tb) : ∃ T : Subgroup G, T ≤ J ∧ SylowAmb T := by
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_two π hk hT.1 hTr
  let eWT : W ≃* Tb := (mulEquivMap π hWinj).trans (MulEquiv.subgroupCongr hWmap)
  let eTW : (W.map J.subtype) ≃* W := (W.equivMapOfInjective J.subtype J.subtype_injective).symm
  have hstr : SylowStr ↥(W.map J.subtype) :=
    (sylowStr_of_amb hT).of_mulEquiv (eWT.symm.trans eTW.symm)
  exact ⟨W.map J.subtype, Subgroup.map_subtype_le _, sylowAmb_of_str hstr⟩

section Row

variable {G : Type} [Group G] [Finite G]

theorem sylowU38At_of_model (hmodel : ∃ T : Subgroup U38Model, SylowAmb T) : SylowU38At G := by
  intro X L hX hL hodd hcat
  obtain ⟨e⟩ := bridge_u3eight hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker L hkc hodd
  obtain ⟨Tb, hTb⟩ := hmodel
  obtain ⟨T, hTL, hT⟩ := lift_sylow_amb π hk2
    (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact le_top) hTb
  exact ⟨T, hTL, hT⟩

theorem sylowU38At_holds : SylowU38At G := sylowU38At_of_model U38Heis.exists_sylowAmb_u38

end Row

end CFSG.LocalAnalysis.GLTheoremA.CatB
