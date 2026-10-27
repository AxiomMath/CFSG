module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem I2018BorelTits_holds : I2018BorelTits := by
  intro S _ _ hS hch T hT hT0
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.chevTwoNonabelian_holds S hS hch
  have hPne : Subgroup.normalizer (T : Set S) ≠ ⊤ := by
    intro htop
    rw [Subgroup.normalizer_eq_top_iff] at htop
    haveI : T.Normal := htop
    rcases hS.eq_bot_or_eq_top_of_normal T with h | h
    · exact hT0 h
    ·
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hT' : IsPGroup 2 ↥(⊤ : Subgroup S) := by
        rw [← h]
        exact hT
      have h2S : IsPGroup 2 S := hT'.of_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup S) ≃* S)
      have hcard : Nat.card S = 2 := (IsPGroup.isSimpleGroup_iff_card_eq h2S).1 hS
      haveI : IsCyclic S := isCyclic_of_prime_card hcard
      letI : CommGroup S := IsCyclic.commGroup
      exact hab (mul_comm a b)
  refine ⟨Subgroup.normalizer (T : Set S), hPne, ?_, le_rfl⟩
  intro x hx
  have hxP : x ∈ Subgroup.normalizer (T : Set S) := Subgroup.le_normalizer hx
  haveI hn : (T.subgroupOf (Subgroup.normalizer (T : Set S))).Normal := inferInstance
  have hpg : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (T : Set S))) :=
    hT.comap_of_injective (Subgroup.normalizer (T : Set S)).subtype Subtype.val_injective
  have hle : T.subgroupOf (Subgroup.normalizer (T : Set S)) ≤
      CFSG.pCore 2 ↥(Subgroup.normalizer (T : Set S)) := le_sSup ⟨hn, hpg⟩
  have hy : (⟨x, hxP⟩ : ↥(Subgroup.normalizer (T : Set S))) ∈
      T.subgroupOf (Subgroup.normalizer (T : Set S)) := Subgroup.mem_subgroupOf.2 hx
  show x ∈ (CFSG.pCore 2 ↥(Subgroup.normalizer (T : Set S))).map
    (Subgroup.normalizer (T : Set S)).subtype
  exact Subgroup.mem_map.2 ⟨⟨x, hxP⟩, hle hy, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
