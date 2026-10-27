module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LieType.SeitzGeneration.ExcPlanePair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

section Quot

variable {G Y : Type} [Group G] [Finite G] [Group Y]

theorem two_le_pRank_three_of_quotient (q : G →* Y) {A : Subgroup G} {α β : G} (hα : α ∈ A)
    (hβ : β ∈ A) (hα3 : q α ^ 3 = 1) (hβ3 : q β ^ 3 = 1) (hc : q α * q β = q β * q α)
    (hα1 : q α ≠ 1) (hβn : q β ∉ Subgroup.zpowers (q α)) : 2 ≤ CFSG.Open.pRank 3 A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup G := Subgroup.closure ({α, β} : Set G) with hP
  have hPA : P ≤ A := (Subgroup.closure_le A).2 (by rintro y (rfl | rfl) <;> assumption)
  have hoα : orderOf (q α) = 3 := orderOf_eq_prime hα3 hα1
  have hβ1 : q β ≠ 1 := fun h => hβn (h ▸ Subgroup.one_mem _)
  have hoβ : orderOf (q β) = 3 := orderOf_eq_prime hβ3 hβ1
  set f : ↥P →* Y := q.comp P.subtype with hf
  have hrange : f.range = Subgroup.closure ({q α, q β} : Set Y) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hP, MonoidHom.map_closure,
      Set.image_pair]
  have hcomm' : Commute (q α) (q β) := hc
  have hEel : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({q α, q β} : Set Y)) :=
    CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair hcomm' hα3 hβ3
  have hEcard : Nat.card ↥(Subgroup.closure ({q α, q β} : Set Y)) = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_sq Nat.prime_three hcomm' hoα hoβ hβn
  have hmem : ∀ y : Y, y ∈ f.range ↔ y ∈ Subgroup.closure ({q α, q β} : Set Y) := fun y => by
    rw [hrange]
  haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict
    (MonoidHom.rangeRestrict_surjective f)
  have hE3 : ∀ x : ↥f.range, x ^ 3 = 1 := fun x => Subtype.ext (hEel.2 x ((hmem x).1 x.2))
  have hEcard' : Nat.card ↥f.range = 3 ^ 2 := by
    rw [hrange]
    exact hEcard
  have hpg : IsPGroup 3 ↥f.range := fun x => ⟨1, by rw [pow_one]; exact hE3 x⟩
  have hnc : ¬ IsCyclic ↥f.range := by
    intro hcy
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hcy
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hE3 g)
    rw [hg, hEcard'] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  obtain ⟨S, hSp, hSmap⟩ := exists_isPGroup_map_eq_top Nat.prime_three
    (f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f) hpg
  have hScyc : ¬ IsCyclic ↥S := by
    intro hS
    have hsurj : Function.Surjective (f.rangeRestrict.comp S.subtype) := by
      intro y
      have hy : y ∈ S.map f.rangeRestrict := by rw [hSmap]; exact Subgroup.mem_top y
      obtain ⟨s, hs, rfl⟩ := hy
      exact ⟨⟨s, hs⟩, rfl⟩
    exact hnc (isCyclic_of_surjective _ hsurj)
  haveI : Fact (IsPGroup 3 ↥S) := ⟨hSp⟩
  obtain ⟨S', -, hS'card, hS'el⟩ := CFSG.lemma_4_5_a (R := ↥S) (p := 3) (by norm_num) hScyc
  have hE' : CFSG.Open.IsElemAbelian 3 S' :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S').mp hS'el
  have h2 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : S' ≤ ⊤) hE' hS'card
  let ι : ↥S →* G := P.subtype.comp S.subtype
  have hι : Function.Injective ι := P.subtype_injective.comp S.subtype_injective
  have h3 := CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) ι hι (⊤ : Subgroup ↥S)
  have h4 : (⊤ : Subgroup ↥S).map ι ≤ A := by
    rintro _ ⟨s, -, rfl⟩
    exact hPA s.1.2
  exact h2.trans (h3.trans (CFSG.SectionRank.pRank_mono (by norm_num) h4))

end Quot

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
