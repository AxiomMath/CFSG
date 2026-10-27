module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwQ8
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
import CFSG.RankThree.SubgroupLists.ExtraspecialCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

private theorem card_le_two_of_isCyclic_of_sq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H : Subgroup C} (hH : ∀ x ∈ H, x * x = 1) : Nat.card H ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic (n := 2) fun c => ?_
  exact Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hH c c.2)

private theorem card_le_four_of_le_closure_pair {Q : Type*} [Group Q] [Finite Q]
    (hQ : ∀ x y : Q, x * y = y * x) {a b : Q} (hab : closure ({a, b} : Set Q) = ⊤)
    {B : Subgroup Q} (hB : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 4 := by
  set C := zpowers a with hC
  have hCn : C.Normal := ⟨fun x hx g => by rw [hQ g x, mul_inv_cancel_right]; exact hx⟩
  set π := QuotientGroup.mk' C with hπ
  have : IsCyclic (Q ⧸ C) := by
    have hle : closure ({a, b} : Set Q) ≤ (zpowers (π b)).comap π := by
      rw [closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, mem_zpowers _⟩
      change π a ∈ zpowers (π b)
      have ha : π a = 1 := (QuotientGroup.eq_one_iff a).mpr (mem_zpowers a)
      rw [ha]
      exact one_mem _
    refine ⟨⟨π b, fun z => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C z
    exact mem_zpowers_iff.mp (hle (hab ▸ mem_top x))
  have hsplit := RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker π B
  rw [QuotientGroup.ker_mk'] at hsplit
  have h1 : Nat.card ↥(B.map π) ≤ 2 := by
    refine card_le_two_of_isCyclic_of_sq fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← map_mul, hB x hx, map_one]
  have h2 : Nat.card ↥(B ⊓ C) ≤ 2 := by
    have hle : B ⊓ C ≤ C := inf_le_right
    rw [← Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    refine card_le_two_of_isCyclic_of_sq fun y hy => Subtype.ext ?_
    rw [mem_subgroupOf] at hy
    simpa using hB y (Subgroup.mem_inf.mp hy).1
  rw [hsplit]
  calc Nat.card ↥(B.map π) * Nat.card ↥(B ⊓ C) ≤ 2 * 2 := Nat.mul_le_mul h1 h2
    _ = 4 := rfl

theorem exists_unitary_invariant_sylow
    {a t : G} {J : Subgroup G} (hT : GSUnbalancingTriple a t J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) :
    IsL34Unitary J t ∧ ∃ P : Subgroup G, IsSylowTwoIn P J ∧ t ∈ normalizer (P : Set G) := by
  have hU := L34Facts.l34UnbalancingUnitaryStep G a t J hT hL
  exact ⟨hU, L34Tw.Q8.exists_a_invariant_sylow hU.1 hU.2.1⟩

theorem card_le_four_of_le_center_jhat
    {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    {B : Subgroup (L34Facts.Jhat J)} (hB : B ≤ center (L34Facts.Jhat J))
    (hB2 : ∀ b ∈ B, b * b = 1) : Nat.card B ≤ 4 := by
  obtain ⟨q, l, -, -, hqker, h3, hl, hls⟩ := L34Facts.exists_setting hJ hL
  obtain ⟨hc1, hc2, -, -⟩ := L34Facts.lam_z_facts (hqker ▸ le_refl _) hl
  have hQ : ∀ x y : ↥(center (L34Facts.Jhat J)), x * y = y * x := fun x y =>
    Subtype.ext ((mem_center_iff.mp x.2 y).symm)
  have hgen : closure ({⟨l L34Facts.z₁, hc1⟩, ⟨l L34Facts.z₂, hc2⟩} :
      Set ↥(center (L34Facts.Jhat J))) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨e, he⟩ -
    rw [← hqker] at he
    obtain ⟨i, j, hij⟩ := (L34Facts.mem_ker_iff hl hls h3).1 he
    have e1 : (⟨e, hqker ▸ he⟩ : ↥(center (L34Facts.Jhat J))) =
        (⟨l L34Facts.z₁, hc1⟩ : ↥(center (L34Facts.Jhat J))) ^ i *
          ⟨l L34Facts.z₂, hc2⟩ ^ j :=
      Subtype.ext (by simp [hij])
    rw [e1]
    exact mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
  have h := card_le_four_of_le_closure_pair hQ hgen
    (B := B.subgroupOf (center (L34Facts.Jhat J)))
    (fun x hx => Subtype.ext (hB2 _ (mem_subgroupOf.mp hx)))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hB).toEquiv] at h

theorem card_le_four_of_le_inf_zStarIn
    {J P B : Subgroup G} (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hP : IsSylowTwoIn P J) (hB : B ≤ P ⊓ zStarIn J) (hB2 : ∀ b ∈ B, b * b = 1) :
    Nat.card B ≤ 4 := by
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hBP : B ≤ P := fun b hb => (hB hb).1
  have hBJ : B ≤ J := hBP.trans hP.1
  set f : ↥B →* L34Facts.Jhat J := (L34Facts.jq J).comp (inclusion hBJ) with hf
  have hinj : Function.Injective f := by
    intro u v huv
    exact Subtype.ext (L34Facts.eq_of_jq_eq hP.1 hP2 (hBP u.2) (hBP v.2) huv)
  have hc : f.range ≤ center (L34Facts.Jhat J) := by
    rintro _ ⟨u, rfl⟩
    exact (L34Facts.mem_zStarIn_iff (hBJ u.2)).1 (hB u.2).2
  have h2 : ∀ e ∈ f.range, e * e = 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← map_mul, show u * u = 1 from Subtype.ext (hB2 _ u.2), map_one]
  have h := card_le_four_of_le_center_jhat hJ hL hc h2
  rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
