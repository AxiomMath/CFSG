module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step6

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

theorem exists_conj_u {G : Type*} [Group G] [Finite G] {S T M : Subgroup G} [IsSimpleGroup ↥S]
    (hnonab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) (hT : IsSylow2In S T) (hMT : M ≤ T)
    (hM : M.relIndex T = 2) {t₀ u : G} (hM1 : ∀ x ∈ M, orderOf x = 2 → x = t₀)
    (huT : u ∈ T) (huM : u ∉ M) (hu : orderOf u = 2) : ∃ g ∈ S, g * t₀ * g⁻¹ = u := by
  have hTS : T ≤ S := hT.1
  have hnonab' : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hp : IsPGroup 2 (T.subgroupOf S) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTS).symm
  have hidx : ¬ 2 ∣ (T.subgroupOf S).index := hT.2.2
  have hle : M.subgroupOf S ≤ T.subgroupOf S := Subgroup.subgroupOf_mono S hMT
  have hrel : (M.subgroupOf S).relIndex (T.subgroupOf S) = 2 :=
    (Subgroup.relIndex_subgroupOf (H := M) hTS).trans hM
  have ht2 : orderOf (⟨u, hTS huT⟩ : ↥S) = 2 :=
    (Subgroup.orderOf_mk (H := S) u (hTS huT)).trans hu
  obtain ⟨g, hg⟩ := exists_conj_mem_complement (G := ↥S) hnonab' hp hidx hle hrel
    (t := (⟨u, hTS huT⟩ : ↥S)) (Subgroup.mem_subgroupOf.2 huT)
    (fun h => huM (Subgroup.mem_subgroupOf.1 h)) ht2
  have horder : orderOf (((g⁻¹ * (⟨u, hTS huT⟩ : ↥S) * g : ↥S)) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    rw [show (g⁻¹ * (⟨u, hTS huT⟩ : ↥S) * g : ↥S) =
        MulAut.conj g⁻¹ (⟨u, hTS huT⟩ : ↥S) by simp [MulAut.conj_apply]]
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk (H := S) u (hTS huT), hu]
  have hgt : ((g⁻¹ * (⟨u, hTS huT⟩ : ↥S) * g : ↥S) : G) = t₀ :=
    hM1 _ (Subgroup.mem_subgroupOf.1 hg) horder
  refine ⟨(g : G), g.2, ?_⟩
  have hgt' : (g : G)⁻¹ * u * (g : G) = t₀ := by simpa using hgt
  calc (g : G) * t₀ * (g : G)⁻¹
      = (g : G) * ((g : G)⁻¹ * u * (g : G)) * (g : G)⁻¹ := by rw [hgt']
    _ = u := by group

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
