module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem sec9u_inducesTypeSome_conj {L : Subgroup G} {s c : G}
    (hc : c ∈ Subgroup.normalizer (L : Set G)) {r : ℕ} (hr1 : 1 ≤ r) (hr5 : r ≤ 5) {α : ℤˣ}
    (hs : InducesTypeSome L s 6 (-1) r α) :
    ∃ α' : ℤˣ, InducesTypeSome L (c * s * c⁻¹) 6 (-1) r α' := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, hd, hε, hix, hty⟩ := hs
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hd, hε⟩
  let w : ProjSim Q := ffInducesHom hm e ⟨c, hc⟩
  have hcsc : c * s * c⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hix.1) (Subgroup.inv_mem _ hc)
  have hmap : ffInducesHom hm e ⟨c * s * c⁻¹, hcsc⟩ = w * x * w⁻¹ := by
    have hprod : (⟨c * s * c⁻¹, hcsc⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨c, hc⟩ * ⟨s, hix.1⟩ * ⟨c, hc⟩⁻¹ := Subtype.ext rfl
    rw [hprod, map_mul, map_mul, map_inv, ffInducesHom_eq hm e hix]
  have hdim : SimHasDim (w * x * w⁻¹) r := simHasDim_conj hty.simHasDim w
  obtain ⟨α', hα'⟩ := sec9g_simHasType_of_simHasDim hQ hd hr1 hr5 hdim
  have hspec := ffInducesHom_spec hm e ⟨c * s * c⁻¹, hcsc⟩
  rw [hmap] at hspec
  exact ⟨α', V, inferInstance, inferInstance, inferInstance, Q, hQ, e, w * x * w⁻¹, hd, hε,
    hspec, hα'⟩

end CFSG.OddStandard.SmallF3.Omega
