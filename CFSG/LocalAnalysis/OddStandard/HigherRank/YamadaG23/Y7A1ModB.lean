module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

theorem y7a_quotModIso_of {X W N Q Z : Subgroup G} [hZ : (Z.subgroupOf Q).Normal]
    (f : ↥W →* ↥Q ⧸ Z.subgroupOf Q) (hf : Function.Surjective f) (hker : f.ker = N.subgroupOf W)
    (hequiv : ∀ n ∈ X, ∀ w w' : ↥W, (w' : G) = n * w * n⁻¹ → ∀ q q' : ↥Q,
      (q' : G) = n * q * n⁻¹ → f w = (q : ↥Q ⧸ Z.subgroupOf Q) →
        f w' = (q' : ↥Q ⧸ Z.subgroupOf Q)) :
    QuotModIso X W N Q Z := by
  refine ⟨hZ, ?_⟩
  have hN : (N.subgroupOf W).Normal := hker ▸ MonoidHom.normal_ker f
  refine ⟨hN, ?_⟩
  let φ : ↥W ⧸ N.subgroupOf W ≃* ↥Q ⧸ Z.subgroupOf Q :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hφ : ∀ w : ↥W, φ (QuotientGroup.mk' (N.subgroupOf W) w) = f w := fun w => rfl
  refine ⟨φ, ?_⟩
  intro n hn w w' hw q q' hq h1
  show φ (QuotientGroup.mk' (N.subgroupOf W) w') = QuotientGroup.mk' (Z.subgroupOf Q) q'
  rw [hφ]
  exact hequiv n hn w w' hw q q' hq (by rw [← hφ]; exact h1)

end CFSG.OddStandard.HigherRank.YamadaG23
