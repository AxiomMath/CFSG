module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Model
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {D : Data} {k : ℕ} {G : Type} [Group G] {P Q : Subgroup G} {Θ : ℕ → G}

theorem y63_mem_cen (hΘ : Y63Model D k P Q Θ) (hC : D.CenSpec k) (g : G) :
    g ∈ cen Q ↔ g = 1 ∨ g = Θ D.z := by
  obtain ⟨hz, -, hzc, hcen⟩ := hC
  have hcomm : ∀ i < 1024, ∀ j < 1024, Θ i * Θ j = Θ j * Θ i ↔ D.mq k i j = D.mq k j i := by
    intro i hi j hj
    rw [← hΘ.mul i hi j hj, ← hΘ.mul j hj i hi]
    exact ⟨fun h => hΘ.inj _ (hΘ.mq_lt i hi j hj) _ (hΘ.mq_lt j hj i hi) h, fun h => by rw [h]⟩
  constructor
  · intro hg
    obtain ⟨hgQ, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨i, hi, rfl⟩ := hΘ.surj g hgQ
    have h01 : i = 0 ∨ i = D.z := by
      refine hcen i hi (fun y hy => ?_)
      have := (Subgroup.mem_centralizer_iff.mp hgC) (Θ y) (hΘ.mem y hy)
      exact (hcomm i hi y hy).mp this.symm
    rcases h01 with rfl | rfl
    · exact Or.inl hΘ.one
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine Subgroup.mem_inf.mpr ⟨hΘ.mem _ hz, Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)⟩
      obtain ⟨j, hj, rfl⟩ := hΘ.surj h hh
      exact ((hcomm D.z hz j hj).mpr (hzc j hj)).symm

theorem y63_card_cen (hΘ : Y63Model D k P Q Θ) (hC : D.CenSpec k) : Nat.card ↥(cen Q) = 2 := by
  have hne : Θ D.z ≠ 1 := fun h =>
    hC.2.1 (hΘ.inj _ hC.1 _ (by norm_num) (h.trans hΘ.one.symm))
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_mem _⟩, ⟨Θ D.z, (y63_mem_cen hΘ hC _).mpr (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h).symm
  · ext ⟨g, hg⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (y63_mem_cen hΘ hC g).mp hg with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end CFSG.OddStandard.HigherRank.YamadaG23
