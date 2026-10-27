module

public import CFSG.ClassicalInvolution.AschTight.S1911SecA
public import CFSG.ClassicalInvolution.AschTight.S1911FusF

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
theorem map_conjSub_perfectCore {a : G} (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    (conjSub c (perfectCoreIn K a)).map (Subgroup.centralizer ({a} : Set G)).subtype =
      conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) := by
  rw [conjSub_subgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left]
  calc conjSub (c : G) (perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
      ≤ conjSub (c : G) (Subgroup.centralizer ({a} : Set G)) :=
        Subgroup.map_mono ((perfectResidualOf_le _).trans inf_le_right)
    _ = Subgroup.centralizer ({a} : Set G) :=
        conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer c.2)

theorem dEdgeless_conjFamily (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    Disconnected.DEdgeless (conjFamily (perfectCoreIn K a)) := by
  have hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.mem_subgroupOf.mp hL.mem
  have key : ∀ M₁ ∈ conjFamily (perfectCoreIn K a),
      ∀ M₂ ∈ conjFamily (perfectCoreIn K a),
      M₂ ∉ omegaNbr (conjFamily (perfectCoreIn K a)) M₁ := by
    rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ ⟨-, hne, R, hR, hRle, hRN⟩
    obtain ⟨⟨x, hx, y, hy, hxy⟩, h8⟩ := exists_ne_comm_of_mem_rSet hd.tight.branch.odd h5 hL hR
    have hR2 := isPGroup_of_mem_rSet hR
    refine false_of_le_normalizer_conjSub hd hzKa c₁.2 c₂.2 ?_
      (hR2.map (Subgroup.centralizer ({a} : Set G)).subtype)
      ⟨(x : G), Subgroup.mem_map_of_mem _ hx, (y : G), Subgroup.mem_map_of_mem _ hy,
        fun h => hxy (Subtype.ext h)⟩ ?_ ?_ ?_
    · intro h
      apply hne
      apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
      rw [map_conjSub_perfectCore, map_conjSub_perfectCore, h]
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective R _
        (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
      omega
    · rw [← map_conjSub_perfectCore]
      exact Subgroup.map_mono hRle
    · rw [← map_conjSub_perfectCore]
      exact (Subgroup.map_mono hRN).trans (Subgroup.le_normalizer_map _)
  intro M₁ hM₁ M₂ hM₂ hadj
  rcases hadj with h | h
  · exact key M₁ hM₁ M₂ hM₂ h
  · exact key M₂ hM₂ M₁ hM₁ h

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
