module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec9g_model_E16 (hT6 : Asc82Tab6M) (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (hL : IsOm6M L) (P : Subgroup G) (hP : IsSylow2Of P L) (B : Subgroup G) (hBP : B ≤ P)
    (hB : IsElemAb2 B 4) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V) (_ : FiniteDimensional (ZMod 3) V)
      (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate)
      (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
      (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
      (F : Subgroup (ProjSim Q)),
      Nat.card F = 2 ^ 4 ∧
      (∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧ 2 ≤ invDim t ∧
        invDim t ≤ 4) ∧
      (∀ (b : G) (hb : b ∈ B), ffInducesHom hm e
        ⟨b, hBP.trans (hP.1.trans Subgroup.le_normalizer) hb⟩ ∈ F) ∧
      (∀ f ∈ F, ∃ (b : G) (hb : b ∈ B), ffInducesHom hm e
        ⟨b, hBP.trans (hP.1.trans Subgroup.le_normalizer) hb⟩ = f) := by
  obtain ⟨V, _, _, _, Q, hQ, hd, hs, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hL
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hd, hs⟩
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    hBP.trans (hP.1.trans Subgroup.le_normalizer)
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e
  let ψ : ↥B →* ProjSim Q := Φ.comp (Subgroup.inclusion hBN)
  let F : Subgroup (ProjSim Q) := ψ.range
  have hψ : ∀ b : ↥B, ψ b = Φ ⟨(b : G), hBN b.2⟩ := fun b => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb1 : Φ ⟨(b : G), hBN b.2⟩ = 1 := by
      rw [← hψ b]; exact hb
    have hcent : (b : G) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf ⟨(b : G), hBN b.2⟩).mp hb1
    by_contra hne
    have hbne : (b : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hbL : (b : G) ∈ L := (hBP.trans hP.1) b.2
    have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime (hB.1.2 (b : G) b.2) hbne
    exact sec711M_not_central hL hbL hb2 hcent
  have hF16 : Nat.card F = 2 ^ 4 := by
    have hcard : Nat.card F = Nat.card ↥B :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    rw [hcard, hB.2]
  have hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧
      2 ≤ invDim t ∧ invDim t ≤ 4 := by
    intro f hf hfne
    obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hf
    have hbne : b ≠ 1 := by
      intro hb1
      exact hfne (by rw [← hb_eq, hb1, map_one])
    have hbne' : (b : G) ≠ 1 := fun h => hbne (Subtype.ext h)
    have hbL : (b : G) ∈ L := (hBP.trans hP.1) b.2
    have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime (hB.1.2 (b : G) b.2) hbne'
    have hnot : (b : G) ∉ Subgroup.centralizer (L : Set G) :=
      sec711M_not_central hL hbL hb2
    have hin : InnerOn L (b : G) := Subgroup.mem_sup_left hbL
    have htype : InducesTypeSome L (b : G) 6 (-1) 4 1 :=
      (hT6.inner_iff G L hL (b : G) hb2 (hBN b.2)).mp ⟨hin, hnot⟩
    have hsim := simHasDim_of_inducesTypeSome hm e (hBN b.2) htype
    obtain ⟨t, htt, ht, htx⟩ := hsim
    refine ⟨t, htt, ?_, by omega, by omega⟩
    rw [← hb_eq]
    exact htx
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e, hm, F, hF16, hlift, ?_, ?_⟩
  · intro b hb
    rw [MonoidHom.mem_range]
    exact ⟨⟨b, hb⟩, rfl⟩
  · intro f hf
    obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hf
    exact ⟨(b : G), b.2, hb_eq⟩

end CFSG.OddStandard.SmallF3.Omega
