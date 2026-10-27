module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CentralizerComponent3
public import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedStructure3Pack

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (ReducedNongeneration)

@[expose] def reducedMeet {G : Type} [Group G] (p : ℕ) (M : Subgroup G) (z : G) :
    Subgroup (ReducedCentralizer p z) :=
  ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore p))

structure D1ConstrainedReducedData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) : Prop where
  pbar : (Pbar : Subgroup (ReducedCentralizer p z)) =
    ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (ReducedCentralizer p z) Pbar (reducedMeet p M z)
  zbar_eq : ∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
    QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC = zbar
  zbar_mem_center : zbar ∈ Subgroup.center (ReducedCentralizer p z)
  zbar_order : orderOf zbar = p

variable {G : Type} [Group G] [Finite G]

theorem D1CentralizerInput3.exists_constrainedData3 {p : ℕ} [Fact p.Prime] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) {P : Sylow p G} {M : Subgroup G}
    {z : G} (h : D1CentralizerInput3 p P M z) :
    ∃ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z),
      D1ConstrainedReducedData3 p P M z Pbar zbar := by
  obtain ⟨Pbar, zbar, hPbar, hred, hzbar, hzZ, hzp, -⟩ := h.exists_reduced_data hs hnab hK
  exact ⟨Pbar, zbar, ⟨hPbar, hred, hzbar, hzZ, hzp⟩⟩

theorem D1CentralizerInput3.exists_reducedStructure3 {p : ℕ} [Fact p.Prime] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) {P : Sylow p G} {M : Subgroup G}
    {z : G} (h : D1CentralizerInput3 p P M z)
    (hlayer : CFSG.layer (ReducedCentralizer p z) = ⊥) :
    ∃ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
      (E C : Subgroup (ReducedCentralizer p z)) (_ : E.Normal)
      (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)),
      D1ConstrainedReducedData3 p P M z Pbar zbar ∧
        ReducedStructure3 p Pbar (reducedMeet p M z) zbar E C e := by
  obtain ⟨Pbar, zbar, hdata⟩ := h.exists_constrainedData3 hs hnab hK
  obtain ⟨E, C, hEn, e, hstr⟩ := hdata.red.exists_reducedStructure3 hlayer hdata.zbar_mem_center
    hdata.zbar_order
  exact ⟨Pbar, zbar, E, C, hEn, e, hdata, hstr⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
