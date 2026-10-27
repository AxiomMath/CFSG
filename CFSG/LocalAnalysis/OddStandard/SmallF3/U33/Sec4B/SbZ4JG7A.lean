module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal] {t : G}

theorem z4j_stageF {Vc Vsub : Subgroup ↥NQ} {Vh Mc K : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc) (hMc : Mc ≤ Vh)
    (hn : ∀ g ∈ Vh, ∀ v ∈ Vsub.map (z4iπ N), g * v * g⁻¹ ∈ Vsub.map (z4iπ N))
    (hd : Vsub.map (z4iπ N) ≤ ⁅Vh, Vh⁆) (h4 : Nat.card (Vsub.map (z4iπ N)) = 4)
    (he : ∀ a ∈ Vsub.map (z4iπ N), ∀ b ∈ Vsub.map (z4iπ N), a * b = b * a ∧ a * a = 1)
    (hu : ∀ W : Subgroup (↥NQ ⧸ N), W ≤ Vh → (∀ g ∈ Vh, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W ≤ ⁅Vh, Vh⁆ → Nat.card W = 4 → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1) →
      W = Vsub.map (z4iπ N))
    (hK : Vh ⊓ centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) = K)
    {σ : ↥NQ ⧸ N} (hσ : σ ∈ Vh) (hσ2 : σ * σ = 1) (hσK : σ ∉ K)
    {T : ↥NQ ⧸ N → Prop}
    (hT : ∀ a : ↥NQ, a * a = 1 → a ≠ 1 → (T (z4iπ N a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹))
    (hTσ : T σ)
    (hfus : ∀ u ∈ Vh, u * u = 1 → T u → u ∉ K → ∃ w ∈ Mc, u = w * σ * w⁻¹)
    (hcard : Nat.card ↥(Vh ⊓ centralizer ({σ} : Set (↥NQ ⧸ N))) = 128)
    (hbound : ∀ (g : G) (R : Subgroup G), IsPGroup 2 R →
      R ≤ centralizer ({g * t * g⁻¹} : Set G) → Nat.card R ≤ 128) :
    ¬ 2 ∣ (Vc.map NQ.subtype).index := by
  obtain ⟨s, hsVg, hs2, hsV, hsconj, hfusG, hcardG⟩ :=
    z4j_fusion_lift hVc hVsub hMc hK hσ hσ2 hσK hT hTσ hfus hcard
  exact z4j_sylow_lift (hVc.isPGroup.map _) hbound (z4j_V_char_lift hVc hVsub hn hd h4 he hu)
    ⟨s, hsVg, hs2, hsV, hsconj, hfusG, hcardG⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
