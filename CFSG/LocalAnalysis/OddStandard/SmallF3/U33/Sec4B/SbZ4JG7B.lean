module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG6B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG6C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal] {t : G}

theorem z4j_d17_lift {S : Subgroup G} {Vc Vsub : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc)
    (hn : ∀ g ∈ Vh, ∀ v ∈ Vsub.map (z4iπ N), g * v * g⁻¹ ∈ Vsub.map (z4iπ N))
    (h4 : Nat.card (Vsub.map (z4iπ N)) = 4)
    (he : ∀ a ∈ Vsub.map (z4iπ N), ∀ b ∈ Vsub.map (z4iπ N), a * b = b * a ∧ a * a = 1)
    (htV : ∀ g : G, ∀ v ∈ Vsub.map NQ.subtype, g * t * g⁻¹ ≠ v)
    (hconj : ∀ (g : G) (P : Subgroup G), IsPGroup 2 P →
      P ≤ centralizer ({g * t * g⁻¹} : Set G) → Nat.card P = 128 →
      ∃ k : G, P.map (MulAut.conj k).toMonoidHom = S)
    (h17 : ∀ V'' : Subgroup G, V'' ≤ S → (∀ s ∈ S, ∀ v ∈ V'', s * v * s⁻¹ ∈ V'') →
      Nat.card V'' = 4 → (∀ a ∈ V'', ∀ b ∈ V'', a * b = b * a ∧ a * a = 1) →
      (∀ g : G, ∀ v ∈ V'', g * t * g⁻¹ ≠ v) →
      17 ≤ {x : G | x ∈ S ⊓ centralizer (V'' : Set G) ∧ x * x = 1}.ncard)
    {T : ↥NQ ⧸ N → Prop}
    (hT : ∀ a : ↥NQ, a * a = 1 → a ≠ 1 → (T (z4iπ N a) ↔ ∃ g : G, (a : G) = g * t * g⁻¹))
    {β : ↥NQ ⧸ N} (hβ : β ∈ Vh) (hβ2 : β * β = 1) (hβ1 : β ≠ 1) (hTβ : T β)
    (hβV : β ∈ centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)))
    (hcard : Nat.card ↥(Vh ⊓ centralizer ({β} : Set (↥NQ ⧸ N))) = 128) :
    17 ≤ {u : ↥NQ ⧸ N | u ∈ Vh ⊓ centralizer ({β} : Set (↥NQ ⧸ N)) ⊓
      centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) ∧
      u * u = 1}.ncard := by
  obtain ⟨b, hbVc, rfl⟩ := hVc.exists_lift hβ
  have hb2 : b * b = 1 := hVc.mul_self_eq_one hbVc hβ2
  have hb1 : b ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  obtain ⟨g₀, hg₀⟩ := (hT b hb2 hb1).mp hTβ
  obtain ⟨hVn, hV4, hVe⟩ := z4j_V_facts_lift hVc hVsub hn h4 he
  have hcardG : Nat.card ↥(Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G)) = 128 := by
    rw [z4j_card_cent_lift hVc hbVc]
    exact hcard
  exact z4j_d17_transport hVc hVsub hbVc
    (z4j_d17_Gset (hVc.isPGroup.map _) (Subgroup.map_mono hVsub) hVn hV4 hVe htV
      (z4j_comm_lift hVc hVsub hbVc hβV) hg₀ hcardG hconj h17)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
