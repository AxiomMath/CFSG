module

public import CFSG.GH74.GLS.C3.Layer1.U1a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_of_isSylowOf_of_central [Finite G] {P S : Subgroup G} (hS : IsSylowOf 2 P S) {z : G}
    (hzS : z ∈ S) (hzc : ∀ s ∈ S, s * z = z * s) (hz : orderOf z = 2) : z ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sy, hSy⟩ := hS.exists_sylow_eq_subgroupOf
  let z' : ↥S := ⟨z, hzS⟩
  have hz' : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hnorm : (zpowers z').Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : g * z' = z' * g := Subtype.ext (hzc g g.2)
    have : g * z' ^ k * g⁻¹ = z' ^ k := by
      calc g * z' ^ k * g⁻¹ = (g * z' * g⁻¹) ^ k := conj_zpow.symm
        _ = z' ^ k := by
          have : g * z' * g⁻¹ = z' := by rw [hc]; group
          rw [this]
    rw [this]
    exact mem_zpowers_iff.2 ⟨k, rfl⟩⟩
  have hpg : IsPGroup 2 (zpowers z') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz', pow_one]
  have hle := IsPGroup.le_sylow_of_normal hpg Sy
  have hmem : z' ∈ (Sy : Subgroup ↥S) := hle (mem_zpowers z')
  rw [hSy] at hmem
  exact hmem

variable {x : G} {K L M T Q : Subgroup G}

theorem _root_.CFSG.GH74.GLS.Hyp9A.orderOf_x (h : Hyp9A x K L M T Q) : orderOf x = 2 :=
  h.twoTerminal.1.1

theorem _root_.CFSG.GH74.GLS.Hyp9A.K_le_centralizer (h : Hyp9A x K L M T Q) :
    K ≤ centralizer ({x} : Set G) :=
  h.twoTerminal.1.2.2.1

theorem _root_.CFSG.GH74.GLS.Hyp9A.x_mem_T [Finite G] (h : Hyp9A x K L M T Q) : x ∈ T :=
  mem_of_isSylowOf_of_central h.sylowT (mem_centralizer_singleton_iff.2 rfl)
    (fun _ hs => mem_centralizer_singleton_iff.1 hs) h.orderOf_x

theorem mem_centralizerSection_of_centralizes {c : G} {K M' : Subgroup G}
    (hc : ∀ k ∈ K, c * k = k * c) (hM : M' ≤ K) : c ∈ centralizerSection K M' := by
  have hcomm : ∀ k ∈ K, k * c = c * k := fun k hk => (hc k hk).symm
  have hcK : c ∈ centralizer (K : Set G) := Subgroup.mem_centralizer_iff.2 hcomm
  have hnK : c ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ hcK
  refine ⟨hnK, ?_, fun k hk => ?_⟩
  · have hcM : c ∈ centralizer (M' : Set G) :=
      Subgroup.mem_centralizer_iff.2 (fun m hm => hcomm m (hM hm))
    exact Subgroup.centralizer_le_normalizer _ hcM
  · have : ⁅k, c⁆ = 1 := by
      rw [commutatorElement_def]
      calc k * c * k⁻¹ * c⁻¹ = (c * k) * k⁻¹ * c⁻¹ := by rw [hcomm k hk]
        _ = 1 := by group
    rw [this]
    exact one_mem _

theorem _root_.CFSG.GH74.GLS.Hyp9A.x_mem_CxK [Finite G] (h : Hyp9A x K L M T Q) : x ∈ CxK x K := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizerSection_of_centralizes ?_ ?_⟩
  · intro k hk
    exact (mem_centralizer_singleton_iff.1 (h.K_le_centralizer hk)).symm
  · unfold pPrimeCoreOf
    intro y hy
    obtain ⟨y', -, rfl⟩ := hy
    exact y'.2

theorem _root_.CFSG.GH74.GLS.Hyp9A.x_mem_Q [Finite G] (h : Hyp9A x K L M T Q) : x ∈ Q := by
  rw [h.hQ]
  exact ⟨h.x_mem_T, h.x_mem_CxK⟩

theorem _root_.CFSG.GH74.GLS.Hyp9A.centralizer_le [Finite G] (h : Hyp9A x K L M T Q) : centralizer ({x} : Set G) ≤ M :=
  (centralizer_le_gammaK h.x_mem_Q h.orderOf_x).trans h.gamma

theorem pPrimeCoreOf_eq_bot [Finite G] {C K : Subgroup G} (hKC : K ≤ C)
    (hnorm : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hC : pPrimeCore 2 ↥C = ⊥) :
    pPrimeCoreOf 2 K = ⊥ := by
  set W : Subgroup G := pPrimeCoreOf 2 K with hW
  have hWK : W ≤ K := by
    intro y hy
    obtain ⟨y', -, rfl⟩ := hy
    exact y'.2
  have hWC : W ≤ C := hWK.trans hKC
  have hN : (W.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := pPrimeCoreOf_norm (M := C) (L := K) hnorm g.2 hn
    simpa using this⟩
  have hcop : Nat.Coprime 2 (Nat.card ↥(W.subgroupOf C)) := by
    have h1 : Nat.card ↥(W.subgroupOf C) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
    have h2 : Nat.card ↥W = Nat.card ↥(pPrimeCore 2 ↥K) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ K.subtype K.subtype_injective).symm.toEquiv
    rw [h1, h2]
    exact CFSG.pPrimeCore_coprime_card
  have hbot := (CFSG.pPrimeCore_eq_bot_iff).1 hC (W.subgroupOf C) hN hcop
  refine eq_bot_iff.2 (fun w hw => ?_)
  have : (⟨w, hWC hw⟩ : ↥C) ∈ W.subgroupOf C := hw
  rw [hbot, Subgroup.mem_bot] at this
  have := congrArg Subtype.val this
  simpa using this

end CFSG.GH74.GLS.C3.Layer1.Back
