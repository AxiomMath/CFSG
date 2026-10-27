module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19B
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Cover
public import CFSG.GH74.GLS.Stage2.Local.Lemma23

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4

section Group

variable {G : Type} [Group G] {z : G}

@[expose] def Nfrak (z : G) : Subgroup ↥(Cen z) := layer ↥(Cen z) ⊔ O2coreRes ↥(Cen z)

instance Nfrak_normal : (Nfrak z).Normal := by
  have h1 : (layer ↥(Cen z)).Characteristic := CFSG.LocalCores.layer_characteristic
  have h2 : (O2coreRes ↥(Cen z)).Normal := O2coreRes_normal
  unfold Nfrak
  infer_instance

theorem directX (h4c : Thm4c z (Cen z)) :
    IsInternalDirectProduct (pPrimeCore 2 ↥(Cen z)) (O2coreRes ↥(Cen z)) (O22Res ↥(Cen z)) := by
  have h := h4c rfl
  rw [O2coreOf_O2Of_eq, O22Of_O2Of_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hf := (Cen z).subtype_injective
  refine ⟨?_, ?_, ?_⟩
  · apply Subgroup.map_injective hf
    rw [Subgroup.map_sup]
    exact h1
  · intro a ha b hb
    apply hf
    exact h2 (a : G) ⟨a, ha, rfl⟩ (b : G) ⟨b, hb, rfl⟩
  · have h3' : (pPrimeCore 2 ↥(Cen z)).map (Cen z).subtype ⊓
        (O2coreRes ↥(Cen z)).map (Cen z).subtype = ⊥ := h3
    rw [← Subgroup.map_inf _ _ _ hf] at h3'
    exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 h3'

theorem WBar_eq_map (h4c : Thm4c z (Cen z)) :
    WBar z = (O2coreRes ↥(Cen z)).map (toBar z) := by
  obtain ⟨h1, -, -⟩ := directX h4c
  have hW : WBar z = (O22Res ↥(Cen z)).map (toBar z) := by
    unfold WBar barOf
    have : WC z = (O22Res ↥(Cen z)).map (Cen z).subtype := rfl
    rw [this]
    unfold Subgroup.subgroupOf
    rw [Subgroup.comap_map_eq_self_of_injective (Cen z).subtype_injective]
  have hbot : (pPrimeCore 2 ↥(Cen z)).map (toBar z) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, ker_toBar]
  rw [hW, ← h1, Subgroup.map_sup, hbot, bot_sup_eq]

end Group

section Lift

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Nfrak_comm_oddCore (h4c : Thm4c z (Cen z)) {x : ↥(Cen z)} (hx : x ∈ Nfrak z) :
    ∀ a ∈ OddCore z, (x : G) * a = a * x := by
  let Cc : Subgroup ↥(Cen z) := (centralizer (OddCore z : Set G)).comap (Cen z).subtype
  have hlay : layer ↥(Cen z) ≤ Cc := by
    intro y hy
    have hmem : ((y : ↥(Cen z)) : G) ∈ Em (Cen z) := by
      rw [Em_eq]
      exact ⟨y, hy, rfl⟩
    have := Em_le_centralizer_odd (Cen z) hmem
    exact this
  have hO2 : O2coreRes ↥(Cen z) ≤ Cc := by
    intro y hy
    obtain ⟨-, hcomm, -⟩ := directX h4c
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hcomm a ha y hy)
  have hle : Nfrak z ≤ Cc := sup_le hlay hO2
  have := hle hx
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at this
  intro a ha
  exact (this a ha).symm

theorem mem_Nfrak_of_toBar_mem {x : ↥(Cen z)} (hx : ∃ a : ℕ, orderOf x = 2 ^ a)
    (h : toBar z x ∈ (Nfrak z).map (toBar z)) : x ∈ Nfrak z :=
  mem_of_twoElt_of_map_mem (toBar z) (Nfrak z) hx (odd_card_ker_toBar z) h

theorem comm_oddCore_of_toBar_mem_Nfrak (h4c : Thm4c z (Cen z)) {x : ↥(Cen z)}
    (hx : ∃ a : ℕ, orderOf x = 2 ^ a) (h : toBar z x ∈ (Nfrak z).map (toBar z)) :
    ∀ a ∈ OddCore z, (x : G) * a = a * x :=
  Nfrak_comm_oddCore h4c (mem_Nfrak_of_toBar_mem hx h)

theorem map_layer_toBar (h4a : Thm4a (Cen z)) :
    (layer ↥(Cen z)).map (toBar z) = layer (CentralizerBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pLayer ↥(Cen z) 2 = layer ↥(Cen z) := by
    apply Subgroup.map_injective (Cen z).subtype_injective
    have h2 : pLayerOf 2 (Cen z) = Em (Cen z) := h4a
    rw [pLayerOf_eq_map, Em_eq] at h2
    exact h2
  rw [← h1]
  exact CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient

theorem comm_oddCore_of_le {U : Subgroup G} (hUC : U ≤ Cen z) (h4c : Thm4c z (Cen z))
    (hU2 : ∀ u ∈ U, ∃ a : ℕ, orderOf u = 2 ^ a)
    (hU : ∀ u (hu : u ∈ U), toBar z ⟨u, hUC hu⟩ ∈ (Nfrak z).map (toBar z)) :
    ∀ a ∈ OddCore z, ∀ u ∈ U, a * u = u * a := by
  intro a ha u hu
  have h2 : ∃ k : ℕ, orderOf (⟨u, hUC hu⟩ : ↥(Cen z)) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hU2 u hu
    exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  exact (comm_oddCore_of_toBar_mem_Nfrak h4c h2 (hU u hu) a ha).symm

end Lift

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key
