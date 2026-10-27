
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma66
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathS

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G}

theorem lemma67 (hZ : Fin76bNotZ2A6) (hBD : Fin76bBetaData)
    (hconf : Rest6Config L z t T₀ E Q x β B) (hW : WFacts L t E) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G)) (hzS : z ∈ S)
    (hBS : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b) :
    ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t := by
  intro g hgS
  have hcfg := hconf.cfg
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = centralizer ({β} : Set G) := ⟨_, rfl⟩
  obtain ⟨hz, N₁, N₂, ⟨e₁⟩, ⟨e₂⟩, hc, hd, -, hidx, hzN, hconj⟩ := lemma66' hZ hconf hW hK
  obtain ⟨hD8, hDK⟩ := hBD G L z t T₀ E Q x β B hconf hW
  rw [← hK] at hD8 hDK
  have hSK : S ≤ K := fun s hs => by
    rw [hK]
    exact mem_centralizer_singleton_iff.2 (hBS β hconf.beta_mem s hs).symm
  have hE2 : IsPGroup 2 E := hcfg.T₀_pgroup.to_le hconf.econfig.le
  let zK : ↥K := ⟨z, hz⟩
  let DK : Subgroup ↥K := (E ⊓ K).subgroupOf K
  have hDK2 : IsPGroup 2 DK := (hE2.to_le (inf_le_left : E ⊓ K ≤ E)).comap_subtype
  have hDK8 : Nat.card DK = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ⊓ K ≤ K)).toEquiv).trans hD8
  have hDKz : ∀ d ∈ DK, d * zK = zK * d := fun d hd' =>
    Subtype.ext (hcfg.z_comm_of_mem_A
      (hconf.econfig.le.trans hcfg.T₀_le (mem_subgroupOf.1 hd').1))
  have hDKN : ∀ d ∈ DK, (QuotientGroup.mk d : ↥K ⧸ fusionOddCore ↥K) ∈ N₁ ⊔ N₂ := by
    intro d hd'
    apply commutator_le_of_index_two hidx
    have := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' (fusionOddCore ↥K)) 1
    rw [derivedSeries_one, derivedSeries_one] at this
    exact this ⟨d, hDK hd', rfl⟩
  have claimA : ∀ s : G, ∀ hs : s ∈ S,
      (QuotientGroup.mk (⟨s, hSK hs⟩ : ↥K) : ↥K ⧸ fusionOddCore ↥K) ∈ N₁ ⊔ N₂ → s * s = 1 := by
    intro s hs hsN
    have h2 : ∃ k : ℕ, orderOf (⟨s, hSK hs⟩ : ↥K) = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨s, hs⟩
      rw [Subgroup.orderOf_mk] at hk
      exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
    have := sq_eq_one_of_wreath (z := zK) (Subtype.ext hcfg.z_sq) e₁ e₂ hc hd hconj hDK2 hDK8
      hDKz hDKN h2 hsN (fun d hd' => Subtype.ext
        (mem_centralizer_iff.1 (hSC hs) (d : G) (mem_subgroupOf.1 hd').1).symm)
    exact congrArg Subtype.val this
  obtain ⟨s, hs⟩ : ∃ s, s = g * z * g⁻¹ := ⟨_, rfl⟩
  rw [← hs] at hgS ⊢
  have hsK : s ∈ K := hSK hgS
  have hss : s * s = 1 := by
    rw [hs]
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hcfg.z_sq]; group
  have hnot : (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : ↥K ⧸ fusionOddCore ↥K) ∉ N₁ ⊔ N₂ := by
    have := hcfg.conj_z_not_mem_sup e₁ e₂ hc hd g (hs ▸ hsK)
    simpa [hs] using this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hcfg.z_sq
  have hw : (QuotientGroup.mk (⟨z⁻¹ * s, mul_mem (inv_mem hz) hsK⟩ : ↥K) :
      ↥K ⧸ fusionOddCore ↥K) ∈ N₁ ⊔ N₂ := by
    have e : (⟨z⁻¹ * s, mul_mem (inv_mem hz) hsK⟩ : ↥K) = zK⁻¹ * ⟨s, hsK⟩ := rfl
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, Subgroup.mul_mem_iff_of_index_two hidx,
      inv_mem_iff]
    exact iff_of_false hzN hnot
  have hwS : z⁻¹ * s ∈ S := mul_mem (inv_mem hzS) hgS
  have hww := claimA (z⁻¹ * s) hwS hw
  rw [hzinv] at hww
  have hcomm : s * z = z * s := by
    have h1 : z * s = (z * s)⁻¹ := eq_inv_of_mul_eq_one_left hww
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hss, hzinv]
  rcases mem_klein_of_comm hcfg hconf.econfig hS2 hSC hzS hgS hcomm with h1 | h1 | h1 | h1
  · exfalso
    apply hcfg.z_ne
    have h2 : g * z * g⁻¹ = 1 := hs.symm.trans h1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  · exact Or.inl h1
  · exact absurd (hs.symm.trans h1) (hcfg.conj_z_ne_t g)
  · exact Or.inr h1

end CFSG.EvenSporadicStandard.Fin76b
