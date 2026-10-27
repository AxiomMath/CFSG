module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreEmbedding
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem sz32_W1 {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {V Z : Subgroup G}
    (hVP : V ≤ (P : Subgroup G)) (hVel : IsElemAbelian 5 V) (hVcard : Nat.card V = 5 ^ 3)
    (hVall : ∀ v ∈ (P : Subgroup G), v ^ 5 = 1 → v ∈ V) (hZV : Z ≤ V)
    (hZcent : ∀ z ∈ (P : Subgroup G), (∀ q ∈ (P : Subgroup G), q * z = z * q) ↔ z ∈ Z)
    (hZwc : ∀ h : G, Z.map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) →
      Z.map (MulAut.conj h).toMonoidHom = Z)
    {b : G} (hbV : b ∈ V) (hbZ : b ∉ Z) (g : G) : g * b * g⁻¹ ∉ Z := by
  intro hu
  have hPu : g * b * g⁻¹ ∈ (P : Subgroup G) := hVP (hZV hu)
  have hcomm : ∀ q ∈ (P : Subgroup G), q * (g * b * g⁻¹) = (g * b * g⁻¹) * q :=
    (hZcent _ hPu).2 hu
  have hR₀ : ((g⁻¹ • P : Sylow 5 G) : Subgroup G) =
      (P : Subgroup G).map (MulAut.conj g⁻¹).toMonoidHom :=
    CFSG.RankThreeCoreUniqueness.Helpers.sylow_conjugate_eq_map 5 P g⁻¹
  have hR₀C : ((g⁻¹ • P : Sylow 5 G) : Subgroup G) ≤ Subgroup.centralizer {b} := by
    intro r hr
    rw [hR₀] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hcomm q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * q * g * b = g⁻¹ * (q * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * q) * g := by rw [h1]
      _ = b * (g⁻¹ * q * g) := by group
  have hVC : V ≤ Subgroup.centralizer {b} := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hVel.1
    exact congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : V) ⟨b, hbV⟩)
  have hVp : IsPGroup 5 V := P.isPGroup'.to_le hVP
  obtain ⟨c, hc⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup
      5 (by norm_num) (g⁻¹ • P) (Subgroup.centralizer {b}) hR₀C V hVp hVC
  have hccC : (c : G) ∈ Subgroup.centralizer {b} := c.2
  have hm1 : ∀ v ∈ V, (g * (c : G)) * v * (g * (c : G))⁻¹ ∈ (P : Subgroup G) := by
    intro v hv
    have h1 : (MulAut.conj (c : G)).toMonoidHom v ∈ ((g⁻¹ • P : Sylow 5 G) : Subgroup G) :=
      hc ⟨v, hv, rfl⟩
    rw [hR₀] at h1
    obtain ⟨q, hq, hqe⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hqe
    have : (g * (c : G)) * v * (g * (c : G))⁻¹ = q := by
      calc (g * (c : G)) * v * (g * (c : G))⁻¹ = g * ((c : G) * v * (c : G)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * q * g) * g⁻¹ := by rw [← hqe]
        _ = q := by group
    rw [this]
    exact hq
  have hm2 : ∀ q ∈ (P : Subgroup G),
      (g * (c : G))⁻¹ * q * (g * (c : G)) ∈ Subgroup.centralizer {b} := by
    intro q hq
    have h1 : g⁻¹ * q * g ∈ ((g⁻¹ • P : Sylow 5 G) : Subgroup G) := by
      rw [hR₀]
      exact ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h2 := hR₀C h1
    have h3 : (g * (c : G))⁻¹ * q * (g * (c : G)) = (c : G)⁻¹ * (g⁻¹ * q * g) * (c : G) := by
      group
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hccC) h2) hccC
  generalize g * (c : G) = m at hm1 hm2
  have hVsub : V ≤ V.map (MulAut.conj m⁻¹).toMonoidHom := by
    intro v hv
    have hy : m * v * m⁻¹ ∈ (P : Subgroup G) := hm1 v hv
    have hy5 : (m * v * m⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hVel.2 v hv]
      simp
    refine ⟨m * v * m⁻¹, hVall _ hy hy5, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hVeq : V.map (MulAut.conj m⁻¹).toMonoidHom = V := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hVsub
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective]
  have hZle : Z.map (MulAut.conj m⁻¹).toMonoidHom ≤ (P : Subgroup G) :=
    calc Z.map (MulAut.conj m⁻¹).toMonoidHom ≤ V.map (MulAut.conj m⁻¹).toMonoidHom :=
          Subgroup.map_mono hZV
      _ = V := hVeq
      _ ≤ (P : Subgroup G) := hVP
  have hZeq := hZwc m⁻¹ hZle
  have hy : m * b * m⁻¹ ∈ (P : Subgroup G) := hm1 b hbV
  have hyZ : m * b * m⁻¹ ∈ Z := by
    refine (hZcent _ hy).1 ?_
    intro q hq
    have h1 := hm2 q hq
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    calc q * (m * b * m⁻¹) = m * (m⁻¹ * q * m * b) * m⁻¹ := by group
      _ = m * (b * (m⁻¹ * q * m)) * m⁻¹ := by rw [h1]
      _ = (m * b * m⁻¹) * q := by group
  apply hbZ
  rw [← hZeq]
  refine ⟨m * b * m⁻¹, hyZ, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
