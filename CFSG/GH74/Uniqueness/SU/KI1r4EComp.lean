module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.GLS.C3.Layer3.A8Cover
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.LocalCores

variable {H : Type} [Group H]

theorem layer_normal (H : Type) [Group H] : (layer H).Normal := by
  have : (layer H).Characteristic := layer_characteristic
  infer_instance

theorem component_le_layer {K : Subgroup H} (hK : IsComponent K) : K ≤ layer H :=
  le_sSup (show K ∈ {K : Subgroup H | IsComponent K} from hK)

theorem layer_perfect : ⁅layer H, layer H⁆ = layer H := by
  have : (layer H).Normal := layer_normal H
  refine le_antisymm (Subgroup.commutator_le_left _ _) (sSup_le fun K hK => ?_)
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  calc K = ⁅K, K⁆ := hKK.symm
    _ ≤ ⁅layer H, layer H⁆ :=
      Subgroup.commutator_mono (component_le_layer hK) (component_le_layer hK)

variable [Finite H]

theorem layer_le_normalizer_component {K : Subgroup H} (hK : IsComponent K) :
    layer H ≤ normalizer (K : Set H) := by
  refine sSup_le fun L hL => ?_
  rcases distinct_components_commute hK hL with h | h
  · rw [← h]
    exact Subgroup.le_normalizer
  · have hL' : L ≤ centralizer (K : Set H) := by
      rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    exact hL'.trans (Subgroup.centralizer_le_normalizer (K : Set H))

theorem center_of_component_central {K : Subgroup H} (hK : IsComponent K) {z : H} (hzK : z ∈ K)
    (hzc : ∀ k ∈ K, z * k = k * z) : ∀ g ∈ layer H, z * g = g * z := by
  have hle : layer H ≤ centralizer ({z} : Set H) := by
    refine sSup_le fun L hL => ?_
    rcases distinct_components_commute hK hL with hLK | hLK
    · rw [← hLK]
      intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hzc l hl).symm
    · intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLK hzK
      exact Subgroup.mem_centralizer_iff.mp this k hk
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm

theorem card_two_subgroup_le_inf (T : Sylow 2 H) (X : Subgroup H) (hX : IsPGroup 2 X)
    (hXL : X ≤ layer H) : Nat.card X ≤ Nat.card ↥((T : Subgroup H) ⊓ layer H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (layer H).Normal := layer_normal H
  obtain ⟨S₀, hS₀⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := layer H)
  have hX' : IsPGroup 2 (X.subgroupOf (layer H)) :=
    hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXL).symm
  obtain ⟨S', hS'⟩ := hX'.exists_le_sylow
  have h1 : Nat.card (X.subgroupOf (layer H)) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
  have h2 : Nat.card S' = Nat.card S₀ := by
    rw [Sylow.card_eq_multiplicity S', Sylow.card_eq_multiplicity S₀]
  have h3 : Nat.card S₀ = Nat.card ↥((T : Subgroup H) ⊓ layer H) := by
    have : Nat.card (S₀ : Subgroup ↥(layer H)) =
        Nat.card (((T : Subgroup H) ⊓ layer H).subgroupOf (layer H)) := by rw [hS₀]
    rw [show Nat.card S₀ = Nat.card (S₀ : Subgroup ↥(layer H)) from rfl, this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h4 : Nat.card (X.subgroupOf (layer H)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv
  omega

theorem exists_noncomm_inf_of_component (T : Sylow 2 H) {K : Subgroup H} (hK : IsComponent K)
    {z : H} (hzK : z ∈ K) (hzc : ∀ k ∈ K, z * k = k * z) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    ∃ a ∈ (T : Subgroup H) ⊓ layer H ⊓ K, ∃ b ∈ (T : Subgroup H) ⊓ layer H ⊓ K,
      a * b ≠ b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (layer H).Normal := layer_normal H
  have hKN : K ≤ layer H := component_le_layer hK
  obtain ⟨S₀, hS₀⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := layer H)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  set z' : ↥K := ⟨z, hzK⟩ with hz'
  have hz'c : z' ∈ Subgroup.center ↥K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hzc k k.2).symm
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hz2)
  have hz'ord : orderOf z' = 2 := orderOf_eq_prime hz'2 hz'1
  have hzP : z' ∈ (P : Subgroup ↥K) := by
    have hnorm : (Subgroup.zpowers z').Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
    have h2 : IsPGroup 2 (Subgroup.zpowers z') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'ord, pow_one])
    exact (h2.le_sylow_of_normal P) (Subgroup.mem_zpowers z')
  have hperf : commutator ↥K = ⊤ := hK.1.1.commutator_eq_top
  have hz'comm : z' ∈ commutator ↥K := hperf ▸ Subgroup.mem_top z'
  have hmem := CFSG.GH74.GLS.Layer3.mem_commutator_of_central_of_transfer (P : Subgroup ↥K)
    Nat.prime_two P.not_dvd_index hz'c hzP ⟨1, by rw [hz'ord, pow_one]⟩ hz'comm
  have hnab : ∃ a ∈ (P : Subgroup ↥K), ∃ b ∈ (P : Subgroup ↥K), a * b ≠ b * a := by
    by_contra hno
    push Not at hno
    have hbot : commutator ↥(P : Subgroup ↥K) = ⊥ := by
      rw [commutator_eq_bot_iff]
      exact ⟨⟨fun a b => Subtype.ext (hno a a.2 b b.2)⟩⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hz'1 (congrArg Subtype.val hmem)
  obtain ⟨a₀, ha₀P, b₀, hb₀P, hab₀⟩ := hnab
  let ι : ↥K →* ↥(layer H) := Subgroup.inclusion hKN
  have hQ2 : IsPGroup 2 ((P : Subgroup ↥K).map ι) := P.isPGroup'.map ι
  obtain ⟨S', hS'⟩ := hQ2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(layer H) S' S₀
  have hconj : ∀ p ∈ (P : Subgroup ↥K),
      (g : H) * ((p : ↥K) : H) * (g : H)⁻¹ ∈ (T : Subgroup H) ⊓ layer H ⊓ K := by
    intro p hp
    have h1 : ι p ∈ (S' : Subgroup ↥(layer H)) := hS' ⟨p, hp, rfl⟩
    have h2 : (MulAut.conj g) (ι p) ∈ ((g • S' : Sylow 2 ↥(layer H)) : Subgroup ↥(layer H)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (ι p) (MulAut.conj g) _ h1
    rw [hg, hS₀, Subgroup.mem_subgroupOf] at h2
    have h3 : (g : H) * ((p : ↥K) : H) * (g : H)⁻¹ ∈ (T : Subgroup H) ⊓ layer H := h2
    refine ⟨h3, ?_⟩
    have hgN : (g : H) ∈ normalizer (K : Set H) := layer_le_normalizer_component hK g.2
    exact (Subgroup.mem_normalizer_iff.mp hgN p).mp p.2
  refine ⟨(g : H) * ((a₀ : ↥K) : H) * (g : H)⁻¹, hconj a₀ ha₀P,
    (g : H) * ((b₀ : ↥K) : H) * (g : H)⁻¹, hconj b₀ hb₀P, fun heq => hab₀ ?_⟩
  apply Subtype.ext
  have e : (g : H) * (((a₀ * b₀ : ↥K) : H)) * (g : H)⁻¹ =
      (g : H) * (((b₀ * a₀ : ↥K) : H)) * (g : H)⁻¹ := by
    calc (g : H) * (((a₀ * b₀ : ↥K) : H)) * (g : H)⁻¹
        = ((g : H) * ((a₀ : ↥K) : H) * (g : H)⁻¹) * ((g : H) * ((b₀ : ↥K) : H) * (g : H)⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = ((g : H) * ((b₀ : ↥K) : H) * (g : H)⁻¹) * ((g : H) * ((a₀ : ↥K) : H) * (g : H)⁻¹) := heq
      _ = (g : H) * (((b₀ * a₀ : ↥K) : H)) * (g : H)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
  exact mul_left_cancel (mul_right_cancel e)

end CFSG.GH74.Uniqueness.SU.K.R4
