module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Orb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Img
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1SN

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {E K : Subgroup G} {x : G}

theorem l34g_p_pGroup (hKN : K ≤ normalizer (E : Set G))
    (h3 : ∀ g ∈ K, ∃ n : ℕ, ∀ e ∈ E, g ^ 3 ^ n * e = e * g ^ 3 ^ n) :
    IsPGroup 3 ↥(l34gImg E K) := by
  rintro ⟨p, hp⟩
  obtain ⟨g, hgN, hgK, rfl⟩ := mem_l34gImg.1 hp
  obtain ⟨n, hn⟩ := h3 g hgK
  refine ⟨n, Subtype.ext ?_⟩
  have hpow : g ^ 3 ^ n ∈ normalizer (E : Set G) := Subgroup.pow_mem _ hgN _
  have h1 : E.normalizerMonoidHom ⟨g, hgN⟩ ^ 3 ^ n = E.normalizerMonoidHom ⟨g ^ 3 ^ n, hpow⟩ := by
    rw [← map_pow]
    rfl
  change E.normalizerMonoidHom ⟨g, hgN⟩ ^ 3 ^ n = 1
  rw [h1]
  exact (l34gAct_eq_one_iff hpow).2 fun e he => hn e he

theorem l34g_p_commute (hKN : K ≤ normalizer (E : Set G)) (hxN : x ∈ normalizer (E : Set G))
    (hxK : ∀ k ∈ K, x * k = k * x) :
    ∀ p ∈ l34gImg E K, p * E.normalizerMonoidHom ⟨x, hxN⟩ =
      E.normalizerMonoidHom ⟨x, hxN⟩ * p := by
  intro p hp
  obtain ⟨k, hkN, hkK, rfl⟩ := mem_l34gImg.1 hp
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (hxK k hkK).symm)

theorem l34g_p_normalizes (hKN : K ≤ normalizer (E : Set G)) (hxK : ∀ k ∈ K, x * k = k * x) :
    ∀ p ∈ l34gImg E K, ∀ c ∈ l34gImg E (E ⊓ centralizer ({x} : Set G)),
      p * c * p⁻¹ ∈ l34gImg E (E ⊓ centralizer ({x} : Set G)) := by
  intro p hp c hc
  obtain ⟨k, hkN, hkK, rfl⟩ := mem_l34gImg.1 hp
  obtain ⟨c0, hc0N, ⟨hc0E, hc0x⟩, rfl⟩ := mem_l34gImg.1 hc
  have hkcE : k * c0 * k⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hkN c0).1 hc0E
  have hxk : x * k = k * x := hxK k hkK
  have hxk' : x * k⁻¹ = k⁻¹ * x := hxK k⁻¹ (K.inv_mem hkK)
  have hc0x' : c0 * x = x * c0 := Subgroup.mem_centralizer_singleton_iff.1 hc0x
  have hcomm : (k * c0 * k⁻¹) * x = x * (k * c0 * k⁻¹) :=
    calc (k * c0 * k⁻¹) * x = k * c0 * (k⁻¹ * x) := mul_assoc _ _ _
      _ = k * c0 * (x * k⁻¹) := by rw [hxk']
      _ = k * (c0 * x) * k⁻¹ := by group
      _ = k * (x * c0) * k⁻¹ := by rw [hc0x']
      _ = (k * x) * c0 * k⁻¹ := by group
      _ = (x * k) * c0 * k⁻¹ := by rw [hxk]
      _ = x * (k * c0 * k⁻¹) := by group
  refine mem_l34gImg.2 ⟨k * c0 * k⁻¹, Subgroup.le_normalizer hkcE,
    ⟨hkcE, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩, ?_⟩
  have hsub : (⟨k * c0 * k⁻¹, Subgroup.le_normalizer hkcE⟩ : normalizer (E : Set G)) =
      ⟨k, hkN⟩ * ⟨c0, hc0N⟩ * ⟨k, hkN⟩⁻¹ := rfl
  rw [hsub, map_mul, map_mul, map_inv]

theorem l34g_p_subnormal (hKN : K ≤ normalizer (E : Set G))
    (hCN : E ⊓ centralizer ({x} : Set G) ≤ normalizer (E : Set G))
    (h : (K.subgroupOf (K ⊔ (E ⊓ centralizer ({x} : Set G)))).IsSubnormal) :
    ((l34gImg E K).subgroupOf
      (l34gImg E K ⊔ l34gImg E (E ⊓ centralizer ({x} : Set G)))).IsSubnormal := by
  have hLN : K ⊔ (E ⊓ centralizer ({x} : Set G)) ≤ normalizer (E : Set G) := sup_le hKN hCN
  let φ : ↥((K ⊔ (E ⊓ centralizer ({x} : Set G))).subgroupOf (normalizer (E : Set G))) ≃*
      ↥(K ⊔ (E ⊓ centralizer ({x} : Set G))) := Subgroup.subgroupOfEquivOfLe hLN
  have hcomap : (K.subgroupOf (K ⊔ (E ⊓ centralizer ({x} : Set G)))).comap φ.toMonoidHom =
      (K.subgroupOf (normalizer (E : Set G))).subgroupOf
        ((K ⊔ (E ⊓ centralizer ({x} : Set G))).subgroupOf (normalizer (E : Set G))) := by
    ext l
    simp [φ, Subgroup.mem_subgroupOf, Subgroup.subgroupOfEquivOfLe]
  have hsn : ((K.subgroupOf (normalizer (E : Set G))).subgroupOf
      ((K ⊔ (E ⊓ centralizer ({x} : Set G))).subgroupOf (normalizer (E : Set G)))).IsSubnormal := by
    rw [← hcomap]
    exact h.comap _
  have hKL : K.subgroupOf (normalizer (E : Set G)) ≤
      (K ⊔ (E ⊓ centralizer ({x} : Set G))).subgroupOf (normalizer (E : Set G)) := fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 ha))
  have hmap := l34g_subnormal_map E.normalizerMonoidHom hKL hsn
  rw [← l34gImg_sup hKN hCN]
  exact hmap

variable {u : G} {𝒪 : Set (Subgroup G)}

theorem L34GOrb.p_perm (hO : L34GOrb u x K 𝒪) :
    ∀ p ∈ l34gImg (sSup 𝒪) K, ∀ S ∈ l34gImg (sSup 𝒪) '' 𝒪,
      CFSG.conjugate S p ∈ l34gImg (sSup 𝒪) '' 𝒪 := by
  intro p hp S hS
  obtain ⟨k, hkN, hkK, rfl⟩ := mem_l34gImg.1 hp
  obtain ⟨J, hJ, rfl⟩ := hS
  exact ⟨CFSG.conjugate J k, hO.conj J hJ k (Subgroup.mem_sup_left hkK),
    (l34gImg_conjugate hkN).symm⟩

end CFSG.OddStandard.SmallF3.Omega
