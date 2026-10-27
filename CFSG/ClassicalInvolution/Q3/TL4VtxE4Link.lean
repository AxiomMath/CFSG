module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4RedB
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrLeaves
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

@[expose] def E4QuatNbrInv (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
    ∀ J ∈ omegaNbr (CoreAssembly.conjClass K) K, IsUniqueInvolution J s

@[expose] def E4QuatActs3 (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
    ∃ x : M, x ^ 3 = 1 ∧ conjSub x K = K ∧ ∃ k ∈ K, x * k ≠ k * x

namespace Vtx

variable {M G : Type} [Group M] [Group G]

theorem isUniqueInvolution_of_map (φ : M →* G) (hφ : Function.Injective φ) {J : Subgroup M}
    {s : M} (h : IsUniqueInvolution (J.map φ) (φ s)) : IsUniqueInvolution J s where
  mem := by
    obtain ⟨j, hj, hjs⟩ := h.mem
    rwa [← hφ hjs]
  ne_one := fun h1 => h.ne_one (by rw [h1, map_one])
  sq := hφ (by rw [map_mul, h.sq, map_one])
  unique := by
    intro y hy hyy
    rcases h.unique (φ y) (Subgroup.mem_map_of_mem φ hy) (by rw [← map_mul, hyy, map_one])
      with h1 | h1
    · exact Or.inl (hφ (by rw [h1, map_one]))
    · exact Or.inr (hφ h1)

theorem e4QuatNbrInv_of_model [Finite M] (H Kc : Subgroup G)
    (hid : ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hN : ∀ sc, IsUniqueInvolution Kc sc → ∀ h ∈ H, conjSub h Kc ≠ Kc →
      conjSub h Kc ≤ Subgroup.normalizer (Kc : Set G) → IsUniqueInvolution (conjSub h Kc) sc) :
    E4QuatNbrInv M := by
  intro K s hd J hJ
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hd
  obtain ⟨eK⟩ := hd.q8
  have h8 : Nat.card ↥K = 8 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  obtain ⟨⟨m, rfl⟩, hne, hle⟩ := (mem_omegaNbr_conjClass_iff h2).mp hJ
  have hmap : (conjSub m K).map φ = conjSub (φ m) Kc := by rw [← conjSub_map, hKc]
  have hs := isUniqueInvolution_map φ hφ hd.inv
  rw [hKc] at hs
  have hJ' := hN (φ s) hs (φ m) (hrange ▸ ⟨m, rfl⟩)
    (by
      rw [← hmap, ← hKc]
      exact fun h => hne (Subgroup.map_injective hφ h))
    (by
      rw [← hmap, ← hKc]
      exact (map_le_normalizer_map_iff φ hφ).mpr hle)
  rw [← hmap] at hJ'
  exact isUniqueInvolution_of_map φ hφ hJ'

theorem e4QuatActs3_of_model (H Kc : Subgroup G)
    (hid : ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (h3 : ∃ x ∈ H, x ^ 3 = 1 ∧ conjSub x Kc = Kc ∧ ∃ k ∈ Kc, x * k ≠ k * x) :
    E4QuatActs3 M := by
  intro K s hd
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hd
  obtain ⟨x, hx, hx3, hxK, k, hk, hxk⟩ := h3
  rw [← hrange] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← hKc] at hk hxK
  obtain ⟨k', hk', rfl⟩ := hk
  refine ⟨y, hφ (by rw [map_pow, hx3, map_one]), ?_, k', hk', fun h => hxk ?_⟩
  · apply Subgroup.map_injective hφ
    rw [← conjSub_map, hxK]
  · rw [← map_mul, h, map_mul]

end Vtx

theorem secIdE4LinkCent_of_nbrInv
    (h : ∀ (M : Type) [Group M] [Finite M], PhilipHall.QuaternionBridge.ExLie M →
      E4QuatNbrInv M) : SecIdE4LinkCent := by
  intro Y _ _ R S t hd hc hO2 hZ hM B hB v hv
  have c := Vtx.centQuotGen_e4 hd hc hO2
  have hBmap := c.omegaNbr_map (CoreAssembly.mem_conjClass_self _) hB
  rw [Vtx.quotFamily_e4] at hBmap
  have ht := h _ hM _ _ (Vtx.quatTwinDatum_quot hd hc hO2 hZ hM) _ hBmap
  have hne : QuotientGroup.mk' (Subgroup.center Y) v ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : v ∈ B ⊓ Subgroup.center Y := ⟨hv.mem, h1⟩
    rw [c.meet B hB.1, Subgroup.mem_bot] at h2
    exact hv.ne_one h2
  have he := (ht.unique _ (Subgroup.mem_map_of_mem _ hv.mem)
    (by rw [← map_mul, hv.sq, map_one])).resolve_left hne
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' (Subgroup.center Y) (t * v) = 1
  rw [map_mul, he, ht.sq]

end CFSG.ClassicalInvolution.Q3.TL4
