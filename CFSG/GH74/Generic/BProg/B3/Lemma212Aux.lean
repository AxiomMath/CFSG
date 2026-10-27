module

public import CFSG.GH74.GLS.TwoThin.Equivariance
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.GH74.GLS.TwoThin.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3.Lemma212Aux

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification Subgroup

section Layer

variable {G : Type} [Group G] [Finite G]

theorem isPCompIn_of_le {H H' K : Subgroup G} (h : IsPCompIn 2 H K) (hKH' : K ≤ H')
    (hH'H : H' ≤ H) : IsPCompIn 2 H' K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hKH', ?_⟩
  have h2 : K.subgroupOf H ≤ H'.subgroupOf H := fun x hx => hKH' hx
  have h3 := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_restrict_overgroup 2 h.2 h2
  exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hH'H 2
    Nat.prime_two).mp h3

theorem pLayerOf_pLayerOf (H : Subgroup G) : pLayerOf 2 (pLayerOf 2 H) = pLayerOf 2 H := by
  refine le_antisymm (TwoThin.pLayerOf_le 2 _) (sSup_le fun L hL => ?_)
  exact le_sSup (isPCompIn_of_le hL (le_sSup hL) (TwoThin.pLayerOf_le 2 H))

end Layer

section Odd

variable {W W' : Type*} [Group W] [Finite W] [Group W'] [Finite W']

theorem mem_twoLayer_of_map_mem (ρ : W →* W') (hs : Function.Surjective ρ)
    (hodd : Odd (Nat.card ρ.ker)) {f : W} (hf : f * f = 1) (hρ : ρ f ∈ TwoLayer.subgroup W') :
    f ∈ TwoLayer.subgroup W := by
  have : (TwoLayer.subgroup W).Characteristic := TwoLayerTransport.characteristic W
  rw [← TwoLayerTransport.image_of_odd_kernel ρ hs hodd] at hρ
  obtain ⟨i, hi, hif⟩ := hρ
  have ho : i⁻¹ * f ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hif, inv_mul_cancel]
  set q := QuotientGroup.mk' (TwoLayer.subgroup W) with hq
  have hqi : q i = 1 := (QuotientGroup.eq_one_iff i).2 hi
  have h1 : q f = q (i⁻¹ * f) := by
    rw [map_mul, map_inv, hqi, inv_one, one_mul]
  have h2 : orderOf (q f) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, hf, map_one])
  have h3 : orderOf (q (i⁻¹ * f)) ∣ Nat.card ρ.ker := by
    refine (orderOf_map_dvd q (i⁻¹ * f)).trans ?_
    exact Subgroup.orderOf_dvd_natCard ρ.ker ho
  rw [← h1] at h3
  have h4 : Odd (orderOf (q f)) := Odd.of_dvd_nat hodd h3
  have h5 : orderOf (q f) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · rw [h] at h4
      exact absurd h4 (by decide)
  exact (QuotientGroup.eq_one_iff f).1 (orderOf_eq_one_iff.1 h5)

end Odd

section Pump

variable {G : Type} [Group G] [Finite G]

theorem le_pumpUp_of_not_le_cSec {a : G} {K' J : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J)
    (hΛ : pLayerOf 2 (K' ⊓ centralizer ({a} : Set G)) ≤ pLayerOf 2 (centralizer ({a} : Set G)))
    (hnot : ¬ pLayerOf 2 (K' ⊓ centralizer ({a} : Set G)) ≤
      centralizerSection J (pPrimeCoreOf 2 J)) :
    J ≤ pumpUp 2 K' a := by
  classical
  set Y' : Subgroup G := centralizer ({a} : Set G) with hY'
  set Λ₀ : Subgroup G := pLayerOf 2 (K' ⊓ Y') with hΛ₀
  have hΛ₀Y : Λ₀ ≤ Y' := (TwoThin.pLayerOf_le 2 _).trans inf_le_right
  set Λ : Subgroup ↥Y' := Λ₀.subgroupOf Y' with hΛdef
  have hΛE : Λ ≤ TwoLayer.subgroup ↥Y' := by
    intro y hy
    have h1 : (y : G) ∈ pLayerOf 2 Y' := hΛ (Subgroup.mem_subgroupOf.mp hy)
    rw [TwoThin.pLayerOf_two_eq_map] at h1
    obtain ⟨y', hy', hyy⟩ := h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'
  have hJ2 : TwoComponents.IsTwoComponent (J.subgroupOf Y') := (isPCompIn_two_iff.mp hJ).2
  rw [TwoThin.pumpUp_eq_map_pumpupY K' a]
  have hmain : J.subgroupOf Y' ≤ pumpupY Λ := by
    set N := pumpupY Λ with hN
    have hNsub : N.IsSubnormal := isSubnormal_pumpupY hΛE
    have hLc : CFSG.IsComponent ((J.subgroupOf Y').map (barMk ↥Y')) := isComponent_map_barMk hJ2
    have hNb : (N.map (barMk ↥Y')).IsSubnormal := hNsub.map barMk_surjective
    rcases CFSG.LocalCores.component_subnormal_subgroup hLc hNb with h | h
    · have hchain : Open.IsSubnormal N ⊤ := Components.chain_of_mathlib_subnormal hNsub
      exact TwoComponentSubnormal.le_of_odd_kernel_map_le (barMk ↥Y') barMk_surjective
        odd_card_ker_barMk (J.subgroupOf Y') N hJ2 hchain h
    · exfalso
      apply hnot
      intro q hq
      have hqY : q ∈ Y' := hΛ₀Y hq
      refine TwoThin.mem_centralizerSection_of_map_eq hJ.1 hJ2 hqY fun m hm => ?_
      have hcomm := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hqN : barMk ↥Y' ⟨q, hqY⟩ ∈ N.map (barMk ↥Y') :=
        ⟨⟨q, hqY⟩, subset_pumpupY Λ (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
      have hmL : barMk ↥Y' m ∈ (J.subgroupOf Y').map (barMk ↥Y') := ⟨m, hm, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.mp (hcomm hmL) _ hqN
      rw [map_mul, map_mul, map_inv]
      exact mul_inv_eq_iff_eq_mul.2 hc
  intro j hj
  exact ⟨⟨j, hJ.1 hj⟩, hmain (Subgroup.mem_subgroupOf.mpr hj), rfl⟩

end Pump

end CFSG.GH74.Generic.BProg.B3.Lemma212Aux
