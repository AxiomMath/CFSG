module

public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift

public section

namespace CFSG.ComponentClassification.LBalance

open Subgroup CFSG.ComponentClassification.CatalogueBPrimeJoin

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

namespace Quot

omit [Finite H] in
theorem range_le_of_range_le_sup {K : Type*} [Group K] [Finite K] (hK : primeResidual p K = ⊤)
    {N M : Subgroup H} [N.Normal] (hM : p.Coprime (Nat.card M)) (f : K →* H)
    (hf : f.range ≤ N ⊔ M) : f.range ≤ N := by
  let ρ := QuotientGroup.mk' N
  have hrange : (ρ.comp f).range ≤ M.map ρ := by
    rw [MonoidHom.range_comp]
    calc f.range.map ρ ≤ (N ⊔ M).map ρ := map_mono hf
      _ = M.map ρ := by rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hindex : p.Coprime (ρ.comp f).ker.index := by
    rw [index_ker]
    exact hM.of_dvd_right ((card_dvd_of_le hrange).trans (card_map_dvd M ρ))
  have hker := primeResidual_le_normal_of_coprime_index p (ρ.comp f).ker hindex
  rw [hK] at hker
  rintro _ ⟨k, rfl⟩
  exact (QuotientGroup.eq_one_iff (f k)).mp (hker (mem_top k))

theorem map_pLayer_eq_layer_quotient :
    (pLayer H p).map (QuotientGroup.mk' (pPrimeCore p H)) = layer (H ⧸ pPrimeCore p H) := by
  refine le_antisymm ?_ layer_quotient_le_map_pLayer
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  obtain ⟨K, hK, -, hLK, -⟩ := hL
  rw [← map_le_iff_le_comap, hLK]
  exact le_sSup hK

theorem comap_layer_quotient_eq :
    (layer (H ⧸ pPrimeCore p H)).comap (QuotientGroup.mk' (pPrimeCore p H)) =
      pLayer H p ⊔ pPrimeCore p H := by
  rw [← map_pLayer_eq_layer_quotient, comap_map_eq, QuotientGroup.ker_mk']

omit [Finite H] [Fact p.Prime] in
theorem exists_mk_pow_eq_one {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    ∃ n : ℕ, QuotientGroup.mk' (pPrimeCore p H) x ^ p ^ n = 1 :=
  hx.imp fun n hn => by rw [← map_pow, hn, map_one]

theorem map_centralizer_eq {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    (centralizer ({x} : Set H)).map (QuotientGroup.mk' (pPrimeCore p H)) =
      centralizer ({QuotientGroup.mk' (pPrimeCore p H) x} : Set (H ⧸ pPrimeCore p H)) := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_prime_pow_iff.mpr hx
  have : Fact (IsPGroup p (zpowers x)) := ⟨IsPGroup.of_card ((Nat.card_zpowers x).trans hk)⟩
  have h : centralizer (((zpowers x).map (QuotientGroup.mk' (pPrimeCore p H)) :
        Subgroup (H ⧸ pPrimeCore p H)) : Set (H ⧸ pPrimeCore p H)) =
      (centralizer ((zpowers x : Subgroup H) : Set H)).map
        (QuotientGroup.mk' (pPrimeCore p H)) :=
    centralizer_map_quotient_eq_map_centralizer p (zpowers x) (pPrimeCore p H) inferInstance
      pPrimeCore_coprime_card
  rw [MonoidHom.map_zpowers, zpowers_eq_closure, zpowers_eq_closure, centralizer_closure,
    centralizer_closure] at h
  exact h.symm

theorem isPComponent_map_of_map_eq {C : Subgroup H} {D : Subgroup (H ⧸ pPrimeCore p H)}
    (hCD : C.map (QuotientGroup.mk' (pPrimeCore p H)) = D) {K : Subgroup C}
    (hK : IsPComponent p K) :
    IsPComponent p
      (((K.map C.subtype).map (QuotientGroup.mk' (pPrimeCore p H))).subgroupOf D) := by
  have hmem : ∀ c : C, ((QuotientGroup.mk' (pPrimeCore p H)).comp C.subtype) c ∈ D :=
    fun c => hCD ▸ mem_map_of_mem _ c.2
  let f : C →* D := ((QuotientGroup.mk' (pPrimeCore p H)).comp C.subtype).codRestrict D hmem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hCD] at hy
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hy
    exact ⟨⟨c, hc⟩, rfl⟩
  have hker : ¬ p ∣ Nat.card f.ker := by
    rw [MonoidHom.ker_codRestrict]
    refine (Fact.out : p.Prime).coprime_iff_not_dvd.mp ?_
    exact coprime_card_restriction_kernel p (QuotientGroup.mk' (pPrimeCore p H))
      (by rw [QuotientGroup.ker_mk']; exact pPrimeCore_coprime_card) C
  have heq : ((K.map C.subtype).map (QuotientGroup.mk' (pPrimeCore p H))).subgroupOf D =
      K.map f := by
    rw [map_map, show (QuotientGroup.mk' (pPrimeCore p H)).comp C.subtype = D.subtype.comp f
      from rfl, ← map_map]
    exact comap_map_eq_self_of_injective D.subtype_injective _
  rw [heq]
  exact (prime_complement_quotient_p_component_bijection f hf hker).1.mapsTo hK

end Quot

theorem pLayer_centralizer_le_pLayer_of_quotient {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1)
    (hcore : ∀ L : Subgroup (H ⧸ pPrimeCore p H),
      L ≤ centralizer ({QuotientGroup.mk' (pPrimeCore p H) x} : Set (H ⧸ pPrimeCore p H)) →
      IsPComponent p (L.subgroupOf
        (centralizer ({QuotientGroup.mk' (pPrimeCore p H) x} : Set (H ⧸ pPrimeCore p H)))) →
      L ≤ layer (H ⧸ pPrimeCore p H)) :
    (pLayer (centralizer ({x} : Set H)) p).map (centralizer ({x} : Set H)).subtype ≤
      pLayer H p := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← map_le_iff_le_comap]
  have hD : (K.map (centralizer ({x} : Set H)).subtype).map
      (QuotientGroup.mk' (pPrimeCore p H)) ≤
        centralizer ({QuotientGroup.mk' (pPrimeCore p H) x} : Set (H ⧸ pPrimeCore p H)) := by
    rw [← Quot.map_centralizer_eq hx]
    exact map_mono (map_subtype_le K)
  have hsup : K.map (centralizer ({x} : Set H)).subtype ≤ pLayer H p ⊔ pPrimeCore p H := by
    rw [← Quot.comap_layer_quotient_eq, ← map_le_iff_le_comap]
    exact hcore _ hD (Quot.isPComponent_map_of_map_eq (Quot.map_centralizer_eq hx) hK)
  have := pLayer_characteristic (G := H) (p := p)
  have h := Quot.range_le_of_range_le_sup (primeResidual_eq_top_of_pComponent p K hK)
    pPrimeCore_coprime_card ((centralizer ({x} : Set H)).subtype.comp K.subtype)
    (by rwa [MonoidHom.range_comp, range_subtype])
  rwa [MonoidHom.range_comp, range_subtype] at h

end CFSG.ComponentClassification.LBalance
