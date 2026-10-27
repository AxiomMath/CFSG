module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Core

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.LocalCores CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatalogueBPrimeJoin
  (primeResidual primeResidual_le_normal_of_coprime_index)

theorem isSylowOf_map {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ} [Fact p.Prime]
    (f : G →* H) {P S : Subgroup G} (h : IsSylowOf p P S) :
    IsSylowOf p (P.map f) (S.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective S), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem not_le_of_coprime {K : Type*} [Group K] [Finite K] {r : ℕ} [Fact r.Prime]
    {R N : Subgroup K} (hR : IsPGroup r R) (hR1 : R ≠ ⊥) (hN : r.Coprime (Nat.card N)) :
    ¬ R ≤ N := by
  intro hle
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcard : Nat.card R = 1 :=
    Nat.eq_one_of_dvd_coprimes (hN.pow_left k) (by rw [hk]) (Subgroup.card_dvd_of_le hle)
  exact hR1 (Subgroup.card_eq_one.mp hcard)

theorem ig414_intrinsic {K : Type} [Group K] [Finite K] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hperf : Group.IsPerfect K) (hgen : primeResidual p K = ⊤)
    (hqs : IsQuasisimple (K ⧸ pPrimeCore p K)) (hS : HasPropS ↥(pPrimeCore p K))
    {R : Subgroup K} (hR : IsSylowOf r R ⁅pPrimeCore p K, ⊤⁆) (hR1 : R ≠ ⊥) :
    Subgroup.centralizer (R : Set K) ≤ pPrimePCore p K := by
  have hOn : (pPrimeCore p K).Normal := pPrimeCore_normal (p := p) (G := K)
  have hNn : (pPrimeCore r K).Normal := pPrimeCore_normal (p := r) (G := K)
  set N : Subgroup K := pPrimeCore r K with hN
  set π : K →* K ⧸ N := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hRN : ¬ R ≤ N := not_le_of_coprime hR.isPGroup hR1 pPrimeCore_coprime_card
  have hNtop : N ≠ ⊤ := fun h => hRN (h ▸ le_top)
  have hNQ : N ≤ pPrimePCore p K := normal_le_pPrimePCore hgen hqs hNtop
  have hgen' : ∀ M : Subgroup K, M.Normal → p.Coprime M.index → M = ⊤ :=
    fun M _ hM => eq_top_of_coprime_index hgen M hM
  have hperfq : Group.IsPerfect (K ⧸ N) := inferInstance
  have hgenq : ∀ M : Subgroup (K ⧸ N), M.Normal → p.Coprime M.index → M = ⊤ := by
    intro M hM hidx
    have hc : (M.comap π).index = M.index := Subgroup.index_comap_of_surjective M hπs
    have htop := hgen' (M.comap π) (hM.comap π) (hc ▸ hidx)
    rw [← Subgroup.map_comap_eq_self_of_surjective hπs M, htop]
    exact Subgroup.map_top_of_surjective π hπs
  have hOq : (pPrimeCore p K).map π |>.Normal := Subgroup.Normal.map hOn π hπs
  have hOpq : p.Coprime (Nat.card ((pPrimeCore p K).map π)) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_surjective ((π.subgroupMap_surjective (pPrimeCore p K))))
      pPrimeCore_coprime_card
  have hSq : HasPropS ↥((pPrimeCore p K).map π) := HasPropS.map π _ hS
  have hrq : pPrimeCore r (K ⧸ N) = ⊥ := pPrimeCore_quotient_eq_bot (Fact.out : r.Prime)
  have hWq : ⁅(pPrimeCore p K).map π, (⊤ : Subgroup (K ⧸ N))⁆ =
      (⁅pPrimeCore p K, (⊤ : Subgroup K)⁆ : Subgroup K).map π := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπs]
  have hRq : IsSylowOf r (R.map π) ⁅(pPrimeCore p K).map π, (⊤ : Subgroup (K ⧸ N))⁆ := by
    rw [hWq]
    exact isSylowOf_map π hR
  have hRq1 : R.map π ≠ ⊥ := by
    intro h
    exact hRN (by simpa [Subgroup.map_eq_bot_iff, hπ] using h)
  have hQq : ∀ M : Subgroup (K ⧸ N), M.Normal → M ≠ ⊤ → M ≤ (pPrimePCore p K).map π := by
    intro M hM hMtop
    have hMc : (M.comap π).Normal := hM.comap π
    have hne : M.comap π ≠ ⊤ := by
      intro h
      apply hMtop
      rw [← Subgroup.map_comap_eq_self_of_surjective hπs M, h]
      exact Subgroup.map_top_of_surjective π hπs
    have := normal_le_pPrimePCore hgen hqs hne
    rw [← Subgroup.map_comap_eq_self_of_surjective hπs M]
    exact Subgroup.map_mono this
  have hcore := ig414_core hperfq hgenq ((pPrimeCore p K).map π) hOpq hSq hrq hRq hRq1 _ hQq
  intro c hc
  have hπc : π c ∈ Subgroup.centralizer ((R.map π : Subgroup (K ⧸ N)) : Set (K ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc x hx
    change π x * π c = π c * π x
    rw [← map_mul, ← map_mul, this]
  obtain ⟨q, hq, hqc⟩ := hcore hπc
  have hmem : q⁻¹ * c ∈ N := by
    rw [← QuotientGroup.eq]
    exact hqc
  have : c = q * (q⁻¹ * c) := by group
  rw [this]
  exact mul_mem hq (hNQ hmem)

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
