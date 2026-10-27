module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsB
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_inf {x : G} {H K : Subgroup G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hH, hK]

theorem mem_normalizer_sup {x : G} {H K : Subgroup G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup _ _ _, hH, hK]

theorem mem_normalizer_commutator {x : G} {H K : Subgroup G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

theorem mem_normalizer_centralizer {x : G} {K : Subgroup G} (hK : x ∈ normalizer (K : Set G)) :
    x ∈ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro k hk
    have hk' : x⁻¹ * k * x ∈ K := (Subgroup.mem_normalizer_iff''.mp hK k).mp hk
    have hy' := hy (x⁻¹ * k * x) hk'
    calc k * (x * y * x⁻¹) = x * ((x⁻¹ * k * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * k * x)) * x⁻¹ := by rw [hy']
      _ = (x * y * x⁻¹) * k := by group
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro k hk
    have hk' : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hK k).mp hk
    have hy' := hy (x * k * x⁻¹) hk'
    calc k * y = x⁻¹ * ((x * k * x⁻¹) * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * (x * k * x⁻¹)) * x := by rw [hy']
      _ = y * k := by group

theorem mem_normalizer_normalizer {x : G} {K : Subgroup G} (hK : x ∈ normalizer (K : Set G)) :
    x ∈ normalizer ((normalizer (K : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem hK hy)
      ((normalizer (K : Set G)).inv_mem hK)
  · intro hy
    have h := (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).inv_mem hK) hy) hK
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h

private theorem conj_mem_centralizerSection {K M : Subgroup G} {x c : G}
    (hK : x ∈ normalizer (K : Set G)) (hM : x ∈ normalizer (M : Set G))
    (hc : c ∈ centralizerSection K M) : x * c * x⁻¹ ∈ centralizerSection K M := by
  obtain ⟨hcK, hcM, hc⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · exact (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem hK hcK)
      ((normalizer (K : Set G)).inv_mem hK)
  · exact (normalizer (M : Set G)).mul_mem ((normalizer (M : Set G)).mul_mem hM hcM)
      ((normalizer (M : Set G)).inv_mem hM)
  · intro k hk
    have hk' : x⁻¹ * k * x ∈ K := (Subgroup.mem_normalizer_iff''.mp hK k).mp hk
    have hcomm : ⁅x⁻¹ * k * x, c⁆ ∈ M := hc _ hk'
    have hconj : x * ⁅x⁻¹ * k * x, c⁆ * x⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp hM _).mp hcomm
    have heq : ⁅k, x * c * x⁻¹⁆ = x * ⁅x⁻¹ * k * x, c⁆ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rwa [heq]

theorem mem_normalizer_centralizerSection {x : G} {K M : Subgroup G}
    (hK : x ∈ normalizer (K : Set G)) (hM : x ∈ normalizer (M : Set G)) :
    x ∈ normalizer ((centralizerSection K M : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact conj_mem_centralizerSection hK hM hc
  · intro hc
    have hK' : x⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem hK
    have hM' : x⁻¹ ∈ normalizer (M : Set G) := (normalizer (M : Set G)).inv_mem hM
    have h := conj_mem_centralizerSection hK' hM' hc
    rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at h

theorem mem_normalizer_pCoreOf {p : ℕ} {x : G} {K : Subgroup G}
    (hK : x ∈ normalizer (K : Set G)) :
    x ∈ normalizer ((pCoreOf p K : Subgroup G) : Set G) := by
  let e : ↥K ≃* ↥K :=
    { toFun := fun k =>
        ⟨x * (k : G) * x⁻¹, (Subgroup.mem_normalizer_iff.mp hK (k : G)).mp k.2⟩
      invFun := fun k =>
        ⟨x⁻¹ * (k : G) * x, (Subgroup.mem_normalizer_iff''.mp hK (k : G)).mp k.2⟩
      left_inv := fun k => by ext; group
      right_inv := fun k => by ext; group
      map_mul' := fun a b => by
        ext
        simp only [Subgroup.coe_mul]
        group }
  have hfac : (MulAut.conj x : G →* G).comp K.subtype = K.subtype.comp e.toMonoidHom := by
    ext k
    rfl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  unfold pCoreOf
  rw [Subgroup.map_map, hfac, ← Subgroup.map_map, CFSG.pCore_map_iso p e]

theorem mem_normalizer_zpowers {x t : G} (h : x * t * x⁻¹ = t) :
    x ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hxt : (MulAut.conj x : G →* G) t = t := by
    change (MulAut.conj x) t = t
    rw [MulAut.conj_apply]
    exact h
  rw [MonoidHom.map_zpowers, hxt]

theorem le_normalizer_of_relIndex_two {W M : Subgroup G} (hMW : M ≤ W) (h2 : M.relIndex W = 2) :
    W ≤ normalizer (M : Set G) := by
  have h2' : (M.subgroupOf W).index = 2 := h2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMW).mp
    (Subgroup.normal_of_index_eq_two h2')

theorem mem_or_mem_of_relIndex_two {W M : Subgroup G} (hMW : M ≤ W) (h2 : M.relIndex W = 2)
    {x k : G} (hx : x ∈ W) (hxM : x ∉ M) (hk : k ∈ W) : k ∈ M ∨ x⁻¹ * k ∈ M := by
  obtain ⟨a, haW, haM, h⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mp h2)
  have hxa : a⁻¹ * x ∈ M := by
    rcases h (a⁻¹ * x) (W.mul_mem (W.inv_mem haW) hx) with h1 | h1
    · exact absurd (by simpa only [mul_inv_cancel_left] using h1) hxM
    · exact h1
  rcases h (a⁻¹ * k) (W.mul_mem (W.inv_mem haW) hk) with hkM | hkM
  · exact Or.inl (by simpa only [mul_inv_cancel_left] using hkM)
  · refine Or.inr ((M.mul_mem_cancel_left hxa).mp ?_)
    convert hkM using 1
    group

theorem isPGroup_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] [Finite G] {H K : Subgroup G}
    (hH : IsPGroup p H) (hK : IsPGroup p K) (h : H ≤ normalizer (K : Set G)) :
    IsPGroup p ↥(H ⊔ K) := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hH
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  refine IsPGroup.iff_card.mpr ?_
  have hcard := card_sup_mul_card_inf_of_le_normalizer h
  rw [hm, hn, ← pow_add] at hcard
  obtain ⟨k, -, hk⟩ :=
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp ⟨_, hcard.symm⟩
  exact ⟨k, hk⟩

theorem eq_one_of_isPGroup_of_pow_prime {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    {X : Subgroup G} (hX : IsPGroup p X) {x : G} (hx : x ∈ X) (hxq : x ^ q = 1) : x = 1 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  obtain ⟨k, hk⟩ := hX.exists_orderOf_eq_pow (⟨x, hx⟩ : ↥X)
  have hk' : orderOf x = p ^ k :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥X)).trans hk
  have hcop : Nat.Coprime (p ^ k) q := by
    simpa using Nat.coprime_pow_primes k 1 hp hq hpq.symm
  have hone : orderOf x = 1 := by
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · rw [hk']
    · exact orderOf_dvd_iff_pow_eq_one.mpr hxq
  exact orderOf_eq_one_iff.mp hone

end CFSG.OddStandard.HigherRank.YamadaG23
