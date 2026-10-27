module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem le_of_normal_isPGroup_of_isSylowOf {p : ℕ} [Fact p.Prime] {K P N : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) (hN : IsPGroup p N) : N ≤ P := by
  obtain ⟨Q, rfl⟩ := hP
  haveI : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hp' : IsPGroup p (N.subgroupOf K) := hN.of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
  have hle : N.subgroupOf K ≤ (Q : Subgroup K) := IsPGroup.le_sylow_of_normal hp' Q
  intro x hx
  have hxK : x ∈ K := hNK hx
  have hmem : (⟨x, hxK⟩ : K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hle hmem, rfl⟩

theorem pCoreOf_two_le_relPPrimeCore {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (M : Subgroup G) :
    pCoreOf 2 M ≤ relPPrimeCore p M := by
  have hp : p.Prime := Fact.out
  have hle : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hnorm : ((pCoreOf 2 M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hcard : Nat.Coprime p (Nat.card (pCoreOf 2 M)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hmem : pCoreOf 2 M ∈
      {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧ Nat.Coprime p (Nat.card N)} :=
    ⟨hle, hnorm, hcard⟩
  unfold relPPrimeCore
  exact le_sSup hmem

theorem pow_eq_one_of_mem_sup_zpowers {p : ℕ} {T : Subgroup G} {x : G}
    (hT : ∀ t ∈ T, t ^ p = 1) (hx : x ^ p = 1) (hxT : ∀ t ∈ T, x * t = t * x) :
    ∀ v ∈ T ⊔ zpowers x, v ^ p = 1 := by
  let D : Subgroup G :=
    { carrier := {v | ∃ t ∈ T, ∃ k : ℤ, v = t * x ^ k}
      mul_mem' := by
        rintro _ _ ⟨t, ht, k, rfl⟩ ⟨t', ht', l, rfl⟩
        have hc : Commute (x ^ k) t' := Commute.zpow_left (hxT t' ht' : Commute x t') k
        refine ⟨t * t', T.mul_mem ht ht', k + l, ?_⟩
        calc t * x ^ k * (t' * x ^ l) = t * (x ^ k * t') * x ^ l := by simp only [mul_assoc]
          _ = t * (t' * x ^ k) * x ^ l := by rw [hc.eq]
          _ = t * t' * (x ^ k * x ^ l) := by simp only [mul_assoc]
          _ = t * t' * x ^ (k + l) := by rw [zpow_add]
      one_mem' := ⟨1, T.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨t, ht, k, rfl⟩
        have hxt : Commute x t := hxT t ht
        have hc : Commute x t⁻¹ := hxt.inv_right
        refine ⟨t⁻¹, T.inv_mem ht, -k, ?_⟩
        calc (t * x ^ k)⁻¹ = (x ^ k)⁻¹ * t⁻¹ := mul_inv_rev _ _
          _ = x ^ (-k) * t⁻¹ := by rw [zpow_neg]
          _ = t⁻¹ * x ^ (-k) := (Commute.zpow_left hc (-k)).eq }
  have hTD : T ≤ D := by
    intro t ht
    exact ⟨t, ht, 0, by simp⟩
  have hxD : zpowers x ≤ D := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨1, T.one_mem, k, by simp⟩
  have hsup : T ⊔ zpowers x ≤ D := sup_le hTD hxD
  intro v hv
  obtain ⟨t, ht, k, rfl⟩ : ∃ t ∈ T, ∃ k : ℤ, v = t * x ^ k := hsup hv
  have hc : Commute t (x ^ k) := (Commute.zpow_left (hxT t ht : Commute x t) k).symm
  have hxk : (x ^ k) ^ p = 1 := by
    rw [← zpow_natCast (x ^ k) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rw [hc.mul_pow p, hT t ht, one_mul, hxk]

theorem mem_normalizer_map_conj_of_commute {Y : Subgroup G} {c u : G} (hcu : c * u = u * c)
    (hu : u ∈ normalizer (Y : Set G)) :
    u ∈ normalizer ((Y.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  have h1 : c⁻¹ * u = u * c⁻¹ := by
    calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * u) * c⁻¹ := by rw [hcu]
      _ = u * c⁻¹ := by group
  have h2 : u⁻¹ * c = c * u⁻¹ := by
    calc u⁻¹ * c = u⁻¹ * (c * u) * u⁻¹ := by group
      _ = u⁻¹ * (u * c) * u⁻¹ := by rw [hcu]
      _ = c * u⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff] at hu ⊢
  intro h
  have key : c⁻¹ * (u * h * u⁻¹) * c = u * (c⁻¹ * h * c) * u⁻¹ := by
    calc c⁻¹ * (u * h * u⁻¹) * c = (c⁻¹ * u) * h * (u⁻¹ * c) := by group
      _ = (u * c⁻¹) * h * (c * u⁻¹) := by rw [h1, h2]
      _ = u * (c⁻¹ * h * c) * u⁻¹ := by group
  simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [key]
  exact hu _

theorem normalizer_le_of_normalizer_map_conj_le {M Y : Subgroup G} {c : G} (hcM : c ∈ M)
    (h : normalizer ((Y.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) ≤ M) :
    normalizer (Y : Set G) ≤ M := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  have hgc : c * g * c⁻¹ ∈
      normalizer ((Y.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have key : c⁻¹ * (c * g * c⁻¹ * z * (c * g * c⁻¹)⁻¹) * c = g * (c⁻¹ * z * c) * g⁻¹ := by
      group
    simp only [SetLike.mem_coe, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [key]
    exact hg _
  have hm : c * g * c⁻¹ ∈ M := h hgc
  have hfin : c⁻¹ * (c * g * c⁻¹) * c ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hcM) hm) hcM
  have e : c⁻¹ * (c * g * c⁻¹) * c = g := by group
  rw [e] at hfin
  exact hfin

theorem le_normalizer_inf_of_le_normalizer {Y R : Subgroup G} (hY : Y ≤ normalizer (R : Set G)) :
    Y ≤ normalizer ((Y ⊓ R : Subgroup G) : Set G) := by
  intro y hy
  have hyR : y ∈ normalizer (R : Set G) := hY hy
  rw [Subgroup.mem_normalizer_iff] at hyR ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  constructor
  · rintro ⟨hhY, hhR⟩
    exact ⟨Y.mul_mem (Y.mul_mem hy hhY) (Y.inv_mem hy), (hyR h).mp hhR⟩
  · rintro ⟨hyhY, hyhR⟩
    have e : y⁻¹ * (y * h * y⁻¹) * y = h := by group
    refine ⟨?_, (hyR h).mpr hyhR⟩
    have hmem := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hyhY) hy
    rw [e] at hmem
    exact hmem

theorem map_conj_le_of_mem {M V : Subgroup G} {l : G} (hl : l ∈ M) (hV : V ≤ M) :
    V.map (MulAut.conj l).toMonoidHom ≤ M := by
  intro s hs
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hs
  have h1 : l⁻¹ * s * l ∈ M := hV hs
  have h2 : l * (l⁻¹ * s * l) * l⁻¹ ∈ M := M.mul_mem (M.mul_mem hl h1) (M.inv_mem hl)
  have e : l * (l⁻¹ * s * l) * l⁻¹ = s := by group
  rw [e] at h2
  exact h2

theorem mem_map_conj_iff {V : Subgroup G} {l s : G} :
    s ∈ V.map (MulAut.conj l).toMonoidHom ↔ l⁻¹ * s * l ∈ V := by
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
