module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma conj_mem_oddCoreIn_self {G : Type} [Group G] {N : Subgroup G} {x y : G}
    (hy : y ∈ oddCoreIn N) (hx : x ∈ N) : x * y * x⁻¹ ∈ oddCoreIn N := by
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹,
    (inferInstance : (CFSG.oddCore ↥N).Normal).conj_mem y' hy' ⟨x, hx⟩, rfl⟩

private lemma le_normalizer_oddCoreIn {G : Type} [Group G] (N : Subgroup G) :
    N ≤ normalizer (oddCoreIn N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_oddCoreIn_self hy hx
  · intro hy
    have h := conj_mem_oddCoreIn_self hy (inv_mem hx)
    have heq : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
    rwa [heq] at h

private lemma mem_oddCoreIn_of_centralizes {G : Type} [Group G] {V K : Subgroup G}
    (hC : centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G)))
    (hKO : oddCoreIn (normalizer (V : Set G)) ≤ K) (hKV : K ⊓ V = ⊥)
    {k : G} (hk : k ∈ K) (hkcent : k ∈ centralizer (V : Set G)) :
    k ∈ oddCoreIn (normalizer (V : Set G)) := by
  have hVO : V ≤ normalizer (oddCoreIn (normalizer (V : Set G)) : Set G) :=
    le_trans Subgroup.le_normalizer (le_normalizer_oddCoreIn (normalizer (V : Set G)))
  have hksup : k ∈ V ⊔ oddCoreIn (normalizer (V : Set G)) := by
    rw [← hC]
    exact hkcent
  change k ∈ (↑(V ⊔ oddCoreIn (normalizer (V : Set G))) : Set G) at hksup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V
    (oddCoreIn (normalizer (V : Set G))) hVO] at hksup
  obtain ⟨v, hv, o, ho, hvo⟩ := Set.mem_mul.mp hksup
  have hv_eq : v = k * o⁻¹ := by rw [← hvo, mul_assoc, mul_inv_cancel, mul_one]
  have hvK : v ∈ K := by rw [hv_eq]; exact mul_mem hk (inv_mem (hKO ho))
  have hvbot : v ∈ K ⊓ V := Subgroup.mem_inf.mpr ⟨hvK, hv⟩
  rw [hKV] at hvbot
  have hv1 : v = 1 := Subgroup.mem_bot.mp hvbot
  rw [← hvo, hv1, one_mul]
  exact ho

theorem sec128_K_side {G : Type} [Group G] {V K : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hKN : K ≤ normalizer (V : Set G))
    (hKsup : K ⊔ V = normalizer (V : Set G)) :
    ∃ κ₀ : ↥K →* ↥(autIn (normalizer (V : Set G)) V),
      (∀ (k : ↥K) (v : ↥V),
        ((((κ₀ k : ↥(autIn (normalizer (V : Set G)) V)) : MulAut ↥V) v : ↥V) : G) =
          (k : G) * (v : G) * (k : G)⁻¹) ∧ Function.Surjective κ₀ := by
  classical
  let f : ↥K →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hKN)
  have hmem : ∀ k : ↥K, f k ∈ autIn (normalizer (V : Set G)) V := by
    intro k
    rw [autIn, Subgroup.mem_map]
    exact ⟨Subgroup.inclusion hKN k,
      Subgroup.mem_subgroupOf.mpr (Subgroup.inclusion hKN k).2, rfl⟩
  refine ⟨f.codRestrict (autIn (normalizer (V : Set G)) V) hmem, ?_, ?_⟩
  · intro k v
    change (Subgroup.inclusion hKN k : G) * (v : G) * (Subgroup.inclusion hKN k : G)⁻¹ =
      (k : G) * (v : G) * (k : G)⁻¹
    rw [Subgroup.coe_inclusion]
  · intro y
    have hy : y.1 ∈ ((normalizer (V : Set G)).subgroupOf
        (normalizer (V : Set G))).map V.normalizerMonoidHom := y.2
    obtain ⟨n, -, hn_eq⟩ := Subgroup.mem_map.mp hy
    have hnN : (n : G) ∈ K ⊔ V := by
      rw [hKsup]
      exact n.2
    change (n : G) ∈ (↑(K ⊔ V) : Set G) at hnN
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K V hKN] at hnN
    obtain ⟨k, hk, v0, hv0, hkvo⟩ := Set.mem_mul.mp hnN
    have hv0N : v0 ∈ normalizer (V : Set G) := Subgroup.le_normalizer hv0
    let g : ↥(normalizer (V : Set G)) := Subgroup.inclusion hKN ⟨k, hk⟩
    have hg : (g : G) = k := Subgroup.coe_inclusion hKN ⟨k, hk⟩
    have hker : V.normalizerMonoidHom (⟨v0, hv0N⟩ : ↥(normalizer (V : Set G))) = 1 := by
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker]
      exact Subgroup.mem_subgroupOf.mpr (by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact congrArg Subtype.val (hV.1.is_comm.comm ⟨h, hh⟩ ⟨v0, hv0⟩))
    have hn_decomp : n = g * ⟨v0, hv0N⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hg]
      exact hkvo.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    show V.normalizerMonoidHom g = y.1
    calc V.normalizerMonoidHom g
        = V.normalizerMonoidHom (g * ⟨v0, hv0N⟩) := by rw [map_mul, hker, mul_one]
      _ = V.normalizerMonoidHom n := by rw [← hn_decomp]
      _ = y.1 := hn_eq

theorem sec128_K_ker {G : Type} [Group G] {V K : Subgroup G}
    (hC : centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G)))
    (hKO : oddCoreIn (normalizer (V : Set G)) ≤ K) (hKV : K ⊓ V = ⊥) {k : G} (hk : k ∈ K)
    (hcent : ∀ v : ↥V, k * (v : G) * k⁻¹ = (v : G)) :
    k ∈ oddCoreIn (normalizer (V : Set G)) := by
  have hkcent : k ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : k * h * k⁻¹ = h := hcent ⟨h, hh⟩
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  exact mem_oddCoreIn_of_centralizes hC hKO hKV hk hkcent

theorem sec128_O_cent {G : Type} [Group G] {V : Subgroup G}
    (hC : centralizer (V : Set G) = V ⊔ oddCoreIn (normalizer (V : Set G)))
    {o : G} (ho : o ∈ oddCoreIn (normalizer (V : Set G))) (v : ↥V) :
    o * (v : G) * o⁻¹ = (v : G) := by
  have ho' : o ∈ centralizer (V : Set G) := by
    rw [hC]
    exact (le_sup_right : oddCoreIn (normalizer (V : Set G)) ≤
      V ⊔ oddCoreIn (normalizer (V : Set G))) ho
  have hcomm : (v : G) * o = o * (v : G) :=
    (Subgroup.mem_centralizer_iff.mp ho') (v : G) v.2
  calc o * (v : G) * o⁻¹ = ((v : G) * o) * o⁻¹ := by rw [hcomm.symm]
    _ = (v : G) := by rw [mul_assoc, mul_inv_cancel, mul_one]

end CFSG.OddStandard.SmallF3.Omega
