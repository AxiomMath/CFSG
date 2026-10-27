module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aTwoQuot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

section Grp

variable {H : Type*} [Group H] [Finite H]

theorem isPComponent_subgroupOf_top_iff (L : Subgroup H) :
    IsPComponent 2 (L.subgroupOf ⊤) ↔ IsPComponent 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L ⊤ le_top,
    CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Subgroup.IsSubnormal.trans le_top h1 (normal_top).isSubnormal, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.subgroupOf, h2, h3⟩

theorem le_coreActionKernel_of_isPComponent_ne {K₁ K₂ : Subgroup H} (h1 : IsPComponent 2 K₁)
    (h2 : IsPComponent 2 K₂) (hne : K₁ ≠ K₂) : K₂ ≤ coreActionKernel K₁ := by
  obtain ⟨-, hd⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ h1 h2
  obtain ⟨hN, -, hc, -⟩ := hd hne
  intro k hk
  refine mem_coreActionKernel.mpr ⟨hN hk, fun j hj => ?_⟩
  have h3 := hc (commutator_mem_commutator (inv_mem hj) (inv_mem hk))
  have h4 : ⁅j⁻¹, k⁻¹⁆ = j⁻¹ * k⁻¹ * j * k := by
    rw [commutatorElement_def, inv_inv, inv_inv]
  rw [h4] at h3
  exact (mem_inf.mp h3).1

omit [Finite H] in
theorem mem_normalizer_of_conjugate_eq' {M : Subgroup H} {x : H} (h : conjugate M x = M) :
    x ∈ normalizer (M : Set H) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h] at hy
    obtain ⟨m, hm, hme⟩ := hy
    have e : x * y * x⁻¹ = m := by
      rw [← hme]
      simp [mul_assoc]
    rw [e]
    exact hm
  · intro hy
    rw [← h]
    refine ⟨x * y * x⁻¹, hy, ?_⟩
    simp [mul_assoc]

omit [Finite H] in
theorem map_centralizer_normal (x : H) [(zpowers (x ^ 2)).Normal] :
    (((centralizer ({x} : Set H)).map (QuotientGroup.mk' (zpowers (x ^ 2)))).subgroupOf
      (centralizer ({QuotientGroup.mk' (zpowers (x ^ 2)) x} : Set (H ⧸ zpowers (x ^ 2))))).Normal
    := by
  set N := zpowers (x ^ 2)
  set f := QuotientGroup.mk' N
  have hle : (centralizer ({x} : Set H)).map f ≤ centralizer ({f x} : Set (H ⧸ N)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  have hconj : ∀ c : H, f c * f x = f x * f c → ∃ k : ℤ, c⁻¹ * x * c = x ^ k := by
    intro c hc
    have h1 : f (c⁻¹ * x * c) = f x := by
      rw [map_mul, map_mul, map_inv]
      calc (f c)⁻¹ * f x * f c = (f c)⁻¹ * (f x * f c) := by group
        _ = (f c)⁻¹ * (f c * f x) := by rw [hc]
        _ = f x := by group
    have h2 : x⁻¹ * (c⁻¹ * x * c) ∈ N := by
      rw [← QuotientGroup.eq]
      exact h1.symm
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h2
    refine ⟨2 * k + 1, ?_⟩
    have h3 : c⁻¹ * x * c = x * (x ^ 2) ^ k := by rw [hk]; group
    rw [h3, ← zpow_natCast, ← zpow_mul, ← zpow_one_add]
    congr 1
    push_cast
    ring
  have hmem : ∀ c : H, ∀ k : ℤ, c⁻¹ * x * c = x ^ k →
      ∀ y ∈ centralizer ({x} : Set H), c * y * c⁻¹ ∈ centralizer ({x} : Set H) := by
    intro c k hk y hy
    rw [mem_centralizer_singleton_iff] at hy ⊢
    have hyk : y * x ^ k = x ^ k * y := (Commute.zpow_right hy k).eq
    have e : x = c * x ^ k * c⁻¹ := by rw [← hk]; group
    have h4 : x * (c * y * c⁻¹) = c * y * c⁻¹ * x := by
      calc x * (c * y * c⁻¹) = c * x ^ k * c⁻¹ * (c * y * c⁻¹) := by rw [← e]
        _ = c * (x ^ k * y) * c⁻¹ := by group
        _ = c * (y * x ^ k) * c⁻¹ := by rw [hyk]
        _ = c * y * c⁻¹ * (c * x ^ k * c⁻¹) := by group
        _ = c * y * c⁻¹ * x := by rw [← e]
    exact h4.symm
  rw [normal_subgroupOf_iff_le_normalizer hle]
  intro c₁ hc₁
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N c₁
  have hc : f c * f x = f x * f c := mem_centralizer_singleton_iff.mp hc₁
  have hc' : f c⁻¹ * f x = f x * f c⁻¹ := by
    rw [map_inv]
    calc (f c)⁻¹ * f x = (f c)⁻¹ * (f x * f c) * (f c)⁻¹ := by group
      _ = (f c)⁻¹ * (f c * f x) * (f c)⁻¹ := by rw [hc]
      _ = f x * (f c)⁻¹ := by group
  obtain ⟨k, hk⟩ := hconj c hc
  obtain ⟨k', hk'⟩ := hconj c⁻¹ hc'
  rw [mem_normalizer_iff]
  intro y₁
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨c * y * c⁻¹, hmem c k hk y hy, ?_⟩
    change f (c * y * c⁻¹) = f c * f y * (f c)⁻¹
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨y, hy, hye⟩
    refine ⟨c⁻¹ * y * c, ?_, ?_⟩
    · have := hmem c⁻¹ k' hk' y hy
      rwa [inv_inv] at this
    · rw [map_mul, map_mul, map_inv]
      have hye' : f y = f c * y₁ * (f c)⁻¹ := hye
      rw [hye']
      group

theorem map_pLayer_le {H₁ : Type*} [Group H₁] [Finite H₁] (f : H →* H₁)
    (hf : Function.Surjective f) (hc : f.ker ≤ center H) : (pLayer H 2).map f ≤ pLayer H₁ 2 := by
  refine map_le_iff_le_comap.mpr (sSup_le fun L hL => ?_)
  rw [← map_le_iff_le_comap]
  refine le_sSup ?_
  have hLc : L ≤ centralizer (f.ker : Set H) := fun l _ =>
    mem_centralizer_iff.mpr fun k hk => (mem_center_iff.mp (hc hk) l).symm
  have h := GSThmB.TwoQuot.isPComponent_map_of_le_centralizer f le_top hLc
    ((isPComponent_subgroupOf_top_iff L).mpr hL)
  rw [map_top_of_surjective f hf] at h
  exact (isPComponent_subgroupOf_top_iff _).mp h

end Grp

end CFSG.ComponentClassification.SolMax
