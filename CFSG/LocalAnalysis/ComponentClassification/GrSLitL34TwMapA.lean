module

import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalOrbits

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw.Map

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G]

structure TwoCompData (M K : Subgroup G) (t : G) : Prop where
  hKM : K ≤ M
  hKc : IsPComponent 2 (K.subgroupOf M)
  htM : t ∈ M
  htK : t ∉ normalizer (K : Set G)
  hr2 : ∀ m ∈ M, conjugate K m = K ∨ conjugate K m = conjugate K t

private theorem mem_normalizer_of_conjugate_eq' {K : Subgroup G} {g : G}
    (h : conjugate K g = K) : g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  rw [← mem_conjugate_iff, h]

private theorem conjugate_eq_of_mem_normalizer' {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : conjugate K g = K := by
  ext y
  rw [mem_conjugate_iff]
  exact (mem_normalizer_iff.mp hg y).symm

private theorem mem_coreActionKernel_conjugate' {J : Subgroup G} {g x : G}
    (hx : g * x * g⁻¹ ∈ coreActionKernel J) : x ∈ coreActionKernel (conjugate J g) := by
  refine ⟨mem_normalizer_iff.mpr fun y => ?_, fun j hj => ?_⟩
  · rw [mem_conjugate_iff, mem_conjugate_iff,
      show g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ by group]
    exact mem_normalizer_iff.mp hx.1 (g * y * g⁻¹)
  · rw [mem_conjugate_iff] at hj
    have h := hx.2 _ hj
    rw [show (g * j * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ * (g * j * g⁻¹) * (g * x * g⁻¹) =
      g * (j⁻¹ * x⁻¹ * j * x) * g⁻¹ by group] at h
    rw [← GSLit.conjugate_map_pPrimeCore J g]
    exact mem_conjugate_iff.mpr h

private theorem conj_mem_coreActionKernel' {K : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (K : Set G)) (hx : x ∈ coreActionKernel K) :
    g * x * g⁻¹ ∈ coreActionKernel K := by
  have h1 := mem_coreActionKernel_conjugate' (J := K) (g := g⁻¹) (x := g * x * g⁻¹)
    (by rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group])
  rwa [conjugate_eq_of_mem_normalizer' (inv_mem hg)] at h1

variable {M K : Subgroup G} {t : G}

theorem mem_normalizer_or (d : TwoCompData M K t) {m : G} (hm : m ∈ M) :
    m ∈ normalizer (K : Set G) ∨ m * t⁻¹ ∈ normalizer (K : Set G) := by
  rcases d.hr2 m hm with h | h
  · exact Or.inl (mem_normalizer_of_conjugate_eq' h)
  · refine Or.inr (mem_normalizer_of_conjugate_eq' ?_)
    rw [← conjugate_conjugate, h, conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem mul_mem_normalizer_iff (d : TwoCompData M K t) {m m' : G} (hm : m ∈ M) (hm' : m' ∈ M) :
    m * m' ∈ normalizer (K : Set G) ↔
      (m ∈ normalizer (K : Set G) ↔ m' ∈ normalizer (K : Set G)) := by
  by_cases h1 : m ∈ normalizer (K : Set G) <;> by_cases h2 : m' ∈ normalizer (K : Set G)
  · exact ⟨fun _ => ⟨fun _ => h2, fun _ => h1⟩, fun _ => mul_mem h1 h2⟩
  · refine ⟨fun h => absurd ?_ h2, fun h => absurd (h.mp h1) h2⟩
    have := mul_mem (inv_mem h1) h
    rwa [inv_mul_cancel_left] at this
  · refine ⟨fun h => absurd ?_ h1, fun h => absurd (h.mpr h2) h1⟩
    have := mul_mem h (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  · refine ⟨fun _ => ⟨fun h => absurd h h1, fun h => absurd h h2⟩, fun _ => ?_⟩
    by_contra hmm
    rcases mem_normalizer_or d (mul_mem hm hm') with h3 | h3
    · exact hmm h3
    · have h4 := (mem_normalizer_or d hm').resolve_left h2
      apply h1
      have := mul_mem h3 (inv_mem h4)
      rwa [show m * m' * t⁻¹ * (m' * t⁻¹)⁻¹ = m by group] at this

private theorem inv_not_mem (htK : t ∉ normalizer (K : Set G)) :
    t⁻¹ ∉ normalizer (K : Set G) := fun h => htK (by simpa using inv_mem h)

theorem sq_mem (d : TwoCompData M K t) : t * t ∈ normalizer (K : Set G) :=
  (mul_mem_normalizer_iff d d.htM d.htM).mpr Iff.rfl

theorem inv_mul_mem (d : TwoCompData M K t) {m : G} (hm : m ∈ M)
    (hmn : m ∉ normalizer (K : Set G)) : t⁻¹ * m ∈ normalizer (K : Set G) :=
  (mul_mem_normalizer_iff d (inv_mem d.htM) hm).mpr
    ⟨fun h => absurd h (inv_not_mem d.htK), fun h => absurd h hmn⟩

theorem mul_mem_of_not_mem (d : TwoCompData M K t) {m : G} (hm : m ∈ M)
    (hmn : m ∉ normalizer (K : Set G)) : m * t ∈ normalizer (K : Set G) :=
  (mul_mem_normalizer_iff d hm d.htM).mpr ⟨fun h => absurd h hmn, fun h => absurd h d.htK⟩

theorem conj_mem (d : TwoCompData M K t) {m : G} (hm : m ∈ M)
    (hmn : m ∈ normalizer (K : Set G)) : t⁻¹ * m * t ∈ normalizer (K : Set G) := by
  have h1 : t⁻¹ * m ∉ normalizer (K : Set G) := fun h =>
    inv_not_mem d.htK (((mul_mem_normalizer_iff d (inv_mem d.htM) hm).mp h).mpr hmn)
  exact (mul_mem_normalizer_iff d (mul_mem (inv_mem d.htM) hm) d.htM).mpr
    ⟨fun h => absurd h h1, fun h => absurd h d.htK⟩

theorem perfect (d : TwoCompData M K t) : ⁅K, K⁆ = K := by
  have h1 : Group.IsPerfect (K.subgroupOf M) := CatalogueBAlternating.pComponent_perfect d.hKc
  have h2 : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe d.hKM).toMonoidHom) (subgroupOfEquivOfLe d.hKM).surjective
  exact Subgroup.isPerfect_iff.mp h2

theorem isPComponent_conjugate (d : TwoCompData M K t) :
    IsPComponent 2 ((conjugate K t).subgroupOf M) := by
  have h := (GSThmB.Six.isPComponent_conjugate d.hKM d.hKc t).2
  rwa [conjugate_eq_of_mem_normalizer' (le_normalizer d.htM)] at h

theorem conjugate_le (d : TwoCompData M K t) : conjugate K t ≤ M := by
  intro y hy
  rw [mem_conjugate_iff] at hy
  have := mul_mem (mul_mem (inv_mem d.htM) (d.hKM hy)) d.htM
  rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at this

theorem subgroupOf_ne (d : TwoCompData M K t) :
    K.subgroupOf M ≠ (conjugate K t).subgroupOf M := by
  intro h
  apply d.htK
  apply mem_normalizer_of_conjugate_eq'
  have h1 := congrArg (Subgroup.map M.subtype) h
  rw [map_subgroupOf_eq_of_le d.hKM, map_subgroupOf_eq_of_le (conjugate_le d)] at h1
  exact h1.symm

theorem conj_mem_K (d : TwoCompData M K t) {m : G} (hm : m ∈ conjugate K t) :
    t⁻¹ * m * t ∈ K := by
  rw [mem_conjugate_iff] at hm
  have h1 := (mem_normalizer_iff.mp (inv_mem (sq_mem d)) (t * m * t⁻¹)).mp hm
  rwa [show (t * t)⁻¹ * (t * m * t⁻¹) * (t * t)⁻¹⁻¹ = t⁻¹ * m * t by group] at h1

theorem mul_mem_conjugate (d : TwoCompData M K t) {k : G} (hk : k ∈ K) :
    t * k * t⁻¹ ∈ conjugate K t := by
  rw [mem_conjugate_iff]
  have h1 := (mem_normalizer_iff.mp (sq_mem d) k).mp hk
  rwa [show t * t * k * (t * t)⁻¹ = t * (t * k * t⁻¹) * t⁻¹ by group] at h1

section Core

variable [Finite G]

theorem core_commutation (d : TwoCompData M K t) :
    conjugate K t ≤ normalizer (K : Set G) ∧
      ∀ j ∈ K, ∀ g ∈ conjugate K t, j⁻¹ * g⁻¹ * j * g ∈ map K.subtype (pPrimeCore 2 ↥K) := by
  obtain ⟨hLn, -, hcomm, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ d.hKc
      (isPComponent_conjugate d)).2 (subgroupOf_ne d)
  refine ⟨fun g hg => ?_, fun j hj g hg => ?_⟩
  · have hgM : g ∈ M := conjugate_le d hg
    have h1 : (⟨g, hgM⟩ : ↥M) ∈ (conjugate K t).subgroupOf M := hg
    have h2 := hLn h1
    rw [UnbalancedCorr.normalizer_subgroupOf_eq d.hKM] at h2
    exact h2
  · have hgM : g ∈ M := conjugate_le d hg
    have hjM : j ∈ M := d.hKM hj
    have h1 : (⟨j, hjM⟩ : ↥M)⁻¹ ∈ K.subgroupOf M := inv_mem (mem_subgroupOf.mpr hj)
    have h2 : (⟨g, hgM⟩ : ↥M)⁻¹ ∈ (conjugate K t).subgroupOf M :=
      inv_mem (mem_subgroupOf.mpr hg)
    have h3 := (mem_inf.mp (hcomm (commutator_mem_commutator h1 h2))).1
    have h4 := mem_map_of_mem M.subtype h3
    rw [pPrimeCore_map_subgroupOf 2 K M d.hKM] at h4
    have h5 : M.subtype ⁅(⟨j, hjM⟩ : ↥M)⁻¹, (⟨g, hgM⟩ : ↥M)⁻¹⁆ = j⁻¹ * g⁻¹ * j * g := by
      simp [commutatorElement_def]
    rwa [h5] at h4

theorem conjugate_le_coreActionKernel (d : TwoCompData M K t) :
    conjugate K t ≤ coreActionKernel K := fun g hg =>
  ⟨(core_commutation d).1 hg, fun j hj => (core_commutation d).2 j hj g hg⟩

theorem conj_mem_oddIn {m o : G} (hm : m ∈ M) (ho : o ∈ oddIn M) : m * o * m⁻¹ ∈ oddIn M := by
  have ho' : o ∈ (pPrimeCore 2 ↥M).map M.subtype := ho
  obtain ⟨o', ho'', hoo⟩ := ho'
  have hoo' : (o' : G) = o := hoo
  show m * o * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype
  refine ⟨⟨m, hm⟩ * o' * ⟨m, hm⟩⁻¹, (pPrimeCore_normal (G := ↥M)).conj_mem o' ho'' ⟨m, hm⟩, ?_⟩
  rw [← hoo']
  rfl

theorem oddIn_le_coreActionKernel (d : TwoCompData M K t) : oddIn M ≤ coreActionKernel K := by
  intro o ho
  have ho' : o ∈ (pPrimeCore 2 ↥M).map M.subtype := ho
  obtain ⟨o', ho'', hoo⟩ := ho'
  have hoo' : (o' : G) = o := hoo
  obtain ⟨-, -, hsub, -, -⟩ := d.hKc
  have hnorm : o ∈ normalizer (K : Set G) := by
    have h1 := pPrimeCore_le_normalizer d.hKc ho''
    rw [UnbalancedCorr.normalizer_subgroupOf_eq d.hKM] at h1
    rw [← hoo']
    exact h1
  refine ⟨hnorm, fun j hj => ?_⟩
  rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_subgroupOf d.hKM hsub]
  refine mem_inf.mpr ⟨?_, ?_⟩
  · have h1 := (mem_normalizer_iff.mp (inv_mem hnorm) j).mp hj
    rw [inv_inv] at h1
    have := mul_mem (inv_mem hj) h1
    rwa [show j⁻¹ * (o⁻¹ * j * o) = j⁻¹ * o⁻¹ * j * o by group] at this
  · have h1 : j⁻¹ * o⁻¹ * j⁻¹⁻¹ ∈ oddIn M :=
      conj_mem_oddIn (inv_mem (d.hKM hj)) (inv_mem ho)
    rw [inv_inv] at h1
    exact mul_mem h1 ho

theorem eq_one_of_conj_mem (d : TwoCompData M K t) {T : Subgroup G}
    (hQ : ∀ y ∈ T, y ∈ coreActionKernel K → y ∈ coreActionKernel (conjugate K t) → y = 1)
    {y : G} (hy : y ∈ T) (h1 : y ∈ coreActionKernel K)
    (h2 : t⁻¹ * y * t ∈ coreActionKernel K) : y = 1 := by
  refine hQ y hy h1 (mem_coreActionKernel_conjugate' ?_)
  have := conj_mem_coreActionKernel' (sq_mem d) h2
  rwa [show t * t * (t⁻¹ * y * t) * (t * t)⁻¹ = t * y * t⁻¹ by group] at this

end Core

theorem le_pPrimeCore_of_inf_sylow_eq_bot {H : Type} [Group H] [Finite H] (P : Sylow 2 H)
    {X : Subgroup H} [X.Normal] (hX : X ⊓ (P : Subgroup H) = ⊥) : X ≤ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨inferInstance, ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 h2
  have hx' : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hQ : IsPGroup 2 (Subgroup.zpowers (x : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx', pow_one])
  obtain ⟨Q, hQle⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hmem : MulAut.conj g (x : H) ∈ ((g • Q : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact smul_mem_pointwise_smul _ _ _ (hQle (mem_zpowers _))
  rw [hg] at hmem
  have hmemX : MulAut.conj g (x : H) ∈ X := by
    have := ‹X.Normal›.conj_mem (x : H) x.2 g
    simpa using this
  have h1 : MulAut.conj g (x : H) ∈ X ⊓ (P : Subgroup H) := mem_inf.mpr ⟨hmemX, hmem⟩
  rw [hX, mem_bot] at h1
  have hx1 : (x : H) = 1 := by
    have h3 : g * (x : H) * g⁻¹ = 1 := by simpa using h1
    calc (x : H) = g⁻¹ * (g * (x : H) * g⁻¹) * g := by group
      _ = 1 := by rw [h3]; group
  rw [hx1, orderOf_one] at hx'
  omega

end CFSG.ComponentClassification.GrSLit.L34Tw.Map
