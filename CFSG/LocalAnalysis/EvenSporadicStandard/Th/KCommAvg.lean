module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Fix

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type*} [Group G] {C : Subgroup G} {k : G}

section Averaging

theorem conj_pow_mem (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (i : ℕ) :
    ∀ c ∈ C, k ^ i * c * (k ^ i)⁻¹ ∈ C := by
  induction i with
  | zero =>
    intro c hc
    simpa using hc
  | succ i ih =>
    intro c hc
    have h := hk _ (ih c hc)
    have e : k * (k ^ i * c * (k ^ i)⁻¹) * k⁻¹ = k ^ (i + 1) * c * (k ^ (i + 1))⁻¹ := by
      rw [pow_succ']
      group
    rwa [e] at h

@[expose] def conjPow (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (i : ℕ) : C →* C where
  toFun c := ⟨k ^ i * c * (k ^ i)⁻¹, conj_pow_mem hk i c c.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem coe_conjPow (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (i : ℕ) (c : C) :
    ((conjPow hk i c : C) : G) = k ^ i * c * (k ^ i)⁻¹ := rfl

@[expose] noncomputable def avgHom (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C)
    (ψ : C →* Multiplicative (ZMod 2)) (n : ℕ) : C →* Multiplicative (ZMod 2) :=
  ∏ i ∈ Finset.range n, ψ.comp (conjPow hk i)

theorem avgHom_apply (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (ψ : C →* Multiplicative (ZMod 2)) (n : ℕ)
    (c : C) : avgHom hk ψ n c = ∏ i ∈ Finset.range n, ψ (conjPow hk i c) := by
  unfold avgHom
  rw [MonoidHom.finsetProd_apply]
  rfl

theorem conjPow_succ (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (i : ℕ) (c : C) :
    conjPow hk (i + 1) c = conjPow hk i (conjPow hk 1 c) := by
  apply Subtype.ext
  simp only [coe_conjPow]
  rw [pow_succ, pow_one]
  group

theorem avgHom_conj (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (ψ : C →* Multiplicative (ZMod 2)) {n : ℕ}
    (hn : k ^ n = 1) (c : C) : avgHom hk ψ n (conjPow hk 1 c) = avgHom hk ψ n c := by
  rw [avgHom_apply, avgHom_apply]
  set g : ℕ → Multiplicative (ZMod 2) := fun i => ψ (conjPow hk i c) with hg
  have h1 : ∀ i, ψ (conjPow hk i (conjPow hk 1 c)) = g (i + 1) := fun i => by
    show ψ (conjPow hk i (conjPow hk 1 c)) = ψ (conjPow hk (i + 1) c)
    rw [conjPow_succ hk i c]
  have hgn : g n = g 0 := by
    rw [hg]
    simp only
    have : conjPow hk n c = conjPow hk 0 c := by
      apply Subtype.ext
      simp only [coe_conjPow, hn]
      simp
    rw [this]
  simp only [h1]
  have e1 := Finset.prod_range_succ' g n
  have e2 := Finset.prod_range_succ g n
  rw [hgn] at e2
  exact mul_right_cancel (e1.symm.trans e2 |>.trans rfl)

end Averaging

section Main

variable {G : Type} [Group G] [Finite G] {C : Subgroup G} {k t : G}

theorem not_mem_kCommutator_of_hom (hk : ∀ c ∈ C, k * c * k⁻¹ ∈ C) (hodd : Odd (orderOf k))
    (htC : t ∈ C) (htk : k * t = t * k) (ψ : C →* Multiplicative (ZMod 2))
    (hψ : ψ ⟨t, htC⟩ ≠ 1) : t ∉ kCommutator C k := by
  classical
  have hkn : k ^ orderOf k = 1 := pow_orderOf_eq_one k
  have hconj_t : ∀ i : ℕ, conjPow hk i ⟨t, htC⟩ = ⟨t, htC⟩ := by
    intro i
    apply Subtype.ext
    rw [coe_conjPow]
    have h : k ^ i * t = t * k ^ i := (Commute.pow_left (show Commute k t from htk) i).eq
    rw [h]
    group
  have hφt : avgHom hk ψ (orderOf k) ⟨t, htC⟩ = ψ ⟨t, htC⟩ := by
    rw [avgHom_apply]
    simp only [hconj_t]
    rw [Finset.prod_const, Finset.card_range]
    obtain ⟨m, hm⟩ := hodd
    have hsq : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hinv : ∀ j : ℕ, ∀ c : C, avgHom hk ψ (orderOf k) (conjPow hk j c) =
      avgHom hk ψ (orderOf k) c := by
    intro j
    induction j with
    | zero =>
      intro c
      have : conjPow hk 0 c = c := by
        apply Subtype.ext
        simp [coe_conjPow]
      rw [this]
    | succ j ih =>
      intro c
      rw [conjPow_succ hk j c, ih, avgHom_conj hk ψ hkn]
  have hKgen : ∀ c ∈ C, ∀ a ∈ zpowers k, c⁻¹ * (a * c * a⁻¹) ∈
      (avgHom hk ψ (orderOf k)).ker.map C.subtype := by
    intro c hc a ha
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 ha)
    refine ⟨(⟨c, hc⟩ : C)⁻¹ * conjPow hk j ⟨c, hc⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [map_mul, map_inv, hinv j]
    exact inv_mul_cancel _
  intro hmem
  have hle : kCommutator C k ≤ (avgHom hk ψ (orderOf k)).ker.map C.subtype := by
    unfold kCommutator
    refine (closure_le _).2 ?_
    rintro x ⟨c, hc, a, ha, rfl⟩
    exact hKgen c hc a ha
  obtain ⟨x, hx, hxt⟩ := hle hmem
  have hxe : x = ⟨t, htC⟩ := Subtype.ext hxt
  have hx' := MonoidHom.mem_ker.1 hx
  rw [hxe, hφt] at hx'
  exact hψ hx'

end Main

end CFSG.EvenSporadicStandard.ThStd
