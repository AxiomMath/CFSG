module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Skeleton

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits

theorem radRigidInner_of_normal {Γ : Type} [Group Γ] [Finite Γ] (T : Subgroup Γ) [hTn : T.Normal]
    (h : RadRigidInner 2 Γ) : RadRigidInner 2 ↥T := by
  intro R hR x hx hxo
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  have hinj : Function.Injective T.subtype := T.subtype_injective
  obtain ⟨R', hR'⟩ : ∃ R' : Subgroup Γ, R' = R.map T.subtype := ⟨_, rfl⟩
  have hR'le : R' ≤ T := by
    rw [hR']
    exact Subgroup.map_subtype_le R
  have hR'p : IsPGroup 2 R' := by
    rw [hR']
    exact hp.map _
  have hR'ne : R' ≠ ⊥ := by
    rw [hR']
    intro hb
    exact h0 ((Subgroup.map_eq_bot_iff_of_injective R hinj).1 hb)
  have hmemR' : ∀ y : T, (y : Γ) ∈ R' ↔ y ∈ R := fun y => by
    rw [hR']
    exact Subgroup.mem_map_iff_mem hinj
  have hRsub : R'.subgroupOf T = R := by
    rw [hR']
    exact Subgroup.comap_map_eq_self_of_injective hinj R
  obtain ⟨N, hN⟩ : ∃ N : Subgroup Γ, N = Subgroup.normalizer (R' : Set Γ) := ⟨_, rfl⟩
  have hNT : ∀ y : T, y ∈ Subgroup.normalizer (R : Set T) ↔ (y : Γ) ∈ N := by
    intro y
    have h1 : N.subgroupOf T = Subgroup.normalizer (R : Set T) := by
      rw [hN, Subgroup.subgroupOf_normalizer_eq hR'le, hRsub]
    rw [← h1, Subgroup.mem_subgroupOf]
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Subgroup Γ, R₁ = pCoreOf 2 N := ⟨_, rfl⟩
  have hR₁p : IsPGroup 2 R₁ := by
    rw [hR₁]
    exact pCoreOf_isPGroup 2 N
  have hR₁N : R₁ ≤ N := by
    rw [hR₁]
    exact pCoreOf_le 2 N
  have hNR₁ : N ≤ Subgroup.normalizer (R₁ : Set Γ) := by
    rw [hR₁]
    exact le_normalizer_pCoreOf 2 N
  have hR'R₁ : R' ≤ R₁ := by
    rw [hR₁, hN]
    exact le_pCoreOf_normalizer 2 R' hR'p
  have hR₁T : ∀ y : Γ, y ∈ R₁ → y ∈ T → y ∈ R' := by
    intro y hy hyT
    have hXN : R₁.subgroupOf T ≤ Subgroup.normalizer (R : Set T) := fun z hz =>
      (hNT z).2 (hR₁N (Subgroup.mem_subgroupOf.1 hz))
    have hXnorm : ((R₁.subgroupOf T).subgroupOf (Subgroup.normalizer (R : Set T))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXN]
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hnN : (n : Γ) ∈ N := (hNT n).1 hn
      have := Subgroup.mem_normalizer_iff.1 (hNR₁ hnN) (z : Γ)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this
    have hXp : IsPGroup 2 (R₁.subgroupOf T) := hR₁p.comap_of_injective _ hinj
    have hle := le_pCoreOf 2 hXN hXnorm hXp
    rw [hc] at hle
    have hyR : (⟨y, hyT⟩ : T) ∈ R := hle (Subgroup.mem_subgroupOf.2 hy)
    exact (hmemR' ⟨y, hyT⟩).2 hyR
  have hR₁Teq : ∀ y : Γ, y ∈ R' ↔ y ∈ R₁ ∧ y ∈ T := fun y =>
    ⟨fun hy => ⟨hR'R₁ hy, hR'le hy⟩, fun hy => hR₁T y hy.1 hy.2⟩
  have hNR₁eq : Subgroup.normalizer (R₁ : Set Γ) = N := by
    refine le_antisymm (fun g hg => ?_) hNR₁
    rw [hN, Subgroup.mem_normalizer_iff]
    intro y
    rw [hR₁Teq, hR₁Teq, ← Subgroup.mem_normalizer_iff.1 hg y]
    refine and_congr Iff.rfl ⟨fun hyT => ?_, fun hyT => ?_⟩
    · exact hTn.conj_mem y hyT g
    · have := hTn.conj_mem _ hyT g⁻¹
      simpa [mul_assoc] using this
  have hrad : IsRadical 2 R₁ := by
    refine ⟨fun hb => hR'ne (le_bot_iff.1 (hb ▸ hR'R₁)), hR₁p, ?_, ?_⟩
    · rw [hNR₁eq, hR₁]
    · rw [hNR₁eq]
      intro htop
      apply hnt
      rw [eq_top_iff]
      intro y _
      exact (hNT y).2 (htop ▸ Subgroup.mem_top _)
  set s : Γ := (x : Γ) with hs
  have hsT : s ∈ T := x.2
  have hcommR' : ∀ r ∈ R', s * r = r * s := by
    intro r hr
    rw [hR'] at hr
    obtain ⟨z, hz, rfl⟩ := hr
    exact congrArg Subtype.val (hx z hz)
  have hsN : s ∈ N := by
    rw [hN]
    exact Subgroup.centralizer_le_normalizer (R' : Set Γ)
      (Subgroup.mem_centralizer_iff.2 fun r hr => (hcommR' r hr).symm)
  have hsodd : Nat.Coprime (orderOf s) 2 := by
    rw [hs, Subgroup.orderOf_coe]
    exact hxo
  have hcomm : ∀ y ∈ R₁, s * y = y * s := by
    intro y hy
    obtain ⟨w, hw⟩ : ∃ w : Γ, w = y⁻¹ * (s * y * s⁻¹) := ⟨_, rfl⟩
    have hwR₁ : w ∈ R₁ := by
      rw [hw]
      exact R₁.mul_mem (R₁.inv_mem hy)
        ((Subgroup.mem_normalizer_iff.1 (hNR₁ hsN) y).1 hy)
    have hwT : w ∈ T := by
      have : w = (y⁻¹ * s * y⁻¹⁻¹) * s⁻¹ := by rw [hw]; group
      rw [this]
      exact T.mul_mem (hTn.conj_mem s hsT y⁻¹) (T.inv_mem hsT)
    have hwR' : w ∈ R' := hR₁T w hwR₁ hwT
    have hsw : s * w = w * s := hcommR' w hwR'
    have hsy : s * y * s⁻¹ = y * w := by rw [hw]; group
    have hpow : ∀ k : ℕ, s ^ k * y * (s ^ k)⁻¹ = y * w ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hswk : s * w ^ k * s⁻¹ = w ^ k := by
          have : Commute s w := hsw
          rw [(this.pow_right k).eq]
          group
        calc s ^ (k + 1) * y * (s ^ (k + 1))⁻¹
            = s * (s ^ k * y * (s ^ k)⁻¹) * s⁻¹ := by group
          _ = s * (y * w ^ k) * s⁻¹ := by rw [ih]
          _ = (s * y * s⁻¹) * (s * w ^ k * s⁻¹) := by group
          _ = (y * w) * w ^ k := by rw [hsy, hswk]
          _ = y * w ^ (k + 1) := by rw [pow_succ', mul_assoc]
    have hwk : w ^ orderOf s = 1 := by
      have h1 := hpow (orderOf s)
      rw [pow_orderOf_eq_one, inv_one, mul_one, one_mul] at h1
      have h2 : y * w ^ orderOf s = y * 1 := by rw [mul_one]; exact h1.symm
      exact mul_left_cancel h2
    have hw1 : w = 1 := by
      obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf.1 hR'p) ⟨w, hwR'⟩
      have hi' : orderOf w = 2 ^ i := by
        rw [← Subgroup.orderOf_coe (⟨w, hwR'⟩ : R')] at hi
        exact hi
      have h9 : Nat.Coprime (orderOf w) (orderOf s) := by
        rw [hi']
        exact Nat.Coprime.pow_left i hsodd.symm
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h9 (orderOf_dvd_of_pow_eq_one hwk))
    rw [hw1, mul_one] at hsy
    calc s * y = (s * y * s⁻¹) * s := by group
      _ = y * s := by rw [hsy]
  have hs1 : s = 1 := h R₁ hrad s (fun r hr => hcomm r hr) hsodd
  exact Subtype.ext hs1

theorem conj_injective_of_center_bot {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have hmem : b⁻¹ * a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : a * x * a⁻¹ = b * x * b⁻¹ := by
      simpa using DFunLike.congr_fun hab x
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [hx]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem radRigid_two_of_inner {T : Type} [Group T] (hZ : Subgroup.center T = ⊥)
    (hinner : ∀ α : MulAut T, Odd (orderOf α) → α ∈ (MulAut.conj : T →* MulAut T).range)
    (h : RadRigidInner 2 T) : RadRigid 2 T := by
  intro R hR α hα hαo
  obtain ⟨s, rfl⟩ := hinner α (Nat.coprime_two_right.1 hαo)
  have hinj := conj_injective_of_center_bot hZ
  have hs : s = 1 := by
    refine h R hR s (fun r hr => ?_) ?_
    · have h1 : s * r * s⁻¹ = r := hα r hr
      calc s * r = (s * r * s⁻¹) * s := by group
        _ = r * s := by rw [h1]
    · rwa [orderOf_injective _ hinj s] at hαo
  rw [hs, map_one]

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
