module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement

section Def

variable {G : Type*} [Group G]

@[expose] def RelA5At (H : Subgroup G) (τ : G) : Prop :=
  ∀ R N : Subgroup G, N ≤ R → R ≤ H ⊓ centralizer ({τ} : Set G) → ⁅R, R⁆ = R →
    (∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) → IsPGroup 2 N →
    (∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1 ∨ x = τ) →
    (∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = τ) → Nat.card N ≤ 2 ^ 5

@[expose] def A5At (s : G) : Prop := RelA5At ⊤ s

theorem RelA5At.of_injective {T : Type*} [Group T] (φ : G →* T) (hφ : Function.Injective φ)
    {H : Subgroup G} {s : G} (h : RelA5At (H.map φ) (φ s)) : RelA5At H s := by
  intro R N hNR hR hperf hnorm hN2 hZ hC
  rw [← card_map_of_injective hφ]
  refine h (R.map φ) (N.map φ) (map_mono hNR) ?_ ?_ ?_ (hN2.map φ) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨hrH, hrs⟩ := mem_inf.mp (hR hr)
    refine mem_inf.mpr ⟨⟨r, hrH, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff] at hrs ⊢
    rw [← map_mul, ← map_mul, hrs]
  · rw [← map_commutator, hperf]
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨r * n * r⁻¹, hnorm r hr n hn, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩ hxc
    have hx' : ∀ y ∈ N, x * y = y * x := fun y hy => hφ (by
      rw [map_mul, map_mul]
      exact hxc _ ⟨y, hy, rfl⟩)
    rcases hZ x hx hx' with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_commutatorElement]
    rcases hC x hx y hy with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])

theorem A5At.of_mulEquiv {T : Type*} [Group T] (e : G ≃* T) {s : G} (h : A5At (e s)) :
    A5At s := by
  refine RelA5At.of_injective e.toMonoidHom e.injective ?_
  have hmap : (⊤ : Subgroup G).map e.toMonoidHom = ⊤ :=
    map_top_of_surjective _ e.surjective
  rw [hmap]
  exact h

theorem a5At_of_rel {H : Subgroup G} {s : H} (h : RelA5At H (s : G)) : A5At s := by
  refine RelA5At.of_injective H.subtype Subtype.val_injective ?_
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact h

end Def

section Reduction

variable {X : Type*} [Group X]

theorem eq_one_or_eq_of_central_extraspecial {N : Subgroup X} {t : X} (htN : t ∈ N)
    (hto : orderOf t = 2) (htc : ∀ y ∈ N, y * t = t * y) (hN : CFSG.IsExtraspecialPGroup 2 N)
    {x : X} (hx : x ∈ N) (hxc : ∀ y ∈ N, x * y = y * x) : x = 1 ∨ x = t := by
  have htZ : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro n
    exact Subtype.ext (htc n n.2)
  have hot : orderOf (⟨t, htN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk, hto]
  have hzp : zpowers (⟨t, htN⟩ : N) = center N := by
    have : Finite (center N) := Nat.finite_of_card_ne_zero (by rw [hN.2.2.2]; norm_num)
    apply eq_of_le_of_card_ge (zpowers_le.mpr htZ)
    rw [hN.2.2.2, Nat.card_zpowers, hot]
  have hxZ : (⟨x, hx⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro n
    exact Subtype.ext (hxc n n.2).symm
  rw [← hzp] at hxZ
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxZ
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    have := congrArg Subtype.val hk
    rw [← zpow_mod_orderOf, hot, Nat.cast_two, h, zpow_zero] at this
    exact this.symm
  · right
    have := congrArg Subtype.val hk
    rw [← zpow_mod_orderOf, hot, Nat.cast_two, h, zpow_one] at this
    exact this.symm

theorem commutator_eq_one_or_eq_extraspecial {N : Subgroup X} {t : X} (htN : t ∈ N)
    (hto : orderOf t = 2) (htc : ∀ y ∈ N, y * t = t * y) (hN : CFSG.IsExtraspecialPGroup 2 N)
    {x y : X} (hx : x ∈ N) (hy : y ∈ N) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = t := by
  have hc : ⁅(⟨x, hx⟩ : N), ⟨y, hy⟩⁆ ∈ center N := by
    rw [← hN.2.1]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have e2 : ((⁅(⟨x, hx⟩ : N), ⟨y, hy⟩⁆ : N) : X) = ⁅x, y⁆ := map_commutatorElement N.subtype _ _
  rw [← e2]
  refine eq_one_or_eq_of_central_extraspecial htN hto htc hN (SetLike.coe_mem _) fun z hz => ?_
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨z, hz⟩).symm

theorem orderOf_mk_center_eq_two {U : Subgroup X} {t : X} (htU : t ∈ U) (hto : orderOf t = 2)
    (hnc : ∃ u ∈ U, u * t ≠ t * u) :
    orderOf (QuotientGroup.mk' (center ↥U) ⟨t, htU⟩) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    have h2 : (⟨t, htU⟩ : U) ^ 2 = 1 := Subtype.ext (by simp [← hto])
    rw [h2, map_one]
  · intro h1
    obtain ⟨u, hu, hut⟩ := hnc
    have h1' : (⟨t, htU⟩ : U) ∈ center ↥U := (QuotientGroup.eq_one_iff _).mp h1
    exact hut (congrArg Subtype.val (mem_center_iff.mp h1' ⟨u, hu⟩))

theorem card_lt_of_a5At [Finite X] {U : Subgroup X} {t : X} (htU : t ∈ U) (hto : orderOf t = 2)
    (hnc : ∃ u ∈ U, u * t ≠ t * u) (hA5 : A5At (QuotientGroup.mk' (center ↥U) ⟨t, htU⟩))
    {R N : Subgroup X} (hNR : N ≤ R) (hRU : R ≤ U) (hRt : R ≤ centralizer ({t} : Set X))
    (hRperf : ⁅R, R⁆ = R) [hNn : (N.subgroupOf R).Normal] (htN : t ∈ N)
    (hN : CFSG.IsExtraspecialPGroup 2 N) : Nat.card N < 2 ^ 9 := by
  let π : ↥U →* ↥U ⧸ center ↥U := QuotientGroup.mk' (center ↥U)
  have hNU : N ≤ U := hNR.trans hRU
  have htc : ∀ y ∈ N, y * t = t * y := fun y hy => mem_centralizer_singleton_iff.mp (hRt (hNR hy))
  have hcen : ∀ n ∈ N, (∀ u ∈ U, u * n = n * u) → n = 1 := by
    intro n hn hnU
    rcases eq_one_or_eq_of_central_extraspecial htN hto htc hN hn
        (fun y hy => (hnU y (hNU hy)).symm) with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu, hut⟩ := hnc
      exact hut (h ▸ hnU u hu)
  set R' : Subgroup U := R.subgroupOf U with hR'
  set N' : Subgroup U := N.subgroupOf U with hN'
  have hR'perf : ⁅R', R'⁆ = R' := by
    apply map_injective U.subtype_injective
    rw [map_commutator, hR', subgroupOf_map_subtype, inf_of_le_left hRU, hRperf]
  have hψ : Function.Injective (π.comp N'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro n hn
    have h1 : ((n : U) : U) ∈ center ↥U := (QuotientGroup.eq_one_iff _).mp hn
    have h2 := hcen ((n : U) : X) (mem_subgroupOf.mp n.2) fun u hu =>
      congrArg Subtype.val (mem_center_iff.mp h1 ⟨u, hu⟩)
    exact mem_bot.mpr (Subtype.ext (Subtype.ext h2))
  have hcard : Nat.card ↥(N'.map π) = Nat.card N := by
    have h1 : N'.map π = (π.comp N'.subtype).range := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm]
    exact Nat.card_congr (subgroupOfEquivOfLe hNU).toEquiv
  have hbound := hA5 (R'.map π) (N'.map π) (map_mono fun x hx => hNR hx) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hcard]
    exact lt_of_le_of_lt hbound (by norm_num)
  · rintro _ ⟨r, hr, rfl⟩
    refine mem_inf.mpr ⟨mem_top _, ?_⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (mem_centralizer_singleton_iff.mp (hRt hr)))
  · rw [← map_commutator, hR'perf]
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨n, hn, rfl⟩
    refine ⟨r * n * r⁻¹, ?_, by simp⟩
    have hc := hNn.conj_mem ⟨n, hNR hn⟩ (mem_subgroupOf.mpr hn) ⟨r, hr⟩
    rw [mem_subgroupOf] at hc
    change ((r * n * r⁻¹ : U) : X) ∈ N
    simpa using hc
  · exact (hN.1.comap_subtype (K := U)).map π
  · rintro _ ⟨x, hx, rfl⟩ hxc
    have hx' : ∀ y ∈ N, (x : X) * y = y * x := by
      intro y hy
      have h1 := hxc (π ⟨y, hNU hy⟩) ⟨⟨y, hNU hy⟩, hy, rfl⟩
      have h2 : π ⁅x, ⟨y, hNU hy⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1
      have h3 : ⁅x, (⟨y, hNU hy⟩ : U)⁆ ∈ center ↥U := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : ((⁅x, (⟨y, hNU hy⟩ : U)⁆ : U) : X) = ⁅(x : X), y⁆ :=
        map_commutatorElement U.subtype _ _
      have h5 : ⁅(x : X), y⁆ ∈ N := by
        rw [commutatorElement_def]
        exact N.mul_mem (N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx)) (N.inv_mem hy)
      have h6 := hcen _ h5 fun u hu => by
        rw [← h4]
        exact congrArg Subtype.val (mem_center_iff.mp h3 ⟨u, hu⟩)
      exact commutatorElement_eq_one_iff_mul_comm.mp h6
    rcases eq_one_or_eq_of_central_extraspecial htN hto htc hN hx hx' with h | h
    · left
      rw [show x = 1 from Subtype.ext h, map_one]
    · right
      rw [show x = ⟨t, htU⟩ from Subtype.ext h]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_commutatorElement]
    have h4 : ((⁅x, y⁆ : U) : X) = ⁅(x : X), (y : X)⁆ := map_commutatorElement U.subtype _ _
    rcases commutator_eq_one_or_eq_extraspecial htN hto htc hN hx hy with h | h
    · left
      rw [show ⁅x, y⁆ = 1 from Subtype.ext (h4.trans h), map_one]
    · right
      rw [show ⁅x, y⁆ = ⟨t, htU⟩ from Subtype.ext (h4.trans h)]

end Reduction

end CFSG.LargeExtraspecial.S8
