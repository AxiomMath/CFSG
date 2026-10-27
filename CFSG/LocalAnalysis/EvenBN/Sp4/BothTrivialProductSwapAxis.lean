module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductUnique
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusThree
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialProduct

namespace SwapAxis

open Subgroup
open scoped MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem mem_normalizer_of_forall_conj_mem [Finite G] {Q : Subgroup G} {g : G}
    (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ normalizer (Q : Set G) := by
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : Q.map (MulAut.conj g).toMonoidHom = Q := eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro q
  refine ⟨h q, fun hq => ?_⟩
  rw [← heq] at hq
  obtain ⟨q', hq', hqq⟩ := hq
  have : q' = q := by
    have h1 : g * q' * g⁻¹ = g * q * g⁻¹ := hqq
    simpa using h1
  rwa [← this]

theorem mem_normalizer_sup [Finite G] {H₁ H₂ : Subgroup G} {y : G}
    (h₁ : y ∈ normalizer (H₁ : Set G)) (h₂ : y ∈ normalizer (H₂ : Set G)) :
    y ∈ normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  have hle : (H₁ ⊔ H₂).map (MulAut.conj y).toMonoidHom ≤ H₁ ⊔ H₂ := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (mem_normalizer_iff.1 h₁ z).1 hz
    · rintro _ ⟨z, hz, rfl⟩
      exact (mem_normalizer_iff.1 h₂ z).1 hz
  exact mem_normalizer_of_forall_conj_mem fun q hq => hle ⟨q, hq, rfl⟩

theorem mem_normalizer_inf_centralizer {X Λ : Subgroup G} {y : G}
    (hX : y ∈ normalizer (X : Set G)) (hΛ : y ∈ normalizer (Λ : Set G)) :
    y ∈ normalizer ((X ⊓ centralizer (Λ : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hX hΛ ⊢
  intro z
  rw [mem_inf, mem_inf]
  refine and_congr (hX z) ?_
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h l hl
    have hl' : y⁻¹ * l * y ∈ Λ := (hΛ (y⁻¹ * l * y)).2 (by
      rwa [show y * (y⁻¹ * l * y) * y⁻¹ = l by group])
    calc l * (y * z * y⁻¹) = y * ((y⁻¹ * l * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * l * y)) * y⁻¹ := by rw [h _ hl']
      _ = (y * z * y⁻¹) * l := by group
  · intro h l hl
    have hl' : y * l * y⁻¹ ∈ Λ := (hΛ l).1 hl
    calc l * z = y⁻¹ * ((y * l * y⁻¹) * (y * z * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * z * y⁻¹) * (y * l * y⁻¹)) * y := by rw [h _ hl']
      _ = z * l := by group

end Generic

section SL2

open CFSG.LocalAnalysis.EvenBN.Common CFSG.SL2MinimalFaithful

variable {k : Type} [Field k] [CharP k 2] [Finite k]

theorem eq_bot_or_eq_map_upperSL {μ : kˣ} (hμ : ∀ x : kˣ, x ∈ Subgroup.zpowers μ)
    (g : SL(2, k)) {A : Subgroup SL(2, k)}
    (hA : A ≤ (upperSL k).map (MulAut.conj g).toMonoidHom)
    (hd : g * diagSL μ * g⁻¹ ∈ normalizer (A : Set SL(2, k))) :
    A = ⊥ ∨ A = (upperSL k).map (MulAut.conj g).toMonoidHom := by
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hA ?_)
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  obtain ⟨u, hu, hua⟩ := hA a.2
  obtain ⟨c₀, rfl⟩ := mem_upperSL_iff.1 hu
  have hua' : g * unipotent c₀ * g⁻¹ = (a : SL(2, k)) := hua
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply ha1
    apply Subtype.ext
    rw [← hua', unipotent_zero]
    simp
  rintro _ ⟨_, hu', rfl⟩
  obtain ⟨c, rfl⟩ := mem_upperSL_iff.1 hu'
  show g * unipotent c * g⁻¹ ∈ A
  by_cases hc : c = 0
  · subst hc
    rw [unipotent_zero]
    simpa using A.one_mem
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) (c / c₀)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim hc hc₀
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hμ (Units.mk0 r hr0))
  have hdj : (g * diagSL μ * g⁻¹) ^ j ∈ normalizer (A : Set SL(2, k)) := Subgroup.zpow_mem _ hd j
  have h1 := (mem_normalizer_iff.1 hdj (a : SL(2, k))).1 a.2
  have e : (g * diagSL μ * g⁻¹) ^ j = g * diagSL (μ ^ j) * g⁻¹ := by
    rw [conj_zpow]
    congr 2
    exact (map_zpow diagSLHom μ j).symm
  rw [e, ← hua', hj] at h1
  have e2 : g * diagSL (Units.mk0 r hr0) * g⁻¹ * (g * unipotent c₀ * g⁻¹) *
      (g * diagSL (Units.mk0 r hr0) * g⁻¹)⁻¹ = g * unipotent c * g⁻¹ := by
    have := diagSL_conj_unipotent (Units.mk0 r hr0) c₀
    calc g * diagSL (Units.mk0 r hr0) * g⁻¹ * (g * unipotent c₀ * g⁻¹) *
        (g * diagSL (Units.mk0 r hr0) * g⁻¹)⁻¹
        = g * (diagSL (Units.mk0 r hr0) * unipotent c₀ * (diagSL (Units.mk0 r hr0))⁻¹) * g⁻¹ := by
          group
      _ = g * unipotent c * g⁻¹ := by
          rw [this]
          congr 3
          rw [Units.val_mk0]
          have : c = r * r * c₀ := by
            rw [div_eq_iff hc₀] at hr
            exact hr
          rw [this]
          ring
  rw [e2] at h1
  exact h1

theorem exists_odd_torus {M : Type*} [Group M] [Finite M] {N V : Subgroup M}
    (ψ : N ≃* SL(2, k)) (hVN : V ≤ N)
    (hV : ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = V) :
    ∃ d : M, d ∈ N ∧ Odd (orderOf d) ∧ d ∈ normalizer (V : Set M) ∧
      ∀ H : Subgroup M, H ≤ V → d ∈ normalizer (H : Set M) → H = ⊥ ∨ H = V := by
  classical
  obtain ⟨P, hP⟩ := hV
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨f, -, hf⟩ := FiniteField.card k 2
  have hcard : Nat.card k = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hPcard : Nat.card (P : Subgroup N) = Nat.card k := card_sylow_two_eq ψ P
  have hUcard : Nat.card ((P : Subgroup N).map ψ.toMonoidHom) = Nat.card k := by
    rw [Subgroup.card_map_of_injective ψ.injective, hPcard]
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hcard hUcard
  have hPg : (P : Subgroup N).map ψ.toMonoidHom = (upperSL k).map (MulAut.conj g).toMonoidHom := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, hu, rfl⟩
      obtain ⟨c, rfl⟩ := mem_upperSL_iff.1 hu
      exact hg c
    · rw [hUcard, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_upperSL]
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := kˣ)
  set d₀ : SL(2, k) := g * diagSL μ * g⁻¹ with hd₀
  have hd₀P : d₀ ∈ normalizer (((P : Subgroup N).map ψ.toMonoidHom : Subgroup SL(2, k)) :
      Set SL(2, k)) := by
    rw [hPg]
    refine mem_normalizer_of_forall_conj_mem ?_
    rintro _ ⟨u, hu, rfl⟩
    have hu' : diagSL μ * u * (diagSL μ)⁻¹ ∈ upperSL k :=
      (mem_normalizer_iff.1 (torusSL_le_normalizer_upperSL (diagSL_mem_torusSL μ)) u).1 hu
    refine ⟨_, hu', ?_⟩
    show g * (diagSL μ * u * (diagSL μ)⁻¹) * g⁻¹ = d₀ * (g * u * g⁻¹) * d₀⁻¹
    simp only [hd₀]
    group
  let dN : N := ψ.symm d₀
  have hψd : ψ dN = d₀ := ψ.apply_symm_apply d₀
  refine ⟨(dN : M), dN.2, ?_, ?_, ?_⟩
  · have h1 : orderOf (dN : M) = orderOf d₀ := by
      rw [Subgroup.orderOf_coe]
      exact (MulEquiv.orderOf_eq ψ dN).symm.trans (by rw [hψd])
    have h2 : orderOf d₀ = orderOf μ := by
      have : d₀ = MulAut.conj g (diagSLHom μ) := by
        simp [hd₀, MulAut.conj_apply, diagSLHom_apply]
      rw [this, MulEquiv.orderOf_eq]
      exact orderOf_injective diagSLHom diagSL_injective μ
    rw [h1, h2]
    exact (odd_card_sub_one (k := k)).of_dvd_nat (by
      rw [← Nat.card_units]; exact orderOf_dvd_natCard μ)
  · refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    have hvP : v ∈ ((P : Subgroup N).map N.subtype) := hP ▸ hv
    obtain ⟨p, hp, rfl⟩ := hvP
    obtain ⟨p', hp', hp'e⟩ := (mem_normalizer_iff.1 hd₀P (ψ p)).1 ⟨p, hp, rfl⟩
    have hp'' : p' = dN * p * dN⁻¹ := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, hψd]
      exact hp'e
    rw [← hP]
    refine ⟨p', hp', ?_⟩
    rw [hp'']
    rfl
  · intro H hHV hdH
    have hH'P : H.subgroupOf N ≤ (P : Subgroup N) := by
      intro x hx
      have : (x : M) ∈ V := hHV hx
      rw [← hP] at this
      obtain ⟨p, hp, hpx⟩ := this
      have : p = x := Subtype.ext hpx
      rwa [← this]
    have hA₀ : (H.subgroupOf N).map ψ.toMonoidHom ≤
        (upperSL k).map (MulAut.conj g).toMonoidHom := by
      rw [← hPg]; exact Subgroup.map_mono hH'P
    have hdA₀ : d₀ ∈ normalizer (((H.subgroupOf N).map ψ.toMonoidHom : Subgroup SL(2, k)) :
        Set SL(2, k)) := by
      refine mem_normalizer_of_forall_conj_mem ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨dN * x * dN⁻¹, ?_, ?_⟩
      · have hx' : (x : M) ∈ H := hx
        show ((dN * x * dN⁻¹ : N) : M) ∈ H
        exact (mem_normalizer_iff.1 hdH _).1 hx'
      · show ψ (dN * x * dN⁻¹) = d₀ * ψ x * d₀⁻¹
        rw [map_mul, map_mul, map_inv, hψd]
    rcases eq_bot_or_eq_map_upperSL hμ g hA₀ hdA₀ with h0 | h1
    · left
      have h0' := (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 h0
      rw [eq_bot_iff]
      intro h hh
      have : (⟨h, hVN (hHV hh)⟩ : N) ∈ H.subgroupOf N := hh
      rw [h0', mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    · right
      rw [← hPg] at h1
      have h1' : H.subgroupOf N = (P : Subgroup N) :=
        Subgroup.map_injective ψ.injective h1
      refine le_antisymm hHV fun x hx => ?_
      have hx' : x ∈ ((P : Subgroup N).map N.subtype) := hP ▸ hx
      obtain ⟨p, hp, rfl⟩ := hx'
      rw [← h1'] at hp
      exact hp

end SL2

section Lift

theorem exists_odd_lift {A B : Type*} [Group A] [Finite A] [Group B] (π : A →* B)
    (Q : Subgroup A) {d : B} (hd : d ∈ Q.map π) (hodd : Odd (orderOf d)) :
    ∃ y ∈ Q, Odd (orderOf y) ∧ Subgroup.zpowers (π y) = Subgroup.zpowers d := by
  obtain ⟨m, hmQ, rfl⟩ := hd
  have hm0 : orderOf m ≠ 0 := (isOfFinOrder_of_finite m).orderOf_pos.ne'
  obtain ⟨a, o, ho, hao⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  refine ⟨m ^ (2 ^ a), Subgroup.pow_mem _ hmQ _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by positivity) (hao ▸ dvd_mul_right _ _), hao,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact ho
  · rw [map_pow]
    apply le_antisymm
    · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    · refine Subgroup.zpowers_le.2 ?_
      rw [mem_zpowers_pow_iff]
      exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hodd)

end Lift

section Bar

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure

variable {G : Type*} [Group G]

theorem mem_normalizer_iff_barMap {Z H : Subgroup G} (hZH : Z ≤ H)
    (hHN : H ≤ normalizer (Z : Set G)) {y : G} (hy : y ∈ normalizer (Z : Set G)) :
    y ∈ normalizer (H : Set G) ↔
      barMap Z ⟨y, hy⟩ ∈ normalizer ((barSub Z H : Subgroup (BarM Z)) : Set (BarM Z)) := by
  have key : ∀ m : ↥(normalizer (Z : Set G)),
      (barMap Z (⟨y, hy⟩ * m * ⟨y, hy⟩⁻¹) ∈ barSub Z H ↔ y * (m : G) * y⁻¹ ∈ H) := fun m => by
    rw [mem_barSub_iff hZH]
    rfl
  constructor
  · intro h
    rw [mem_normalizer_iff]
    intro b
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (normalizer (Z : Set G))) b
    have e : barMap Z ⟨y, hy⟩ * barMap Z m * (barMap Z ⟨y, hy⟩)⁻¹ =
        barMap Z (⟨y, hy⟩ * m * ⟨y, hy⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    change barMap Z m ∈ barSub Z H ↔ barMap Z ⟨y, hy⟩ * barMap Z m * (barMap Z ⟨y, hy⟩)⁻¹ ∈
      barSub Z H
    rw [e, key m, mem_barSub_iff hZH]
    exact mem_normalizer_iff.1 h (m : G)
  · intro h
    rw [mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ normalizer (Z : Set G)
    · have := mem_normalizer_iff.1 h (barMap Z ⟨g, hg⟩)
      have e : barMap Z ⟨y, hy⟩ * barMap Z ⟨g, hg⟩ * (barMap Z ⟨y, hy⟩)⁻¹ =
          barMap Z (⟨y, hy⟩ * ⟨g, hg⟩ * ⟨y, hy⟩⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e, key ⟨g, hg⟩, mem_barSub_iff hZH] at this
      exact this
    · have h1 : g ∉ H := fun hgH => hg (hHN hgH)
      have h2 : y * g * y⁻¹ ∉ H := fun hgH => hg (by
        have := mul_mem (mul_mem (inv_mem hy) (hHN hgH)) hy
        simpa [mul_assoc] using this)
      exact ⟨fun hgH => (h1 hgH).elim, fun hgH => (h2 hgH).elim⟩

theorem barSub_mono {Z H H' : Subgroup G} (h : H ≤ H') : barSub Z H ≤ barSub Z H' := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, mem_subgroupOf.2 (h (mem_subgroupOf.1 hm)), rfl⟩

end Bar

section Exist

open CFSG.LocalAnalysis.EvenBN.Common

variable {G : Type*} [Group G] [Finite G]

theorem exists_mem_prodFst_not_mem {K : Type} [Field K] [Fintype K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Fintype.card K = 2 ^ m) {N X X' S : Subgroup G}
    (ρ : N →* SL(2, K) × SL(2, K)) (hker : ρ.ker = X.subgroupOf N) (hSN : S ≤ N) (hXS : X ≤ S)
    (hS2 : IsPGroup 2 S) (hScard : Nat.card S = (2 ^ m) ^ 2 * Nat.card X)
    (hS : X ⊔ X' = S) (hX'N : X' ≤ normalizer (X : Set G)) :
    ∃ x ∈ X', x ∈ prodFst ρ ∧ x ∉ X := by
  have hXN : X ≤ N := hXS.trans hSN
  have hS2' : IsPGroup 2 (S.subgroupOf N) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  set R : Subgroup (SL(2, K) × SL(2, K)) := (S.subgroupOf N).map ρ with hR
  have hcard : Nat.card R = (2 ^ m) ^ 2 := by
    have h1 := card_map_mul_card_inf_ker ρ (S.subgroupOf N)
    have h2 : S.subgroupOf N ⊓ ρ.ker = X.subgroupOf N := by
      rw [hker]
      exact inf_of_le_right (fun x hx => mem_subgroupOf.2 (hXS (mem_subgroupOf.1 hx)))
    rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hScard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hR2 : IsPGroup 2 (R.map (MonoidHom.snd (SL(2, K)) (SL(2, K)))) :=
    (hS2'.map ρ).map _
  have hle := card_le_of_isPGroup_SL2 hm hK hR2
  have h1 := card_map_mul_card_inf_ker (MonoidHom.snd (SL(2, K)) (SL(2, K))) R
  rw [hcard] at h1
  have hgt : 1 < Nat.card (R ⊓ (MonoidHom.snd (SL(2, K)) (SL(2, K))).ker : Subgroup _) := by
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    by_contra hlt
    have hlt' := not_lt.1 hlt
    have hpos : 0 < Nat.card (R.map (MonoidHom.snd (SL(2, K)) (SL(2, K)))) := Nat.card_pos
    have h3 := Nat.mul_le_mul hle hlt'
    nlinarith
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot _).1 hgt)
  obtain ⟨hrR, hrker⟩ := mem_inf.1 r.2
  obtain ⟨s', hs', hs'r⟩ := hrR
  have hsS : (s' : G) ∈ S := hs'
  have hs2 : (ρ s').2 = 1 := by
    rw [hs'r]
    exact MonoidHom.mem_ker.1 hrker
  have hsΛ : (s' : G) ∈ prodFst ρ := (mem_prodFst_iff ρ).2 ⟨s'.2, hs2⟩
  have hsX : (s' : G) ∉ X := by
    intro hX
    apply hr1
    apply Subtype.ext
    have : s' ∈ ρ.ker := by rw [hker]; exact mem_subgroupOf.2 hX
    rw [MonoidHom.mem_ker.1 this] at hs'r
    exact hs'r.symm
  have hs' : (s' : G) ∈ ((X ⊔ X' : Subgroup G) : Set G) := by rw [hS]; exact hsS
  rw [coe_mul_of_right_le_normalizer_left X X' hX'N] at hs'
  obtain ⟨x₀, hx₀, x', hx', hxx⟩ := hs'
  refine ⟨x', hx', ?_, ?_⟩
  · have : x' = x₀⁻¹ * (s' : G) := by rw [← hxx]; group
    rw [this]
    exact mul_mem (inv_mem (le_prodFst hXN hker hx₀)) hsΛ
  · intro hx'X
    apply hsX
    rw [← hxx]
    exact mul_mem hx₀ hx'X

end Exist

section Core

open CFSG.LocalAnalysis.EvenBN.Common

variable {G : Type*} [Group G] {S₀ : Type*} [Group S₀]

theorem not_inf_centralizer_prodFst_le {N X F P : Subgroup G}
    (ρ : N →* S₀ × S₀) (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N)
    (hXN : X ≤ N) {t w : G} (htN : t ∈ normalizer (N : Set G))
    (hswap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (htX : t ∈ normalizer (X : Set G)) (htF : t ∈ normalizer (F : Set G))
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hFX : F ≤ X)
    (hPΛ : P ≤ prodFst ρ) (hPperf : ⁅P, P⁆ = P) (hPX : P ⊔ X = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P)
    (hwN : w ∈ N) {a₀ : S₀} (hw : ρ ⟨w, hwN⟩ = (a₀, a₀))
    (hwinv : w⁻¹ = w) (hXw : X ≤ F ⊔ F.map (MulAut.conj w⁻¹).toMonoidHom) (hXF : ¬ X ≤ F) :
    ¬ X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ≤ F := by
  intro hB
  have hNX : N ≤ normalizer (X : Set G) := le_normalizer_of_ker hXN hker
  have hXΛ : X ≤ prodFst ρ := le_prodFst hXN hker
  have hPN : P ≤ normalizer (X : Set G) := fun p hp => hNX (prodFst_le ρ (hPΛ hp))
  have htF' : ∀ f : G, f ∈ F ↔ t * f * t⁻¹ ∈ F := mem_normalizer_iff.1 htF
  have hXP : ∀ x ∈ X, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    have hQ : P.map (MulAut.conj x).toMonoidHom ≤ P := by
      refine hPmax _ ?_ ?_
      · rintro _ ⟨q, hq, rfl⟩
        exact mul_mem (mul_mem (hXΛ hx) (hPΛ hq)) (inv_mem (hXΛ hx))
      · rw [← Subgroup.map_commutator, hPperf]
    exact hQ ⟨p, hp, rfl⟩
  have hstep1 : ∀ x ∈ X, ∀ l ∈ prodFst ρ, x * l * x⁻¹ * l⁻¹ ∈ F := by
    intro x hx l hl
    have hl' : l ∈ ((P ⊔ X : Subgroup G) : Set G) := by rw [hPX]; exact hl
    rw [coe_mul_of_left_le_normalizer_right P X hPN] at hl'
    obtain ⟨p, hp, x₀, hx₀, rfl⟩ := hl'
    have hcX : x * (p * x⁻¹ * p⁻¹) ∈ X :=
      mul_mem hx ((mem_normalizer_iff.1 (hPN hp) x⁻¹).1 (inv_mem hx))
    have hcP : x * (p * x⁻¹ * p⁻¹) ∈ P := by
      have : x * (p * x⁻¹ * p⁻¹) = (x * p * x⁻¹) * p⁻¹ := by group
      rw [this]
      exact mul_mem (hXP x hx p hp) (inv_mem hp)
    have e1 : x₀ * x⁻¹ * x₀⁻¹ = x⁻¹ := by
      rw [hXab x₀ hx₀ x⁻¹ (inv_mem hx)]
      group
    have hcomm : x * (p * x₀) * x⁻¹ * (p * x₀)⁻¹ = x * (p * x⁻¹ * p⁻¹) := by
      calc x * (p * x₀) * x⁻¹ * (p * x₀)⁻¹ = x * p * (x₀ * x⁻¹ * x₀⁻¹) * p⁻¹ := by group
        _ = x * (p * x⁻¹ * p⁻¹) := by rw [e1]; group
    rw [hcomm]
    have hbX : t * (x * (p * x⁻¹ * p⁻¹)) * t⁻¹ ∈ X := (mem_normalizer_iff.1 htX _).1 hcX
    have hbP : t * (x * (p * x⁻¹ * p⁻¹)) * t⁻¹ ∈ P.map (MulAut.conj t).toMonoidHom :=
      ⟨_, hcP, rfl⟩
    have hPc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hPt
    have hb : t * (x * (p * x⁻¹ * p⁻¹)) * t⁻¹ ∈
        X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hbX, ?_⟩
      have hle : prodFst ρ ≤ centralizer ({t * (x * (p * x⁻¹ * p⁻¹)) * t⁻¹} : Set G) := by
        rw [← hPX]
        refine sup_le (fun p' hp' => ?_) (fun x' hx' => ?_)
        · rw [mem_centralizer_singleton_iff]
          exact (mem_centralizer_iff.1 (hPc hp') _ hbP).symm
        · rw [mem_centralizer_singleton_iff]
          exact hXab x' hx' _ hbX
      rw [mem_centralizer_iff]
      intro z hz
      exact mem_centralizer_singleton_iff.1 (hle hz)
    exact (htF' _).2 (hB hb)
  have hstep2 : ∀ l ∈ prodFst ρ, ∀ f ∈ F, l * f * l⁻¹ ∈ F := by
    intro l hl f hf
    have h1 := inv_mem (hstep1 f (hFX hf) l hl)
    have e : l * f * l⁻¹ = (f * l * f⁻¹ * l⁻¹)⁻¹ * f := by group
    rw [e]
    exact mul_mem h1 hf
  have hstep3 : ∀ l ∈ prodFst ρ, ∀ f ∈ F, (t * l * t⁻¹) * f * (t * l * t⁻¹)⁻¹ ∈ F := by
    intro l hl f hf
    have h1 : t⁻¹ * f * t ∈ F :=
      (htF' _).2 (by rwa [show t * (t⁻¹ * f * t) * t⁻¹ = f by group])
    have h2 := hstep2 l hl _ h1
    have h3 := (htF' _).1 h2
    have e : (t * l * t⁻¹) * f * (t * l * t⁻¹)⁻¹ = t * (l * (t⁻¹ * f * t) * l⁻¹) * t⁻¹ := by
      group
    rw [e]
    exact h3
  obtain ⟨l₀, hl₀⟩ := hρ (a₀, 1)
  have hl₀Λ : (l₀ : G) ∈ prodFst ρ :=
    (mem_prodFst_iff ρ).2 ⟨l₀.2, by simpa using congrArg Prod.snd hl₀⟩
  have hl₁N : t * (l₀ : G) * t⁻¹ ∈ N := (mem_normalizer_iff.1 htN l₀).1 l₀.2
  let l₁ : N := ⟨t * l₀ * t⁻¹, hl₁N⟩
  have hl₁ : ρ l₁ = (1, a₀) := by rw [hswap l₀ l₁ rfl, hl₀]; rfl
  have hw' : ρ (l₀ * l₁) = ρ ⟨w, hwN⟩ := by rw [map_mul, hl₀, hl₁, hw]; simp
  have hmem : (⟨w, hwN⟩ : N)⁻¹ * (l₀ * l₁) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hw', inv_mul_cancel]
  rw [hker, mem_subgroupOf] at hmem
  have hx₀ : w⁻¹ * ((l₀ : G) * (t * l₀ * t⁻¹)) ∈ X := hmem
  have hstep4 : ∀ f ∈ F, w * f * w⁻¹ ∈ F := by
    intro f hf
    have e : w * f * w⁻¹ = ((l₀ : G) * (t * l₀ * t⁻¹)) * f * ((l₀ : G) * (t * l₀ * t⁻¹))⁻¹ := by
      have hc := hXab _ hx₀ f (hFX hf)
      calc w * f * w⁻¹ = w * ((w⁻¹ * ((l₀ : G) * (t * l₀ * t⁻¹))) * f *
            (w⁻¹ * ((l₀ : G) * (t * l₀ * t⁻¹)))⁻¹) * w⁻¹ := by
            rw [hc]; group
        _ = _ := by group
    rw [e]
    have h1 := hstep3 l₀ hl₀Λ f hf
    have h2 := hstep2 l₀ hl₀Λ _ h1
    have e2 : ((l₀ : G) * (t * l₀ * t⁻¹)) * f * ((l₀ : G) * (t * l₀ * t⁻¹))⁻¹ =
        l₀ * ((t * l₀ * t⁻¹) * f * (t * l₀ * t⁻¹)⁻¹) * (l₀ : G)⁻¹ := by group
    rw [e2]
    exact h2
  have hFw : F.map (MulAut.conj w⁻¹).toMonoidHom ≤ F := by
    rintro _ ⟨f, hf, rfl⟩
    show w⁻¹ * f * w⁻¹⁻¹ ∈ F
    rw [hwinv]
    exact hstep4 f hf
  exact hXF (hXw.trans (sup_le le_rfl hFw))

theorem not_le_sup_inf_centralizer_prodFst {N X X' F S A : Subgroup G}
    (ρ : N →* S₀ × S₀)
    (hXX' : X ⊓ X' = F) (hXS : X ≤ S) (hX'S : X' ≤ S) (hSX' : S ≤ normalizer (X' : Set G))
    (hFS : ∀ f ∈ F, ∀ s ∈ S, s * f = f * s) (hAX : A ≤ X)
    (hCA : ∀ x ∈ X', (∀ a ∈ A, x * a = a * x) → x ∈ F)
    {x₁ : G} (hx₁ : x₁ ∈ X') (hx₁Λ : x₁ ∈ prodFst ρ) (hx₁X : x₁ ∉ X) :
    ¬ X ≤ X' ⊔ (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G)) := by
  intro hX
  apply hx₁X
  have hFX : F ≤ X := hXX' ▸ inf_le_left
  refine hFX (hCA x₁ hx₁ fun a ha => ?_)
  have haX : a ∈ X := hAX ha
  have hYN : X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ≤ normalizer (X' : Set G) :=
    inf_le_left.trans (hXS.trans hSX')
  have ha' : a ∈ ((X' ⊔ (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G)) : Subgroup G) :
      Set G) := hX haX
  rw [coe_mul_of_right_le_normalizer_left X' _ hYN] at ha'
  obtain ⟨u, hu, b, hb, rfl⟩ := ha'
  have huX : u ∈ X := by
    have := mul_mem haX (inv_mem (mem_inf.1 hb).1)
    rwa [mul_inv_cancel_right] at this
  have huF : u ∈ F := hXX' ▸ mem_inf.2 ⟨huX, hu⟩
  have h1 : x₁ * u = u * x₁ := hFS u huF x₁ (hX'S hx₁)
  have h2 : x₁ * b = b * x₁ := mem_centralizer_iff.1 (mem_inf.1 hb).2 x₁ hx₁Λ
  calc x₁ * (u * b) = (x₁ * u) * b := by group
    _ = (u * x₁) * b := by rw [h1]
    _ = u * (x₁ * b) := by group
    _ = u * (b * x₁) := by rw [h2]
    _ = u * b * x₁ := by group

end Core

section Master

open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (ProductAlternative FieldAlternative
  xor_of_exactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)

theorem master {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {m : ℕ}
    {N X X' S F A A' P Nc : Subgroup G}
    (ρ : N →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N)
    (hXN : X ≤ N) {t w w₀ : G} (htN : t ∈ normalizer (N : Set G))
    (hswap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (htX : t ∈ normalizer (X : Set G)) (htF : t ∈ normalizer (F : Set G))
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hFX : F ≤ X)
    (hPΛ : P ≤ prodFst ρ) (hPperf : ⁅P, P⁆ = P) (hPX : P ⊔ X = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P)
    (hwN : w ∈ N) {a₀ : SL(2, K)} (hw : ρ ⟨w, hwN⟩ = (a₀, a₀)) (hww₀ : w = w₀)
    (hw₀inv : w₀⁻¹ = w₀) (hXw : X ≤ F ⊔ F.map (MulAut.conj w₀⁻¹).toMonoidHom)
    (hq : Nat.card K = 2 ^ m) (hm : 2 ≤ m)
    (hXc : Nat.card X = Nat.card K ^ 6) (hFc : Nat.card F = Nat.card K ^ 4)
    (hSc : Nat.card S = Nat.card K ^ 8)
    (hSN : S ≤ N) (hXS : X ≤ S) (hX'S : X' ≤ S) (hSX' : S ≤ normalizer (X' : Set G))
    (hSX : S ≤ normalizer (X : Set G)) (hS : X ⊔ X' = S)
    (hXX' : X ⊓ X' = F) (hFS : ∀ f ∈ F, ∀ s ∈ S, s * f = f * s) (hAX : A ≤ X) (hAA' : A' = A)
    (hCA : X' ⊓ centralizer (A' : Set G) = F)
    (hnormX : ∀ y : G, y ∈ normalizer (S : Set G) → y ∈ normalizer (X' : Set G) →
      y ∈ normalizer (X : Set G))
    (hnormΛ : ∀ y : G, y ∈ normalizer (X : Set G) → Odd (orderOf y) →
      y ∈ normalizer ((prodFst ρ : Subgroup G) : Set G))
    {B : Subgroup (BarM X')} {α : B ≃* SL(2, K)} {τ : BarM X'}
    (hex : ExactClosure B α τ (barSub X' S) m)
    (hNbar : normalClosure (B : Set (BarM X')) ≤ barSub X' Nc) :
    ProductAlternative B α τ := by
  classical
  by_contra hnP
  subst hww₀
  subst hAA'
  have hxor := xor_of_exactClosure hex
  obtain ⟨-, -, hVN, hSyl, -⟩ := hex
  have hF : FieldAlternative B τ m := by
    rcases hxor with ⟨hP', -⟩ | ⟨hF', -⟩
    · exact absurd hP' hnP
    · exact hF'
  obtain ⟨k₂, _, _, hk₂, ψ, -, -⟩ := hF
  have hk₂' : Nat.card k₂ = 2 ^ (2 * m) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
  haveI : CharP k₂ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk₂'
  have hq4 : 4 ≤ Nat.card K := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hXF : ¬ X ≤ F := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hXc, hFc] at h1
    have h2 := Nat.pow_lt_pow_right (a := Nat.card K) (by omega : 1 < Nat.card K)
      (by norm_num : 4 < 6)
    omega
  have hobs1 : ¬ X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ≤ F :=
    not_inf_centralizer_prodFst_le ρ hρ hker hXN htN hswap htX htF hXab hFX hPΛ hPperf hPX hPt
      hPmax hwN hw hw₀inv hXw hXF
  have hobs2 : ¬ X ≤ X' ⊔ (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G)) := by
    letI : Fintype K := Fintype.ofFinite K
    have hK : Fintype.card K = 2 ^ m := by
      rw [← Nat.card_eq_fintype_card]
      exact hq
    have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 8 * m) (by
      rw [hSc, hq, ← pow_mul, mul_comm])
    have hScard : Nat.card S = (2 ^ m) ^ 2 * Nat.card X := by
      rw [hSc, hXc, hq]
      ring
    obtain ⟨x₁, hx₁, hx₁Λ, hx₁X⟩ := exists_mem_prodFst_not_mem (by omega) hK ρ hker hSN hXS hS2
      hScard hS (hX'S.trans hSX)
    refine not_le_sup_inf_centralizer_prodFst ρ hXX' hXS hX'S hSX' hFS hAX ?_ hx₁ hx₁Λ hx₁X
    intro x hx hc
    exact hCA.le ⟨hx, mem_centralizer_iff.mpr fun a ha => (hc a ha).symm⟩
  obtain ⟨d, hdN, hdodd, hdV, hdmin⟩ := exists_odd_torus ψ hVN hSyl
  obtain ⟨y, -, hyodd, hyz⟩ := exists_odd_lift (barMap X') (Nc.subgroupOf (normalizer (X' : Set G)))
    (hNbar hdN) hdodd
  have hyN : (y : G) ∈ normalizer (X' : Set G) := y.2
  have hyodd' : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe]
    exact hyodd
  have hyd : barMap X' y ∈ Subgroup.zpowers d := by
    rw [← hyz]
    exact Subgroup.mem_zpowers _
  have hdy : d ∈ Subgroup.zpowers (barMap X' y) := by
    rw [hyz]
    exact Subgroup.mem_zpowers _
  have hyV : barMap X' y ∈ normalizer ((barSub X' S : Subgroup (BarM X')) : Set (BarM X')) :=
    (Subgroup.zpowers_le.2 hdV) hyd
  have hyS : (y : G) ∈ normalizer (S : Set G) :=
    (mem_normalizer_iff_barMap hX'S hSX' hyN).2 hyV
  have hyX : (y : G) ∈ normalizer (X : Set G) := hnormX y hyS hyN
  have hyΛ : (y : G) ∈ normalizer ((prodFst ρ : Subgroup G) : Set G) := hnormΛ y hyX hyodd'
  have hYX : X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ≤ X := inf_le_left
  have hYN : X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ≤ normalizer (X' : Set G) :=
    hYX.trans (hXS.trans hSX')
  have hHN : X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X' ≤ normalizer (X' : Set G) :=
    sup_le hYN le_normalizer
  have hyYX' : (y : G) ∈ normalizer ((X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X' :
      Subgroup G) : Set G) :=
    mem_normalizer_sup (mem_normalizer_inf_centralizer hyX hyΛ) hyN
  have hyH : barMap X' y ∈ normalizer ((barSub X'
      (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X') : Subgroup (BarM X')) :
        Set (BarM X')) :=
    (mem_normalizer_iff_barMap le_sup_right hHN hyN).1 hyYX'
  have hdH : d ∈ normalizer ((barSub X'
      (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X') : Subgroup (BarM X')) :
        Set (BarM X')) :=
    (Subgroup.zpowers_le.2 hyH) hdy
  have hHV : barSub X' (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X') ≤
      barSub X' S :=
    barSub_mono (sup_le (hYX.trans hXS) hX'S)
  rcases hdmin _ hHV hdH with hH0 | hHV'
  ·
    apply hobs1
    intro g hg
    have hgN := hYN hg
    have h1 : barMap X' ⟨g, hgN⟩ ∈ barSub X'
        (X ⊓ centralizer ((prodFst ρ : Subgroup G) : Set G) ⊔ X') :=
      (mem_barSub_iff le_sup_right ⟨g, hgN⟩).2 (mem_sup_left hg)
    rw [hH0, Subgroup.mem_bot] at h1
    exact hXX'.le ⟨hYX hg, barMap_eq_one_iff.1 h1⟩
  ·
    apply hobs2
    intro x hx
    have hxN : x ∈ normalizer (X' : Set G) := hSX' (hXS hx)
    have h1 : barMap X' ⟨x, hxN⟩ ∈ barSub X' S := (mem_barSub_iff hX'S ⟨x, hxN⟩).2 (hXS hx)
    rw [← hHV'] at h1
    have h2 := (mem_barSub_iff le_sup_right ⟨x, hxN⟩).1 h1
    rwa [sup_comm] at h2

end Master

end SwapAxis

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.SymplecticFourStandard
open GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
  BothTrivialClosure BothTrivialLayer BothTrivialRankOne BothTrivialSlice BothTrivialField
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.EvenBN.Common (prodFst prodFstHom)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (ProductAlternative FieldAlternative)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialProductAxis
open scoped MatrixGroups

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)
set_option quotPrecheck false in
local notation "𝐒" => (𝐗[Axis.one] ⊔ 𝐗[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐊[" i "]" => barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))
set_option quotPrecheck false in
local notation "𝐍𝐂[" i "]" => closure {x : G | ∃ g ∈ normalizer (𝐗[i] : Set G),
  ∃ y ∈ (L ⊓ centralizer (𝐔[i] : Set G) : Subgroup G) ⊔ 𝐗[i], x = g⁻¹ * y * g}

theorem productAlternative_swap (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis)
    (ρ : 𝐍𝐂[i] →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = 𝐗[i].subgroupOf 𝐍𝐂[i])
    (hswap : ∀ x y : 𝐍𝐂[i], (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap)
    (β : SL(2, K) ≃* SL(2, K))
    (hβ : ∀ (M : SL(2, K)) (hM : ((φ.symm (sHom K i M) : L) : G) ∈ 𝐍𝐂[i]),
      ρ ⟨_, hM⟩ = (β M, β M))
    {P : Subgroup G} (hPΛ : P ≤ prodFst ρ) (hP : ⁅P, P⁆ = P) (hPX : P ⊔ 𝐗[i] = prodFst ρ)
    (hPt : ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hPmax : ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P)
    (α' : 𝐊[i.swap] ≃* SL(2, K))
    (hex' : ExactClosure 𝐊[i.swap] α' (barMap 𝐗[i.swap] ⟨t, t_mem_normalizer_X h i.swap⟩)
      (barSub 𝐗[i.swap] 𝐒) n) :
    ProductAlternative 𝐊[i.swap] α' (barMap 𝐗[i.swap] ⟨t, t_mem_normalizer_X h i.swap⟩) := by
  have hrM := sup_le_NC (t := t) i (mem_sup_left (s_mem_CU h i (weylSL2 K)))
  exact SwapAxis.master (t := t) ρ hρ hker (le_sup_right.trans (sup_le_NC i))
    (SwapAxis.mem_normalizer_of_forall_conj_mem fun z hz =>
      conj_mem_NC i (t_mem_normalizer_X h i) hz)
    hswap (t_mem_normalizer_X h i) (H_le_normalizer_F h t_mem_H)
    (fun x hx y hy => comm_of_mul_self (fun _ hz => X_mul_self h hbt i hz) hx hy) le_sup_left
    hPΛ hP hPX hPt hPmax hrM (hβ (weylSL2 K) hrM)
    (congrArg (fun z => ((φ.symm z : L) : G)) (sHom_weylSL2 i)) (FullCenterWeyl.w_inv i) le_rfl
    h.setup.card_K h.setup.two_le (card_X h i) (card_F h) (BothTrivialHeisenberg.card_S h hbt)
    (S_le_NC h hbt i) (X_le_S i) (X_le_S i.swap) (S_le_normalizer_X h hbt i.swap)
    (S_le_normalizer_X h hbt i) (X_sup_X_swap i) (X_inf_X_swap h i)
    (fun f hf s hs => F_comm_S h hbt hf hs) (A_le_X h i)
    (congrArg (fun j => pull φ (rootA K j)) (swap_swap_axis i)) (X_inf_centralizer h hbt i.swap)
    (fun y hyS hyX => mem_normalizer_X_of_mem_normalizer_S h hbt i ρ hρ hker hswap β hβ hPΛ hP hPX
      hPt hPmax hyS hyX)
    (fun y hyX hyodd => mem_normalizer_prodFst_of_odd h hbt i ρ hρ hker hswap hyX hyodd)
    hex' (barSub_NC_eq h hbt i.swap).ge

end Setting

end BothTrivialProduct

end CFSG.LocalAnalysis.EvenBN.Sp4
