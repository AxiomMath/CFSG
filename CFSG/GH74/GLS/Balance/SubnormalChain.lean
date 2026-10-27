module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup
open scoped commutatorElement

theorem le_of_commutator_eq_of_isSubnormal_aux {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.IsSubnormal) :
    ∀ u ∈ H, ∀ T : Subgroup G, ⁅T, zpowers u⁆ = T → T ≤ H := by
  induction hH with
  | top => intro u _ T _; exact le_top
  | step H K h_le hSubn hN ih =>
    intro u hu T hT
    have hTK : T ≤ K := ih u (h_le hu) T hT
    have hKH := (Subgroup.normal_subgroupOf_iff h_le).mp hN
    rw [← hT]
    refine Subgroup.commutator_le.mpr (fun t ht a ha => ?_)
    have haH : a ∈ H := (Subgroup.zpowers_le.mpr hu) ha
    have h1 : t * a * t⁻¹ ∈ H := hKH a t haH (hTK ht)
    have e : ⁅t, a⁆ = (t * a * t⁻¹) * a⁻¹ := commutatorElement_def t a
    rw [e]
    exact mul_mem h1 (inv_mem haH)

theorem le_of_commutator_eq_of_isSubnormal {X : Type*} [Group X] {C V : Subgroup X} (hVC : V ≤ C)
    (hV : (V.subgroupOf C).IsSubnormal) {u : X} (hu : u ∈ V) {T : Subgroup X} (hTC : T ≤ C)
    (hT : ⁅T, zpowers u⁆ = T) : T ≤ V := by
  have hu' : (⟨u, hVC hu⟩ : C) ∈ V.subgroupOf C := hu
  have key := le_of_commutator_eq_of_isSubnormal_aux hV ⟨u, hVC hu⟩ hu' (T.subgroupOf C) ?_
  · intro t ht
    have := key (show (⟨t, hTC ht⟩ : C) ∈ T.subgroupOf C from ht)
    exact this
  · apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTC, MonoidHom.map_zpowers]
    exact hT

theorem centralizes_of_centralizes_fixed {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsPGroup 2 T) {x u : X} (hx : ∃ k : ℕ, orderOf x = 2 ^ k) (hu : ¬ 2 ∣ orderOf u)
    (hxu : x * u = u * x) (hxT : x ∈ normalizer (T : Set X)) (huT : u ∈ normalizer (T : Set X))
    (h : ∀ t ∈ T, x * t = t * x → u * t = t * u) : ∀ t ∈ T, u * t = t * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hx
  have hB : IsPGroup 2 (zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hk]
    exact ⟨k, rfl⟩
  have hA : ¬ 2 ∣ Nat.card (zpowers u) := by rw [Nat.card_zpowers]; exact hu
  let α : zpowers u →* MulAut T :=
    T.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr huT))
  let β : zpowers x →* MulAut T :=
    T.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hxT))
  have hαv : ∀ (a : zpowers u) (t : T), ((α a t : T) : X) = (a : X) * t * (a : X)⁻¹ := fun a t => rfl
  have hβv : ∀ (b : zpowers x) (t : T), ((β b t : T) : X) = (b : X) * t * (b : X)⁻¹ := fun b t => rfl
  have hcommute : ∀ (a : zpowers u) (b : zpowers x), (a : X) * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((Commute.symm (show Commute x u from hxu)).zpow_zpow i j).eq
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    ext t
    simp only [MulAut.mul_apply]
    rw [hαv, hβv, hβv, hαv]
    have := hcommute a b
    calc (a : X) * ((b : X) * t * (b : X)⁻¹) * (a : X)⁻¹
        = ((a : X) * b) * t * ((a : X) * b)⁻¹ := by group
      _ = ((b : X) * a) * t * ((b : X) * a)⁻¹ := by rw [this]
      _ = (b : X) * ((a : X) * t * (a : X)⁻¹) * (b : X)⁻¹ := by group
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    have hxr : x * (r : X) = (r : X) * x := by
      have := congrArg Subtype.val (hr ⟨x, Subgroup.mem_zpowers x⟩)
      rw [hβv] at this
      calc x * (r : X) = x * r * x⁻¹ * x := by group
        _ = (r : X) * x := by rw [this]
    have hur := h r r.2 hxr
    apply Subtype.ext
    rw [hαv]
    obtain ⟨a, ha⟩ := a
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have : Commute u (r : X) := hur
    have h2 : Commute (u ^ i) (r : X) := this.zpow_left i
    show u ^ i * r * (u ^ i)⁻¹ = r
    rw [h2.eq]; group
  intro t ht
  have h1 := CFSG.GroupTheory.thompson_A_times_B (p := 2) (R := T) (A := zpowers u)
    (B := zpowers x) hT hA hB α β hcomm hfix ⟨u, Subgroup.mem_zpowers u⟩
  have h2 := congrArg (fun φ : MulAut T => ((φ ⟨t, ht⟩ : T) : X)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : u * t * u⁻¹ = t := h2
  calc u * t = u * t * u⁻¹ * u := by group
    _ = t * u := by rw [h3]

theorem commutator_commutator_eq_of_three {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {w : G} (hw : ∃ k : ℕ, orderOf w = 3 ^ k)
    (hwT : w ∈ normalizer (T : Set G)) :
    ⁅⁅T, zpowers w⁆, zpowers w⁆ = ⁅T, zpowers w⁆ := by
  obtain ⟨k, hk⟩ := hw
  have hA : IsPGroup 3 (zpowers w) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hk]
    exact ⟨k, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨m, hm⟩ := hT.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m (by norm_num)
  exact CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3 Nat.prime_three
    (zpowers w) T hA (Subgroup.zpowers_le.mpr hwT) hcop

end CFSG.GH74.GLS.Balance
