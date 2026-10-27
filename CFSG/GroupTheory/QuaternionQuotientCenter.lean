module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.GroupTheory

open Subgroup QuaternionGroup

variable {G : Type*} [Group G]

theorem quaternionGroup_two_eq_one_or_eq_a_two_of_commute (x : QuaternionGroup 2)
    (hx : ∀ y, x * y = y * x) : x = 1 ∨ x = a 2 := by
  revert x
  decide

private theorem quaternionGroup_two_a_two_central (x : QuaternionGroup 2) :
    a 2 * x = x * a 2 := by
  revert x
  decide

theorem quaternionGroup_two_apply_a_two (α : QuaternionGroup 2 →* QuaternionGroup 2)
    (h3 : ∀ x, α (α (α x)) = x) : α (a 2) = a 2 := by
  have hinj : Function.Injective α := fun x y hxy => by
    calc x = α (α (α x)) := (h3 x).symm
      _ = α (α (α y)) := by rw [hxy]
      _ = y := h3 y
  have hcomm : ∀ y, α (a 2) * y = y * α (a 2) := by
    intro y
    obtain ⟨z, rfl⟩ := Finite.surjective_of_injective hinj y
    calc α (a 2) * α z = α (a 2 * z) := (map_mul α _ _).symm
      _ = α (z * a 2) := by rw [quaternionGroup_two_a_two_central]
      _ = α z * α (a 2) := map_mul α _ _
  rcases quaternionGroup_two_eq_one_or_eq_a_two_of_commute (α (a 2)) hcomm with h | h
  · exact absurd (hinj (by rw [h, map_one] : α (a 2) = α 1)) (by decide)
  · exact h

private def q8Map (p q : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => p ^ k.val
  | .xa k => q * p ^ k.val

private theorem q8Map_check : ∀ p q : QuaternionGroup 2,
    (∀ g h, q8Map p q (g * h) = q8Map p q g * q8Map p q h) →
    (∀ g, q8Map p q (q8Map p q (q8Map p q g)) = g) → (∃ g, q8Map p q g ≠ g) →
    ∀ x, x * q8Map p q x * q8Map p q (q8Map p q x) = 1 ∨
      x * q8Map p q x * q8Map p q (q8Map p q x) = a 2 := by
  decide

theorem quaternionGroup_two_mul_apply_mul_apply_apply
    (α : QuaternionGroup 2 →* QuaternionGroup 2) (h3 : ∀ x, α (α (α x)) = x)
    (hne : ∃ x, α x ≠ x) (x : QuaternionGroup 2) :
    x * α x * α (α x) = 1 ∨ x * α x * α (α x) = a 2 := by
  have hmap : ∀ g, α g = q8Map (α (a 1)) (α (xa 0)) g := by
    intro g
    cases g with
    | a k =>
      have h : (a k : QuaternionGroup 2) = a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      calc α (a k) = α (a 1 ^ k.val) := by rw [h]
        _ = α (a 1) ^ k.val := map_pow ..
        _ = q8Map (α (a 1)) (α (xa 0)) (a k) := rfl
    | xa k =>
      have h : (xa k : QuaternionGroup 2) = xa 0 * a 1 ^ k.val := by
        rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val, QuaternionGroup.xa_mul_a,
          zero_add]
      calc α (xa k) = α (xa 0 * a 1 ^ k.val) := by rw [h]
        _ = α (xa 0) * α (a 1) ^ k.val := by rw [map_mul, map_pow]
        _ = q8Map (α (a 1)) (α (xa 0)) (xa k) := rfl
  have hhom : ∀ g h, q8Map (α (a 1)) (α (xa 0)) (g * h) =
      q8Map (α (a 1)) (α (xa 0)) g * q8Map (α (a 1)) (α (xa 0)) h := by
    intro g h
    rw [← hmap, ← hmap, ← hmap, map_mul]
  have hcube : ∀ g, q8Map (α (a 1)) (α (xa 0))
      (q8Map (α (a 1)) (α (xa 0)) (q8Map (α (a 1)) (α (xa 0)) g)) = g := by
    intro g
    rw [← hmap, ← hmap, ← hmap, h3]
  have hnid : ∃ g, q8Map (α (a 1)) (α (xa 0)) g ≠ g := by
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, fun h => hg (by rw [hmap]; exact h)⟩
  have hcheck := q8Map_check (α (a 1)) (α (xa 0)) hhom hcube hnid x
  simpa only [← hmap] using hcheck

theorem exists_quaternionGroup_two_endomorphism_of_conj {T N : Subgroup G} (hNT : N ≤ T)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    ∃ α : QuaternionGroup 2 →* QuaternionGroup 2,
      (∀ g : ↥T, π ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = α (π g)) ∧ (∀ x, α (α (α x)) = x) ∧
        ∃ x, α x ≠ x := by
  classical
  let cT : ↥T →* ↥T :=
    { toFun := fun g => ⟨ρ * g * ρ⁻¹, hρT g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcT_coe : ∀ g : ↥T, (cT g : G) = ρ * g * ρ⁻¹ := fun _ => rfl
  have hNofker : ∀ g : ↥T, g ∈ π.ker → (g : G) ∈ N := by
    intro g hg
    simpa only [hker, Subgroup.mem_subgroupOf] using hg
  have hfker : π.ker ≤ (π.comp cT).ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    change π (cT g) = 1
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    simpa only [hcT_coe] using hρN g (hNofker g hg)
  let α : QuaternionGroup 2 →* QuaternionGroup 2 :=
    π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
      ⟨π.comp cT, hfker⟩
  have hαπ : ∀ g : ↥T, α (π g) = π (cT g) := by
    intro g
    exact MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨π.comp cT, hfker⟩ g
  have hπn : π ⟨ρ ^ 3, hNT hρ3⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact hρ3
  refine ⟨α, fun g => (hαπ g).symm, ?_, ?_⟩
  · intro x
    obtain ⟨g, rfl⟩ := hπ x
    rw [hαπ, hαπ, hαπ]
    have h3c : cT (cT (cT g)) = ⟨ρ ^ 3, hNT hρ3⟩ * g * ⟨ρ ^ 3, hNT hρ3⟩⁻¹ := by
      apply Subtype.ext
      simp only [hcT_coe, Subgroup.coe_mul, Subgroup.coe_inv, pow_three]
      group
    rw [h3c, map_mul, map_mul, map_inv, hπn]
    group
  · obtain ⟨g, hgT, hg⟩ := hρ
    refine ⟨π ⟨g, hgT⟩, fun hα => hg ?_⟩
    have hα' : π (cT ⟨g, hgT⟩) = π ⟨g, hgT⟩ := by
      rw [← hαπ]
      exact hα
    have hmem : cT ⟨g, hgT⟩ * ⟨g, hgT⟩⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, hα', map_inv, mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    simpa only [hcT_coe, Subgroup.coe_mul, Subgroup.coe_inv] using hmem

theorem eq_one_of_quaternion_quotient_of_conj_invariant {T N : Subgroup G} (hNT : N ≤ T)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N)
    {A : Type*} [Group A] (hA : ∀ a : A, a * a = 1) (ψ : ↥T →* A)
    (hψN : ∀ g : ↥T, (g : G) ∈ N → ψ g = 1)
    (hψρ : ∀ g : ↥T, ψ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = ψ g) (g : ↥T) : ψ g = 1 := by
  classical
  obtain ⟨α, hα, hα3, hαne⟩ :=
    exists_quaternionGroup_two_endomorphism_of_conj hNT π hπ hker hρT hρN hρ3 hρ
  let cT : ↥T →* ↥T :=
    { toFun := fun g => ⟨ρ * g * ρ⁻¹, hρT g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcT_coe : ∀ g : ↥T, (cT g : G) = ρ * g * ρ⁻¹ := fun _ => rfl
  have hψρ' : ∀ g : ↥T, ψ (cT g) = ψ g := fun g => hψρ g
  have hα' : ∀ g : ↥T, π (cT g) = α (π g) := fun g => hα g
  let y : ↥T := g * cT g * cT (cT g)
  have hψy : ψ y = ψ g := by
    have h1 : ψ y = ψ g * ψ g * ψ g := by
      simp only [y, map_mul, hψρ']
    rw [h1, hA (ψ g), one_mul]
  have hπy : π y = 1 ∨ π y = a 2 := by
    have h1 : π y = π g * α (π g) * α (α (π g)) := by
      simp only [y, map_mul, hα']
    rw [h1]
    exact quaternionGroup_two_mul_apply_mul_apply_apply α hα3 hαne (π g)
  have ha11 : (a 1 * a 1 : QuaternionGroup 2) = a 2 := by decide
  rcases hπy with h1 | h2
  · have hyN : (y : G) ∈ N := by
      rw [← Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      exact h1
    rw [← hψy]
    exact hψN y hyN
  · obtain ⟨s, hs⟩ := hπ (a 1)
    have hs2 : π (y * (s * s)⁻¹) = 1 := by
      have h1 : π (s * s) = a 2 := by
        rw [map_mul, hs, ha11]
      have hmul : π (y * (s * s)⁻¹) = π y * (π (s * s))⁻¹ := by
        rw [map_mul, map_inv]
      rw [hmul, h1, h2]
      simp
    have hyN : ((y * (s * s)⁻¹ : ↥T) : G) ∈ N := by
      rw [← Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      exact hs2
    rw [← hψy]
    have h1 : ψ (y * (s * s)⁻¹ * (s * s)) = 1 := by
      rw [map_mul, hψN _ hyN, one_mul, map_mul, hA (ψ s)]
    rwa [show y * (s * s)⁻¹ * (s * s) = y from by group] at h1

theorem card_le_two_of_isPGroup_of_card_eq_four {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 4) {R : Subgroup (MulAut Q)} (hR : IsPGroup 2 R) :
    Nat.card R ≤ 2 := by
  classical
  let g : MulAut Q →* Equiv.Perm {u : Q // u ≠ 1} :=
    { toFun := fun α => Equiv.Perm.subtypePerm α.toEquiv fun u => map_ne_one_iff α α.injective
      map_one' := by ext; rfl
      map_mul' := fun α β => by ext; rfl }
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro α hα
    refine MulEquiv.ext fun u => ?_
    by_cases hu : u = 1
    · rw [hu, map_one, MulAut.one_apply]
    · have := congrArg (fun π : Equiv.Perm {u : Q // u ≠ 1} => (π ⟨u, hu⟩ : Q)) hα
      simpa [g] using this
  have h3 : Nat.card {u : Q // u ≠ 1} = 3 := by
    have : Fintype Q := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hQ]
  have hfin : Finite (MulAut Q) := Finite.of_injective g hginj
  have hdvd : Nat.card R ∣ 6 := by
    have h1 : Nat.card (MulAut Q) = Nat.card g.range :=
      Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
    have h2 : Nat.card g.range ∣ Nat.card (Equiv.Perm {u : Q // u ≠ 1}) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm, h3] at h2
    exact (Subgroup.card_subgroup_dvd_card R).trans (h1 ▸ h2)
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rw [hk] at hdvd ⊢
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · exfalso
    have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ k + 2)).trans hdvd
    omega

theorem eq_one_of_mulAut_of_card_eq_four_of_quaternion_quotient {T N : Subgroup G}
    (hNT : N ≤ T) (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T) (hT2 : IsPGroup 2 ↥T)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N)
    {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) (Φ : ↥T →* MulAut Q)
    (hΦN : ∀ g : ↥T, (g : G) ∈ N → Φ g = 1) (R : MulAut Q)
    (hΦρ : ∀ g : ↥T, Φ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = R * Φ g * R⁻¹) (g : ↥T) : Φ g = 1 := by
  classical
  have hsurj : Function.Surjective Φ.rangeRestrict := by
    intro x
    obtain ⟨t, ht⟩ := x.2
    exact ⟨t, Subtype.ext ht⟩
  have hH2 : IsPGroup 2 ↥(Φ.range) := hT2.of_surjective Φ.rangeRestrict hsurj
  have hHcard : Nat.card ↥(Φ.range) ≤ 2 :=
    card_le_two_of_isPGroup_of_card_eq_four hQ hH2
  have hA : ∀ a : ↥(Φ.range), a * a = 1 := by
    intro a
    have hle : orderOf a ≤ 2 := (_root_.orderOf_le_card (x := a)).trans hHcard
    have hpos : 0 < orderOf a := orderOf_pos a
    have h2 : a ^ 2 = 1 := by
      rcases (by omega : orderOf a = 1 ∨ orderOf a = 2) with h | h
      · rw [orderOf_eq_one_iff.mp h]
        simp
      · rw [← orderOf_dvd_iff_pow_eq_one, h]
    simpa [pow_two] using h2
  have huniq : ∀ a b : ↥(Φ.range), a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb
    have hsub : Subsingleton {x : ↥(Φ.range) // x ≠ 1} := by
      rw [← Finite.card_le_one_iff_subsingleton]
      have h1 : Nat.card {x : ↥(Φ.range) // x ≠ 1} = Nat.card ↥(Φ.range) - 1 := by
        have : Fintype ↥(Φ.range) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
          ← Nat.card_eq_fintype_card]
      have hpos : 0 < Nat.card ↥(Φ.range) := Nat.card_pos
      omega
    have hEq : (⟨a, ha⟩ : {x : ↥(Φ.range) // x ≠ 1}) = ⟨b, hb⟩ := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp hEq
  have hψN : ∀ h : ↥T, (h : G) ∈ N → Φ.rangeRestrict h = 1 := by
    intro h hh
    apply Subtype.ext
    simpa using hΦN h hh
  have hψρ : ∀ h : ↥T,
      Φ.rangeRestrict ⟨ρ * h * ρ⁻¹, hρT h h.2⟩ = Φ.rangeRestrict h := by
    intro h
    by_cases hh : Φ.rangeRestrict h = 1
    · have hh' : Φ h = 1 := by simpa using congrArg Subtype.val hh
      apply Subtype.ext
      change Φ ⟨ρ * h * ρ⁻¹, hρT h h.2⟩ = Φ h
      rw [hΦρ h, hh']
      simp
    · have hd : Φ.rangeRestrict ⟨ρ * h * ρ⁻¹, hρT h h.2⟩ ≠ 1 := by
        intro hconj
        apply hh
        have h' : Φ ⟨ρ * h * ρ⁻¹, hρT h h.2⟩ = 1 := by
          simpa using congrArg Subtype.val hconj
        rw [hΦρ h] at h'
        have h'' := congrArg (fun x => R⁻¹ * x * R) h'
        apply Subtype.ext
        simpa [mul_assoc] using h''
      exact huniq _ _ hd hh
  have hψ := eq_one_of_quaternion_quotient_of_conj_invariant hNT π hπ hker hρT hρN hρ3 hρ
    hA Φ.rangeRestrict hψN hψρ g
  simpa using congrArg Subtype.val hψ

private theorem conj_inv_mem_of_pow_three_mem {N : Subgroup G} {ρ : G}
    (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρ3 : ρ ^ 3 ∈ N) :
    ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := by
  intro n hn
  have h1 : ρ * n * ρ⁻¹ ∈ N := hρN n hn
  have h2 : ρ ^ 2 * n * (ρ ^ 2)⁻¹ ∈ N := by
    have := hρN _ h1
    simpa [pow_two, mul_assoc] using this
  have h3 : (ρ ^ 3)⁻¹ ∈ N := N.inv_mem hρ3
  have hid : ρ⁻¹ * n * ρ = (ρ ^ 3)⁻¹ * (ρ ^ 2 * n * (ρ ^ 2)⁻¹) * ρ ^ 3 := by group
  rw [hid]
  exact N.mul_mem (N.mul_mem h3 h2) hρ3

theorem commute_sq_and_commutator_of_commutator_mem_centerIn {T N : Subgroup G}
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) (hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g)
    (h1 : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ centerIn N) :
    (∀ g ∈ T, ∀ n ∈ N, g * g * n = n * (g * g)) ∧
      ∀ g ∈ T, ∀ h ∈ T, ∀ n ∈ N, g * h * g⁻¹ * h⁻¹ * n = n * (g * h * g⁻¹ * h⁻¹) := by
  classical
  have hZcomm : ∀ a ∈ centerIn N, ∀ b ∈ centerIn N, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
  have hδmul : ∀ n ∈ N, ∀ x ∈ T, ∀ y ∈ T,
      x * y * n * (x * y)⁻¹ * n⁻¹ =
        (x * n * x⁻¹ * n⁻¹) * (y * n * y⁻¹ * n⁻¹) := by
    intro n hn x hx y hy
    have hdy : y * n * y⁻¹ * n⁻¹ ∈ centerIn N := h1 y hy n hn
    have hxdy : x * (y * n * y⁻¹ * n⁻¹) = (y * n * y⁻¹ * n⁻¹) * x := hTZ x hx _ hdy
    have hdx : x * n * x⁻¹ * n⁻¹ ∈ centerIn N := h1 x hx n hn
    have hcomm := hZcomm _ hdx _ hdy
    calc x * y * n * (x * y)⁻¹ * n⁻¹
        = x * (y * n * y⁻¹) * x⁻¹ * n⁻¹ := by group
      _ = x * ((y * n * y⁻¹ * n⁻¹) * n) * x⁻¹ * n⁻¹ := by
            conv_lhs => rw [show y * n * y⁻¹ = (y * n * y⁻¹ * n⁻¹) * n from by group]
      _ = (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹) * (x * n * x⁻¹ * n⁻¹) := by group
      _ = (y * n * y⁻¹ * n⁻¹) * (x * n * x⁻¹ * n⁻¹) := by rw [hxdy]; group
      _ = (x * n * x⁻¹ * n⁻¹) * (y * n * y⁻¹ * n⁻¹) := hcomm.symm
  constructor
  · intro g hg n hn
    let δ : ↥T →* ↥(centerIn N) :=
      { toFun := fun x => ⟨x * n * x⁻¹ * n⁻¹, h1 x x.2 n hn⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (hδmul n hn x x.2 y y.2) }
    have hsq : δ ⟨g, hg⟩ * δ ⟨g, hg⟩ = 1 := by
      apply Subtype.ext
      simpa using hZ2 _ (δ ⟨g, hg⟩).2
    have hgg : δ (⟨g, hg⟩ * ⟨g, hg⟩) = 1 := by
      rw [map_mul]
      exact hsq
    have hval : (g * g) * n * (g * g)⁻¹ * n⁻¹ = 1 := by
      have := congrArg Subtype.val hgg
      simpa [δ] using this
    have h3 : (g * g) * n * (g * g)⁻¹ = n := by
      have := congrArg (fun x => x * n) hval
      simpa [mul_assoc] using this
    calc (g * g) * n = ((g * g) * n * (g * g)⁻¹) * (g * g) := by group
      _ = n * (g * g) := by rw [h3]
  · intro g hg h hh n hn
    let δ : ↥T →* ↥(centerIn N) :=
      { toFun := fun x => ⟨x * n * x⁻¹ * n⁻¹, h1 x x.2 n hn⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (hδmul n hn x x.2 y y.2) }
    have hsq : ∀ a : ↥(centerIn N), a * a = 1 := by
      intro a
      apply Subtype.ext
      simpa using hZ2 _ a.2
    have hcom : ∀ a b : ↥(centerIn N), a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact hZcomm _ a.2 _ b.2
    have hinv : ∀ a : ↥(centerIn N), a⁻¹ = a := fun a => (mul_eq_one_iff_inv_eq).mp (hsq a)
    have hδc : δ (⟨g, hg⟩ * ⟨h, hh⟩ * ⟨g, hg⟩⁻¹ * ⟨h, hh⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      calc δ ⟨g, hg⟩ * δ ⟨h, hh⟩ * (δ ⟨g, hg⟩)⁻¹ * (δ ⟨h, hh⟩)⁻¹
          = δ ⟨g, hg⟩ * δ ⟨h, hh⟩ * δ ⟨g, hg⟩ * δ ⟨h, hh⟩ := by rw [hinv, hinv]
        _ = (δ ⟨g, hg⟩ * δ ⟨g, hg⟩) * (δ ⟨h, hh⟩ * δ ⟨h, hh⟩) := by
              calc δ ⟨g, hg⟩ * δ ⟨h, hh⟩ * δ ⟨g, hg⟩ * δ ⟨h, hh⟩
                  = δ ⟨g, hg⟩ * (δ ⟨h, hh⟩ * δ ⟨g, hg⟩) * δ ⟨h, hh⟩ := by group
                _ = δ ⟨g, hg⟩ * (δ ⟨g, hg⟩ * δ ⟨h, hh⟩) * δ ⟨h, hh⟩ := by
                      rw [hcom (δ ⟨h, hh⟩) (δ ⟨g, hg⟩)]
                _ = (δ ⟨g, hg⟩ * δ ⟨g, hg⟩) * (δ ⟨h, hh⟩ * δ ⟨h, hh⟩) := by group
        _ = 1 := by rw [hsq, hsq, mul_one]
    have hval : (g * h * g⁻¹ * h⁻¹) * n * (g * h * g⁻¹ * h⁻¹)⁻¹ * n⁻¹ = 1 := by
      have := congrArg Subtype.val hδc
      simpa [δ] using this
    have h3 : (g * h * g⁻¹ * h⁻¹) * n * (g * h * g⁻¹ * h⁻¹)⁻¹ = n := by
      have := congrArg (fun x => x * n) hval
      simpa [mul_assoc] using this
    calc (g * h * g⁻¹ * h⁻¹) * n
        = ((g * h * g⁻¹ * h⁻¹) * n * (g * h * g⁻¹ * h⁻¹)⁻¹) * (g * h * g⁻¹ * h⁻¹) := by
            group
      _ = n * (g * h * g⁻¹ * h⁻¹) := by rw [h3]

theorem commutator_mem_centerIn_of_quaternion_quotient [Finite G] {T N : Subgroup G}
    (hNT : N ≤ T) (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    (hidx : Nat.card N = 4 * Nat.card (centerIn N)) (hT2 : IsPGroup 2 ↥T)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ centerIn N := by
  classical
  have hρNinv : ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := conj_inv_mem_of_pow_three_mem hρN hρ3
  have hρNnorm : ρ ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨hρN n, fun h => by
      have := hρNinv (ρ * n * ρ⁻¹) h
      simpa [mul_assoc] using this⟩
  have hTnorm : T ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨hNnorm g hg n, fun h => by
      have := hNnorm g⁻¹ (T.inv_mem hg) (g * n * g⁻¹) h
      simpa [mul_assoc] using this⟩
  have hZcard : Nat.card (Subgroup.center ↥N) = Nat.card (centerIn N) := by
    rw [centerIn_eq_map_center, Subgroup.card_map_of_injective N.subtype_injective]
  have hZpos : 0 < Nat.card (centerIn N) := by
    have : Nonempty ↥(centerIn N) :=
      Nonempty.intro (Subtype.mk (1 : G) (Subgroup.one_mem (centerIn N)))
    exact Nat.card_pos
  have hZpos' : 0 < Nat.card (Subgroup.center ↥N) := by rw [hZcard]; exact hZpos
  have hQ : Nat.card (↥N ⧸ Subgroup.center ↥N) = 4 := by
    have h1 : Nat.card (↥N ⧸ Subgroup.center ↥N) * Nat.card (Subgroup.center ↥N) =
        4 * Nat.card (Subgroup.center ↥N) := by
      rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥N), hidx, hZcard]
    exact Nat.eq_of_mul_eq_mul_right hZpos' h1
  have hQcomm : ∀ a b : ↥N ⧸ Subgroup.center ↥N, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 2) (by rw [hQ]; norm_num)
  have hZchar : (Subgroup.center ↥N).Characteristic := Subgroup.centerCharacteristic
  let Φ₀ : ↥T →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hTnorm)
  let Φ : ↥T →* MulAut (↥N ⧸ Subgroup.center ↥N) :=
    (MulAut.mapQuotient (Subgroup.center ↥N)).comp Φ₀
  let RN : MulAut ↥N := (Subgroup.normalizerMonoidHom N) ⟨ρ, hρNnorm⟩
  let R : MulAut (↥N ⧸ Subgroup.center ↥N) := (MulAut.mapQuotient (Subgroup.center ↥N)) RN
  have hΦ₀_coe : ∀ (g : ↥T) (n : ↥N), (((Φ₀ g) n : ↥N) : G) = (g : G) * n * (g : G)⁻¹ := by
    intro g n
    simp [Φ₀]
  have hRN_coe : ∀ n : ↥N, ((RN n : ↥N) : G) = ρ * n * ρ⁻¹ := by
    intro n
    simp [RN]
  have hRNinv_coe : ∀ n : ↥N, ((RN⁻¹ n : ↥N) : G) = ρ⁻¹ * n * ρ := by
    intro n
    have h : RN (RN⁻¹ n) = n := by
      have := congrArg (fun f : MulAut ↥N => f n) (mul_inv_cancel RN)
      simp
    have h' := congrArg Subtype.val h
    rw [hRN_coe] at h'
    calc ((RN⁻¹ n : ↥N) : G) = ρ⁻¹ * (ρ * ((RN⁻¹ n : ↥N) : G) * ρ⁻¹) * ρ := by group
      _ = ρ⁻¹ * (n : G) * ρ := by rw [h']
  have hΦN : ∀ g : ↥T, (g : G) ∈ N → Φ g = 1 := by
    intro g hg
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hΦy : ((Φ₀ g) y : ↥N) = (⟨g, hg⟩ : ↥N) * y * (⟨g, hg⟩ : ↥N)⁻¹ := by
      apply Subtype.ext
      simpa using hΦ₀_coe g y
    rw [show Φ g = (MulAut.mapQuotient (Subgroup.center ↥N)) (Φ₀ g) from rfl,
      MulAut.mapQuotient_mk, MulAut.one_apply, hΦy]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hQcomm]
    group
  have hΦρ : ∀ g : ↥T, Φ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = R * Φ g * R⁻¹ := by
    intro g
    have hΦ₀ : Φ₀ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = RN * Φ₀ g * RN⁻¹ := by
      ext n
      have h1 : (((RN * Φ₀ g * RN⁻¹) n : ↥N) : G) = ρ * (g * (ρ⁻¹ * n * ρ) * g⁻¹) * ρ⁻¹ := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hRN_coe, hΦ₀_coe, hRNinv_coe]
        simp only [Subgroup.coe_inv]
      rw [hΦ₀_coe, h1]
      simp only [Subgroup.coe_inv]
      group
    calc Φ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩
        = (MulAut.mapQuotient (Subgroup.center ↥N)) (Φ₀ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩) := rfl
      _ = (MulAut.mapQuotient (Subgroup.center ↥N)) (RN * Φ₀ g * RN⁻¹) := by rw [hΦ₀]
      _ = R * Φ g * R⁻¹ := by simp [R, Φ, map_mul]
  have htriv : ∀ g : ↥T, Φ g = 1 :=
    eq_one_of_mulAut_of_card_eq_four_of_quaternion_quotient hNT π hπ hker hT2 hρT hρN hρ3 hρ
      hQ Φ hΦN R hΦρ
  intro g hg n hn
  have hΦg : Φ ⟨g, hg⟩ = 1 := htriv ⟨g, hg⟩
  have hx : ((Φ₀ ⟨g, hg⟩) ⟨n, hn⟩ / ⟨n, hn⟩ : ↥N) ∈ Subgroup.center ↥N := by
    have h := congrArg (fun φ : MulAut (↥N ⧸ Subgroup.center ↥N) =>
      φ ((⟨n, hn⟩ : ↥N) : ↥N ⧸ Subgroup.center ↥N)) hΦg
    rw [show Φ ⟨g, hg⟩ = (MulAut.mapQuotient (Subgroup.center ↥N)) (Φ₀ ⟨g, hg⟩) from rfl,
      MulAut.mapQuotient_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq_iff_div_mem.mp h
  have hval : ((((Φ₀ ⟨g, hg⟩) ⟨n, hn⟩ / ⟨n, hn⟩ : ↥N)) : G) = g * n * g⁻¹ * n⁻¹ := by
    simp [Φ₀, div_eq_mul_inv, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
  refine Subgroup.mem_inf.mpr ⟨N.mul_mem (hNnorm g hg n hn) (N.inv_mem hn), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcy := congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hx (⟨y, hy⟩ : ↥N))
  simpa [hval, Subgroup.coe_mul] using hcy

theorem mem_centerIn_of_quaternion_quotient {T N : Subgroup G} (hNT : N ≤ T)
    (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) (hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρZ : ∀ x ∈ centerIn N, ρ * x = x * ρ) (hρ3 : ρ ^ 3 ∈ N)
    (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N)
    (x : ↥T) (hxN : ∀ n ∈ N, (x : G) * n = n * x) (hxπ : π x = 1 ∨ π x = a 2) :
    (x : G) ∈ centerIn T := by
  classical
  have hZcomm : ∀ a ∈ centerIn N, ∀ b ∈ centerIn N, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
  have hρNinv : ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := conj_inv_mem_of_pow_three_mem hρN hρ3
  have heT : ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹ ∈ T := by
    simpa using T.mul_mem (hρT x x.2) (T.inv_mem x.2)
  have heN : ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹ ∈ N := by
    obtain ⟨α, hα, hα3, _⟩ :=
      exists_quaternionGroup_two_endomorphism_of_conj hNT π hπ hker hρT hρN hρ3 hρ
    have hπe : π ⟨ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹, heT⟩ = 1 := by
      have h1 : π ⟨ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹, heT⟩ = α (π x) * (π x)⁻¹ := by
        rw [show (⟨ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹, heT⟩ : ↥T) =
            ⟨ρ * x * ρ⁻¹, hρT x x.2⟩ * x⁻¹ from rfl]
        rw [map_mul, map_inv, hα]
      rcases hxπ with hx1 | hx2
      · rw [h1, hx1]
        simp
      · rw [h1, hx2, quaternionGroup_two_apply_a_two α hα3]
        simp
    have hmem : (⟨ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹, heT⟩ : ↥T) ∈ N.subgroupOf T := by
      rw [← hker, MonoidHom.mem_ker]
      exact hπe
    exact Subgroup.mem_subgroupOf.mp hmem
  set e : G := ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹ with he
  have heZ : e ∈ centerIn N := by
    rw [he]
    refine Subgroup.mem_inf.mpr ⟨heN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hxn' : (x : G)⁻¹ * n * (x : G) = n := by
      have h := congrArg (fun z => (x : G)⁻¹ * z) (hxN n hn)
      simpa [mul_assoc] using h.symm
    have hρinvn : ρ⁻¹ * n * ρ ∈ N := hρNinv n hn
    have hxconj : (x : G) * (ρ⁻¹ * n * ρ) * (x : G)⁻¹ = ρ⁻¹ * n * ρ := by
      rw [hxN _ hρinvn]
      group
    have he2 : (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) * n * (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹)⁻¹ = n := by
      calc (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) * n * (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹)⁻¹
          = ρ * (x : G) * ρ⁻¹ * ((x : G)⁻¹ * n * (x : G)) * ρ * (x : G)⁻¹ * ρ⁻¹ := by group
        _ = ρ * (x : G) * ρ⁻¹ * n * ρ * (x : G)⁻¹ * ρ⁻¹ := by rw [hxn']
        _ = ρ * ((x : G) * (ρ⁻¹ * n * ρ) * (x : G)⁻¹) * ρ⁻¹ := by group
        _ = ρ * (ρ⁻¹ * n * ρ) * ρ⁻¹ := by rw [hxconj]
        _ = n := by group
    have he2' : (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) * n =
        n * (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) := by
      calc (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) * n
          = ((ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) * n *
              (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹)⁻¹) *
              (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) := by group
        _ = n * (ρ * (x : G) * ρ⁻¹ * (x : G)⁻¹) := by rw [he2]
    exact he2'.symm
  have hρe : ρ * e = e * ρ := hρZ e heZ
  have hxe : ρ * (x : G) * ρ⁻¹ = e * (x : G) := by
    rw [he]
    group
  have hρ2 : ρ ^ 2 * (x : G) * (ρ ^ 2)⁻¹ = (x : G) := by
    rw [pow_two]
    calc ρ * ρ * (x : G) * (ρ * ρ)⁻¹
        = ρ * (ρ * (x : G) * ρ⁻¹) * ρ⁻¹ := by group
      _ = ρ * (e * (x : G)) * ρ⁻¹ := by rw [hxe]
      _ = (ρ * e * ρ⁻¹) * (ρ * (x : G) * ρ⁻¹) := by group
      _ = e * (e * (x : G)) := by rw [hρe, hxe]; group
      _ = (x : G) := by rw [← mul_assoc, hZ2 e heZ, one_mul]
  have hρ3x : ρ ^ 3 * (x : G) * (ρ ^ 3)⁻¹ = (x : G) := by
    have hxρ3 : (x : G) * ρ ^ 3 = ρ ^ 3 * (x : G) := hxN _ hρ3
    calc ρ ^ 3 * (x : G) * (ρ ^ 3)⁻¹ = (x : G) * ρ ^ 3 * (ρ ^ 3)⁻¹ := by rw [← hxρ3]
      _ = (x : G) := by group
  have he1 : e = 1 := by
    have h : ρ ^ 3 * (x : G) * (ρ ^ 3)⁻¹ =
        ρ * (ρ ^ 2 * (x : G) * (ρ ^ 2)⁻¹) * ρ⁻¹ := by
      rw [pow_two, pow_three]
      group
    rw [hρ2, hρ3x] at h
    rw [hxe] at h
    have h3 : e * (x : G) = 1 * (x : G) := by rw [← h, one_mul]
    exact mul_right_cancel h3
  have hρx : ρ * (x : G) * ρ⁻¹ = (x : G) := by
    rw [hxe, he1, one_mul]
  have hρxcomm : ρ * (x : G) = (x : G) * ρ := by
    calc ρ * (x : G) = (ρ * (x : G) * ρ⁻¹) * ρ := by group
      _ = (x : G) * ρ := by rw [hρx]
  have hρinvx : (ρ : G)⁻¹ * (x : G) * ρ = (x : G) := by
    calc (ρ : G)⁻¹ * (x : G) * ρ = (ρ : G)⁻¹ * ((x : G) * ρ) := by group
      _ = (ρ : G)⁻¹ * (ρ * (x : G)) := by rw [← hρxcomm]
      _ = (x : G) := by group
  let Y : ↥T → G := fun g => (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹
  have hY : ∀ g : ↥T, Y g = (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹ := fun g => rfl
  have hψN : ∀ g : ↥T, Y g ∈ N := by
    intro g
    have hmemT : Y g ∈ T := by
      rw [hY]
      exact T.mul_mem (T.mul_mem (T.mul_mem g.2 x.2) (T.inv_mem g.2)) (T.inv_mem x.2)
    have hπ : π ⟨Y g, hmemT⟩ = 1 := by
      have hsub : (⟨Y g, hmemT⟩ : ↥T) = g * x * g⁻¹ * x⁻¹ := by
        apply Subtype.ext
        show Y g = (↑(g * x * g⁻¹ * x⁻¹) : G)
        rw [hY]
        rfl
      rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv]
      rcases hxπ with hx1 | hx2
      · rw [hx1]
        simp
      · rw [hx2, ← quaternionGroup_two_a_two_central (π g)]
        group
    have hmem : (⟨Y g, hmemT⟩ : ↥T) ∈ N.subgroupOf T := by
      rw [← hker, MonoidHom.mem_ker]
      exact hπ
    exact Subgroup.mem_subgroupOf.mp hmem
  have hψC : ∀ g : ↥T, Y g ∈ Subgroup.centralizer (N : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hxn' : (x : G)⁻¹ * n * (x : G) = n := by
      have h := congrArg (fun z => (x : G)⁻¹ * z) (hxN n hn)
      simpa [mul_assoc] using h.symm
    have hg'n : (g : G)⁻¹ * n * (g : G) ∈ N := by
      have h := hNnorm g⁻¹ (T.inv_mem g.2) n hn
      simpa using h
    have hxconj : (x : G) * ((g : G)⁻¹ * n * (g : G)) * (x : G)⁻¹ = (g : G)⁻¹ * n * (g : G) := by
      rw [hxN _ hg'n]
      group
    have he2 : Y g * n * (Y g)⁻¹ = n := by
      rw [hY]
      calc ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) * n *
            ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹)⁻¹
          = (g : G) * (x : G) * (g : G)⁻¹ * ((x : G)⁻¹ * n * (x : G)) *
              (g : G) * (x : G)⁻¹ * (g : G)⁻¹ := by group
        _ = (g : G) * (x : G) * (g : G)⁻¹ * n * (g : G) * (x : G)⁻¹ * (g : G)⁻¹ := by
              rw [hxn']
        _ = (g : G) * ((x : G) * ((g : G)⁻¹ * n * (g : G)) * (x : G)⁻¹) * (g : G)⁻¹ := by group
        _ = (g : G) * ((g : G)⁻¹ * n * (g : G)) * (g : G)⁻¹ := by rw [hxconj]
        _ = n := by group
    have he2' : Y g * n = n * Y g := by
      calc Y g * n = (Y g * n * (Y g)⁻¹) * Y g := by group
        _ = n * Y g := by rw [he2]
    exact he2'.symm
  have hψmem : ∀ g : ↥T, Y g ∈ centerIn N :=
    fun g => Subgroup.mem_inf.mpr ⟨hψN g, hψC g⟩
  have hψmul : ∀ g h : ↥T, Y (g * h) = Y g * Y h := by
    intro g h
    have hψh : Y h ∈ centerIn N := hψmem h
    have hgψ : (g : G) * Y h = Y h * (g : G) := hTZ g g.2 _ hψh
    have hcomm : Y g * Y h = Y h * Y g := hZcomm _ (hψmem g) _ hψh
    have hYgh : Y (g * h) =
        (g : G) * (h : G) * (x : G) * ((g : G) * (h : G))⁻¹ * (x : G)⁻¹ := by
      rw [hY]
      rfl
    calc Y (g * h)
        = (g : G) * ((h : G) * (x : G) * (h : G)⁻¹) * (g : G)⁻¹ * (x : G)⁻¹ := by
            rw [hYgh]; group
      _ = (g : G) * (((h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹) * (x : G)) *
            (g : G)⁻¹ * (x : G)⁻¹ := by
            conv_lhs => rw [show (h : G) * (x : G) * (h : G)⁻¹ =
              ((h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹) * (x : G) from by group]
      _ = (g : G) * (Y h * (x : G)) * (g : G)⁻¹ * (x : G)⁻¹ := by rw [← hY h]
      _ = ((g : G) * Y h * (g : G)⁻¹) * ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) := by
            group
      _ = ((Y h * (g : G)) * (g : G)⁻¹) * ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) := by
            rw [hgψ]
      _ = Y h * Y g := by rw [← hY g]; group
      _ = Y g * Y h := hcomm.symm
  let ψ : ↥T →* ↥(centerIn N) :=
    { toFun := fun g => ⟨Y g, hψmem g⟩
      map_one' := by
        apply Subtype.ext
        change Y 1 = 1
        rw [hY]
        simp
      map_mul' := fun g h => Subtype.ext (hψmul g h) }
  have hψker : ∀ g : ↥T, (g : G) ∈ N → ψ g = 1 := by
    intro g hg
    apply Subtype.ext
    change Y g = 1
    rw [hY]
    have hxg : (g : G) * (x : G) = (x : G) * (g : G) := (hxN g hg).symm
    rw [hxg]
    group
  have hψρ : ∀ g : ↥T, ψ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = ψ g := by
    intro g
    apply Subtype.ext
    change Y ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = Y g
    have hYc : Y ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ =
        (ρ * (g : G) * ρ⁻¹) * (x : G) * (ρ * (g : G) * ρ⁻¹)⁻¹ * (x : G)⁻¹ := by
      rw [hY]
    have hρinvxinv : (ρ : G)⁻¹ * (x : G)⁻¹ * ρ = (x : G)⁻¹ := by
      calc (ρ : G)⁻¹ * (x : G)⁻¹ * ρ = ((ρ : G)⁻¹ * (x : G) * ρ)⁻¹ := by group
        _ = (x : G)⁻¹ := by rw [hρinvx]
    have hρxinv : (ρ : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * ρ⁻¹ := by
      have h' := congrArg (fun z => z * ρ⁻¹) hρinvxinv
      simpa [mul_assoc] using h'
    have hstep1 : (ρ * (g : G) * ρ⁻¹) * (x : G) * (ρ * (g : G) * ρ⁻¹)⁻¹ * (x : G)⁻¹ =
        ρ * ((g : G) * (x : G) * (g : G)⁻¹) * ρ⁻¹ * (x : G)⁻¹ := by
      rw [show (ρ * (g : G) * ρ⁻¹) * (x : G) * (ρ * (g : G) * ρ⁻¹)⁻¹ * (x : G)⁻¹ =
          ρ * (g : G) * (ρ⁻¹ * (x : G) * ρ) * (g : G)⁻¹ * ρ⁻¹ * (x : G)⁻¹ from by group]
      rw [hρinvx]
      group
    have hstep2 : ρ * ((g : G) * (x : G) * (g : G)⁻¹) * ρ⁻¹ * (x : G)⁻¹ =
        ρ * ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) * ρ⁻¹ := by
      calc ρ * ((g : G) * (x : G) * (g : G)⁻¹) * ρ⁻¹ * (x : G)⁻¹
          = ρ * ((g : G) * (x : G) * (g : G)⁻¹) * (ρ⁻¹ * (x : G)⁻¹) := by group
        _ = ρ * ((g : G) * (x : G) * (g : G)⁻¹) * ((x : G)⁻¹ * ρ⁻¹) := by rw [hρxinv]
        _ = ρ * ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) * ρ⁻¹ := by group
    rw [hYc, hstep1, hstep2, ← hY g, hρZ (Y g) (hψmem g)]
    group
  have hA : ∀ a : ↥(centerIn N), a * a = 1 := by
    intro a
    apply Subtype.ext
    simpa using hZ2 _ a.2
  have htriv : ∀ g : ↥T, ψ g = 1 :=
    eq_one_of_quaternion_quotient_of_conj_invariant hNT π hπ hker hρT hρN hρ3 hρ
      hA ψ hψker hψρ
  refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 : ψ ⟨g, hg⟩ = 1 := htriv ⟨g, hg⟩
  have h2 : Y ⟨g, hg⟩ = 1 := congrArg Subtype.val h1
  rw [hY] at h2
  calc (g : G) * (x : G) = ((g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹) * ((x : G) * (g : G)) := by
        group
    _ = 1 * ((x : G) * (g : G)) := by rw [h2]
    _ = (x : G) * (g : G) := one_mul _

theorem card_centerIn_eq_two_mul_and_sq_eq_one_of_quaternion_quotient [Finite G]
    {T N : Subgroup G} (hNT : N ≤ T) (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    (hidx : Nat.card N = 4 * Nat.card (centerIn N))
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    (hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρZ : ∀ x ∈ centerIn N, ρ * x = x * ρ) (hρ3 : ρ ^ 3 ∈ N)
    (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    Nat.card (centerIn T) = 2 * Nat.card (centerIn N) ∧ ∀ x ∈ centerIn T, x * x = 1 := by
  classical
  have hZsq : ∀ z : ↥(centerIn N), z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    simpa [pow_two] using hZ2 (z : G) z.2
  have hZP : IsPGroup 2 ↥(centerIn N) := fun z => ⟨1, by simpa using hZsq z⟩
  obtain ⟨k, hk⟩ := hZP.exists_card_eq
  have hQ8card : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hkerCard : Nat.card (N.subgroupOf T) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  have hTcard : Nat.card ↥T = 8 * Nat.card ↥N := by
    have h := Subgroup.card_ker_mul_card_of_surjective (G := ↥T) (G' := QuaternionGroup 2) hπ
    rw [hker, hkerCard, hQ8card] at h
    rw [← h]; ring
  have hcardT : Nat.card ↥T = 2 ^ (k + 5) := by
    rw [hTcard, hidx, hk, pow_add]
    ring
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hcardT
  have h1 : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ centerIn N :=
    commutator_mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hidx hT2 hρT hρN hρ3 hρ
  have hsqcomm := commute_sq_and_commutator_of_commutator_mem_centerIn hZ2 hTZ h1
  have hZNle : centerIn N ≤ centerIn T := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hNT hz.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact hTZ t ht z hz
  obtain ⟨u, hu⟩ := hπ (a 1)
  obtain ⟨v, hv⟩ := hπ (xa 0)
  have hab : (a 1 * xa 0 * (a 1)⁻¹ * (xa 0)⁻¹ : QuaternionGroup 2) = a 2 := by decide
  have haa : (a 1 * a 1 : QuaternionGroup 2) = a 2 := by decide
  have hcπ0 : π (u * v * u⁻¹ * v⁻¹) = a 2 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv, hab]
  have ha2π : π (u * u) = a 2 := by
    rw [map_mul, hu, haa]
  set c : ↥T := u * v * u⁻¹ * v⁻¹ with hc_def
  have hcπ : π c = a 2 := by rw [hc_def]; exact hcπ0
  have hc_centN : ∀ n ∈ N, (c : G) * n = n * c := by
    intro n hn
    have h := hsqcomm.2 u u.2 v v.2 n hn
    rw [hc_def]
    simpa using h
  have hcZ : (c : G) ∈ centerIn T :=
    mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hZ2 hTZ hρT hρN hρZ hρ3 hρ
      c hc_centN (Or.inr hcπ)
  have ha2_centN : ∀ n ∈ N, ((u * u : ↥T) : G) * n = n * (u * u : ↥T) := by
    intro n hn
    have h := hsqcomm.1 u u.2 n hn
    simpa using h
  have ha2Z : ((u * u : ↥T) : G) ∈ centerIn T :=
    mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hZ2 hTZ hρT hρN hρZ hρ3 hρ
      (u * u) ha2_centN (Or.inr ha2π)
  have hcaG : (u : G) * (c : G) = (c : G) * (u : G) :=
    Subgroup.mem_centralizer_iff.mp hcZ.2 u u.2
  have hca : (u : ↥T) * c = c * (u : ↥T) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hcaG
  have hcbG : (v : G) * (c : G) = (c : G) * (v : G) :=
    Subgroup.mem_centralizer_iff.mp hcZ.2 v v.2
  have hcb : (v : ↥T) * c = c * (v : ↥T) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using hcbG
  have ha2bG : (v : G) * ((u * u : ↥T) : G) = ((u * u : ↥T) : G) * (v : G) :=
    Subgroup.mem_centralizer_iff.mp ha2Z.2 v v.2
  have ha2b : (v : ↥T) * (u * u) = (u * u) * (v : ↥T) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using ha2bG
  have hc2 : c * c = 1 := by
    have h1' : (u : ↥T) * (v : ↥T) * (u : ↥T)⁻¹ = c * (v : ↥T) := by
      rw [hc_def]
      group
    have h2' : (u : ↥T) * c * (u : ↥T)⁻¹ = c := by
      rw [hca]
      group
    have h3' : ((u * u : ↥T)) * (v : ↥T) * ((u * u : ↥T))⁻¹ * (v : ↥T)⁻¹ = 1 := by
      rw [← ha2b]
      group
    have hgoal : ((u * u : ↥T)) * (v : ↥T) * ((u * u : ↥T))⁻¹ * (v : ↥T)⁻¹ = c * c := by
      calc ((u * u : ↥T)) * (v : ↥T) * ((u * u : ↥T))⁻¹ * (v : ↥T)⁻¹
          = (u : ↥T) * ((u : ↥T) * (v : ↥T) * (u : ↥T)⁻¹) * (u : ↥T)⁻¹ * (v : ↥T)⁻¹ := by
              group
        _ = (u : ↥T) * (c * (v : ↥T)) * (u : ↥T)⁻¹ * (v : ↥T)⁻¹ := by rw [h1']
        _ = ((u : ↥T) * c * (u : ↥T)⁻¹) *
              ((u : ↥T) * (v : ↥T) * (u : ↥T)⁻¹) * (v : ↥T)⁻¹ := by group
        _ = c * (c * (v : ↥T)) * (v : ↥T)⁻¹ := by rw [h2', h1']
        _ = c * c := by group
    rw [← hgoal]
    exact h3'
  have hcc : (c : G) * (c : G) = 1 := by
    simpa using congrArg Subtype.val hc2
  have hπcentral : ∀ x : ↥T, (x : G) ∈ centerIn T →
      ∀ y : QuaternionGroup 2, π x * y = y * π x := by
    intro x hx y
    obtain ⟨g, rfl⟩ := hπ y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using (Subgroup.mem_centralizer_iff.mp hx.2 g g.2).symm
  have hxcZN : ∀ x : ↥T, (x : G) ∈ centerIn T → π x = a 2 →
      ((x : G) * (c : G)⁻¹) ∈ centerIn N := by
    intro x hx hx2
    have hmemT : (x : G) * (c : G)⁻¹ ∈ T :=
      T.mul_mem hx.1 (T.inv_mem hcZ.1)
    have hπy : π ⟨(x : G) * (c : G)⁻¹, hmemT⟩ = 1 := by
      rw [show (⟨(x : G) * (c : G)⁻¹, hmemT⟩ : ↥T) = x * c⁻¹ from rfl]
      rw [map_mul, map_inv, hx2, hcπ]
      simp
    have hyN : (x : G) * (c : G)⁻¹ ∈ N := by
      have hmem : (⟨(x : G) * (c : G)⁻¹, hmemT⟩ : ↥T) ∈ N.subgroupOf T := by
        rw [← hker, MonoidHom.mem_ker]
        exact hπy
      exact Subgroup.mem_subgroupOf.mp hmem
    refine Subgroup.mem_inf.mpr ⟨hyN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hxn : n * (x : G) = (x : G) * n :=
      Subgroup.mem_centralizer_iff.mp hx.2 n (hNT hn)
    have hcn : n * (c : G) = (c : G) * n :=
      Subgroup.mem_centralizer_iff.mp hcZ.2 n (hNT hn)
    have hcinvn : n * (c : G)⁻¹ = (c : G)⁻¹ * n := by
      calc n * (c : G)⁻¹
          = (c : G)⁻¹ * ((c : G) * n) * (c : G)⁻¹ := by group
        _ = (c : G)⁻¹ * (n * (c : G)) * (c : G)⁻¹ := by rw [hcn]
        _ = (c : G)⁻¹ * n := by group
    calc n * ((x : G) * (c : G)⁻¹)
        = (n * (x : G)) * (c : G)⁻¹ := by group
      _ = ((x : G) * n) * (c : G)⁻¹ := by rw [hxn]
      _ = (x : G) * (n * (c : G)⁻¹) := by group
      _ = (x : G) * ((c : G)⁻¹ * n) := by rw [hcinvn]
      _ = ((x : G) * (c : G)⁻¹) * n := by group
  have hNOT : (⟨c, hcZ⟩ : ↥(centerIn T)) ∉ (centerIn N).subgroupOf (centerIn T) := by
    intro hmem
    have hcN : (c : G) ∈ N := by
      have h := Subgroup.mem_subgroupOf.mp hmem
      exact h.1
    have htriv : π c = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hcN
    rw [hcπ] at htriv
    exact absurd htriv (by decide : (a 2 : QuaternionGroup 2) ≠ 1)
  have hindex : ((centerIn N).subgroupOf (centerIn T)).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨c, hcZ⟩, hNOT, fun x => ?_⟩
    let xT : ↥T := ⟨(x : G), x.2.1⟩
    have hxTcent : (xT : G) ∈ centerIn T := by simp [xT]
    rcases quaternionGroup_two_eq_one_or_eq_a_two_of_commute (π xT)
      (hπcentral xT hxTcent) with hx1 | hx2
    · have hxN : (x : G) ∈ N := by
        have hmem : xT ∈ N.subgroupOf T := by
          rw [← hker, MonoidHom.mem_ker]
          exact hx1
        exact Subgroup.mem_subgroupOf.mp hmem
      have hxZN : (x : G) ∈ centerIn N := by
        refine Subgroup.mem_inf.mpr ⟨hxN, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact Subgroup.mem_centralizer_iff.mp x.2.2 n (hNT hn)
      exact Or.inr (Subgroup.mem_subgroupOf.mpr hxZN)
    · have hyZN : ((xT : G) * (c : G)⁻¹) ∈ centerIn N := hxcZN xT hxTcent hx2
      have hcinv : (c : G)⁻¹ = (c : G) := (mul_eq_one_iff_inv_eq).mp hcc
      have hxc : ((x * ⟨c, hcZ⟩ : ↥(centerIn T)) : G) = (xT : G) * (c : G)⁻¹ := by
        change (x : G) * (c : G) = (xT : G) * (c : G)⁻¹
        rw [hcinv]
      exact Or.inl (Subgroup.mem_subgroupOf.mpr (by rw [hxc]; exact hyZN))
  constructor
  ·
    have hcardK : Nat.card ((centerIn N).subgroupOf (centerIn T)) = Nat.card ↥(centerIn N) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZNle).toEquiv
    have h := Subgroup.card_mul_index ((centerIn N).subgroupOf (centerIn T))
    rw [hindex, hcardK] at h
    rw [← h]
    ring
  ·
    intro x hx
    let xT : ↥T := ⟨x, hx.1⟩
    have hxTcent : (xT : G) ∈ centerIn T := by simpa [xT] using hx
    rcases quaternionGroup_two_eq_one_or_eq_a_two_of_commute (π xT)
      (hπcentral xT hxTcent) with hx1 | hx2
    · have hxN : x ∈ N := by
        have hmem : xT ∈ N.subgroupOf T := by
          rw [← hker, MonoidHom.mem_ker]
          exact hx1
        exact Subgroup.mem_subgroupOf.mp hmem
      have hxZN : x ∈ centerIn N := by
        refine Subgroup.mem_inf.mpr ⟨hxN, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact Subgroup.mem_centralizer_iff.mp hx.2 n (hNT hn)
      exact hZ2 x hxZN
    · have hyZN : (x * (c : G)⁻¹) ∈ centerIn N := hxcZN xT hxTcent hx2
      have hcinv : (c : G)⁻¹ = (c : G) := (mul_eq_one_iff_inv_eq).mp hcc
      have hyc : (x * (c : G)⁻¹) * (c : G) = (c : G) * (x * (c : G)⁻¹) := by
        have h1 : (x * (c : G)⁻¹) ∈ centerIn T := by
          refine Subgroup.mem_inf.mpr ⟨T.mul_mem hx.1 (T.inv_mem hcZ.1), ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.mp hx.2 t ht
          have hct : t * (c : G) = (c : G) * t :=
            Subgroup.mem_centralizer_iff.mp hcZ.2 t ht
          have hctinv : t * (c : G)⁻¹ = (c : G)⁻¹ * t := by
            calc t * (c : G)⁻¹ = (c : G)⁻¹ * ((c : G) * t) * (c : G)⁻¹ := by group
              _ = (c : G)⁻¹ * (t * (c : G)) * (c : G)⁻¹ := by rw [hct]
              _ = (c : G)⁻¹ * t := by group
          calc t * (x * (c : G)⁻¹) = (t * x) * (c : G)⁻¹ := by group
            _ = (x * t) * (c : G)⁻¹ := by rw [hxt]
            _ = x * (t * (c : G)⁻¹) := by group
            _ = x * ((c : G)⁻¹ * t) := by rw [hctinv]
            _ = (x * (c : G)⁻¹) * t := by group
        exact (Subgroup.mem_centralizer_iff.mp h1.2 (c : G) hcZ.1).symm
      have hxeq : x = (x * (c : G)⁻¹) * (c : G) := by
        rw [hcinv, mul_assoc, hcc, mul_one]
      calc x * x
          = ((x * (c : G)⁻¹) * (c : G)) * ((x * (c : G)⁻¹) * (c : G)) := by rw [← hxeq]
        _ = ((x * (c : G)⁻¹) * (x * (c : G)⁻¹)) * ((c : G) * (c : G)) := by
              calc ((x * (c : G)⁻¹) * (c : G)) * ((x * (c : G)⁻¹) * (c : G))
                  = (x * (c : G)⁻¹) * ((c : G) * (x * (c : G)⁻¹)) * (c : G) := by group
                _ = (x * (c : G)⁻¹) * ((x * (c : G)⁻¹) * (c : G)) * (c : G) := by rw [hyc]
                _ = ((x * (c : G)⁻¹) * (x * (c : G)⁻¹)) * ((c : G) * (c : G)) := by group
        _ = 1 := by rw [hZ2 _ hyZN, hcc, mul_one]

theorem commute_of_mem_centerIn_of_quaternion_quotient [Finite G] {T N : Subgroup G}
    (hNT : N ≤ T) (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T) (hZN : Nat.card (centerIn N) = 4) (hT2 : IsPGroup 2 ↥T)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g := by
  classical
  have hρNinv : ∀ n ∈ N, ρ⁻¹ * n * ρ ∈ N := conj_inv_mem_of_pow_three_mem hρN hρ3
  have hρNnorm : ρ ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨hρN n, fun h => by
      have := hρNinv (ρ * n * ρ⁻¹) h
      simpa [mul_assoc] using this⟩
  have hTnorm : T ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    exact ⟨hNnorm g hg n, fun h => by
      have := hNnorm g⁻¹ (T.inv_mem hg) (g * n * g⁻¹) h
      simpa [mul_assoc] using this⟩
  have hZcard : Nat.card (Subgroup.center ↥N) = Nat.card (centerIn N) := by
    rw [centerIn_eq_map_center, Subgroup.card_map_of_injective N.subtype_injective]
  have hZchar : (Subgroup.center ↥N).Characteristic := Subgroup.centerCharacteristic
  let Φ₀ : ↥T →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom N).comp (Subgroup.inclusion hTnorm)
  let Φ : ↥T →* MulAut ↥(Subgroup.center ↥N) :=
    (MulAut.characteristic (Subgroup.center ↥N)).comp Φ₀
  let RN : MulAut ↥N := (Subgroup.normalizerMonoidHom N) ⟨ρ, hρNnorm⟩
  let R : MulAut ↥(Subgroup.center ↥N) := (MulAut.characteristic (Subgroup.center ↥N)) RN
  have hΦ₀_coe : ∀ (g : ↥T) (n : ↥N), (((Φ₀ g) n : ↥N) : G) = (g : G) * n * (g : G)⁻¹ := by
    intro g n
    simp [Φ₀]
  have hRN_coe : ∀ n : ↥N, ((RN n : ↥N) : G) = ρ * n * ρ⁻¹ := by
    intro n
    simp [RN]
  have hRNinv_coe : ∀ n : ↥N, ((RN⁻¹ n : ↥N) : G) = ρ⁻¹ * n * ρ := by
    intro n
    have h : RN (RN⁻¹ n) = n := by
      have := congrArg (fun f : MulAut ↥N => f n) (mul_inv_cancel RN)
      simp
    have h' := congrArg Subtype.val h
    rw [hRN_coe] at h'
    calc ((RN⁻¹ n : ↥N) : G) = ρ⁻¹ * (ρ * ((RN⁻¹ n : ↥N) : G) * ρ⁻¹) * ρ := by group
      _ = ρ⁻¹ * (n : G) * ρ := by rw [h']
  have hQ : Nat.card ↥(Subgroup.center ↥N) = 4 := by
    rw [hZcard, hZN]
  have hΦN : ∀ g : ↥T, (g : G) ∈ N → Φ g = 1 := by
    intro g hg
    ext y
    rw [show Φ g = (MulAut.characteristic (Subgroup.center ↥N)) (Φ₀ g) from rfl,
      MulAut.one_apply]
    rw [MulAut.characteristic_apply_apply_coe, hΦ₀_coe]
    have hy : (y : ↥N) ∈ Subgroup.center ↥N := y.2
    have hcomm : (g : G) * (y : G) = (y : G) * (g : G) := by
      have h := Subgroup.mem_center_iff.mp hy (⟨(g : G), hg⟩ : ↥N)
      exact congrArg Subtype.val h
    calc (g : G) * (y : G) * (g : G)⁻¹ = ((y : G) * (g : G)) * (g : G)⁻¹ := by rw [hcomm]
      _ = (y : G) := by group
  have hΦρ : ∀ g : ↥T, Φ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = R * Φ g * R⁻¹ := by
    intro g
    have hΦ₀ : Φ₀ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩ = RN * Φ₀ g * RN⁻¹ := by
      ext n
      have h1 : (((RN * Φ₀ g * RN⁻¹) n : ↥N) : G) = ρ * (g * (ρ⁻¹ * n * ρ) * g⁻¹) * ρ⁻¹ := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hRN_coe, hΦ₀_coe, hRNinv_coe]
        simp only [Subgroup.coe_inv]
      rw [hΦ₀_coe, h1]
      simp only [Subgroup.coe_inv]
      group
    calc Φ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩
        = (MulAut.characteristic (Subgroup.center ↥N)) (Φ₀ ⟨ρ * g * ρ⁻¹, hρT g g.2⟩) := rfl
      _ = (MulAut.characteristic (Subgroup.center ↥N)) (RN * Φ₀ g * RN⁻¹) := by rw [hΦ₀]
      _ = R * Φ g * R⁻¹ := by simp [R, Φ, map_mul]
  have htriv : ∀ g : ↥T, Φ g = 1 :=
    eq_one_of_mulAut_of_card_eq_four_of_quaternion_quotient hNT π hπ hker hT2 hρT hρN hρ3 hρ
      hQ Φ hΦN R hΦρ
  intro g hg x hx
  rw [centerIn_eq_map_center] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : Φ ⟨g, hg⟩ = 1 := htriv ⟨g, hg⟩
  have h2 := congrArg (fun φ : MulAut ↥(Subgroup.center ↥N) => φ ⟨y, hy⟩) h1
  rw [MulAut.one_apply] at h2
  have h3 : (g : G) * (y : G) * (g : G)⁻¹ = (y : G) := by
    have h4 := congrArg Subtype.val h2
    rw [show Φ ⟨g, hg⟩ = (MulAut.characteristic (Subgroup.center ↥N)) (Φ₀ ⟨g, hg⟩) from rfl,
      MulAut.characteristic_apply_apply_coe] at h4
    have h5 := congrArg Subtype.val h4
    rw [hΦ₀_coe] at h5
    simpa using h5
  calc g * (y : G) = ((g : G) * (y : G) * (g : G)⁻¹) * (g : G) := by group
    _ = (y : G) * g := by rw [h3]

theorem commute_of_mem_centerIn_of_pow_three_mem [Finite G] {N : Subgroup G}
    (hZN : Nat.card (centerIn N) = 4) (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    {z : G} (hz : z ∈ centerIn N) (hz1 : z ≠ 1)
    {ρ : G} (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N) (hρz : ρ * z = z * ρ) (hρ3 : ρ ^ 3 ∈ N) :
    ∀ x ∈ centerIn N, ρ * x = x * ρ := by
  classical
  have hK4 : IsKleinFour ↥(centerIn N) := by
    refine IsKleinFour.mk hZN ?_
    have hdvd : Monoid.exponent ↥(centerIn N) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => by
        apply Subtype.ext
        simpa [pow_two] using hZ2 (g : G) g.2)
    have hne : Monoid.exponent ↥(centerIn N) ≠ 1 := by
      intro h1
      have hz' : (⟨z, hz⟩ : ↥(centerIn N)) = 1 := by
        have h := Monoid.pow_exponent_eq_one (⟨z, hz⟩ : ↥(centerIn N))
        rwa [h1, pow_one] at h
      exact hz1 (congrArg Subtype.val hz')
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  have hρZmem : ∀ x ∈ centerIn N, ρ * x * ρ⁻¹ ∈ centerIn N := by
    intro x hx
    have hxN : ρ * x * ρ⁻¹ ∈ N := hρN x hx.1
    refine Subgroup.mem_inf.mpr ⟨hxN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hρinv : ρ⁻¹ * n * ρ ∈ N := conj_inv_mem_of_pow_three_mem hρN hρ3 n hn
    have hxcent : (ρ⁻¹ * n * ρ) * (x : G) = (x : G) * (ρ⁻¹ * n * ρ) :=
      Subgroup.mem_centralizer_iff.mp hx.2 (ρ⁻¹ * n * ρ) hρinv
    calc n * (ρ * x * ρ⁻¹) = (n * ρ) * x * ρ⁻¹ := by group
      _ = (ρ * (ρ⁻¹ * n * ρ)) * x * ρ⁻¹ := by
            rw [show n * ρ = ρ * (ρ⁻¹ * n * ρ) from by group]
      _ = ρ * ((ρ⁻¹ * n * ρ) * x) * ρ⁻¹ := by group
      _ = ρ * (x * (ρ⁻¹ * n * ρ)) * ρ⁻¹ := by rw [hxcent]
      _ = (ρ * x * ρ⁻¹) * n := by group
  have hρZinvmem : ∀ x ∈ centerIn N, ρ⁻¹ * x * ρ ∈ centerIn N := by
    intro x hx
    have hxN : ρ⁻¹ * x * ρ ∈ N := conj_inv_mem_of_pow_three_mem hρN hρ3 x hx.1
    refine Subgroup.mem_inf.mpr ⟨hxN, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hρn : ρ * n * ρ⁻¹ ∈ N := hρN n hn
    have hxcent : (ρ * n * ρ⁻¹) * (x : G) = (x : G) * (ρ * n * ρ⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hx.2 (ρ * n * ρ⁻¹) hρn
    calc n * (ρ⁻¹ * x * ρ) = (n * ρ⁻¹) * x * ρ := by group
      _ = (ρ⁻¹ * (ρ * n * ρ⁻¹)) * x * ρ := by
            rw [show n * ρ⁻¹ = ρ⁻¹ * (ρ * n * ρ⁻¹) from by group]
      _ = ρ⁻¹ * ((ρ * n * ρ⁻¹) * x) * ρ := by group
      _ = ρ⁻¹ * (x * (ρ * n * ρ⁻¹)) * ρ := by rw [hxcent]
      _ = (ρ⁻¹ * x * ρ) * n := by group
  have hρZnorm : ρ ∈ Subgroup.normalizer (centerIn N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨hρZmem x, fun h => by
      have := hρZinvmem (ρ * x * ρ⁻¹) h
      simpa [mul_assoc] using this⟩
  let φ : MulAut ↥(centerIn N) :=
    (Subgroup.normalizerMonoidHom (centerIn N)) ⟨ρ, hρZnorm⟩
  have hφ_coe : ∀ x : ↥(centerIn N), ((φ x : ↥(centerIn N)) : G) = ρ * x * ρ⁻¹ := by
    intro x
    simp [φ]
  have hφpow : ∀ (k : ℕ) (x : ↥(centerIn N)),
      (((φ ^ k) x : ↥(centerIn N)) : G) = ρ ^ k * (x : G) * (ρ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, hφ_coe, ih x]
        rw [pow_succ]
        group
  have hφz : φ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    apply Subtype.ext
    rw [hφ_coe]
    calc ρ * (z : G) * ρ⁻¹ = ((z : G) * ρ) * ρ⁻¹ := by rw [hρz]
      _ = (z : G) := by group
  have hφ3 : φ ^ 3 = 1 := by
    ext x
    rw [hφpow 3 x, MulAut.one_apply]
    have hcomm : (ρ ^ 3 : G) * (x : G) = (x : G) * ρ ^ 3 :=
      Subgroup.mem_centralizer_iff.mp x.2.2 (ρ ^ 3) hρ3
    calc ρ ^ 3 * (x : G) * (ρ ^ 3)⁻¹ = ((x : G) * ρ ^ 3) * (ρ ^ 3)⁻¹ := by rw [hcomm]
      _ = (x : G) := by group
  have hφone : φ = 1 := by
    have horder : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
    rcases (Nat.dvd_prime Nat.prime_three).mp horder with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · have hcyc := kleinFour_order_three_cycle (E := ↥(centerIn N)) φ h3 ⟨z, hz⟩
        (by simpa using hz1)
      exact absurd hφz hcyc.1
  intro x hx
  have h1 : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hφone]; rfl
  have h2 : ((φ ⟨x, hx⟩ : ↥(centerIn N)) : G) = (x : G) := congrArg Subtype.val h1
  rw [hφ_coe] at h2
  calc ρ * x = (ρ * x * ρ⁻¹) * ρ := by group
    _ = x * ρ := by rw [h2]

theorem card_centerIn_eq_eight_and_sq_eq_one_of_quaternion_quotient [Finite G]
    {T N : Subgroup G} (hNT : N ≤ T) (hNnorm : ∀ g ∈ T, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (π : ↥T →* QuaternionGroup 2) (hπ : Function.Surjective π)
    (hker : π.ker = N.subgroupOf T)
    (hN : Nat.card N = 16) (hZN : Nat.card (centerIn N) = 4)
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1)
    {z : G} (hz : z ∈ centerIn N) (hz1 : z ≠ 1)
    {ρ : G} (hρT : ∀ g ∈ T, ρ * g * ρ⁻¹ ∈ T) (hρN : ∀ n ∈ N, ρ * n * ρ⁻¹ ∈ N)
    (hρz : ρ * z = z * ρ) (hρ3 : ρ ^ 3 ∈ N) (hρ : ∃ g ∈ T, ρ * g * ρ⁻¹ * g⁻¹ ∉ N) :
    Nat.card (centerIn T) = 8 ∧ ∀ x ∈ centerIn T, x * x = 1 := by
  classical
  have hQ8card : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hkerCard : Nat.card (N.subgroupOf T) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT).toEquiv
  have hTcard : Nat.card ↥T = 8 * Nat.card ↥N := by
    have h := Subgroup.card_ker_mul_card_of_surjective (G := ↥T) (G' := QuaternionGroup 2) hπ
    rw [hker, hkerCard, hQ8card] at h
    rw [← h]; ring
  have hcardT : Nat.card ↥T = 2 ^ 7 := by
    rw [hTcard, hN]
    norm_num
  have hT2 : IsPGroup 2 ↥T := IsPGroup.of_card hcardT
  have hidx : Nat.card N = 4 * Nat.card (centerIn N) := by
    rw [hN, hZN]
  have hTZ : ∀ g ∈ T, ∀ x ∈ centerIn N, g * x = x * g :=
    commute_of_mem_centerIn_of_quaternion_quotient hNT hNnorm π hπ hker hZN hT2 hρT hρN hρ3 hρ
  have hρZ : ∀ x ∈ centerIn N, ρ * x = x * ρ :=
    commute_of_mem_centerIn_of_pow_three_mem hZN hZ2 hz hz1 hρN hρz hρ3
  obtain ⟨hcard, hsq⟩ :=
    card_centerIn_eq_two_mul_and_sq_eq_one_of_quaternion_quotient hNT hNnorm π hπ hker hidx hZ2 hTZ
      hρT hρN hρZ hρ3 hρ
  exact ⟨by rw [hcard, hZN], hsq⟩

end CFSG.GroupTheory
