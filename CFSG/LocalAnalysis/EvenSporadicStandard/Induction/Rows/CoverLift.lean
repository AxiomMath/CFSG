module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSFuse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuot

public section

namespace CFSG.EvenSporadicStandard.Induction.Cover

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {X : Type} [Group X]

abbrev q (X : Type) [Group X] : X →* X ⧸ center X := QuotientGroup.mk' (center X)

theorem q_apply (x : X) : q X x = (x : X ⧸ center X) := rfl

theorem q_eq_one_iff {x : X} : q X x = 1 ↔ x ∈ center X := QuotientGroup.eq_one_iff x

theorem center_mul_conj {z : X} (hz : z ∈ center X) (w : X) : z * w * z⁻¹ = w := by
  rw [← Subgroup.mem_center_iff.1 hz w]
  group

theorem commutator_central_mul_left {z : X} (hz : z ∈ center X) (x y : X) :
    ⁅z * x, y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  calc z * x * y * (z * x)⁻¹ * y⁻¹ = (z * (x * y * x⁻¹) * z⁻¹) * y⁻¹ := by group
    _ = (x * y * x⁻¹) * y⁻¹ := by rw [center_mul_conj hz]
    _ = x * y * x⁻¹ * y⁻¹ := rfl

theorem commutator_central_mul_right {z : X} (hz : z ∈ center X) (x y : X) :
    ⁅x, z * y⁆ = ⁅x, y⁆ := by
  simp only [commutatorElement_def]
  have h : x * z = z * x := Subgroup.mem_center_iff.1 hz x
  calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
    _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by rw [h]; group
    _ = x * y * x⁻¹ * y⁻¹ := center_mul_conj hz _

theorem commutator_central_mul {z z' : X} (hz : z ∈ center X) (hz' : z' ∈ center X) (m m' : X) :
    ⁅z * m, z' * m'⁆ = ⁅m, m'⁆ := by
  rw [commutator_central_mul_left hz, commutator_central_mul_right hz']

theorem commutator_self_le (M : Subgroup X) : ⁅M, M⁆ ≤ M :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem commutator_sup_center_le (M : Subgroup X) :
    ⁅M ⊔ center X, M ⊔ center X⁆ ≤ ⁅M, M⁆ := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have hc : M ≤ centralizer (center X : Set X) := fun m _ =>
    mem_centralizer_iff.2 fun z hz => (Subgroup.mem_center_iff.1 hz m).symm
  obtain ⟨z, hz, m, hm, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (A := center X) (B := M) hc (sup_comm M (center X) ▸ ha)
  obtain ⟨z', hz', m', hm', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (A := center X) (B := M) hc (sup_comm M (center X) ▸ hb)
  rw [commutator_central_mul hz hz']
  exact Subgroup.commutator_mem_commutator hm hm'

theorem le_of_perfect_of_le_sup_center {P M : Subgroup X} (hP : ⁅P, P⁆ = P)
    (h : P ≤ M ⊔ center X) : P ≤ M := by
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅M ⊔ center X, M ⊔ center X⁆ := Subgroup.commutator_mono h h
    _ ≤ ⁅M, M⁆ := commutator_sup_center_le M
    _ ≤ M := commutator_self_le M

section Finite

variable [Finite X]

omit [Finite X] in
theorem comap_map_q (K : Subgroup X) : (K.map (q X)).comap (q X) = K ⊔ center X := by
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem map_conj_eq_of_perfect {K : Subgroup X} (hK : ⁅K, K⁆ = K) {c : X}
    (hc : ∀ k ∈ K, q X (c * k * c⁻¹) ∈ K.map (q X)) : K.map (conjHom c) = K := by
  have hle : K.map (conjHom c) ≤ K ⊔ center X := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← comap_map_q]
    exact hc k hk
  have hperf : ⁅K.map (conjHom c), K.map (conjHom c)⁆ = K.map (conjHom c) := by
    rw [← Subgroup.map_commutator, hK]
  have h1 := le_of_perfect_of_le_sup_center hperf hle
  exact Subgroup.eq_of_le_of_card_ge h1
    (by rw [Subgroup.card_map_of_injective (conjHom_injective c)])

omit [Finite X] in
theorem mem_centralizer_iff_of_perfect {K : Subgroup X} (hK : ⁅K, K⁆ = K) {x : X} :
    x ∈ centralizer (K : Set X) ↔
      q X x ∈ centralizer ((K.map (q X) : Subgroup (X ⧸ center X)) : Set (X ⧸ center X)) := by
  constructor
  · intro hx
    rw [mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_iff.1 hx k hk
  · intro hx
    have hconj : ∀ k ∈ K, ∃ z ∈ center X, x * k * x⁻¹ = z * k := by
      intro k hk
      have hc : q X k * q X x = q X x * q X k := mem_centralizer_iff.1 hx (q X k) ⟨k, hk, rfl⟩
      have hq : q X (x * k * x⁻¹) = q X k := by
        rw [map_mul, map_mul, map_inv, ← hc]
        group
      refine ⟨(x * k * x⁻¹) * k⁻¹, ?_, by group⟩
      rw [← q_eq_one_iff, map_mul, map_inv, hq]
      group
    have hcomm : ⁅K, K⁆ ≤ centralizer ({x} : Set X) := by
      refine Subgroup.commutator_le.2 fun k₁ hk₁ k₂ hk₂ => ?_
      obtain ⟨z₁, hz₁, h₁⟩ := hconj k₁ hk₁
      obtain ⟨z₂, hz₂, h₂⟩ := hconj k₂ hk₂
      rw [mem_centralizer_singleton_iff]
      have hxc : x * ⁅k₁, k₂⁆ * x⁻¹ = ⁅k₁, k₂⁆ := by
        calc x * ⁅k₁, k₂⁆ * x⁻¹ = ⁅x * k₁ * x⁻¹, x * k₂ * x⁻¹⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅z₁ * k₁, z₂ * k₂⁆ := by rw [h₁, h₂]
          _ = ⁅k₁, k₂⁆ := commutator_central_mul hz₁ hz₂ k₁ k₂
      calc ⁅k₁, k₂⁆ * x = (x * ⁅k₁, k₂⁆ * x⁻¹) * x := by rw [hxc]
        _ = x * ⁅k₁, k₂⁆ := by group
    rw [hK] at hcomm
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizer_singleton_iff.1 (hcomm hk)

variable (hodd : Odd (Nat.card (center X)))
include hodd

omit [Finite X] in
theorem exists_involution_lift {K : Subgroup X} {kt : X ⧸ center X} (hkt : kt ∈ K.map (q X))
    (h2 : kt * kt = 1) : ∃ k ∈ K, k * k = 1 ∧ q X k = kt := by
  obtain ⟨k₀, hk₀, rfl⟩ := hkt
  obtain ⟨j, hj⟩ := hodd
  have hz : k₀ * k₀ ∈ center X := q_eq_one_iff.1 (by rw [map_mul]; exact h2)
  have h1 : (k₀ * k₀) ^ (2 * j + 1) = 1 := by
    have := pow_card_eq_one' (G := ↥(center X)) (x := ⟨k₀ * k₀, hz⟩)
    rw [hj] at this
    exact congrArg Subtype.val this
  refine ⟨k₀ ^ (2 * j + 1), K.pow_mem hk₀ _, ?_, ?_⟩
  · calc k₀ ^ (2 * j + 1) * k₀ ^ (2 * j + 1) = (k₀ * k₀) ^ (2 * j + 1) := by
          rw [(Commute.refl k₀).mul_pow]
      _ = 1 := h1
  · rw [map_pow, pow_succ, pow_mul, sq, h2, one_pow, one_mul]

omit [Finite X] in
theorem mem_centralizer_singleton_iff_mk {u : X} (hu : u * u = 1) {x : X} :
    x ∈ centralizer ({u} : Set X) ↔
      q X x ∈ centralizer ({q X u} : Set (X ⧸ center X)) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    have hc : q X (x * u) = q X (u * x) := by rw [map_mul, map_mul, h]
    have h1 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
      calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu]; group
    have h2 : q X (x * u * x⁻¹) = q X u := by
      rw [map_mul, map_mul, map_inv, h]
      group
    have := Closing.eq_of_mk_eq_of_sq hodd h1 hu h2
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [this]

theorem twoAdic_map_eq (S : Subgroup X) : twoAdic (S.map (q X)) = twoAdic S := by
  have h1 := card_eq_card_map_mul_card_ker (q X) S
  let f : ↥((q X).ker.subgroupOf S) →* ↥(q X).ker :=
    { toFun := fun x => ⟨((x : S) : X), Subgroup.mem_subgroupOf.1 x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥(q X).ker => (z : X)) h))
  have hdvd : Nat.card ((q X).ker.subgroupOf S) ∣ Nat.card (q X).ker :=
    Subgroup.card_dvd_of_injective f hf
  have hkerodd : Odd (Nat.card (q X).ker) := by rw [QuotientGroup.ker_mk']; exact hodd
  have hodd' : Odd (Nat.card ((q X).ker.subgroupOf S)) := hkerodd.of_dvd_nat hdvd
  have hpos1 : Nat.card (S.map (q X)) ≠ 0 := Nat.card_pos.ne'
  have hpos2 : Nat.card ((q X).ker.subgroupOf S) ≠ 0 := Nat.card_pos.ne'
  have hndvd : ¬ 2 ∣ Nat.card ((q X).ker.subgroupOf S) := fun h2 =>
    (Nat.not_even_iff_odd.2 hodd') (even_iff_two_dvd.2 h2)
  unfold twoAdic
  rw [h1, Nat.factorization_mul hpos1 hpos2, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

omit [Finite X] in
theorem map_inf_centralizer_eq (S : Subgroup X) {k : X} (hk : k * k = 1) :
    (S ⊓ centralizer ({k} : Set X)).map (q X) =
      S.map (q X) ⊓ centralizer ({q X k} : Set (X ⧸ center X)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxS, hxk⟩, rfl⟩
    exact ⟨⟨x, hxS, rfl⟩, (mem_centralizer_singleton_iff_mk hodd hk).1 hxk⟩
  · rintro ⟨⟨x, hxS, rfl⟩, hxk⟩
    exact ⟨x, ⟨hxS, (mem_centralizer_singleton_iff_mk hodd hk).2 hxk⟩, rfl⟩

theorem twoAdic_inf_centralizer_map_eq (K : Subgroup X) {k : X} (hk : k * k = 1) :
    twoAdic (K.map (q X) ⊓ centralizer ({q X k} : Set (X ⧸ center X))) =
      twoAdic (K ⊓ centralizer ({k} : Set X)) := by
  rw [← map_inf_centralizer_eq hodd K hk, twoAdic_map_eq hodd]

theorem twoCentralFused_of_quotient {K : Subgroup X} (h : TwoCentralFused (K.map (q X))) :
    TwoCentralFused K := by
  intro k hk k' hk' hk2 hk2' hk1 hk1' hkm hk'm
  have hne : ∀ {a : X}, a * a = 1 → a ≠ 1 → q X a ≠ 1 := fun {a} ha2 ha1 h1 =>
    ha1 (Closing.eq_one_of_sq_eq_one_of_odd_center hodd (q_eq_one_iff.1 h1) ha2)
  have hsq : ∀ {a : X}, a * a = 1 → q X a * q X a = 1 := fun {a} ha2 => by
    rw [← map_mul, ha2, map_one]
  have hcentral : ∀ {a : X}, a * a = 1 → twoAdic K ≤ twoAdic (K ⊓ centralizer ({a} : Set X)) →
      twoAdic (K.map (q X)) ≤
        twoAdic (K.map (q X) ⊓ centralizer ({q X a} : Set (X ⧸ center X))) := fun {a} ha2 hm => by
    rw [twoAdic_inf_centralizer_map_eq hodd K ha2, twoAdic_map_eq hodd]
    exact hm
  obtain ⟨ct, hct, hcc⟩ := h (q X k) ⟨k, hk, rfl⟩ (q X k') ⟨k', hk', rfl⟩ (hsq hk2) (hsq hk2')
    (hne hk2 hk1) (hne hk2' hk1') (hcentral hk2 hkm) (hcentral hk2' hk'm)
  obtain ⟨c, hcK, rfl⟩ := hct
  refine ⟨c, hcK, ?_⟩
  have h1 : (c * k * c⁻¹) * (c * k * c⁻¹) = 1 := by
    calc c * k * c⁻¹ * (c * k * c⁻¹) = c * (k * k) * c⁻¹ := by group
      _ = 1 := by rw [hk2]; group
  refine Closing.eq_of_mk_eq_of_sq hodd h1 hk2' ?_
  rw [← q_apply, ← q_apply, map_mul, map_mul, map_inv]
  exact hcc

end Finite

theorem map_map_q_conjHom (K : Subgroup X) (c : X) :
    (K.map (conjHom c)).map (q X) = (K.map (q X)).map (conjHom (q X c)) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem eq_top_of_map_q_eq_top (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) {M : Subgroup X}
    (h : M.map (q X) = ⊤) : M = ⊤ := by
  have h1 : (⊤ : Subgroup X) ≤ M ⊔ center X := by
    rw [← comap_map_q, h]
    exact le_rfl
  exact top_le_iff.1 (le_of_perfect_of_le_sup_center hX h1)

theorem odd_orderOf_of_mk (hodd : Odd (Nat.card (center X))) {x : X}
    (h : Odd (orderOf (q X x))) : Odd (orderOf x) := by
  have h1 : (x ^ orderOf (q X x)) ∈ center X := by
    rw [← q_eq_one_iff, map_pow]
    exact pow_orderOf_eq_one _
  have h2 : (x ^ orderOf (q X x)) ^ Nat.card (center X) = 1 := by
    have := pow_card_eq_one' (G := ↥(center X)) (x := ⟨x ^ orderOf (q X x), h1⟩)
    exact congrArg Subtype.val this
  have h3 : orderOf x ∣ orderOf (q X x) * Nat.card (center X) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul]
    exact h2
  exact (h.mul hodd).of_dvd_nat h3

end CFSG.EvenSporadicStandard.Induction.Cover
