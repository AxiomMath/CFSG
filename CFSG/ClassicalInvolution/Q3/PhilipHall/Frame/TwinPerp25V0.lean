module

public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion
public import CFSG.ClassicalInvolution.Asc77.AscC5O1G

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Asc77.C5O (eq_one_of_isPGroup_of_odd)

section Frattini

variable {X : Type} [Group X] [Finite X]

theorem mem_sup_normal {P N : Subgroup X} [N.Normal] {h : X} (hh : h ∈ N ⊔ P) :
    ∃ o ∈ N, ∃ p ∈ P, h = o * p := by
  obtain ⟨o, ho, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
  exact ⟨o, ho, p, hp, rfl⟩

theorem conjSubgroup_sup_eq {N P : Subgroup X} [N.Normal] {x : X} (hx : conjSubgroup x P ≤ P ⊔ N) :
    conjSubgroup x (P ⊔ N) = P ⊔ N := by
  have hN : conjSubgroup x N = N := by
    ext y
    rw [mem_conjSubgroup_iff]
    constructor
    · intro hy
      have := (inferInstance : N.Normal).conj_mem _ hy x
      simpa [mul_assoc] using this
    · intro hy
      have := (inferInstance : N.Normal).conj_mem _ hy x⁻¹
      simpa [mul_assoc] using this
  have hle : conjSubgroup x (P ⊔ N) ≤ P ⊔ N := by
    unfold conjSubgroup at *
    rw [Subgroup.map_sup]
    exact sup_le hx ((le_of_eq hN).trans le_sup_right)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_conjSubgroup]

theorem frattini_lift {N P : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    {x : X} (hx : conjSubgroup x P ≤ P ⊔ N) :
    ∃ o ∈ N, conjSubgroup (o⁻¹ * x) P = P := by
  have hH : IsSylow2Of P (N ⊔ P) := by
    refine ⟨le_sup_right, hP, fun P' hP'H hP'2 hPP' => ?_⟩
    refine le_antisymm (fun p' hp' => ?_) hPP'
    obtain ⟨o, ho, p, hp, hop⟩ := mem_sup_normal (hP'H hp')
    have hpP' : p ∈ P' := hPP' hp
    have hoP' : o ∈ P' := by
      have : o = p' * p⁻¹ := by rw [hop]; group
      rw [this]
      exact P'.mul_mem hp' (P'.inv_mem hpP')
    have ho1 : o = 1 := eq_one_of_isPGroup_of_odd hP'2 hN hoP' ho
    rw [hop, ho1, one_mul]
    exact hp
  have hxH : conjSubgroup x (N ⊔ P) = N ⊔ P := by
    rw [sup_comm]
    exact conjSubgroup_sup_eq hx
  have hQ : IsSylow2Of (conjSubgroup x P) (N ⊔ P) := by
    refine ⟨?_, isPGroup_conjSubgroup hP, fun P' hP'H hP'2 hPP' => ?_⟩
    · rw [sup_comm]
      exact hx
    · have h1 : conjSubgroup x⁻¹ P' ≤ N ⊔ P :=
        calc conjSubgroup x⁻¹ P' ≤ conjSubgroup x⁻¹ (N ⊔ P) := conjSubgroup_mono hP'H
          _ = conjSubgroup x⁻¹ (conjSubgroup x (N ⊔ P)) := by rw [hxH]
          _ = N ⊔ P := conjSubgroup_inv_conjSubgroup _ _
      have h2 : P ≤ conjSubgroup x⁻¹ P' := by
        calc P = conjSubgroup x⁻¹ (conjSubgroup x P) := (conjSubgroup_inv_conjSubgroup _ _).symm
          _ ≤ conjSubgroup x⁻¹ P' := conjSubgroup_mono hPP'
      have h3 : conjSubgroup x⁻¹ P' = P := hH.2.2 _ h1 (isPGroup_conjSubgroup hP'2) h2
      calc P' = conjSubgroup x (conjSubgroup x⁻¹ P') := (conjSubgroup_conjSubgroup_inv _ _).symm
        _ = conjSubgroup x P := by rw [h3]
  obtain ⟨h, hh, hconj⟩ := IsSylow2Of.exists_conj hH hQ
  obtain ⟨o, ho, p, hp, rfl⟩ := mem_sup_normal hh
  refine ⟨o, ho, ?_⟩
  rw [← conjSubgroup_conjSubgroup, hconj, ← conjSubgroup_conjSubgroup,
    conjSubgroup_eq_self_of_mem hp, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

theorem exists_pow_two_part (g : X) :
    ∃ s m : ℕ, Odd m ∧ orderOf g = 2 ^ s * m ∧ IsPGroup 2 (Subgroup.zpowers (g ^ m)) := by
  obtain ⟨s, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨s, m, hm, hn, ?_⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hord : orderOf (g ^ m) = 2 ^ s := by
    rw [orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hn.symm), hn, Nat.mul_div_cancel _ hm.pos]
  exact IsPGroup.of_card (n := s) (by rw [Nat.card_zpowers, hord])

theorem exists_involution_lift {N P : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P)
    {τ : X} (hτ : τ * τ = 1) (hτP : conjSubgroup τ P ≤ P ⊔ N) :
    ∃ ν ∈ N, conjSubgroup (ν * τ * ν⁻¹) P = P := by
  obtain ⟨o, ho, hn⟩ := frattini_lift hN hP hτP
  set n : X := o⁻¹ * τ with hn_def
  obtain ⟨s, m, hm, hord, h2⟩ := exists_pow_two_part n
  set n₂ : X := n ^ m with hn₂
  have hnP : ∀ k : ℕ, conjSubgroup (n ^ k) P = P := by
    intro k
    induction k with
    | zero => rw [pow_zero, conjSubgroup_one]
    | succ k ih => rw [pow_succ, ← conjSubgroup_conjSubgroup, hn, ih]
  have hn₂P : conjSubgroup n₂ P = P := hnP m
  have ho1 : QuotientGroup.mk' N o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hmk : QuotientGroup.mk' N n = QuotientGroup.mk' N τ := by
    rw [hn_def, map_mul, map_inv, ho1, inv_one, one_mul]
  have hτ2 : QuotientGroup.mk' N τ * QuotientGroup.mk' N τ = 1 := by
    rw [← map_mul, hτ, map_one]
  have hmk₂ : QuotientGroup.mk' N n₂ = QuotientGroup.mk' N τ := by
    obtain ⟨k, hk⟩ := hm
    rw [hn₂, map_pow, hmk, hk, pow_succ, pow_mul, pow_two, hτ2, one_pow, one_mul]
  have hn₂N : n₂ * n₂ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, hmk₂, hτ2]
  have hn₂sq : n₂ * n₂ = 1 :=
    eq_one_of_isPGroup_of_odd h2 hN (Subgroup.mul_mem _ (Subgroup.mem_zpowers n₂)
      (Subgroup.mem_zpowers n₂)) hn₂N
  have hτn₂ : τ * n₂ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, hmk₂, hτ2]
  obtain ⟨ν, hν, hνn⟩ := CFSG.ClassicalInvolution.Asc77.C25Y.exists_conj_of_involutions_odd hN hτ hn₂sq hτn₂
  exact ⟨ν, hν, by rw [← hνn]; exact hn₂P⟩

end Frattini

theorem mem_sup_comm {G : Type} [Group G] {P Q : Subgroup G} (h : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    {e : G} (he : e ∈ P ⊔ Q) : ∃ x ∈ P, ∃ y ∈ Q, e = x * y := by
  rw [Subgroup.sup_eq_closure] at he
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ he
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, Q.one_mem, (mul_one x).symm⟩
    · exact ⟨1, P.one_mem, x, hx, (one_mul x).symm⟩
  · exact ⟨1, P.one_mem, 1, Q.one_mem, (mul_one 1).symm⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, P.mul_mem hy₁ hy₂, z₁ * z₂, Q.mul_mem hz₁ hz₂, ?_⟩
    calc y₁ * z₁ * (y₂ * z₂) = y₁ * (z₁ * y₂) * z₂ := by group
      _ = y₁ * (y₂ * z₁) * z₂ := by rw [← h y₂ hy₂ z₁ hz₁]
      _ = y₁ * y₂ * (z₁ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, P.inv_mem hy, z⁻¹, Q.inv_mem hz, ?_⟩
    calc (y * z)⁻¹ = z⁻¹ * y⁻¹ := by group
      _ = y⁻¹ * z⁻¹ := by rw [← h y⁻¹ (P.inv_mem hy) z⁻¹ (Q.inv_mem hz)]

theorem conj_mem_sup_of {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (hA : ∀ x ∈ A, g * x * g⁻¹ ∈ A ⊔ B) (hB : ∀ x ∈ B, g * x * g⁻¹ ∈ A ⊔ B) :
    ∀ x ∈ A ⊔ B, g * x * g⁻¹ ∈ A ⊔ B := by
  have h1 : A ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := fun x hx => by
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hA x hx
  have h2 : B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := fun x hx => by
    simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hB x hx
  intro x hx
  have := sup_le h1 h2 hx
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

theorem norm_inv_of_norm {G : Type} [Group G] [Finite G] {P : Subgroup G} {n : G}
    (h : ∀ y ∈ P, n * y * n⁻¹ ∈ P) : ∀ y ∈ P, n⁻¹ * y * n ∈ P := by
  have hle : conjSubgroup n P ≤ P := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    exact h y hy
  have heq : conjSubgroup n P = P := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  intro y hy
  rw [← heq] at hy
  exact mem_conjSubgroup_iff.mp hy

section Lift

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf {X N : Subgroup G} (hNX : N ≤ X) (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    (N.subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact hNn g g.2 n hn

theorem frattini_G {X N P : Subgroup G} (hNX : N ≤ X) (hPX : P ≤ X)
    (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ X) (hxP : ∀ y ∈ P, ∃ y' ∈ P, ∃ n ∈ N, x * y * x⁻¹ = y' * n) :
    ∃ o ∈ N, ∀ y ∈ P, (o⁻¹ * x) * y * (o⁻¹ * x)⁻¹ ∈ P := by
  haveI := normal_subgroupOf hNX hNn
  have hNodd : Odd (Nat.card (N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact hN
  have hP2 : IsPGroup 2 (P.subgroupOf X) := hP.comap_subtype
  have hxle : conjSubgroup (⟨x, hx⟩ : X) (P.subgroupOf X) ≤ P.subgroupOf X ⊔ N.subgroupOf X := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨y', hy', n, hn, he⟩ := hxP (y : G) (Subgroup.mem_subgroupOf.mp hy)
    have e : (MulAut.conj (⟨x, hx⟩ : X)).toMonoidHom y =
        (⟨y', hPX hy'⟩ : X) * (⟨n, hNX hn⟩ : X) := by
      apply Subtype.ext
      exact he
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hy') (Subgroup.mem_subgroupOf.mpr hn)
  obtain ⟨o, ho, hoe⟩ := frattini_lift hNodd hP2 hxle
  refine ⟨(o : G), Subgroup.mem_subgroupOf.mp ho, fun y hy => ?_⟩
  have hmem : (⟨y, hPX hy⟩ : X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hy
  have h1 := mem_conjSubgroup_of_mem (g := o⁻¹ * (⟨x, hx⟩ : X)) hmem
  rw [hoe] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem involution_G {X N P : Subgroup G} (hNX : N ≤ X) (hPX : P ≤ X)
    (hNn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN : Odd (Nat.card N)) (hP : IsPGroup 2 P) {τ : G}
    (hτ : τ ∈ X) (hτ2 : τ * τ = 1) (hτP : ∀ y ∈ P, ∃ y' ∈ P, ∃ n ∈ N, τ * y * τ⁻¹ = y' * n) :
    ∃ ν ∈ N, ∀ y ∈ P, (ν * τ * ν⁻¹) * y * (ν * τ * ν⁻¹)⁻¹ ∈ P := by
  haveI := normal_subgroupOf hNX hNn
  have hNodd : Odd (Nat.card (N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact hN
  have hP2 : IsPGroup 2 (P.subgroupOf X) := hP.comap_subtype
  have hxle : conjSubgroup (⟨τ, hτ⟩ : X) (P.subgroupOf X) ≤ P.subgroupOf X ⊔ N.subgroupOf X := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨y', hy', n, hn, he⟩ := hτP (y : G) (Subgroup.mem_subgroupOf.mp hy)
    have e : (MulAut.conj (⟨τ, hτ⟩ : X)).toMonoidHom y =
        (⟨y', hPX hy'⟩ : X) * (⟨n, hNX hn⟩ : X) := by
      apply Subtype.ext
      exact he
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hy') (Subgroup.mem_subgroupOf.mpr hn)
  have hτ2' : (⟨τ, hτ⟩ : X) * ⟨τ, hτ⟩ = 1 := Subtype.ext hτ2
  obtain ⟨ν, hν, hνe⟩ := exists_involution_lift hNodd hP2 hτ2' hxle
  refine ⟨(ν : G), Subgroup.mem_subgroupOf.mp hν, fun y hy => ?_⟩
  have hmem : (⟨y, hPX hy⟩ : X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hy
  have h1 := mem_conjSubgroup_of_mem (g := ν * (⟨τ, hτ⟩ : X) * ν⁻¹) hmem
  rw [hνe] at h1
  exact Subgroup.mem_subgroupOf.mp h1

end Lift

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
