module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55HH

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

section Act

variable {Γ : Type} [Group Γ] {K : Subgroup Γ} [K.Normal]

@[expose] noncomputable def actY (g : Γ) : MulAut (K ⧸ center ↥K) :=
  QuotientGroup.congr (center ↥K) (center ↥K) (MulAut.conjNormal g : MulAut ↥K)
    (Subgroup.map_center_eq _)

theorem actY_mk (g : Γ) (k : ↥K) :
    actY g (QuotientGroup.mk k : K ⧸ center ↥K) =
      QuotientGroup.mk (MulAut.conjNormal g k : ↥K) := rfl

@[expose] noncomputable def actYHom : Γ →* MulAut (K ⧸ center ↥K) where
  toFun := actY
  map_one' := by
    ext w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    show actY 1 (QuotientGroup.mk k : K ⧸ center ↥K) = _
    rw [actY_mk, map_one]
    rfl
  map_mul' g h := by
    ext w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    show actY (g * h) (QuotientGroup.mk k : K ⧸ center ↥K) = _
    rw [actY_mk, map_mul]
    rfl

theorem actYHom_mk (g : Γ) (k : ↥K) :
    actYHom g (QuotientGroup.mk k : K ⧸ center ↥K) =
      QuotientGroup.mk (MulAut.conjNormal g k : ↥K) := rfl

theorem actYHom_of_mem {s : Γ} (hs : s ∈ K) :
    actYHom (K := K) s = MulAut.conj (QuotientGroup.mk (⟨s, hs⟩ : ↥K) : K ⧸ center ↥K) := by
  ext w
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
  rw [actYHom_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

omit [K.Normal] in
theorem center_quot_eq_bot (hq : IsQuasisimple ↥K) : center (K ⧸ center ↥K) = ⊥ := by
  have : Group.IsPerfect ↥K := hq.1
  exact Group.IsPerfect.center_quotient_center_eq_bot ↥K

theorem eq_one_of_conj_eq_one {Y : Type} [Group Y] (hY : center Y = ⊥) {y : Y}
    (h : MulAut.conj y = 1) : y = 1 := by
  have hy : y ∈ center Y := by
    rw [Subgroup.mem_center_iff]
    intro w
    have := congrArg (fun φ : MulAut Y => φ w) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc w * y = (y * w * y⁻¹) * y := by rw [this]
      _ = y * w := by group
  rw [hY] at hy
  exact hy

end Act

section CaseA

@[expose] def BorelTitsConcl (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ U : Subgroup Y, U ≠ ⊥ → IsPGroup p ↥U →
    ∃ (S : Sylow p Y) (M : Subgroup Y), M ≠ ⊤ ∧ normalizer (U : Set Y) ≤ M ∧
      normalizer ((S : Subgroup Y) : Set Y) ≤ M

@[expose] def EvenParabolics (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ (S : Sylow p Y) (M : Subgroup Y), normalizer ((S : Subgroup Y) : Set Y) ≤ M → M ≠ ⊤ →
    Even M.index

theorem false_of_odd_index_le_normalizer {p : ℕ} {Y : Type} [Group Y]
    (hBT : BorelTitsConcl p Y) (hEP : EvenParabolics p Y) {U S0 : Subgroup Y} (hU : U ≠ ⊥)
    (hUp : IsPGroup p ↥U) (hS0 : Odd S0.index) (hN : S0 ≤ normalizer (U : Set Y)) : False := by
  obtain ⟨S, M, hM, hUM, hSM⟩ := hBT U hU hUp
  have hev := hEP S M hSM hM
  have hdvd : M.index ∣ S0.index := Subgroup.index_dvd_of_le (hN.trans hUM)
  exact (Nat.not_even_iff_odd.mpr hS0) (even_iff_two_dvd.mpr
    ((even_iff_two_dvd.mp hev).trans hdvd))

end CaseA

section Inner

variable {Γ : Type} [Group Γ] {K : Subgroup Γ} [K.Normal]

@[expose] noncomputable def innerPart (P : Subgroup Γ) : Subgroup (K ⧸ center ↥K) :=
  (P.map (actYHom (K := K))).comap
    (MulAut.conj : (K ⧸ center ↥K) →* MulAut (K ⧸ center ↥K))

theorem mem_innerPart {P : Subgroup Γ} {y : K ⧸ center ↥K} :
    y ∈ innerPart (K := K) P ↔ ∃ x ∈ P, actYHom (K := K) x = MulAut.conj y := by
  simp only [innerPart, Subgroup.mem_comap, Subgroup.mem_map]

theorem isPGroup_innerPart {p : ℕ} {P : Subgroup Γ} (hY : center (K ⧸ center ↥K) = ⊥)
    (hP : IsPGroup p ↥P) : IsPGroup p ↥(innerPart (K := K) P) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, hxy⟩ := mem_innerPart.mp hy
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxn : x ^ p ^ n = 1 := congrArg Subtype.val hn
  refine ⟨n, Subtype.ext ?_⟩
  have h1 : MulAut.conj (y ^ p ^ n) = 1 := by
    rw [map_pow, ← hxy, ← map_pow, hxn, map_one]
  exact eq_one_of_conj_eq_one hY h1

theorem conj_mem_innerPart {P R : Subgroup Γ} (hR : R ≤ normalizer (P : Set Γ)) {s : Γ}
    (hsR : s ∈ R) (hsK : s ∈ K) {y : K ⧸ center ↥K} (hy : y ∈ innerPart (K := K) P) :
    (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : K ⧸ center ↥K) * y *
      (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : K ⧸ center ↥K)⁻¹ ∈ innerPart (K := K) P := by
  obtain ⟨x, hx, hxy⟩ := mem_innerPart.mp hy
  refine mem_innerPart.mpr ⟨s * x * s⁻¹, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hR hsR) x).mp hx
  · rw [map_mul, map_mul, map_inv, hxy, actYHom_of_mem hsK, map_mul, map_mul, map_inv]

theorem mk_mem_normalizer_innerPart {P R : Subgroup Γ} (hR : R ≤ normalizer (P : Set Γ)) {s : Γ}
    (hsR : s ∈ R) (hsK : s ∈ K) :
    (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : K ⧸ center ↥K) ∈
      normalizer ((innerPart (K := K) P : Subgroup (K ⧸ center ↥K)) : Set (K ⧸ center ↥K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_innerPart hR hsR hsK, fun h => ?_⟩
  have h' := conj_mem_innerPart (K := K) hR (inv_mem hsR) (inv_mem hsK) h
  have e : (QuotientGroup.mk (⟨s⁻¹, inv_mem hsK⟩ : ↥K) : K ⧸ center ↥K) =
      (QuotientGroup.mk (⟨s, hsK⟩ : ↥K) : K ⧸ center ↥K)⁻¹ := by
    rw [← QuotientGroup.mk_inv]
    rfl
  rw [e] at h'
  simpa [mul_assoc] using h'

end Inner

section Frame

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} [K.Normal] {a : Γ}
  {P R : Subgroup Γ}

theorem commute_of_actYHom_eq_one (hq : IsQuasisimple ↥K) {g : Γ} (h1 : actYHom (K := K) g = 1)
    {x : Γ} (hx : x ∈ K) : g * x = x * g := by
  set φ : MulAut ↥K := MulAut.conjNormal g with hφ
  have hcen : ∀ y : ↥K, y⁻¹ * φ y ∈ center ↥K := by
    intro y
    have h2 := congrArg (fun α : MulAut (K ⧸ center ↥K) => α (QuotientGroup.mk y)) h1
    simp only [MulAut.one_apply] at h2
    rw [← QuotientGroup.eq]
    exact h2.symm
  let δ : ↥K →* ↥(center ↥K) :=
    { toFun := fun y => ⟨y⁻¹ * φ y, hcen y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro y z
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hcen y) z⁻¹
        calc (y * z)⁻¹ * φ (y * z) = z⁻¹ * (y⁻¹ * φ y) * φ z := by
              rw [map_mul, mul_inv_rev]
              group
          _ = (y⁻¹ * φ y * z⁻¹) * φ z := by rw [hc]
          _ = (y⁻¹ * φ y) * (z⁻¹ * φ z) := by group }
  have hker : commutator ↥K ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hq.1.commutator_eq_top] at hker
  have hδ : ∀ y : ↥K, φ y = y := by
    intro y
    have := (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top y)))
    have h3 := congrArg Subtype.val this
    simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h3
    calc φ y = y * (y⁻¹ * φ y) := by group
      _ = y := by rw [h3, mul_one]
  have := congrArg Subtype.val (hδ ⟨x, hx⟩)
  rw [hφ, MulAut.conjNormal_apply] at this
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [show g * x * g⁻¹ = x from this]

theorem Mod55.actYHom_ne_one (hf : Mod55 p ρ K a P) : actYHom (K := K) a ≠ 1 := by
  intro h1
  apply hf.acts
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : a * x = x * a := commute_of_actYHom_eq_one hf.quasi h1 hx
  have : Commute (a ^ n) x := (Commute.zpow_left (show Commute a x from hc) n)
  rw [Subgroup.mem_bot, commutatorElement_def]
  have h3 : x * a ^ n = a ^ n * x := this.symm.eq
  calc x * a ^ n * x⁻¹ * (a ^ n)⁻¹ = (a ^ n * x) * x⁻¹ * (a ^ n)⁻¹ := by rw [h3]
    _ = 1 := by group

theorem Mod55.actYHom_pow [Finite Γ] [Module.Finite (ZMod p) V] (hf : Mod55 p ρ K a P) :
    actYHom (K := K) a ^ p = 1 := by
  rw [← map_pow, hf.pow_prime, map_one]

end Frame

section CaseAFrame

variable {k : Kind} {p : ℕ} {Γ : Type} [Group Γ] [Finite Γ] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V] {ρ : Γ →* (V →ₗ[ZMod p] V)ˣ} {K : Subgroup Γ} [K.Normal] {a : Γ}
  {P R : Subgroup Γ}

theorem Frame55.false_of_innerPart_ne_bot (hf : Frame55 k p ρ K a P R)
    (hBT : BorelTitsConcl p (K ⧸ center ↥K)) (hEP : EvenParabolics p (K ⧸ center ↥K))
    (hU : innerPart (K := K) P ≠ ⊥) : False := by
  obtain ⟨Q, hQ⟩ := hf.sylow
  have hUp : IsPGroup p ↥(innerPart (K := K) P) :=
    isPGroup_innerPart (center_quot_eq_bot hf.quasi) hf.pgrp
  let π : ↥K →* K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S0 : Subgroup (K ⧸ center ↥K) := (Q : Subgroup ↥K).map π
  have hS0N : S0 ≤ normalizer ((innerPart (K := K) P : Subgroup (K ⧸ center ↥K)) :
      Set (K ⧸ center ↥K)) := by
    rintro _ ⟨q, hq, rfl⟩
    have hqRK : (q : Γ) ∈ R ⊓ K := by
      rw [← hQ]
      exact ⟨q, hq, rfl⟩
    exact mk_mem_normalizer_innerPart hf.norm hqRK.1 hqRK.2
  have hS0 : Odd S0.index := by
    have h1 : S0.index ∣ (Q : Subgroup ↥K).index := Subgroup.index_map_dvd (Q : Subgroup ↥K) hπ
    have h2 : ¬ 2 ∣ (Q : Subgroup ↥K).index := Sylow.not_dvd_index Q
    by_contra hodd
    exact h2 ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)).trans h1)
  exact false_of_odd_index_le_normalizer hBT hEP hU hUp hS0 hS0N

end CaseAFrame

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
