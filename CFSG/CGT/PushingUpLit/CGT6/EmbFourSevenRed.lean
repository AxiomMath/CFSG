module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG

theorem perfect_map_eq_one {Γ : Type*} [Group Γ] [Group.IsPerfect Γ] {M : Type*} [Group M]
    [IsMulCommutative M] (χ : Γ → M) (hχ : ∀ g h, χ (g * h) = χ g * χ h) : ∀ g, χ g = 1 := by
  let f : Γ →* M := MonoidHom.mk' χ hχ
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  intro s
  have h : (⟨f s, s, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

section Stable

variable {G : Type*} [Group G]

theorem stable_mem_centralizer {Y X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN : N ≤ Subgroup.centralizer (Y : Set G))
    {x : G} (hx : x ∈ X) {y : G} (hy : y ∈ Y) :
    x⁻¹ * (y * x * y⁻¹) ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : y * f * y⁻¹ = f := by
    have := (Subgroup.mem_centralizer_iff.mp (hN hf)) y hy
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have h2 : x * f * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hXN hx) f).mp hf
  have h3 : y * (x * f * x⁻¹) * y⁻¹ = x * f * x⁻¹ := by
    have := (Subgroup.mem_centralizer_iff.mp (hN h2)) y hy
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have h5 : y⁻¹ * f * y = f := by
    calc y⁻¹ * f * y = y⁻¹ * (y * f * y⁻¹) * y := by rw [h1]
      _ = f := by group
  have h4 : (y * x * y⁻¹) * f * (y * x * y⁻¹)⁻¹ = x * f * x⁻¹ := by
    calc (y * x * y⁻¹) * f * (y * x * y⁻¹)⁻¹
        = y * (x * (y⁻¹ * f * y) * x⁻¹) * y⁻¹ := by group
      _ = y * (x * f * x⁻¹) * y⁻¹ := by rw [h5]
      _ = x * f * x⁻¹ := h3
  calc f * (x⁻¹ * (y * x * y⁻¹))
      = x⁻¹ * ((x * f * x⁻¹) * (y * x * y⁻¹)) := by group
    _ = x⁻¹ * ((y * x * y⁻¹) * f) := by
      rw [← h4]
      group
    _ = (x⁻¹ * (y * x * y⁻¹)) * f := by group

theorem le_centralizer_of_stable {Y X N : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hN : N ≤ Subgroup.centralizer (Y : Set G))
    (hd : ∀ x ∈ X, ∀ y ∈ Y, x⁻¹ * (y * x * y⁻¹) ∈ N) :
    X ≤ Subgroup.centralizer (Y : Set G) := by
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  have hZ : ∀ y : ↥Y, x⁻¹ * ((y : G) * x * (y : G)⁻¹) ∈ N ⊓ Subgroup.centralizer (N : Set G) :=
    fun y => ⟨hd x hx y y.2, stable_mem_centralizer hXN hN hx y.2⟩
  have : IsMulCommutative ↥(N ⊓ Subgroup.centralizer (N : Set G)) :=
    ⟨⟨fun a b => Subtype.ext (by
      have := (Subgroup.mem_centralizer_iff.mp b.2.2) a a.2.1
      exact this)⟩⟩
  have key := perfect_map_eq_one (M := ↥(N ⊓ Subgroup.centralizer (N : Set G)))
    (fun y : ↥Y => (⟨x⁻¹ * ((y : G) * x * (y : G)⁻¹), hZ y⟩ :
      ↥(N ⊓ Subgroup.centralizer (N : Set G)))) (fun y y' => by
      apply Subtype.ext
      show x⁻¹ * (((y : G) * (y' : G)) * x * ((y : G) * (y' : G))⁻¹) =
        (x⁻¹ * ((y : G) * x * (y : G)⁻¹)) * (x⁻¹ * ((y' : G) * x * (y' : G)⁻¹))
      have h5 : (y : G) * (x⁻¹ * ((y' : G) * x * (y' : G)⁻¹)) * (y : G)⁻¹ =
          x⁻¹ * ((y' : G) * x * (y' : G)⁻¹) := by
        have := Subgroup.mem_centralizer_iff.mp (hN (hd x hx y' y'.2)) y y.2
        rw [mul_inv_eq_iff_eq_mul]
        exact this
      calc x⁻¹ * (((y : G) * (y' : G)) * x * ((y : G) * (y' : G))⁻¹)
          = x⁻¹ * ((y : G) * ((y' : G) * x * (y' : G)⁻¹) * (y : G)⁻¹) := by group
        _ = x⁻¹ * ((y : G) * (x * (x⁻¹ * ((y' : G) * x * (y' : G)⁻¹))) * (y : G)⁻¹) := by
            congr 3; group
        _ = (x⁻¹ * ((y : G) * x * (y : G)⁻¹)) *
            ((y : G) * (x⁻¹ * ((y' : G) * x * (y' : G)⁻¹)) * (y : G)⁻¹) := by group
        _ = (x⁻¹ * ((y : G) * x * (y : G)⁻¹)) * (x⁻¹ * ((y' : G) * x * (y' : G)⁻¹)) := by
            rw [h5])
  intro y hy
  have h6 := congrArg Subtype.val (key ⟨y, hy⟩)
  have h7 : x⁻¹ * (y * x * y⁻¹) = 1 := h6
  rw [inv_mul_eq_one, eq_comm, mul_inv_eq_iff_eq_mul] at h7
  exact h7

end Stable

section Minimal

variable {G : Type} [Group G] [Finite G]

@[expose] def normConj (X : Subgroup G) (y : G) (hy : y ∈ Subgroup.normalizer (X : Set G)) :
    ↥X ≃* ↥X where
  toFun x := ⟨y * x * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy (x : G)).mp x.2⟩
  invFun x := ⟨y⁻¹ * x * y, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hy) (x : G)).mp x.2
    simpa using this⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

omit [Finite G] in
theorem coe_normConj (X : Subgroup G) (y : G) (hy : y ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) : ((normConj X y hy x : ↥X) : G) = y * x * y⁻¹ := rfl

omit [Finite G] in
theorem mem_normalizer_map_subtype_of_characteristic {X : Subgroup G} (K : Subgroup ↥X)
    [hK : K.Characteristic] {y : G} (hy : y ∈ Subgroup.normalizer (X : Set G)) :
    y ∈ Subgroup.normalizer ((K.map X.subtype : Subgroup G) : Set G) := by
  have hfix := Subgroup.characteristic_iff_map_eq.mp hK (normConj X y hy)
  have hiff : ∀ k : ↥X, normConj X y hy k ∈ K ↔ k ∈ K := by
    intro k
    constructor
    · intro hk
      rw [← hfix] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      have : k' = k := (normConj X y hy).injective hkk
      rwa [← this]
    · intro hk
      rw [← hfix]
      exact ⟨k, hk, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨normConj X y hy k, (hiff k).mpr hk, rfl⟩
  · rintro ⟨k', hk', hz⟩
    have hzX : z ∈ X := by
      have h1 : y * z * y⁻¹ ∈ X := by rw [← hz]; exact k'.2
      exact (Subgroup.mem_normalizer_iff.mp hy z).mpr h1
    refine ⟨⟨z, hzX⟩, (hiff ⟨z, hzX⟩).mp ?_, rfl⟩
    have : normConj X y hy ⟨z, hzX⟩ = k' := Subtype.ext hz.symm
    rw [this]
    exact hk'

theorem exists_prime_pCore_not_centralized {X Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (hXs : Group.IsSolvable ↥X) (hYX : Y ≤ Subgroup.normalizer (X : Set G))
    (hne : ¬ X ≤ Subgroup.centralizer (Y : Set G)) :
    ∃ q : ℕ, q.Prime ∧ ¬ ((pCore q ↥X).map X.subtype ≤ Subgroup.centralizer (Y : Set G)) := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hF : (fittingSubgroup ↥X).map X.subtype ≤ Subgroup.centralizer (Y : Set G) := by
    rw [fitting_eq_sup_pCore, Subgroup.map_iSup]
    exact iSup_le fun q => hcon q.1.1 (Nat.prime_of_mem_primeFactors q.1.2)
  have hXN : X ≤ Subgroup.normalizer (((fittingSubgroup ↥X).map X.subtype : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_map_subtype_of_characteristic (fittingSubgroup ↥X)
      (Subgroup.le_normalizer hx)
  refine le_centralizer_of_stable (N := (fittingSubgroup ↥X).map X.subtype) hY hXN hF ?_
  intro x hx y hy
  have hc := stable_mem_centralizer (Y := Y) (X := X)
    (N := (fittingSubgroup ↥X).map X.subtype) hXN hF hx hy
  have hxy : y * x * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hYX hy) x).mp hx
  set d : ↥X := (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y * x * y⁻¹, hxy⟩ with hd
  have hdG : (d : G) = x⁻¹ * (y * x * y⁻¹) := rfl
  have hdF : d ∈ fittingSubgroup ↥X := by
    refine centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hXs ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h1 : (f : G) * (d : G) = (d : G) * (f : G) := by
      rw [hdG]
      exact Subgroup.mem_centralizer_iff.mp hc (f : G) ⟨f, hf, rfl⟩
    exact Subtype.ext h1
  exact ⟨d, hdF, hdG⟩

theorem isPGroup_map_subtype {q : ℕ} [Fact q.Prime] {X : Subgroup G} {K : Subgroup ↥X}
    (hK : IsPGroup q K) : IsPGroup q ↥(K.map X.subtype) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
  exact IsPGroup.iff_card.mpr ⟨n, by rw [Subgroup.card_map_of_injective X.subtype_injective, hn]⟩

theorem exists_minimal_pSubgroup {X Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hX : Odd (Nat.card X))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hne : ¬ X ≤ Subgroup.centralizer (Y : Set G)) :
    ∃ (p : ℕ) (P : Subgroup G), p.Prime ∧ Odd p ∧ P ≤ X ∧ IsPGroup p P ∧
      Y ≤ Subgroup.normalizer (P : Set G) ∧ ¬ P ≤ Subgroup.centralizer (Y : Set G) ∧
      ∀ Q : Subgroup G, Q < P → Y ≤ Subgroup.normalizer (Q : Set G) →
        Q ≤ Subgroup.centralizer (Y : Set G) := by
  classical
  have hXs : Group.IsSolvable ↥X := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hX
  obtain ⟨q, hq, hQ₀⟩ := exists_prime_pCore_not_centralized hY hXs hYX hne
  have : Fact q.Prime := ⟨hq⟩
  let T : Subgroup G → Prop := fun Q => Q ≤ X ∧ IsPGroup q Q ∧
    Y ≤ Subgroup.normalizer (Q : Set G) ∧ ¬ Q ≤ Subgroup.centralizer (Y : Set G)
  have hT0 : T ((pCore q ↥X).map X.subtype) :=
    ⟨by rintro _ ⟨k, -, rfl⟩; exact k.2, isPGroup_map_subtype pCore_isPGroup,
      fun y hy => mem_normalizer_map_subtype_of_characteristic (pCore q ↥X) (hYX hy), hQ₀⟩
  have hex : ∃ n, ∃ Q, T Q ∧ Nat.card Q = n := ⟨_, _, hT0, rfl⟩
  obtain ⟨P, hP, hPn⟩ := Nat.find_spec hex
  have hmin : ∀ Q, T Q → Nat.card P ≤ Nat.card Q := fun Q hQ => by
    rw [hPn]
    exact Nat.find_min' hex ⟨Q, hQ, rfl⟩
  refine ⟨q, P, hq, ?_, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, ?_⟩
  · have hPbot : P ≠ ⊥ := fun h => hP.2.2.2 (h ▸ bot_le)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP.2.1
    have hn0 : n ≠ 0 := fun h0 => hPbot (Subgroup.eq_bot_of_card_eq P (by rw [hn, h0, pow_zero]))
    have hdvd : q ∣ Nat.card X :=
      (dvd_pow_self q hn0).trans (hn ▸ Subgroup.card_dvd_of_le hP.1)
    exact Odd.of_dvd_nat hX hdvd
  · intro Q hQP hYQ
    by_contra hQc
    have hQT : T Q := ⟨hQP.le.trans hP.1, hP.2.1.to_le hQP.le, hYQ, hQc⟩
    exact hQP.ne (Subgroup.eq_of_le_of_card_ge hQP.le (hmin Q hQT))

end Minimal

end CFSG.CGT.PushingUpLit.CGT6
