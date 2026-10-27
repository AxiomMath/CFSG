module

public import CFSG.GH74.GLS.IVK.Prod32.Dec
public import CFSG.GH74.GLS.IVK.Prod32.Out

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass squareClassMap)

section BFAbs

variable {F : Type} [Field F] [Finite F]

theorem qc_comm (x y : SquareClass F × (F ≃+* F)) : x * y = y * x := by
  have : IsCyclic (F ≃+* F) := CFSG.ABGDGroups.isCyclic_ringEquiv F
  refine Prod.ext (mul_comm _ _) ?_
  exact (IsCyclic.isMulCommutative (α := F ≃+* F)).is_comm.comm _ _

theorem card_squareClass (hF : GoodF F) : Nat.card (SquareClass F) = 2 :=
  CFSG.Semidihedral.SemilinearOuterQuotient.squareClass_card_two F
    (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hF.odd)

theorem squareClass_sq (hF : GoodF F) (q : SquareClass F) : q * q = 1 := by
  have h := pow_card_eq_one' (G := SquareClass F) (x := q)
  rw [card_squareClass hF, sq] at h
  exact h

variable {Γ : Type} [Group Γ]

structure BFAbs (u v : Γ →* SquareClass F × (F ≃+* F)) (a₀ h₀ : Γ) (σ : F ≃+* F) : Prop where
  ker : ∀ x, u x = 1 → v x = 1
  ker' : ∀ x, v x = 1 → u x = 1
  range : ∀ x, ∃ x', v x = u x'
  ua : u a₀ = (1, σ)
  va : v a₀ = (1, σ)
  σ_ne : σ ≠ 1
  σ_sq : σ * σ = 1
  F2 : u a₀ = u h₀ * (v h₀)⁻¹
  compat : ∀ x, u x * u x = 1 → (u x).2 = 1 → ¬ ((v x).2 ≠ 1 ∧ (v x).1 ≠ 1)

variable {u v : Γ →* SquareClass F × (F ≃+* F)} {a₀ h₀ : Γ} {σ : F ≃+* F}

theorem BFAbs.eq_iff (hb : BFAbs u v a₀ h₀ σ) (x y : Γ) : u x = u y ↔ v x = v y := by
  constructor
  · intro h
    have h1 : u (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, ← h, inv_mul_cancel]
    have h2 := hb.ker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  · intro h
    have h1 : v (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, ← h, inv_mul_cancel]
    have h2 := hb.ker' _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2


structure BFDec (u v : Γ →* SquareClass F × (F ≃+* F)) (σ : F ≃+* F)
    (Yx Ax : Subgroup (SquareClass F × (F ≃+* F))) : Prop where
  Yx_le : Yx ≤ u.range
  Ax_le : Ax ≤ u.range
  inf : Yx ⊓ Ax = ⊥
  sup : Yx ⊔ Ax = u.range
  card_Y : Nat.card Yx ≤ 2
  cyc : IsCyclic ↥Ax
  s_mem : ((1 : SquareClass F), σ) ∈ Ax
  card_A : 4 ≤ Nat.card Ax
  dvd_A : 4 ∣ Nat.card Ax
  inj : ∀ p ∈ Ax, p.2 = 1 → p = 1
  fix : ∀ x, u x ∈ Yx → v x = u x
  gen : Yx ≠ ⊥ → ∃ y₀ : SquareClass F × (F ≃+* F), Yx = zpowers y₀ ∧ y₀.2 = 1 ∧ y₀.1 ≠ 1

theorem BFAbs.fix_of_diag (hF : GoodF F) (hb : BFAbs u v a₀ h₀ σ)
    {Yx Ax : Subgroup (SquareClass F × (F ≃+* F))} (hsup : Yx ⊔ Ax = u.range)
    (hY : Yx ≠ ⊥ → (∃ y ∈ u.range, Yx = zpowers y ∧ y.2 = 1 ∧ y.1 ≠ 1) ∧ ∀ p ∈ Ax, p.1 = 1) :
    ∀ x, u x ∈ Yx → v x = u x := by
  classical
  have : IsCyclic (F ≃+* F) := CFSG.ABGDGroups.isCyclic_ringEquiv F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hY0 : Yx = ⊥
  · intro x hx
    rw [hY0, Subgroup.mem_bot] at hx
    rw [hx]; exact hb.ker x hx
  · obtain ⟨⟨y₀, hy₀X, hYeq, hy₀2, hy₀1⟩, hAfst⟩ := hY hY0
    obtain ⟨y, hy⟩ := hy₀X
    have hy02 : y₀ * y₀ = 1 := Prod.ext (squareClass_sq hF _) (by simp [hy₀2])
    have hy0ne : y₀ ≠ 1 := fun h => hy₀1 (congrArg Prod.fst h)
    have hord : orderOf y₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hy02) hy0ne
    have hs2 : σ ^ 2 = 1 := by rw [sq]; exact hb.σ_sq
    have hvy : v y = y₀ := by
      have hww : v y * v y = 1 := by
        rw [← map_mul]; apply hb.ker; rw [map_mul, hy, hy02]
      have hcompat := hb.compat y (by rw [hy, hy02]) (by rw [hy]; exact hy₀2)
      have hw1 : v y ≠ 1 := fun h => by
        have := hb.ker' y h
        rw [hy] at this
        exact hy0ne this
      have hws : v y ≠ ((1 : SquareClass F), σ) := fun h => by
        have h1 : v y = v a₀ := by rw [h, hb.va]
        have h2 := (hb.eq_iff y a₀).mpr h1
        rw [hy, hb.ua] at h2
        have h3 : y₀.2 = σ := congrArg Prod.snd h2
        exact hb.σ_ne (h3.symm.trans hy₀2)
      obtain ⟨x', hx'⟩ := hb.range y
      have hwX : v y ∈ u.range := ⟨x', hx'.symm⟩
      rw [← hsup] at hwX
      obtain ⟨p, hp, q, hq, hpq⟩ := (mem_sup_of_comm (fun x _ y _ => qc_comm x y) (v y)).mp hwX
      have hq1 : q.1 = 1 := hAfst q hq
      have hpp : p * p = 1 := by
        rw [hYeq] at hp
        rcases eq_one_or_eq_of_mem_zpowers hord hp with rfl | rfl
        · simp
        · exact hy02
      have hqq : q * q = 1 := by
        have h1 : (p * q) * (p * q) = (p * p) * (q * q) := by
          calc (p * q) * (p * q) = p * (q * p) * q := by simp only [mul_assoc]
            _ = p * (p * q) * q := by rw [qc_comm q p]
            _ = (p * p) * (q * q) := by simp only [mul_assoc]
        rw [← hpq, hww, hpp, one_mul] at h1
        exact h1.symm
      have hq22 : q.2 ^ 2 = 1 := by
        have := congrArg Prod.snd hqq
        simpa [sq] using this
      have hγ : q.2 = 1 ∨ q.2 = σ := by
        by_cases hγ : q.2 = 1
        · exact Or.inl hγ
        · exact Or.inr (CFSG.ABGDGroups.ringEquiv_eq_of_sq_eq_one hq22 hs2 hγ hb.σ_ne)
      have hqe : q = (1, q.2) := Prod.ext hq1 rfl
      rw [hYeq] at hp
      rcases eq_one_or_eq_of_mem_zpowers hord hp with rfl | rfl
      · rcases hγ with hγ | hγ
        · exfalso; apply hw1; rw [hpq, hqe, hγ]; simp
        · exfalso; apply hws; rw [hpq, hqe, hγ]; simp
      · rcases hγ with hγ | hγ
        · rw [hpq, hqe, hγ]
          apply Prod.ext
          · simp
          · simp [hy₀2]
        · exfalso
          apply hcompat
          have hw : v y = (p.1, σ) := by
            rw [hpq, hqe, hγ]
            apply Prod.ext
            · simp
            · simp [hy₀2]
          rw [hw]
          exact ⟨hb.σ_ne, hy₀1⟩
    intro x hx
    rw [hYeq] at hx
    rcases eq_one_or_eq_of_mem_zpowers hord hx with h | h
    · rw [h]; exact hb.ker x h
    · have h1 : u x = u y := by rw [h, hy]
      rw [(hb.eq_iff x y).mp h1, hvy, h, ← hy]


theorem BFAbs.main [Finite Γ] (hF : GoodF F) (hb : BFAbs u v a₀ h₀ σ) (hΓ : ∃ m, Nat.card Γ = 2 ^ m) :
    ∃ Yx Ax : Subgroup (SquareClass F × (F ≃+* F)), BFDec u v σ Yx Ax := by
  classical
  have hQ := card_squareClass hF
  have : IsCyclic (F ≃+* F) := CFSG.ABGDGroups.isCyclic_ringEquiv F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : ((1 : SquareClass F), σ) ∈ u.range := ⟨a₀, hb.ua⟩
  obtain ⟨Yx, Ax, hYX, hAX, hinf, hsup, hcardY, hcyc, hsA, hinj, hY⟩ :=
    exists_YA_decomp hQ u.range hs rfl
  have hfix := hb.fix_of_diag hF hsup (fun hne => by
    obtain ⟨⟨y₀, hy, h1, h2, h3⟩, h4⟩ := hY hne
    exact ⟨⟨y₀, hy, h1, h2, h3⟩, h4⟩)
  have hs2 : ((1 : SquareClass F), σ) * (1, σ) = 1 := Prod.ext (by simp) hb.σ_sq
  have hs1 : ((1 : SquareClass F), σ) ≠ 1 := fun h => hb.σ_ne (congrArg Prod.snd h)
  obtain ⟨m, hm⟩ := hΓ
  have hd1 : Nat.card Ax ∣ Nat.card u.range := Subgroup.card_dvd_of_le hAX
  have hd2 : Nat.card u.range ∣ Nat.card Γ := by
    rw [← Subgroup.index_ker]
    exact Subgroup.index_dvd_card _
  obtain ⟨k, hkm, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hm ▸ hd1.trans hd2)
  have hAfin : Finite Ax := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ two_ne_zero)
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero, Subgroup.card_eq_one] at hk
    rw [hk, Subgroup.mem_bot] at hsA
    exact hs1 hsA
  have hA4 : 4 ≤ Nat.card Ax := by
    by_contra hlt
    rw [not_le] at hlt
    have hk1' : k = 1 := by
      by_contra hne
      have : 2 ≤ k := by omega
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
      omega
    have hcard2 : Nat.card Ax = 2 := by rw [hk, hk1']; norm_num
    have hord : orderOf ((1 : SquareClass F), σ) = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
    have hAz : Ax = zpowers ((1 : SquareClass F), σ) := by
      symm
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsA)
      rw [Nat.card_zpowers, hord, hcard2]
    let Fix : Subgroup Γ := MonoidHom.eqLocus u v
    have hrange_le : u.range ≤ Fix.map u := by
      rw [← hsup]
      refine sup_le (fun p hp => ?_) (fun p hp => ?_)
      · obtain ⟨x₁, hx₁⟩ := hYX hp
        refine ⟨x₁, ?_, hx₁⟩
        exact (hfix x₁ (hx₁ ▸ hp)).symm
      · rw [hAz] at hp
        have hs' : ((1 : SquareClass F), σ) ∈ Fix.map u :=
          ⟨a₀, show u a₀ = v a₀ by rw [hb.ua, hb.va], hb.ua⟩
        exact (Subgroup.zpowers_le.mpr hs') hp
    have hall : ∀ x, v x = u x := by
      intro x
      obtain ⟨f, hf, hfx⟩ := hrange_le (⟨x, rfl⟩ : u x ∈ u.range)
      have h2 := (hb.eq_iff f x).mp hfx
      have hf' : u f = v f := hf
      rw [← h2, ← hfx]; exact hf'.symm
    have h3 := hb.F2
    rw [hall h₀, mul_inv_cancel] at h3
    exact hs1 (hb.ua ▸ h3)
  have h4 : 4 ∣ Nat.card Ax := by
    rw [hk]
    have : 2 ≤ k := by
      by_contra hk2
      have hk1' : k = 1 := by omega
      rw [hk, hk1'] at hA4
      omega
    exact (pow_dvd_pow 2 this : 2 ^ 2 ∣ 2 ^ k)
  exact ⟨Yx, Ax, ⟨hYX, hAX, hinf, hsup, hcardY, hcyc, hsA, hA4, h4, hinj, hfix, fun hne => by
    obtain ⟨⟨y₀, _, h1, h2, h3⟩, _⟩ := hY hne
    exact ⟨y₀, h1, h2, h3⟩⟩⟩

end BFAbs

end CFSG.GH74.GLS.IVK.Prod3
