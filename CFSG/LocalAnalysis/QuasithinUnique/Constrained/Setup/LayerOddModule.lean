module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {X : Type*} [Group X]

theorem add_self_eq_zero_charTwo [CharP k 2] {M : Type*} [AddCommGroup M] [Module k M] (x : M) :
    x + x = 0 := by
  rw [← two_smul k x, show (2 : k) = 0 from CharP.cast_eq_zero k 2, zero_smul]

theorem neg_eq_self_charTwo [CharP k 2] {M : Type*} [AddCommGroup M] [Module k M] (x : M) :
    -x = x :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero_charTwo (k := k) x)

theorem natCast_eq_one_of_odd [CharP k 2] {n : ℕ} (h : Odd n) : (n : k) = 1 := by
  obtain ⟨m, rfl⟩ := h
  have h2 : ((2 : ℕ) : k) = 0 := CharP.cast_eq_zero k 2
  rw [Nat.cast_add, Nat.cast_mul, h2, zero_mul, zero_add, Nat.cast_one]

theorem isInvariant_commSub {ρ : X →* (V ≃ₗ[k] V)} {H : Subgroup X} {U : Submodule k V}
    (h : Offender.IsInvariant ρ H U) : Offender.IsInvariant ρ H (commSub ρ H U) := by
  intro b hb w hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h', hh', u, hu, rfl⟩ := hy
    have e : ρ b (ρ h' u - u) = ρ (b * h' * b⁻¹) (ρ b u) - ρ b u := by
      rw [map_sub, ρ_mul_apply, ρ_mul_apply, ρ_inv_apply]
    rw [e]
    exact mem_commSub_of (H.mul_mem (H.mul_mem hb hh') (H.inv_mem hb)) (h b hb u hu)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem fix_of_quadratic_oddOrder [CharP k 2] (ρ : X →* (V ≃ₗ[k] V)) {x : X}
    (hodd : Odd (orderOf x)) {S : Submodule k V}
    (hx : ∀ u ∈ S, ρ x (ρ x u - u) = ρ x u - u) : ∀ u ∈ S, ρ x u = u := by
  intro u hu
  have h2 : ρ (x * x) u = u := by
    rw [ρ_mul_apply]
    have h := hx u hu
    rw [map_sub] at h
    have e : ρ x (ρ x u) = (ρ x u + ρ x u) - u := by
      calc ρ x (ρ x u) = (ρ x (ρ x u) - ρ x u) + ρ x u := by abel
        _ = (ρ x u - u) + ρ x u := by rw [h]
        _ = (ρ x u + ρ x u) - u := by abel
    rw [e, add_self_eq_zero_charTwo (k := k), zero_sub, neg_eq_self_charTwo (k := k)]
  have hit : ∀ n : ℕ, ρ ((x * x) ^ n) u = u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ρ_mul_apply, h2, ih]
  obtain ⟨j, hj⟩ := hodd
  have hxx : x = (x * x) ^ (j + 1) := by
    have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
    rw [hj] at h1
    calc x = x ^ (2 * j + 1) * x := by rw [h1, one_mul]
      _ = x ^ (2 * j + 1 + 1) := (pow_succ x _).symm
      _ = x ^ (2 * (j + 1)) := by rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      _ = (x ^ 2) ^ (j + 1) := pow_mul x 2 (j + 1)
      _ = (x * x) ^ (j + 1) := by rw [pow_two]
  rw [hxx]
  exact hit (j + 1)

section Good

variable (ρ : X →* (V ≃ₗ[k] V)) (L : Subgroup X)

theorem exists_minimal_noncentral [Finite V] (h : ¬ (⊤ : Submodule k V) ≤ fixSub ρ L) :
    ∃ I : Submodule k V, Offender.IsInvariant ρ L I ∧ ¬ I ≤ fixSub ρ L ∧
      ∀ U : Submodule k V, Offender.IsInvariant ρ L U → U ≤ I → ¬ U ≤ fixSub ρ L → U = I := by
  classical
  have hne : ∃ n, ∃ U : Submodule k V,
      Offender.IsInvariant ρ L U ∧ ¬ U ≤ fixSub ρ L ∧ Nat.card U = n :=
    ⟨_, ⊤, fun _ _ _ _ => Submodule.mem_top, h, rfl⟩
  obtain ⟨I, hI1, hI2, hI3⟩ := Nat.find_spec hne
  refine ⟨I, hI1, hI2, fun U hU hUI hUn => ?_⟩
  have hle : Nat.card ↥I ≤ Nat.card ↥U := by
    rw [hI3]; exact Nat.find_min' hne ⟨U, hU, hUn, rfl⟩
  exact submodule_eq_of_le_of_card_ge hUI hle

theorem commSub_eq_of_minimal [CharP k 2] (hodd : Odd (Nat.card L)) {I : Submodule k V}
    (hI1 : Offender.IsInvariant ρ L I) (hI2 : ¬ I ≤ fixSub ρ L)
    (hmin : ∀ U : Submodule k V, Offender.IsInvariant ρ L U → U ≤ I → ¬ U ≤ fixSub ρ L → U = I) :
    commSub ρ L I = I := by
  have hc : Offender.IsInvariant ρ L (commSub ρ L I) := isInvariant_commSub hI1
  have hle : commSub ρ L I ≤ I := commSub_le_of_isInvariant hI1
  by_cases hf : commSub ρ L I ≤ fixSub ρ L
  · exfalso
    apply hI2
    intro u hu l hl
    have hodd' : Odd (orderOf l) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard L hl)
    refine fix_of_quadratic_oddOrder (k := k) ρ (x := l) hodd' (S := I) (fun u hu => ?_) u hu
    exact hf (mem_commSub_of hl hu) l hl
  · exact hmin _ hc hle hf

theorem inf_fixSub_eq_bot [CharP k 2] [Finite X] (hodd : Odd (Nat.card L)) {I : Submodule k V}
    (hcomm : commSub ρ L I = I) : I ⊓ fixSub ρ L = ⊥ := by
  classical
  have : Fintype L := Fintype.ofFinite L
  let e : V →ₗ[k] V := ∑ l : L, (ρ l : V →ₗ[k] V)
  have he_mul : ∀ (l₀ : L) (x : V), e (ρ l₀ x) = e x := by
    intro l₀ x
    show (∑ l : L, (ρ l : V →ₗ[k] V)) (ρ l₀ x) = (∑ l : L, (ρ l : V →ₗ[k] V)) x
    simp only [LinearMap.sum_apply, LinearEquiv.coe_coe]
    have hl : ∀ l : L, ρ l (ρ l₀ x) = ρ ((l * l₀ : L)) x := by
      intro l; rw [← ρ_mul_apply]; rfl
    simp only [hl]
    exact Fintype.sum_equiv (Equiv.mulRight l₀) _ _ (fun l => rfl)
  have he_fix : ∀ x ∈ fixSub ρ L, e x = x := by
    intro x hx
    show (∑ l : L, (ρ l : V →ₗ[k] V)) x = x
    simp only [LinearMap.sum_apply, LinearEquiv.coe_coe]
    have : ∀ l : L, ρ l x = x := fun l => hx l l.2
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card]
    rw [← Nat.cast_smul_eq_nsmul k, natCast_eq_one_of_odd hodd, one_smul]
  have hker : commSub ρ L I ≤ LinearMap.ker e := by
    rw [commSub_le_iff]
    intro l hl u hu
    rw [LinearMap.mem_ker, map_sub]
    have := he_mul ⟨l, hl⟩ u
    rw [this, sub_self]
  refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
  have hxc : x ∈ commSub ρ L I := by rw [hcomm]; exact hx.1
  have h1 : x ∈ LinearMap.ker e := hker hxc
  have h2 : e x = x := he_fix x hx.2
  rw [LinearMap.mem_ker] at h1
  rw [← h2, h1]

theorem exists_good_oddOrder [CharP k 2] [Finite V] [Finite X] (hodd : Odd (Nat.card L))
    (h : ¬ (⊤ : Submodule k V) ≤ fixSub ρ L) :
    ∃ I : Submodule k V, IsGoodModule ρ L I ∧ I ⊓ fixSub ρ L = ⊥ := by
  obtain ⟨I, hI1, hI2, hmin⟩ := exists_minimal_noncentral ρ L h
  have hc := commSub_eq_of_minimal ρ L hodd hI1 hI2 hmin
  have hbot := inf_fixSub_eq_bot ρ L hodd hc
  refine ⟨I, ⟨hI1, hc, hI2, fun U hU hlo hhi => ?_⟩, hbot⟩
  by_cases hUf : U ≤ fixSub ρ L
  · left
    exact le_antisymm (le_inf hhi hUf) hlo
  · right
    exact hmin U hU hhi hUf

end Good

end CFSG.QuasithinUnique.Setup.Layer
