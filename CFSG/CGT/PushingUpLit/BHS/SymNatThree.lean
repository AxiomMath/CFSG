module

public import CFSG.CGT.PushingUpLit.BHS.SymNatWeight

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

section Generic

variable {V : Type*} [CommGroup V]

theorem card_le_card_fixV_mul_card_commV [Finite V] {X : Subgroup (MulAut V)} (a : MulAut V)
    (hX : X = Subgroup.zpowers a) : Nat.card V ≤ Nat.card (fixV X) * Nat.card (commV X) := by
  subst hX
  let ψ : V →* V := MonoidHom.mk' (fun v => a v * v⁻¹) fun x y => by
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  have hker : ψ.ker ≤ fixV (Subgroup.zpowers a) := by
    intro v hv
    rw [mem_fixV_iff_le, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    have h1 : a v * v⁻¹ = 1 := hv
    exact mul_inv_eq_one.1 h1
  have hrange : ψ.range ≤ commV (Subgroup.zpowers a) := by
    rintro _ ⟨v, rfl⟩
    exact G6.mem_commV_of_mem (Subgroup.mem_zpowers a) v
  calc Nat.card V = Nat.card ψ.ker * Nat.card ψ.range := (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card (fixV (Subgroup.zpowers a)) * Nat.card (commV (Subgroup.zpowers a)) :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hker) (Subgroup.card_le_of_le hrange)

theorem commV_le_bot_of_eq_one {X : Subgroup (MulAut V)} (a : MulAut V)
    (hX : X = Subgroup.zpowers a) (ha : a = 1) : commV X ≤ ⊥ := by
  subst hX ha
  rw [G6.commV_le_iff]
  intro x hx v
  rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
  subst hx
  simp

end Generic

theorem zpow_eq_one_or_self_or_sq {G : Type*} [Group G] {d : G} (hd : d ^ 3 = 1) (k : ℤ) :
    d ^ k = 1 ∨ d ^ k = d ∨ d ^ k = d ^ 2 := by
  have h1 : d ^ k = d ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    have h3 : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have h2 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h2 with h | h | h
  · left
    rw [h1, h, zpow_zero]
  · right
    left
    rw [h1, h, zpow_one]
  · right
    right
    rw [h1, h]
    exact zpow_ofNat d 2

variable {n : ℕ}

theorem sum_orbSize_pred_add (A : Subgroup (Equiv.Perm (Fin n))) :
    ∑ q : OrbQ A, (orbSize A q - 1) + Nat.card (OrbQ A) = n := by
  have h1 := sum_orbSize A
  have h2 : ∑ q : OrbQ A, (orbSize A q - 1) + ∑ _q : OrbQ A, 1 = ∑ q : OrbQ A, orbSize A q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Nat.sub_add_cancel (orbSize_pos A q)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← Nat.card_eq_fintype_card] at h2
  omega

theorem two_orbits_collapse {A : Subgroup (Equiv.Perm (Fin n))} {q₁ q₂ : OrbQ A} (h : q₁ ≠ q₂) :
    (orbSize A q₁ - 1) + (orbSize A q₂ - 1) + Nat.card (OrbQ A) ≤ n := by
  classical
  have h1 := sum_orbSize_pred_add A
  have h2 : (orbSize A q₁ - 1) + (orbSize A q₂ - 1) ≤ ∑ q : OrbQ A, (orbSize A q - 1) :=
    calc orbSize A q₁ - 1 + (orbSize A q₂ - 1)
        = ∑ q ∈ ({q₁, q₂} : Finset (OrbQ A)), (orbSize A q - 1) :=
          (Finset.sum_pair (f := fun q : OrbQ A => orbSize A q - 1) h).symm
      _ ≤ ∑ q : OrbQ A, (orbSize A q - 1) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem sym_isThreeCycle (n : ℕ) (hn : Odd n) {d : Equiv.Perm (Fin n)} (hd : d ^ 3 = 1)
    (hc : Nat.card (commV ((Subgroup.zpowers d).map (coreAct n))) = 4) : d.IsThreeCycle := by
  have hmap : (Subgroup.zpowers d).map (coreAct n) = Subgroup.zpowers (coreAct n d) :=
    MonoidHom.map_zpowers _ _
  have hd1 : d ≠ 1 := by
    intro h
    have h1 : coreAct n d = 1 := by rw [h, map_one]
    have h2 := hc.symm.le.trans
      (Subgroup.card_le_of_le (commV_le_bot_of_eq_one (coreAct n d) hmap h1))
    rw [Subgroup.card_bot] at h2
    omega
  have hfix : Nat.card (coreMod n) ≤
      Nat.card (fixV ((Subgroup.zpowers d).map (coreAct n))) * 4 :=
    (card_le_card_fixV_mul_card_commV (coreAct n d) hmap).trans (Nat.mul_le_mul_left _ hc.le)
  have hQ : n ≤ Nat.card (OrbQ (Subgroup.zpowers d)) + 2 := by
    have h1 := card_fixV_mul_two hn (Subgroup.zpowers d)
    have h2 := card_coreMod_mul_two hn
    have h3 : 2 ^ n ≤ 2 ^ (Nat.card (OrbQ (Subgroup.zpowers d)) + 2) := by
      calc 2 ^ n = Nat.card (coreMod n) * 2 := h2.symm
        _ ≤ (Nat.card (fixV ((Subgroup.zpowers d).map (coreAct n))) * 4) * 2 :=
            Nat.mul_le_mul_right _ hfix
        _ = (Nat.card (fixV ((Subgroup.zpowers d).map (coreAct n))) * 2) * 2 ^ 2 := by ring
        _ = 2 ^ (Nat.card (OrbQ (Subgroup.zpowers d)) + 2) := by rw [h1, pow_add]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have h3le : ∀ x, d x ≠ x →
      3 ≤ orbSize (Subgroup.zpowers d) (orbOf (Subgroup.zpowers d) x) := by
    intro x hx
    have hdd : (d (d (d x))) = x := by
      have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) hd
      simpa [pow_succ, Equiv.Perm.mul_apply] using this
    have hdx : orbOf (Subgroup.zpowers d) (d x) = orbOf (Subgroup.zpowers d) x :=
      orbOf_apply (Subgroup.mem_zpowers d) x
    have hddx : orbOf (Subgroup.zpowers d) (d (d x)) = orbOf (Subgroup.zpowers d) x := by
      rw [orbOf_apply (Subgroup.mem_zpowers d), hdx]
    have hxdd : x ≠ d (d x) := by
      intro h
      apply hx
      exact (congrArg d h).trans hdd
    exact three_le_orbSize rfl hdx hddx (Ne.symm hx) hxdd
      (fun h => hx (d.injective h).symm)
  obtain ⟨x₀, hx₀⟩ : ∃ x, d x ≠ x := by
    by_contra hall
    push Not at hall
    exact hd1 (Equiv.ext hall)
  have hsame : ∀ y, d y ≠ y →
      orbOf (Subgroup.zpowers d) y = orbOf (Subgroup.zpowers d) x₀ := by
    intro y hy
    by_contra hne
    have h1 := two_orbits_collapse hne
    have h2 := h3le y hy
    have h3 := h3le x₀ hx₀
    omega
  have hcases : ∀ y, d y ≠ y → y = x₀ ∨ y = d x₀ ∨ y = d (d x₀) := by
    intro y hy
    obtain ⟨a, ha, hax⟩ := orbOf_eq_iff.1 (hsame y hy)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rcases zpow_eq_one_or_self_or_sq hd k with h | h | h
    · left
      rw [← hax, h]
      rfl
    · right
      left
      rw [← hax, h]
    · right
      right
      rw [← hax, h]
      simp [pow_two, Equiv.Perm.mul_apply]
  have hdd : (d (d (d x₀))) = x₀ := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ x₀) hd
    simpa [pow_succ, Equiv.Perm.mul_apply] using this
  have hxdd : x₀ ≠ d (d x₀) := by
    intro h
    apply hx₀
    exact (congrArg d h).trans hdd
  rw [← card_support_eq_three_iff, Finset.card_eq_three]
  refine ⟨x₀, d x₀, d (d x₀), Ne.symm hx₀, hxdd, fun h => hx₀ (d.injective h).symm, ?_⟩
  ext y
  simp only [Equiv.Perm.mem_support, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact hcases y
  · rintro (rfl | rfl | rfl)
    · exact hx₀
    · intro h
      exact hx₀ (d.injective h)
    · intro h
      exact hxdd (hdd.symm.trans h)

end CFSG.CGT.PushingUpLit.BHS
