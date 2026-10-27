module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveYSide

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open CFSG.CGT.PushingUpLit.CGT6M CFSG.Quasithin MulAction

section YSide

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_sixteen_fixSub_odd (hV : ∀ v : V, v ^ 2 = 1) (Y : Subgroup (MulAut V))
    {y : MulAut V} (hy : y ∈ Y) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1)
    (hU : Nat.card ↥(commV Y) ≤ 2 ^ 4 * Nat.card ↥(commV Y ⊓ fixV Y)) :
    Nat.card V ≤ 2 ^ 4 * Nat.card ↥(fixSub y) := by
  have hNC : commSub y ⊓ (commV Y ⊓ fixV Y) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun u hu => ?_
    have h1 : u ∈ commSub y ⊓ fixSub y := ⟨hu.1, hu.2.2 y hy⟩
    rwa [commSub_inf_fixSub_eq_bot hm hym hV, Subgroup.mem_bot] at h1
  have hNU : commSub y ≤ commV Y := commSub_le_commV Y hy
  let f : ↥(commSub y) × ↥(commV Y ⊓ fixV Y) → ↥(commV Y) := fun p =>
    ⟨(p.1 : V) * (p.2 : V), Subgroup.mul_mem _ (hNU p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨n, c⟩ ⟨n', c'⟩ h
    have h' : (n : V) * (c : V) = (n' : V) * (c' : V) := congrArg Subtype.val h
    have hmem : (n' : V)⁻¹ * n ∈ commSub y ⊓ (commV Y ⊓ fixV Y) := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ n'.2) n.2, ?_⟩
      have : (n' : V)⁻¹ * n = c' * (c : V)⁻¹ := by
        calc (n' : V)⁻¹ * n = (n' : V)⁻¹ * (n * c) * (c : V)⁻¹ := by group
          _ = (n' : V)⁻¹ * (n' * c') * (c : V)⁻¹ := by rw [h']
          _ = c' * (c : V)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ c'.2 (Subgroup.inv_mem _ c.2)
    rw [hNC, Subgroup.mem_bot] at hmem
    have hn : (n : V) = n' := (inv_mul_eq_one.mp hmem).symm
    have hc : (c : V) = c' := by
      rw [← hn] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hn) (Subtype.ext hc)
  have h1 : Nat.card ↥(commSub y) * Nat.card ↥(commV Y ⊓ fixV Y) ≤ Nat.card ↥(commV Y) := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod] at this
  have hCpos : 0 < Nat.card ↥(commV Y ⊓ fixV Y) := Nat.card_pos
  have h2 : Nat.card ↥(commSub y) ≤ 2 ^ 4 := by
    by_contra hlt
    have hlt' : 2 ^ 4 < Nat.card ↥(commSub y) := Nat.lt_of_not_le hlt
    have := Nat.mul_lt_mul_of_pos_right hlt' hCpos
    omega
  calc Nat.card V = Nat.card ↥(commSub y) * Nat.card ↥(fixSub y) :=
        (card_commSub_mul_card_fixSub y).symm
    _ ≤ 2 ^ 4 * Nat.card ↥(fixSub y) := Nat.mul_le_mul_right _ h2

end YSide

section Burnside

variable {V : Type} [CommGroup V] [Finite V] {K : Type*} [Group K]

abbrev C33 : Type := Multiplicative (ZMod 3 × ZMod 3)

@[expose] def phi3 (A B : K) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1) (hAB : Commute A B) :
    C33 →* K :=
  MonoidHom.mk' (fun u => A ^ (Multiplicative.toAdd u).1.val * B ^ (Multiplicative.toAdd u).2.val)
    (by
      intro u v
      obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
      obtain ⟨⟨i', j'⟩, rfl⟩ : ∃ w, v = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd v, rfl⟩
      simp only [← ofAdd_add, toAdd_ofAdd, Prod.mk_add_mk, ZMod.val_add]
      have hmod : ∀ {x : K}, x ^ 3 = 1 → ∀ n : ℕ, x ^ (n % 3) = x ^ n := fun {x} hx n => by
        conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]
      rw [hmod hA, hmod hB, pow_add, pow_add]
      have h := (hAB.pow_pow i'.val j.val).eq
      calc A ^ i.val * A ^ i'.val * (B ^ j.val * B ^ j'.val)
          = A ^ i.val * (A ^ i'.val * B ^ j.val) * B ^ j'.val := by simp only [mul_assoc]
        _ = A ^ i.val * (B ^ j.val * A ^ i'.val) * B ^ j'.val := by rw [h]
        _ = A ^ i.val * B ^ j.val * (A ^ i'.val * B ^ j'.val) := by simp only [mul_assoc])

theorem dvd_sum_card_fixSub3 (Φ : C33 →* MulAut V) :
    9 ∣ ∑ u : C33, Nat.card (fixSub (Φ u)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let _ : MulAction C33 V := MulAction.compHom V Φ
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group C33 V
  have hc : Fintype.card C33 = 9 := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, ZMod.card]
  rw [hc] at h
  have h2 : ∀ u : C33, Fintype.card (fixedBy V u) = Nat.card (fixSub (Φ u)) := fun u => by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  simp only [h2] at h
  exact ⟨_, h.trans (mul_comm _ _)⟩

omit [Finite V] in
theorem sum_card_fixSub3 (Φ : C33 →* MulAut V) {c : ℕ}
    (hc : ∀ u : C33, u ≠ 1 → Nat.card (fixSub (Φ u)) = c) :
    ∑ u : C33, Nat.card (fixSub (Φ u)) = Nat.card V + 8 * c := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ (fun u : C33 => Nat.card (fixSub (Φ u)))
    (Finset.mem_univ 1)
  have h2 : ∑ u ∈ Finset.univ.erase (1 : C33), Nat.card (fixSub (Φ u)) =
      ∑ u ∈ Finset.univ.erase (1 : C33), c :=
    Finset.sum_congr rfl fun u hu => hc u (Finset.ne_of_mem_erase hu)
  have hcard : (Finset.univ.erase (1 : C33)).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_congr Multiplicative.toAdd, Fintype.card_prod, ZMod.card]
  rw [h2, Finset.sum_const, hcard, smul_eq_mul, map_one, fixSub_one] at h1
  have h3 : Nat.card ↥(⊤ : Subgroup V) = Nat.card V := Subgroup.card_top
  rw [h3] at h1
  omega

end Burnside

section Config

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem fixSub_inv (x : MulAut V) : fixSub x⁻¹ = fixSub x := by
  ext v
  simp only [mem_fixSub]
  constructor
  · intro h
    have := congrArg x h
    simpa using this.symm
  · intro h
    have := congrArg (⇑x⁻¹) h
    simpa using this.symm

omit [Finite V] in
theorem card_fixSub_inv (x : MulAut V) : Nat.card ↥(fixSub x⁻¹) = Nat.card ↥(fixSub x) := by
  rw [fixSub_inv]

theorem pow_two_eq_inv {K : Type*} [Group K] {x : K} (h : x ^ 3 = 1) : x ^ 2 = x⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h)

theorem false_of_l34_config (hV : ∀ v : V, v ^ 2 = 1) {α β f₁ f₂ f₃ : MulAut V}
    (hα3 : α ^ 3 = 1) (hβ3 : β ^ 3 = 1) (hαβ : Commute α β)
    (h1 : f₁ * α * f₁⁻¹ = β⁻¹) (h2 : f₂ * α * f₂⁻¹ = (α * β)⁻¹)
    (h3 : f₃ * α * f₃⁻¹ = α * β⁻¹) (hα1 : α ≠ 1)
    (hr : Nat.card V ≤ 2 ^ 4 * Nat.card ↥(fixSub α)) : False := by
  set c := Nat.card ↥(fixSub α) with hc
  have hβ : Nat.card ↥(fixSub β) = c := by
    have := card_fixSub_conj f₁ α
    rw [h1, card_fixSub_inv] at this
    exact this
  have hαβc : Nat.card ↥(fixSub (α * β)) = c := by
    have := card_fixSub_conj f₂ α
    rw [h2, card_fixSub_inv] at this
    exact this
  have hαβ' : Nat.card ↥(fixSub (α * β⁻¹)) = c := by
    have := card_fixSub_conj f₃ α
    rw [h3] at this
    exact this
  have hαβ3 : (α * β) ^ 3 = 1 := by rw [hαβ.mul_pow, hα3, hβ3, one_mul]
  have hαβ'3 : (α * β⁻¹) ^ 3 = 1 := by
    rw [(hαβ.inv_right).mul_pow, hα3, inv_pow, hβ3, inv_one, one_mul]
  let Φ : C33 →* MulAut V := phi3 α β hα3 hβ3 hαβ
  have hΦ : ∀ u : C33, u ≠ 1 → Nat.card ↥(fixSub (Φ u)) = c := by
    intro u hu
    obtain ⟨⟨i, j⟩, rfl⟩ : ∃ w, u = Multiplicative.ofAdd w := ⟨Multiplicative.toAdd u, rfl⟩
    show Nat.card ↥(fixSub (α ^ i.val * β ^ j.val)) = c
    have hu' : ¬ (i = 0 ∧ j = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hu rfl
    have hβ2 : β ^ 2 = β⁻¹ := pow_two_eq_inv hβ3
    have hα2 : α ^ 2 = α⁻¹ := pow_two_eq_inv hα3
    have hv0 : (0 : ZMod 3).val = 0 := rfl
    have hv1 : (1 : ZMod 3).val = 1 := rfl
    have hv2 : (2 : ZMod 3).val = 2 := rfl
    have hz3 : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
    rcases hz3 i with rfl | rfl | rfl <;> rcases hz3 j with rfl | rfl | rfl <;>
      simp only [hv0, hv1, hv2, pow_zero, pow_one, mul_one, one_mul]
    · exact absurd ⟨rfl, rfl⟩ hu'
    · exact hβ
    · rw [hβ2, card_fixSub_inv, hβ]
    · rfl
    · exact hαβc
    · rw [hβ2]
      exact hαβ'
    · rw [hα2, card_fixSub_inv]
    · have : α ^ 2 * β = (α * β⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, hα2]
        exact hαβ.inv_left.eq
      rw [this, card_fixSub_inv]
      exact hαβ'
    · have : α ^ 2 * β ^ 2 = (α * β)⁻¹ := by
        rw [hα2, hβ2, ← mul_inv_rev, hαβ.eq]
      rw [this, card_fixSub_inv]
      exact hαβc
  have hsum := sum_card_fixSub3 Φ hΦ
  have hdvd := dvd_sum_card_fixSub3 Φ
  rw [hsum] at hdvd
  obtain ⟨m, hm⟩ := exists_card_eq_two_pow hV (fixSub α)
  obtain ⟨k, hk⟩ := exists_card_eq_two_pow hV (commSub α)
  have hVcard : Nat.card V = 2 ^ k * c := by
    rw [← hk, hc]
    exact (card_commSub_mul_card_fixSub α).symm
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have : commSub α = ⊥ := by
      rw [← Subgroup.card_eq_one, hk, hk0', pow_zero]
    exact hα1 (commSub_eq_bot_iff.mp this)
  have hcpos : 0 < c := by rw [hc]; exact Nat.card_pos
  have hk4 : k ≤ 4 := by
    by_contra hk5
    have h16 : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ 5 * c ≤ 2 ^ k * c := Nat.mul_le_mul_right _ h16
    rw [← hVcard] at this
    have := hr.trans (le_of_eq rfl)
    nlinarith
  rw [hVcard] at hdvd
  have hfac : 2 ^ k * c + 8 * c = c * (2 ^ k + 8) := by ring
  rw [hfac] at hdvd
  have hcop : Nat.Coprime 9 c := by
    rw [hc, hm]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h9 : 9 ∣ 2 ^ k + 8 := hcop.dvd_of_dvd_mul_left hdvd
  interval_cases k <;> omega

end Config

end CFSG.CGT.PushingUpLit.CGT6X.End4
