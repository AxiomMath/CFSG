module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCyc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCycB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAlt5

open Equiv Equiv.Perm Subgroup CFSG FinGen FinCyc
open scoped Nat

variable {n : ℕ}

theorem eq_bot_of_fix {I : Subgroup (Perm (Fin n))} (hI : ⁅I, I⁆ = I) {B : Finset (Fin n)}
    (hB : Bᶜ.card ≤ 4) (hIB : I ≤ pointwiseFix B) : I = ⊥ := by
  have hd : Nat.card ↥I ∣ 2 ^ 3 * 3 ^ 1 :=
    (card_dvd_of_fix B hIB).trans ((Nat.factorial_dvd_factorial hB).trans (by decide))
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 hd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
  exact eq_bot_of_perfect_of_le le_rfl
    (isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hk.symm) hI

theorem card_perm_dvd (h11 : n ≤ 11) : Nat.card (Perm (Fin n)) ∣ 11 ! := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Nat.factorial_dvd_factorial h11

theorem false_of_ge_seven (h11 : n ≤ 11) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {X I : Subgroup (Perm (Fin n))} (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hI1 : I ≠ ⊥)
    (hI : ⁅I, I⁆ = I) (hIX : I ≤ normalizer (X : Set (Perm (Fin n)))) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hpX : p ∣ Nat.card ↥X := by
    have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
    obtain ⟨k, hk, hck⟩ := hX.nontrivial_iff_card.mp this
    rw [hck]
    exact dvd_pow_self p hk.ne'
  have hp11 : p ≤ 11 := (Nat.Prime.dvd_factorial hp).mp
    (hpX.trans ((Subgroup.card_subgroup_dvd_card X).trans (card_perm_dvd h11)))
  have h7 : p = 7 ∨ p = 11 := by
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  have hrank : ∀ E : Subgroup (Perm (Fin n)), IsElementaryAbelian p ↥E →
      Nat.card ↥E ≤ p ∨ (p = 3 ∧ Nat.card ↥E ≤ 9) := fun E hE =>
    FinGlue.rank_of_dvd hp (fun k hk => Or.inl (by
      by_contra hk2
      have : p ^ 2 ∣ 11 ! := (Nat.pow_dvd_pow p (by omega)).trans (hk.trans (card_perm_dvd h11))
      rcases h7 with rfl | rfl <;> exact absurd this (by decide))) E hE
  obtain ⟨x, -, hxp, hIx⟩ := exists_centralized hp hX hX1 hI hIX hrank
  have hxs : x.support.card < 2 * p := by
    have := Finset.card_le_univ x.support
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨hxc, hxs'⟩ := isCycle_of_orderOf hp hxp hxs
  have hcompl : (x.support)ᶜ.card ≤ 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hxs']
    omega
  exact hI1 (eq_bot_of_fix hI hcompl fun g hg y hy => fix_of_perfect hxc hI hIx g hg y hy)

theorem false_of_fiveCycle (h11 : n ≤ 11) {X U I : Subgroup (Perm (Fin n))}
    (hX : IsPGroup 5 ↥X) (hU : IVK.IsFourSubgroup U) (hI1 : I ≠ ⊥) (hI : ⁅I, I⁆ = I)
    (hIU : I ≤ centralizer (U : Set (Perm (Fin n))))
    (hUX : U ≤ normalizer (X : Set (Perm (Fin n))))
    (hIX : I ≤ normalizer (X : Set (Perm (Fin n)))) {σ : Perm (Fin n)} (hσX : σ ∈ X)
    (hσc : σ.IsCycle) (hσ5 : σ.support.card = 5) : False := by
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  have hσo : orderOf σ = 5 := by rw [hσc.orderOf, hσ5]
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := comm_of_not_dvd hp5 hX fun h =>
    absurd (h.trans (card_perm_dvd h11)) (by decide)
  have hdich : ∀ g ∈ normalizer (X : Set (Perm (Fin n))),
      (∀ x ∈ σ.support, g x ∈ σ.support) ∨ ∀ x ∈ σ.support, g x ∉ σ.support := fun g hg =>
    maps_or_disjoint hσc (hXc _ ((mem_normalizer_iff.mp hg σ).mp hσX) σ hσX)
  have hpow : ∀ g ∈ normalizer (X : Set (Perm (Fin n))), g ∈ setwiseStab σ.support →
      g * σ * g⁻¹ ∈ zpowers σ := by
    intro g hg hgA
    refine mem_zpowers_of_commute hσc (hXc _ ((mem_normalizer_iff.mp hg σ).mp hσX) σ hσX)
      fun x hx => ?_
    have hx' : g⁻¹ x ∉ σ.support := fun h => hx (((setwiseStab σ.support).inv_mem hgA x).mp h)
    rw [Perm.mul_apply, Perm.mul_apply, notMem_support.mp hx', ← Perm.mul_apply, mul_inv_cancel,
      Perm.one_apply]
  have hAc : (σ.support)ᶜ.card ≤ 6 := by
    rw [Finset.card_compl, Fintype.card_fin, hσ5]
    omega
  have hout : ∀ k ∈ normalizer (X : Set (Perm (Fin n))), k ∉ setwiseStab σ.support →
      ∀ x ∈ σ.support, k x ∉ σ.support := fun k hk hkA =>
    (hdich k hk).resolve_left fun h => hkA (mem_stabSet_of_maps h)
  have hIA : I ≤ setwiseStab σ.support := by
    refine perfect_le_of_two hI fun g hg h hh hgA hhA => ?_
    have hg' := hout g⁻¹ (hIX (I.inv_mem hg)) fun h' =>
      hgA (by simpa using (setwiseStab σ.support).inv_mem h')
    have hh' := hout h (hIX hh) hhA
    rcases hdich (g * h) (hIX (I.mul_mem hg hh)) with h1 | h1
    · exact mem_stabSet_of_maps h1
    exfalso
    have hdisj : _root_.Disjoint (σ.support.image h) (σ.support.image ⇑g⁻¹) := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x', hx', hxx'⟩ := Finset.mem_image.mp hy'
      apply h1 x hx
      rw [Perm.mul_apply, ← hxx', ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
      exact hx'
    have hsub : σ.support.image h ∪ σ.support.image ⇑g⁻¹ ⊆ (σ.support)ᶜ := by
      intro y hy
      rw [Finset.mem_compl]
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hh' x hx
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hg' x hx
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ h.injective,
      Finset.card_image_of_injective _ (g⁻¹).injective, hσ5] at this
    omega
  have hIσ : I ≤ centralizer ({σ} : Set (Perm (Fin n))) :=
    le_centralizer_of_conj_mem hI fun g hg => hpow g (hIX hg) (hIA hg)
  have hIfix : I ≤ pointwiseFix σ.support := fun g hg x hx => fix_of_perfect hσc hI hIσ g hg x hx
  have hdvd : Nat.card ↥I ∣ 2 ^ 4 * 3 ^ 2 * 5 :=
    (card_dvd_of_fix _ hIfix).trans ((Nat.factorial_dvd_factorial hAc).trans (by decide))
  have h5 : 5 ∣ Nat.card ↥I := by
    by_contra h5
    have hcop : Nat.Coprime (Nat.card ↥I) 5 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp5).mpr h5)
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 (hcop.dvd_of_dvd_mul_right hdvd)
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
    exact hI1 (eq_bot_of_perfect_of_le le_rfl
      (isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hk.symm) hI)
  obtain ⟨⟨c, hcI⟩, hco⟩ := exists_prime_orderOf_dvd_card' (G := ↥I) 5 h5
  have hco' : orderOf c = 5 := by
    rw [← hco]
    exact Subgroup.orderOf_coe (⟨c, hcI⟩ : ↥I)
  have hcA : ∀ x ∈ σ.support, c x = x := hIfix hcI
  have hcsub : c.support ⊆ (σ.support)ᶜ := fun x hx =>
    Finset.mem_compl.mpr fun hxA => (mem_support.mp hx) (hcA x hxA)
  obtain ⟨hcc, hc5⟩ := isCycle_of_orderOf hp5 hco' (by
    have := Finset.card_le_card hcsub
    omega)
  have := hU.1
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
  have hUc : ∀ u ∈ U, ∀ x ∈ c.support, u x = x := fun u hu =>
    fix_of_commute_of_mul_self hcc (by rw [hc5]; decide)
      (mem_centralizer_iff.mp (hIU hcI) u hu) (hsq u hu)
  have hAC : _root_.Disjoint σ.support c.support := by
    rw [Finset.disjoint_left]
    intro x hxA hxC
    exact (mem_support.mp hxC) (hcA x hxA)
  have hACc : (σ.support ∪ c.support)ᶜ.card ≤ 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hAC, hσ5, hc5]
    omega
  have hUA : ∀ u ∈ U, u ∈ setwiseStab σ.support := by
    intro u hu
    rcases hdich u (hUX hu) with h1 | h1
    · exact mem_stabSet_of_maps h1
    exfalso
    have hsub : σ.support.image u ⊆ (σ.support ∪ c.support)ᶜ := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      refine ⟨h1 x hx, fun hxC => ?_⟩
      have h2 : u x = x := u.injective (hUc u hu _ hxC)
      rw [h2] at hxC
      exact Finset.disjoint_left.mp hAC hx hxC
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ u.injective, hσ5] at this
    omega
  obtain ⟨u, huU, hu1, hcomm⟩ :=
    exists_commute_of_four hU hσo fun u hu => hpow u (hUX hu) (hUA u hu)
  have huA := fix_of_commute_of_mul_self hσc (by rw [hσ5]; decide) hcomm (hsq u huU)
  refine hu1 (eq_one_of_fix hACc fun x hx => ?_)
  rcases Finset.mem_union.mp hx with hx | hx
  · exact huA x hx
  · exact hUc u huU x hx

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAlt5
