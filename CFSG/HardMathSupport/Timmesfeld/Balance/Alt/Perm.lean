module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.PrincipalIdealDomain

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv Equiv.Perm

variable {Ω : Type*}

section
variable [Fintype Ω] [DecidableEq Ω]

theorem conj_cycleOf_of_commute (z d : Perm Ω) (h : z * d = d * z) (x : Ω) :
    z * d.cycleOf x * z⁻¹ = d.cycleOf (z x) := by
  have hd : z * d * z⁻¹ = d := by rw [h]; simp
  ext y
  have key : d.SameCycle x (z⁻¹ y) ↔ d.SameCycle (z x) y := by
    have := Equiv.Perm.sameCycle_conj (f := d) (g := z) (x := z x) (y := y)
    rw [hd] at this
    simpa using this.symm
  simp only [Perm.mul_apply, Equiv.Perm.cycleOf_apply]
  by_cases hs : d.SameCycle (z x) y
  · have h1 := key.2 hs
    have := congrArg (fun f : Perm Ω => f y) hd
    simp only [h1, hs, ↓reduceIte]
    simpa using this
  · have h1 : ¬ d.SameCycle x (z⁻¹ y) := fun h' => hs (key.1 h')
    simp only [h1, hs, ↓reduceIte]
    simp

end

theorem eq_one_of_pow_eq_one_of_mem {p : ℕ} (N : Subgroup (Perm Ω))
    (hNcop : Nat.Coprime p (Nat.card N)) {w : Perm Ω} (hw : w ∈ N) (hwp : w ^ p = 1) :
    w = 1 := by
  have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwp
  have h2 : orderOf w ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hw
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hNcop) h2
  exact orderOf_eq_one_iff.mp this

theorem zpow_apply_eq_self_iff_dvd {p : ℕ} (hp : p.Prime) {d : Perm Ω} (hd : orderOf d = p)
    {x : Ω} (hx : d x ≠ x) (k : ℤ) (hk : (d ^ k) x = x) : (p : ℤ) ∣ k := by
  by_contra hnd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime (p : ℤ) k :=
    (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hnd
  obtain ⟨u, v, huv⟩ := hcop
  have hdp : d ^ (p : ℤ) = 1 := by
    rw [← hd, zpow_natCast, pow_orderOf_eq_one]
  have : d = (d ^ k) ^ v := by
    calc d = d ^ (u * (p : ℤ) + v * k) := by rw [huv, zpow_one]
      _ = (d ^ k) ^ v := by
        rw [zpow_add, mul_comm u, zpow_mul, hdp, one_zpow, one_mul, mul_comm v, zpow_mul]
  apply hx
  conv_lhs => rw [this]
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hk v

section
variable [Fintype Ω] [DecidableEq Ω]

theorem cycleOf_pow_eq_one {p : ℕ} {d : Perm Ω} (hd : orderOf d = p) (x : Ω) :
    d.cycleOf x ^ p = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (hd ▸ Equiv.Perm.orderOf_cycleOf_dvd_orderOf d x)

theorem sign_cycleOf_eq_one {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) {d : Perm Ω}
    (hd : orderOf d = p) (x : Ω) : Perm.sign (d.cycleOf x) = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h := congrArg Perm.sign (cycleOf_pow_eq_one hd x)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Perm.sign (d.cycleOf x)) with h1 | h1
  · exact h1
  · rw [h1, hodd.neg_one_pow] at h
    exact absurd h (by decide)

theorem fixes_supp_of_mem
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup (Perm Ω)) (hH : alternatingGroup Ω ≤ H)
    (d : Perm Ω) (hd : orderOf d = p)
    (N : Subgroup (Perm Ω))
    (hNle : N ≤ H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))
    (hNnorm : (N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))).Normal)
    (hNcop : Nat.Coprime p (Nat.card N))
    {z : Perm Ω} (hz : z ∈ N) {x : Ω} (hx : d x ≠ x) : z x = x := by
  have hzc : z * d = d * z := by
    have := (Subgroup.mem_centralizer_iff.mp (hNle hz).2) d (Set.mem_singleton d)
    exact this.symm
  set c := d.cycleOf x with hcdef
  have hcsupp : x ∈ d.support := Equiv.Perm.mem_support.mpr hx
  have hdc : d * c = c * d := by
    have := conj_cycleOf_of_commute d d rfl x
    have h2 : d.cycleOf (d x) = d.cycleOf x :=
      (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl d x)).symm.cycleOf_eq
    rw [h2] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  have hcK : c ∈ H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)) := by
    refine ⟨hH ?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · exact Equiv.Perm.mem_alternatingGroup.mpr (sign_cycleOf_eq_one hp2 hp hd x)
    · intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hdc
  have hdzx : d (z x) ≠ z x := by
    intro h
    apply hx
    have : z (d x) = z x := by
      have h3 := congrArg (fun f : Perm Ω => f x) hzc
      simp only [Perm.mul_apply] at h3
      rw [h3, h]
    exact z.injective this
  have hconj := conj_cycleOf_of_commute z d hzc x
  have hK : (⟨z⁻¹, (hNle (N.inv_mem hz))⟩ : ↥(H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))) ∈
      N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω))) := N.inv_mem hz
  have hmem := hNnorm.conj_mem _ hK ⟨c, hcK⟩
  have hcz : c * z⁻¹ * c⁻¹ ∈ N := hmem
  have hw : (d.cycleOf (z x)) * c⁻¹ ∈ N := by
    have : (d.cycleOf (z x)) * c⁻¹ = z * (c * z⁻¹ * c⁻¹) := by
      rw [← hconj, ← hcdef]; group
    rw [this]; exact N.mul_mem hz hcz
  have hcomm : Commute (d.cycleOf (z x)) c := by
    apply Equiv.Perm.cycleFactorsFinset_mem_commute'
    · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hdzx)
    · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hcsupp
  have hwp : ((d.cycleOf (z x)) * c⁻¹) ^ p = 1 := by
    rw [(hcomm.inv_right).mul_pow, cycleOf_pow_eq_one hd, inv_pow, cycleOf_pow_eq_one hd]
    simp
  have hw1 := eq_one_of_pow_eq_one_of_mem N hNcop hw hwp
  have hceq : d.cycleOf (z x) = c := mul_inv_eq_one.mp hw1
  have hsc : d.SameCycle x (z x) :=
    (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support hcsupp
      (Equiv.Perm.mem_support.mpr hdzx)).mpr hceq.symm
  obtain ⟨i, hi⟩ := hsc
  have hcomm0 : Commute z d := hzc
  have hpowz : ∀ k : ℕ, (z ^ k) x = (d ^ (i * (k : ℤ))) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc1 : Commute (z ^ k) (d ^ i) := (hcomm0.pow_left k).zpow_right i
      have e1 : (z ^ (k + 1)) x = (z ^ k) ((d ^ i) x) := by
        rw [pow_succ, Perm.mul_apply, hi]
      have e2 : (z ^ k) ((d ^ i) x) = (d ^ i) ((z ^ k) x) := by
        have := congrArg (fun f : Perm Ω => f x) hc1.eq
        simpa only [Perm.mul_apply] using this
      rw [e1, e2, ih, ← Perm.mul_apply, ← zpow_add]
      congr 2
      push_cast
      ring
  have hzm : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hxfix : (d ^ (i * (orderOf z : ℤ))) x = x := by
    rw [← hpowz, hzm]; rfl
  have hdvd : (p : ℤ) ∣ i * (orderOf z : ℤ) :=
    zpow_apply_eq_self_iff_dvd hp hd hx _ hxfix
  have hcop : Nat.Coprime p (orderOf z) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hz) hNcop
  have hcopZ : IsCoprime (p : ℤ) (orderOf z : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hpi : (p : ℤ) ∣ i := hcopZ.dvd_of_dvd_mul_right hdvd
  have hdi : d ^ i = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hd]; exact hpi
  rw [← hi, hdi]
  rfl


theorem exists_even_not_comm {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 4 ≤ Fintype.card α) (z : Perm α) (hz : z ≠ 1) :
    ∃ c : Perm α, Perm.sign c = 1 ∧ z * c ≠ c * z := by
  obtain ⟨x, hx⟩ : ∃ x, z x ≠ x := by
    by_contra h
    push Not at h
    exact hz (Equiv.ext h)
  set y := z x with hy
  have hcard : 1 < (({x, y} : Finset α)ᶜ).card := by
    rw [Finset.card_compl]
    have : ({x, y} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨w, hw, w', hw', hww'⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hw hw'
  refine ⟨Equiv.swap x w * Equiv.swap x w', ?_, ?_⟩
  · rw [map_mul, Perm.sign_swap (Ne.symm hw.1), Perm.sign_swap (Ne.symm hw'.1)]
    decide
  · intro hcomm
    have hxw : x ≠ w := fun h => hw.1 h.symm
    have hxw' : x ≠ w' := fun h => hw'.1 h.symm
    have hcy : (Equiv.swap x w * Equiv.swap x w') y = y := by
      simp only [Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hx (fun h => hw'.2 h.symm),
        Equiv.swap_apply_of_ne_of_ne hx (fun h => hw.2 h.symm)]
    have hcx : (Equiv.swap x w * Equiv.swap x w') x = w' := by
      simp only [Perm.mul_apply, Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne hw'.1 (Ne.symm hww')
    have h1 := congrArg (fun f : Perm α => f x) hcomm
    simp only [Perm.mul_apply] at h1
    have h1' : z ((Equiv.swap x w * Equiv.swap x w') x) =
        (Equiv.swap x w * Equiv.swap x w') (z x) := by
      simpa only [Perm.mul_apply] using h1
    rw [hcx, ← hy, hcy] at h1'
    exact hw'.1 (z.injective (h1'.trans hy))


theorem card_fixed_le_of_ne_one
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup (Perm Ω)) (hH : alternatingGroup Ω ≤ H)
    (d : Perm Ω) (hd : orderOf d = p)
    (N : Subgroup (Perm Ω))
    (hNle : N ≤ H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))
    (hNnorm : (N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω)))).Normal)
    (hNcop : Nat.Coprime p (Nat.card N))
    (z : Perm Ω) (hz : z ∈ N) (hz1 : z ≠ 1) :
    Fintype.card {x // d x = x} ≤ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  set α := {x // d x = x} with hαdef
  have hcardα : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  have hlt' : p + 1 < Fintype.card α := hlt
  have hα5 : 5 ≤ Nat.card α := by omega
  have hzc : z * d = d * z := by
    have := (Subgroup.mem_centralizer_iff.mp (hNle hz).2) d (Set.mem_singleton d)
    exact this.symm
  have hzd : ∀ x, z (d x) = d (z x) := fun x => by
    have := congrArg (fun f : Perm Ω => f x) hzc
    simpa only [Perm.mul_apply] using this
  have h₁ : ∀ x, d (z x) = z x ↔ d x = x := fun x => by
    rw [← hzd]; exact z.injective.eq_iff
  have h₂ : ∀ x, z x ≠ x → d x = x := fun x hx => by
    by_contra h
    exact hx (fixes_supp_of_mem hp hp2 H hH d hd N hNle hNnorm hNcop hz h)
  let z' : Perm α := z.subtypePerm h₁
  have hz' : (Perm.ofSubtype z' : Perm Ω) = z := Perm.ofSubtype_subtypePerm h₁ h₂
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    rw [← hz', h, map_one]
  let K := H ⊓ Subgroup.centralizer ({d} : Set (Perm Ω))
  let ψ : alternatingGroup α →* Perm Ω :=
    (Perm.ofSubtype : Perm α →* Perm Ω).comp (alternatingGroup α).subtype
  have hψinj : Function.Injective ψ :=
    Perm.ofSubtype_injective.comp (alternatingGroup α).subtype_injective
  have hψK : ∀ a, ψ a ∈ K := by
    intro a
    refine ⟨hH ?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · have := a.2
      rw [mem_alternatingGroup] at this ⊢
      show Perm.sign (Perm.ofSubtype (a : Perm α)) = 1
      rw [Perm.sign_ofSubtype]; exact this
    · intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hdisj : Perm.Disjoint (Perm.ofSubtype (a : Perm α) : Perm Ω) h := by
        intro y
        by_cases hy : h y = y
        · exact Or.inr hy
        · exact Or.inl (Perm.ofSubtype_apply_of_not_mem _ hy)
      exact hdisj.commute.symm.eq
  let M : Subgroup (alternatingGroup α) := N.comap ψ
  have hMnorm : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    have hm' : ψ m ∈ N := hm
    have hK1 : (⟨ψ m, hψK m⟩ : K) ∈ N.subgroupOf K := hm'
    have := hNnorm.conj_mem _ hK1 ⟨ψ g, hψK g⟩
    show ψ (g * m * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact this
  have : IsSimpleGroup (alternatingGroup α) := alternatingGroup.isSimpleGroup hα5
  have _ := hMnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
  ·
    have hcomm : ∀ a : alternatingGroup α, z' * (a : Perm α) = (a : Perm α) * z' := by
      intro a
      have hsign : Perm.sign (z' * (a : Perm α) * z'⁻¹ * (a : Perm α)⁻¹) = 1 := by
        have ha := a.2
        rw [mem_alternatingGroup] at ha
        simp [ha]
      let b : alternatingGroup α := ⟨_, mem_alternatingGroup.mpr hsign⟩
      have hbN : ψ b ∈ N := by
        have hK1 : (⟨z⁻¹, hNle (N.inv_mem hz)⟩ : K) ∈ N.subgroupOf K := N.inv_mem hz
        have := hNnorm.conj_mem _ hK1 ⟨ψ a, hψK a⟩
        have hcz : ψ a * z⁻¹ * (ψ a)⁻¹ ∈ N := this
        have : ψ b = z * (ψ a * z⁻¹ * (ψ a)⁻¹) := by
          show Perm.ofSubtype (z' * (a : Perm α) * z'⁻¹ * (a : Perm α)⁻¹) =
            z * (Perm.ofSubtype (a : Perm α) * z⁻¹ * (Perm.ofSubtype (a : Perm α))⁻¹)
          simp only [map_mul, map_inv, hz']
          group
        rw [this]
        exact N.mul_mem hz hcz
      have hb : b ∈ M := hbN
      rw [hM, Subgroup.mem_bot] at hb
      have hb' : z' * (a : Perm α) * z'⁻¹ * (a : Perm α)⁻¹ = 1 := congrArg Subtype.val hb
      calc z' * (a : Perm α) = (z' * (a : Perm α) * z'⁻¹ * (a : Perm α)⁻¹) * (a : Perm α) * z' := by
            group
        _ = (a : Perm α) * z' := by rw [hb']; simp
    obtain ⟨c, hc1, hc2⟩ := exists_even_not_comm (by omega) z' hz'1
    exact hc2 (hcomm ⟨c, mem_alternatingGroup.mpr hc1⟩)
  ·
    have hp_le : p ≤ Fintype.card α := by omega
    have : Nontrivial α := by
      rw [← Fintype.one_lt_card_iff_nontrivial]; omega
    have hdvd : p ∣ Nat.card (alternatingGroup α) := by
      rw [nat_card_alternatingGroup, hcardα]
      have h2 : 2 ∣ (Fintype.card α).factorial := Nat.dvd_factorial two_pos (by omega)
      have h3 : p ∣ (Fintype.card α).factorial := Nat.dvd_factorial hp.pos hp_le
      have h4 : 2 * ((Fintype.card α).factorial / 2) = (Fintype.card α).factorial :=
        Nat.mul_div_cancel' h2
      rw [← h4] at h3
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).dvd_of_dvd_mul_left h3
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have haM : a ∈ M := by rw [hM]; trivial
    have haN : ψ a ∈ N := haM
    have hord : orderOf (ψ a) = p := by rw [orderOf_injective ψ hψinj a, ha]
    have : p ∣ Nat.card N := hord ▸ Subgroup.orderOf_dvd_natCard N haN
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hNcop this)


theorem fixed_subset_of_card
    {p : ℕ} (hp : p.Prime) {a b : Perm Ω} (hab : a * b = b * a) (hbp : b ^ p = 1)
    (hcard : Fintype.card {x // a x = x} ≤ p + 1)
    {x₁ x₂ : Ω} (hne : x₁ ≠ x₂) (h1 : a x₁ = x₁ ∧ b x₁ = x₁) (h2 : a x₂ = x₂ ∧ b x₂ = x₂) :
    ∀ x, a x = x → b x = x := by
  have : Fact p.Prime := ⟨hp⟩
  have hmap : ∀ x, a (b x) = b x ↔ a x = x := fun x => by
    have h3 : a (b x) = b (a x) := by
      have := congrArg (fun f : Perm Ω => f x) hab
      simpa only [Perm.mul_apply] using this
    rw [h3]; exact b.injective.eq_iff
  let σ : Perm {x // a x = x} := b.subtypePerm hmap
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext y
    simp [σ, hbp]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  set T := σ.supportᶜ with hT
  have hTc : T.card ≤ Fintype.card {x // a x = x} := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ T
  have h2T : 2 ≤ T.card := by
    have hx1 : (⟨x₁, h1.1⟩ : {x // a x = x}) ∈ T := by
      simp [hT, σ, h1.2]
    have hx2 : (⟨x₂, h2.1⟩ : {x // a x = x}) ∈ T := by
      simp [hT, σ, h2.2]
    have hne' : (⟨x₁, h1.1⟩ : {x // a x = x}) ≠ ⟨x₂, h2.1⟩ := fun h =>
      hne (congrArg Subtype.val h)
    calc 2 = ({⟨x₁, h1.1⟩, ⟨x₂, h2.1⟩} : Finset {x // a x = x}).card :=
          (Finset.card_pair hne').symm
      _ ≤ T.card := Finset.card_le_card (by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl <;> assumption)
  have hdvd : p ∣ Fintype.card {x // a x = x} - T.card :=
    (Nat.modEq_iff_dvd' hTc).mp hmod
  have heq : T.card = Fintype.card {x // a x = x} := by
    by_contra hne2
    have hpos : 0 < Fintype.card {x // a x = x} - T.card := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hTuniv : T = Finset.univ := Finset.eq_univ_of_card T (by rw [heq])
  intro x hx
  have : (⟨x, hx⟩ : {x // a x = x}) ∈ T := by rw [hTuniv]; exact Finset.mem_univ _
  simpa [hT, σ] using this


end

theorem fixed_card_le_of_primeCore
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (H : Subgroup (Equiv.Perm Ω)) (hH : alternatingGroup Ω ≤ H)
    (d : Equiv.Perm Ω) (hd : orderOf d = p)
    (N : Subgroup (Equiv.Perm Ω))
    (hNle : N ≤ H ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm Ω)))
    (hNnorm : (N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm Ω)))).Normal)
    (hNcop : Nat.Coprime p (Nat.card N))
    (z : Equiv.Perm Ω) (hz : z ∈ N) (hz1 : z ≠ 1) :
    (∀ x, z x ≠ x → d x = x) ∧ Fintype.card {x // d x = x} ≤ p + 1 := by
  refine ⟨fun x hx => ?_, card_fixed_le_of_ne_one hp hp2 H hH d hd N hNle hNnorm hNcop z hz hz1⟩
  by_contra h
  exact hx (fixes_supp_of_mem hp hp2 H hH d hd N hNle hNnorm hNcop hz h)

theorem fixedSet_eq_of_delta
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (D H : Subgroup (Equiv.Perm Ω)) (hDe : ∀ x ∈ D, x ^ p = 1) (hDc : IsMulCommutative D)
    (hH : alternatingGroup Ω ≤ H) (hDne : D ≠ ⊥)
    (z : Equiv.Perm Ω) (hz1 : z ≠ 1)
    (hz : ∀ d ∈ D, d ≠ 1 → ∃ N : Subgroup (Equiv.Perm Ω),
      N ≤ H ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm Ω)) ∧
      (N.subgroupOf (H ⊓ Subgroup.centralizer ({d} : Set (Equiv.Perm Ω)))).Normal ∧
      Nat.Coprime p (Nat.card N) ∧ z ∈ N) :
    ∃ F : Finset Ω, F.card ≤ p + 1 ∧ ∀ d ∈ D, d ≠ 1 → ∀ x, d x = x ↔ x ∈ F := by
  have : Fact p.Prime := ⟨hp⟩
  have key : ∀ d ∈ D, d ≠ 1 →
      (∀ x, z x ≠ x → d x = x) ∧ Fintype.card {x // d x = x} ≤ p + 1 := by
    intro d hdD hd1
    obtain ⟨N, hNle, hNnorm, hNcop, hzN⟩ := hz d hdD hd1
    exact fixed_card_le_of_primeCore hp hp2 H hH d (orderOf_eq_prime (hDe d hdD) hd1) N hNle
      hNnorm hNcop z hzN hz1
  obtain ⟨⟨d₀, hd₀D⟩, hd₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hDne
  have hd₀1' : d₀ ≠ 1 := fun h => hd₀1 (Subtype.ext h)
  obtain ⟨x₁, hx₁⟩ : ∃ x, z x ≠ x := by
    by_contra h
    push Not at h
    exact hz1 (Equiv.ext h)
  have hx₂ : z (z x₁) ≠ z x₁ := fun h => hx₁ (z.injective h)
  have hne : x₁ ≠ z x₁ := fun h => hx₁ h.symm
  have hcard₀ : (Finset.univ.filter (fun x => d₀ x = x)).card ≤ p + 1 := by
    rw [← Fintype.card_subtype]; exact (key d₀ hd₀D hd₀1').2
  refine ⟨Finset.univ.filter (fun x => d₀ x = x), hcard₀, ?_⟩
  intro d hdD hd1 x
  have hcomm : d₀ * d = d * d₀ := by
    have := hDc.is_comm.comm (⟨d₀, hd₀D⟩ : D) ⟨d, hdD⟩
    exact congrArg Subtype.val this
  have kd := key d hdD hd1
  have kd₀ := key d₀ hd₀D hd₀1'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fixed_subset_of_card hp hcomm.symm (hDe d₀ hd₀D) kd.2 hne
      ⟨kd.1 _ hx₁, kd₀.1 _ hx₁⟩ ⟨kd.1 _ hx₂, kd₀.1 _ hx₂⟩ x
  · exact fixed_subset_of_card hp hcomm (hDe d hdD) kd₀.2 hne
      ⟨kd₀.1 _ hx₁, kd.1 _ hx₁⟩ ⟨kd₀.1 _ hx₂, kd.1 _ hx₂⟩ x

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
