module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk

open Subgroup CFSG.Semidihedral.Principal CFSG.Semidihedral.Principal.CoprimeFixedPoint

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

theorem isPGroup_zpowers {σ : MulAut Y} (hσ : σ ^ p = 1) : IsPGroup p (zpowers σ) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  show (g : MulAut Y) ^ p ^ 1 = 1
  rw [pow_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]

theorem map_eq_of_forall_mem (σ : MulAut Y) (N' : Subgroup Y) (hN : ∀ n ∈ N', σ n ∈ N') :
    N'.map ((σ : Y ≃* Y) : Y →* Y) = N' := by
  have hle : N'.map ((σ : Y ≃* Y) : Y →* Y) ≤ N' := by
    rintro _ ⟨n, hn, rfl⟩
    exact hN n hn
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (σ : Y ≃* Y).injective])

@[expose] noncomputable def quotAut (σ : MulAut Y) (N' : Subgroup Y) [N'.Normal]
    (hN : ∀ n ∈ N', σ n ∈ N') : MulAut (Y ⧸ N') :=
  QuotientGroup.congr N' N' σ (map_eq_of_forall_mem σ N' hN)

theorem quotAut_mk (σ : MulAut Y) (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N') (y : Y) :
    quotAut σ N' hN (y : Y ⧸ N') = ((σ y : Y) : Y ⧸ N') := rfl

theorem quotAut_pow_mk (σ : MulAut Y) (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N')
    (k : ℕ) (y : Y) : (quotAut σ N' hN ^ k) (y : Y ⧸ N') = (((σ ^ k) y : Y) : Y ⧸ N') := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, quotAut_mk, ih, pow_succ, MulAut.mul_apply]

theorem quotAut_pow (σ : MulAut Y) (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N')
    (hσ : σ ^ p = 1) : quotAut σ N' hN ^ p = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [quotAut_pow_mk, hσ]
    rfl

theorem exists_pow_eq_of_mem_zpowers {σ : MulAut Y} (hσ : σ ^ p = 1) (hp : 0 < p) {a : MulAut Y}
    (ha : a ∈ zpowers σ) : ∃ j : ℕ, σ ^ j = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have h1 : σ ^ (p : ℤ) = 1 := by rw [zpow_natCast, hσ]
  refine ⟨(k % p).toNat, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))]
  exact (zpow_eq_zpow_emod k h1).symm

theorem mem_of_mem_zpowers {σ : MulAut Y} (hσ : σ ^ p = 1) (hp : 0 < p) {N' : Subgroup Y}
    (hN : ∀ n ∈ N', σ n ∈ N') {a : MulAut Y} (ha : a ∈ zpowers σ) {n : Y} (hn : n ∈ N') :
    a n ∈ N' := by
  obtain ⟨j, rfl⟩ := exists_pow_eq_of_mem_zpowers hσ hp ha
  clear ha
  induction j generalizing n with
  | zero => simpa using hn
  | succ j ih =>
    rw [pow_succ, MulAut.mul_apply]
    exact ih (hN n hn)

theorem exists_fixed_of_quotAut_fixed [Fact p.Prime] (σ : MulAut Y) (hσ : σ ^ p = 1)
    (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N') (hcop : ¬ p ∣ Nat.card N') (y : Y)
    (hy : quotAut σ N' hN (y : Y ⧸ N') = (y : Y ⧸ N')) : ∃ c : Y, σ c = c ∧ y⁻¹ * c ∈ N' := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let A : Subgroup (MulAut Y) := zpowers σ
  let α : ↥A →* MulAut Y := A.subtype
  have hA : IsPGroup p A := isPGroup_zpowers hσ
  have hN' : ∀ a : ↥A, ∀ n ∈ N', α a n ∈ N' := fun a n hn =>
    mem_of_mem_zpowers hσ hp0 hN a.2 hn
  have hfix := coprime_fixed_point_lifting p hA α N' hN' hcop
  have hpow : ∀ j : ℕ, (quotAut σ N' hN ^ j) (y : Y ⧸ N') = (y : Y ⧸ N') := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ, MulAut.mul_apply, hy, ih]
  have hmem : (y : Y ⧸ N') ∈ {q : Y ⧸ N' | ∀ a : ↥A, quotientAction α N' hN' a q = q} := by
    intro a
    obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_zpowers hσ hp0 a.2
    have h1 : quotientAction α N' hN' a (y : Y ⧸ N') = ((α a y : Y) : Y ⧸ N') := rfl
    have h2 : (α a) y = (σ ^ j) y := by
      show (a : MulAut Y) y = (σ ^ j) y
      rw [hj]
    rw [h1, h2, ← quotAut_pow_mk σ N' hN j y]
    exact hpow j
  rw [hfix] at hmem
  obtain ⟨c, hc, hcy⟩ := hmem
  refine ⟨c, hc ⟨σ, Subgroup.mem_zpowers σ⟩, ?_⟩
  have := QuotientGroup.eq.mp hcy.symm
  simpa using this

theorem mulAut_eq_one_of_card_three {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 3)
    {ρ : MulAut K} (hρ : ρ ^ p = 1) (hp : p.Prime) (hp2 : p ≠ 2) : ρ = 1 := by
  have hnt : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg1⟩ := exists_ne (1 : K)
  have hord : orderOf g = 3 := by
    have hd : orderOf g ∣ 3 := hK ▸ orderOf_dvd_natCard g
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have htop : zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hK])
  have hmem : ∀ x : K, ∃ k : ℤ, g ^ k = x := fun x =>
    Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top x)
  have hmod : ∀ k : ℤ, g ^ k = g ^ (k % 3) := fun k => by
    have := zpow_mod_orderOf g k
    rw [hord] at this
    exact this.symm
  have hsq : ρ ^ 2 = 1 := by
    obtain ⟨j, hj⟩ := hmem (ρ g)
    have hρg1 : ρ g ≠ 1 := fun h => hg1 (ρ.injective (by rw [h, map_one]))
    have h3 : j % 3 = 1 ∨ j % 3 = 2 := by
      rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
      · exfalso
        apply hρg1
        rw [← hj, hmod j, h, zpow_zero]
      · exact Or.inl h
      · exact Or.inr h
    have hjj : (j * j) % 3 = 1 := by
      rcases h3 with h | h <;> simp [Int.mul_emod, h]
    have hg2 : (ρ ^ 2) g = g := by
      rw [pow_two, MulAut.mul_apply, ← hj, map_zpow, ← hj, ← zpow_mul, hmod (j * j), hjj, zpow_one]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨k, rfl⟩ := hmem x
    rw [map_zpow, hg2]
    rfl
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h1 : orderOf ρ ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hρ)
    rwa [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem quotAut_eq_one_alt (hp : p.Prime) (hp5 : 5 ≤ p) (σ : MulAut Y) (hσ : σ ^ p = 1)
    (N' : Subgroup Y) [N'.Normal] (hN : ∀ n ∈ N', σ n ∈ N') (hcop : ¬ p ∣ Nat.card Y) {m : ℕ}
    (hm : m = 3 ∨ 5 ≤ m) (e : (Y ⧸ N') ≃* alternatingGroup (Fin m)) :
    quotAut σ N' hN = 1 := by
  have hρ := quotAut_pow σ N' hN hσ
  have hp2 : p ≠ 2 := by omega
  have hKp : ¬ p ∣ Nat.card (Y ⧸ N') := fun h =>
    hcop (h.trans (Subgroup.card_quotient_dvd_card N'))
  rcases hm with rfl | hm5
  · refine mulAut_eq_one_of_card_three ?_ hρ hp hp2
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  · set K := Y ⧸ N' with hKdef
    have hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K) := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup m hm5 p hp hp2
    have hcop' : p.Coprime
        (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hout
    have hmk : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)
        (quotAut σ N' hN) = 1 :=
      (pow_eq_one_iff_of_coprime hcop').mp ⟨by rw [← map_pow, hρ, map_one], pow_card_eq_one'⟩
    obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hmk
    have hcpz : c ^ p ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 : (MulAut.conj c) ^ p = 1 := by
        rw [show MulAut.conj c = quotAut σ N' hN from hc, hρ]
      have h2 := congrArg (fun a : MulAut K => a x) h1
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at h2
      calc x * c ^ p = (c ^ p * x * (c ^ p)⁻¹) * c ^ p := by rw [h2]
        _ = c ^ p * x := by group
    have hcopc : Nat.Coprime (orderOf c) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
        hKp (h.trans (orderOf_dvd_natCard c))).symm
    have hzp : Subgroup.zpowers (c ^ p) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) p)) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, hcopc.gcd_eq_one, Nat.div_one]
    have hcz : c ∈ Subgroup.center K := by
      have : c ∈ Subgroup.zpowers (c ^ p) := by rw [hzp]; exact Subgroup.mem_zpowers c
      exact Subgroup.zpowers_le.mpr hcpz this
    rw [← hc]
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.conj_apply, MulAut.one_apply]
    have := Subgroup.mem_center_iff.mp hcz x
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [this]
      _ = x := by group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlk
