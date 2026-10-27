module

public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.T3

theorem not_dvd_pow_sub_pow_of_primitive {p ℓ N d e : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hℓp : ℓ ≠ p) (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1) (hdN : d < N)
    (hed : e < d) : ¬ ℓ ∣ p ^ d - p ^ e := by
  intro hdvd
  have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd
  have hℓpe : ¬ ℓ ∣ p ^ e := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h))
  exact hprim (d - e) (by omega) (by omega)
    (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓpe) hdvd)

theorem fixed_of_invariant_of_card_lt {C P : Type*} [Group C] [CommGroup P] [Finite P]
    {p ℓ N d : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1)
    (ρ : C →* MulAut P) {y : C} (hy : orderOf y = ℓ)
    (U : Subgroup P) (hU : ∀ v ∈ U, ρ y v ∈ U) (hUcard : Nat.card U = p ^ d) (hdN : d < N) :
    ∀ v ∈ U, ρ y v = v := by
  by_contra hne
  push Not at hne
  obtain ⟨v₀, hv₀, hv₀ne⟩ := hne
  let f : U →* U := ((ρ y : P →* P).comp U.subtype).codRestrict U (fun x => hU x x.2)
  have hf : ∀ x : U, ((f x : U) : P) = ρ y x := fun _ => rfl
  have hfinj : Function.Injective f := fun a b h =>
    Subtype.ext ((ρ y).injective (by simpa [hf] using congrArg Subtype.val h))
  let σ : MulAut U := MulEquiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.mp hfinj⟩
  have hσ : ∀ x : U, ((σ x : U) : P) = ρ y x := fun _ => rfl
  have hσpow : ∀ (k : ℕ) (x : U), (((σ ^ k) x : U) : P) = ρ (y ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ', map_mul, MulAut.mul_apply]
  have hσℓ : σ ^ ℓ = 1 := by
    ext x
    rw [hσpow, ← hy, pow_orderOf_eq_one, map_one]
    rfl
  have hσ1 : σ ≠ 1 := by
    intro h
    exact hv₀ne (by simpa [hσ] using congrArg (fun τ : MulAut U => ((τ ⟨v₀, hv₀⟩ : U) : P)) h)
  have hord : orderOf σ = ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact orderOf_eq_prime hσℓ hσ1
  obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hℓ
    (MonoidHom.id (MulAut U)) hord hσ1 hUcard
  exact not_dvd_pow_sub_pow_of_primitive hp hℓ hℓp hprim hdN hed hdvd

theorem exists_card_eq_pow_of_ne_top {P : Type*} [Group P] [Finite P] {p N : ℕ} (hp : p.Prime)
    (hPcard : Nat.card P = p ^ N) {U : Subgroup P} (hU : U ≠ ⊤) :
    ∃ d < N, Nat.card U = p ^ d := by
  obtain ⟨d, hdN, hd⟩ := (Nat.dvd_prime_pow hp).mp (hPcard ▸ Subgroup.card_subgroup_dvd_card U)
  refine ⟨d, lt_of_le_of_ne hdN fun h => hU ?_, hd⟩
  exact Subgroup.eq_top_of_card_eq U (by rw [hd, hPcard, h])

theorem fixed_of_invariant_of_ne_top {C P : Type*} [Group C] [CommGroup P] [Finite P]
    {p ℓ N : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1) (hPcard : Nat.card P = p ^ N)
    (ρ : C →* MulAut P) {y : C} (hy : orderOf y = ℓ)
    (U : Subgroup P) (hU : ∀ v ∈ U, ρ y v ∈ U) (hne : U ≠ ⊤) : ∀ v ∈ U, ρ y v = v := by
  obtain ⟨d, hdN, hd⟩ := exists_card_eq_pow_of_ne_top hp hPcard hne
  exact fixed_of_invariant_of_card_lt hp hℓ hℓp hprim ρ hy U hU hd hdN

theorem eq_one_of_fixed_of_primitive {C P : Type*} [Group C] [CommGroup P] [Finite P]
    {p ℓ N : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1) (hPcard : Nat.card P = p ^ N)
    (hPexp : ∀ v : P, v ^ p = 1) (ρ : C →* MulAut P) (hρ : Function.Injective ρ) {y : C}
    (hy : orderOf y = ℓ) (v : P) (hv : ρ y v = v) : v = 1 := by
  let φ : P →* P := MonoidHom.mk' (fun v => ρ y v / v) (fun a b => by
    simp only [map_mul]; exact mul_div_mul_comm _ _ _ _)
  have hφ : ∀ v, φ v = ρ y v / v := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    by_contra hns
    have hrange : φ.range ≠ ⊤ := fun h => hns (MonoidHom.range_eq_top.mp h)
    have hinv : ∀ w ∈ φ.range, ρ y w ∈ φ.range := by
      rintro _ ⟨u, rfl⟩
      refine ⟨ρ y u, ?_⟩
      rw [hφ, hφ, map_div]
    have hfix := fixed_of_invariant_of_ne_top hp hℓ hℓp hprim hPcard ρ hy φ.range hinv hrange
    have hpow : ∀ (k : ℕ) (u : P), ρ (y ^ k) u = u * φ u ^ k := by
      intro k u
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : ρ y (φ u) = φ u := hfix _ ⟨u, rfl⟩
        have hu : ρ y u = u * φ u := by rw [hφ, mul_div_cancel]
        rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, h1, hu, pow_succ',
          mul_assoc]
    have hφ1 : ∀ u, φ u = 1 := by
      intro u
      have hyℓ : y ^ ℓ = 1 := hy ▸ pow_orderOf_eq_one y
      have h1 : φ u ^ ℓ = 1 := by
        have := hpow ℓ u
        rw [hyℓ, map_one, MulAut.one_apply] at this
        exact mul_eq_left.mp this.symm
      have h2 : φ u ^ p = 1 := hPexp _
      have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ hp).mpr hℓp
      have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rwa [hcop, pow_one] at this
    have hρ1 : ρ y = 1 := by
      ext u
      have := hφ1 u
      rw [hφ, div_eq_one] at this
      simpa using this
    have hy1 : y = 1 := hρ (by rw [hρ1, map_one])
    rw [hy1, orderOf_one] at hy
    exact hℓ.one_lt.ne hy
  have hinj : Function.Injective φ := Finite.injective_iff_surjective.mpr hsurj
  apply hinj
  rw [map_one, hφ, hv, div_self']

theorem eq_bot_or_top_of_invariant_of_primitive {C P : Type*} [Group C] [CommGroup P] [Finite P]
    {p ℓ N : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1) (hPcard : Nat.card P = p ^ N)
    (hPexp : ∀ v : P, v ^ p = 1) (ρ : C →* MulAut P) (hρ : Function.Injective ρ) {y : C}
    (hy : orderOf y = ℓ) (U : Subgroup P) (hU : ∀ v ∈ U, ρ y v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases htop : U = ⊤
  · exact Or.inr htop
  · refine Or.inl ((Subgroup.eq_bot_iff_forall U).mpr fun v hv => ?_)
    exact eq_one_of_fixed_of_primitive hp hℓ hℓp hprim hPcard hPexp ρ hρ hy v
      (fixed_of_invariant_of_ne_top hp hℓ hℓp hprim hPcard ρ hy U hU htop v hv)

theorem isCyclic_of_injective_noZeroDivisors {K D : Type*} [Group K] [Finite K] [Ring D]
    [Nontrivial D] [NoZeroDivisors D] [Finite D] (Φ : K →* D) (hΦ : Function.Injective Φ) :
    IsCyclic K := by
  have : IsDomain D := NoZeroDivisors.to_isDomain D
  let _ : Field D := (Finite.isDomain_to_isField D).toField
  exact isCyclic_of_injective_ringHom Φ hΦ

theorem isCyclic_of_simple_commuting {K P : Type*} [Group K] [Finite K] [CommGroup P] [Finite P]
    [Nontrivial P] (τ : MulAut P)
    (hsimple : ∀ U : Subgroup P, (∀ v ∈ U, τ v ∈ U) → U = ⊥ ∨ U = ⊤)
    (ψ : K →* MulAut P) (hψ : Function.Injective ψ) (hcomm : ∀ a, ψ a * τ = τ * ψ a) :
    IsCyclic K := by
  let Θ : MulAut P →* AddMonoid.End (Additive P) :=
    { toFun := fun σ => MonoidHom.toAdditive σ.toMonoidHom
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hΘ : ∀ (σ : MulAut P) (v : P), Θ σ (Additive.ofMul v) = Additive.ofMul (σ v) :=
    fun _ _ => rfl
  have hΘinj : Function.Injective Θ := by
    intro σ σ' h
    ext v
    have := congrArg (fun f : AddMonoid.End (Additive P) => f (Additive.ofMul v)) h
    simpa [hΘ] using this
  let T : AddMonoid.End (Additive P) := Θ τ
  let D : Subring (AddMonoid.End (Additive P)) := Subring.centralizer {T}
  have hker : ∀ s : D, s ≠ 0 → ∀ x : Additive P, s.1 x = 0 → x = 0 := by
    intro s hs x hx
    let U : Subgroup P :=
      { carrier := {v | s.1 (Additive.ofMul v) = 0}
        one_mem' := map_zero s.1
        mul_mem' := fun {a b} ha hb => by
          show s.1 (Additive.ofMul a + Additive.ofMul b) = 0
          rw [map_add, show s.1 (Additive.ofMul a) = 0 from ha,
            show s.1 (Additive.ofMul b) = 0 from hb, add_zero]
        inv_mem' := fun {a} ha => by
          show s.1 (-Additive.ofMul a) = 0
          rw [map_neg, show s.1 (Additive.ofMul a) = 0 from ha, neg_zero] }
    have hsT := Subring.mem_centralizer_iff.mp s.2 T rfl
    have hUinv : ∀ v ∈ U, τ v ∈ U := by
      intro v hv
      have h1 : s.1 (T (Additive.ofMul v)) = T (s.1 (Additive.ofMul v)) := by
        have := congrArg (fun f : AddMonoid.End (Additive P) => f (Additive.ofMul v)) hsT
        exact this.symm
      show s.1 (Additive.ofMul (τ v)) = 0
      change s.1 (T (Additive.ofMul v)) = 0
      rw [h1, show s.1 (Additive.ofMul v) = 0 from hv, map_zero]
    rcases hsimple U hUinv with h | h
    · have hx' : Additive.toMul x ∈ U := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Additive.toMul.injective hx'
    · exfalso
      apply hs
      apply Subtype.ext
      ext y
      have hy' : Additive.toMul y ∈ U := h ▸ Subgroup.mem_top _
      exact hy'
  have : NoZeroDivisors D := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · refine Or.inr (Subtype.ext ?_)
      ext x
      have h1 : a.1 (b.1 x) = 0 := by
        have := congrArg (fun f : AddMonoid.End (Additive P) => f x) (congrArg Subtype.val hab)
        exact this
      exact hker a ha _ h1⟩
  obtain ⟨v₀, hv₀⟩ := exists_ne (1 : P)
  have : Nontrivial D := ⟨⟨1, 0, fun h => by
    have := congrArg (fun f : AddMonoid.End (Additive P) => f (Additive.ofMul v₀))
      (congrArg Subtype.val h)
    exact hv₀ this⟩⟩
  have : Finite D :=
    Finite.of_injective (fun s : D => (s.1 : Additive P → Additive P))
      (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  have hmem : ∀ a : K, (Θ.comp ψ) a ∈ D := by
    intro a
    refine Subring.mem_centralizer_iff.mpr fun g hg => ?_
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show Θ τ * Θ (ψ a) = Θ (ψ a) * Θ τ
    rw [← map_mul, ← map_mul, hcomm]
  let Φ : K →* D := (Θ.comp ψ).codRestrict D hmem
  have hΦ : Function.Injective Φ := by
    intro a b h
    exact hψ (hΘinj (congrArg Subtype.val h))
  exact isCyclic_of_injective_noZeroDivisors Φ hΦ

theorem isCyclic_centralizer_of_primitive
    {C P : Type} [Group C] [Finite C] [CommGroup P] [Finite P] {p ℓ N : ℕ}
    (hp : p.Prime) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hprim : ∀ k : ℕ, 0 < k → k < N → ¬ ℓ ∣ p ^ k - 1)
    (hPcard : Nat.card P = p ^ N) (hPexp : ∀ v : P, v ^ p = 1)
    (ρ : C →* MulAut P) (hρ : Function.Injective ρ)
    {y : C} (hy : orderOf y = ℓ) :
    IsCyclic ↥(Subgroup.centralizer ({y} : Set C)) := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact hℓ.one_lt.ne hy
  have hρy : ρ y ≠ 1 := fun h => hy1 (hρ (by rw [h, map_one]))
  obtain ⟨v₀, hv₀⟩ : ∃ v : P, ρ y v ≠ v := by
    by_contra h
    push Not at h
    exact hρy (MulEquiv.ext h)
  have : Nontrivial P := ⟨⟨ρ y v₀, v₀, hv₀⟩⟩
  refine isCyclic_of_simple_commuting (ρ y)
    (fun U hU => eq_bot_or_top_of_invariant_of_primitive hp hℓ hℓp hprim hPcard hPexp ρ hρ hy U hU)
    (ρ.comp (Subgroup.centralizer ({y} : Set C)).subtype) ?_ ?_
  · exact hρ.comp Subtype.val_injective
  · intro a
    have h : (a : C) * y = y * a := Subgroup.mem_centralizer_singleton_iff.mp a.2
    show ρ a * ρ y = ρ y * ρ a
    rw [← map_mul, ← map_mul, h]

end CFSG.GH74.GLS.Stage2.Bender.Thm2.T3
