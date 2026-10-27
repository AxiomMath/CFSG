module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP

theorem twoPart_fixNum_quotient {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z)) (ρ : MulAut H) (f : MulAut (H ⧸ Z))
    (hmk : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ x)) :
    twoPart (fixNum f) = twoPart (fixNum ρ) := by
  set C : Subgroup H := fixSub ρ with hC
  set C' : Subgroup (H ⧸ Z) := fixSub f with hC'
  rw [fixNum_eq_card_fixSub, fixNum_eq_card_fixSub]
  set g : C →* H ⧸ Z := (QuotientGroup.mk' Z).comp C.subtype with hg
  set D : Subgroup (H ⧸ Z) := g.range with hD
  have hDC' : D ≤ C' := by
    rintro _ ⟨x, rfl⟩
    have hx : ρ x.1 = x.1 := x.2
    show f (QuotientGroup.mk x.1) = QuotientGroup.mk x.1
    rw [hmk, hx]
  have hker : Odd (Nat.card g.ker) := by
    have h1 : (g.ker.map C.subtype) ≤ Z := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hx
    have h2 : Nat.card g.ker ∣ Nat.card Z := by
      calc Nat.card g.ker = Nat.card (g.ker.map C.subtype) :=
            (Subgroup.card_map_of_injective C.subtype_injective).symm
        _ ∣ Nat.card Z := Subgroup.card_dvd_of_le h1
    exact Odd.of_dvd_nat hZ h2
  have hCD : Nat.card C = Nat.card g.ker * Nat.card D := (Subgroup.card_ker_mul_card_range g).symm
  have h2 : twoPart (Nat.card C) = twoPart (Nat.card D) := by
    rw [hCD]
    unfold twoPart
    rw [Nat.factorization_mul (Nat.card_pos (α := g.ker)).ne' (Nat.card_pos (α := D)).ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by
        rintro ⟨c, hc⟩
        exact (Nat.not_even_iff_odd.2 hker) ⟨c, by omega⟩), zero_add]
  have h3 : twoPart (Nat.card C') = twoPart (Nat.card D) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P⟩ : Nonempty (Sylow 2 C') := inferInstance
    have hPD : (P : Subgroup C') ≤ D.subgroupOf C' := by
      intro y hy
      obtain ⟨k, hk⟩ := P.isPGroup' (⟨y, hy⟩ : P)
      have hk' : (y : H ⧸ Z) ^ (2 ^ k) = 1 := by
        have := congrArg (fun t : P => ((t : C') : H ⧸ Z)) hk
        simpa using this
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (y : H ⧸ Z)
      have hfix : (QuotientGroup.mk (ρ x) : H ⧸ Z) = QuotientGroup.mk x := by
        have := mem_fixSub.1 y.2
        rw [← hmk, hx]
        exact this
      obtain ⟨x', hx', hxx'⟩ := exists_fixed_lift (Z := Z) hZc hZ ρ x (k := k)
        (by rw [hx]; exact hk') hfix
      rw [Subgroup.mem_subgroupOf]
      exact ⟨⟨x', mem_fixSub.2 hx'⟩, by rw [← hx, ← hxx']; rfl⟩
    have h4 : Nat.card P ∣ Nat.card D := by
      have := Subgroup.card_dvd_of_le hPD
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC').toEquiv] at this
    have h5 : Nat.factorization (Nat.card C') 2 ≤ Nat.factorization (Nat.card D) 2 := by
      have hpow : 2 ^ Nat.factorization (Nat.card C') 2 ∣ Nat.card D := by
        rw [← Sylow.card_eq_multiplicity P]; exact h4
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.card_pos (α := D)).ne').1 hpow
    have h6 : Nat.factorization (Nat.card D) 2 ≤ Nat.factorization (Nat.card C') 2 :=
      (Nat.factorization_le_iff_dvd (Nat.card_pos (α := D)).ne' (Nat.card_pos (α := C')).ne').2
        (Subgroup.card_dvd_of_le hDC') 2
    unfold twoPart
    rw [le_antisymm h5 h6]
  exact h3.trans h2.symm

theorem fixNum_one {R : Type*} [Group R] : fixNum (1 : MulAut R) = Nat.card R :=
  Nat.card_congr (Equiv.subtypeUnivEquiv fun x => rfl)

theorem twoPart_card_quotient {H : Type*} [Group H] [Finite H] (Z : Subgroup H) [Z.Normal]
    (hZ : Odd (Nat.card Z)) : twoPart (Nat.card (H ⧸ Z)) = twoPart (Nat.card H) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, mul_comm, twoPart_mul_odd hZ
    Nat.card_pos.ne']

theorem card_fixedPoints_field {K : Type} [Field K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) (σ : K ≃+* K) :
    orderOf σ ∣ m ∧ Nat.card {x : K // σ x = x} = 2 ^ (m / orderOf σ) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  rw [← hcard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  have h1 : a ∈ S ↔ ∀ τ ∈ Subgroup.zpowers σ, τ a = a := by
    have := congrArg (a ∈ ·) hS
    simpa using this
  rw [h1]
  constructor
  · intro h τ hτ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
    have : ∀ k : ℤ, (σ ^ k) a = a := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ i ih =>
        rw [zpow_add_one, RingAut.mul_apply, h, ih]
      | pred i ih =>
        have h2 : σ⁻¹ a = a := by
          conv_lhs => rw [← h]
          simp
        rw [zpow_sub_one, RingAut.mul_apply, h2, ih]
    exact this k
  · intro h
    exact h σ (Subgroup.mem_zpowers σ)

section Core

variable {K : Type} [Field K] {H : Type} [Group H] [Finite H]

theorem stOrder_core {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z))
    (ρ : (K ≃+* K) →* MulAut H) (good : (K ≃+* K) → Prop)
    (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n)) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hC : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (fixNum (ρ σ)) ^ v = 2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (f : MulAut (H ⧸ Z)) (σ : K ≃+* K) (hσ : good σ)
    (hσf : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ σ x)) (hord : orderOf f = p) :
    twoPart (fixNum f) ^ p = twoPart (Nat.card (H ⧸ Z)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ n : ℕ, ∀ x : H, (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((ρ (σ ^ n)) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hσf, ih, pow_succ, map_mul, MulAut.mul_apply]
  have hHZ : (twoPart (Nat.card (H ⧸ Z))) ^ v = 2 ^ (m * u) := by
    rw [twoPart_card_quotient Z hZ]; exact hH
  have hfp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  have hσp : σ ^ p = 1 := by
    have h1 := twoPart_fixNum_quotient Z hZc hZ (ρ (σ ^ p)) (f ^ p) (hpow p)
    rw [hfp, fixNum_one] at h1
    obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK (σ ^ p)
    have h2 := hC (σ ^ p) (hgood σ hσ p) _ hcard
    rw [← h1, hHZ] at h2
    have h3 : m * u = (m / orderOf (σ ^ p)) * u := by
      have := Nat.pow_right_injective (le_refl 2) h2
      exact this
    have h4 : m = m / orderOf (σ ^ p) := Nat.eq_of_mul_eq_mul_right hu h3
    have hpos : 0 < orderOf (σ ^ p) := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have h5 : orderOf (σ ^ p) = 1 := by
      by_contra hne
      have h6 : 2 ≤ orderOf (σ ^ p) := by omega
      have h7 : m / orderOf (σ ^ p) < m := Nat.div_lt_self (by omega) h6
      omega
    exact orderOf_eq_one_iff.1 h5
  have hσ1 : σ ≠ 1 := by
    intro h
    subst h
    have : f = 1 := by
      ext y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hσf]
      simp
    rw [this, orderOf_one] at hord
    exact hp.one_lt.ne hord
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hdvd, hcard⟩ := card_fixedPoints_field hm hK σ
  rw [hσo] at hdvd hcard
  have h1 := twoPart_fixNum_quotient Z hZc hZ (ρ σ) f hσf
  have h2 := hC σ hσ _ hcard
  have h3 : (twoPart (fixNum f) ^ p) ^ v = (twoPart (Nat.card (H ⧸ Z))) ^ v := by
    rw [hHZ, ← pow_mul, mul_comm p v, pow_mul, h1, h2, ← pow_mul]
    congr 1
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.mul_div_cancel_left _ hp.pos]
    ring
  exact Nat.pow_left_injective hv.ne' h3

theorem stOrder_core_red {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    (Z : Subgroup H) [Z.Normal] (hZc : Z ≤ Subgroup.center H) (hZ : Odd (Nat.card Z))
    (ρ : (K ≃+* K) →* MulAut H) (good : (K ≃+* K) → Prop)
    (hgood : ∀ σ, good σ → ∀ n : ℕ, good (σ ^ n)) {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hH : twoPart (Nat.card H) ^ v = 2 ^ (m * u))
    (hC : ∀ σ, good σ → ∀ e : ℕ, Nat.card {x : K // σ x = x} = 2 ^ e →
      twoPart (fixNum (ρ σ)) ^ v = 2 ^ (e * u))
    {p : ℕ} (hp : p.Prime) (hred : ∀ σ : K ≃+* K, ∃ n : ℕ, ¬ p ∣ n ∧ good (σ ^ n))
    (f : MulAut (H ⧸ Z)) (σ : K ≃+* K)
    (hσf : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ σ x)) (hord : orderOf f = p) :
    twoPart (fixNum f) ^ p = twoPart (Nat.card (H ⧸ Z)) := by
  obtain ⟨n, hn, hgn⟩ := hred σ
  have hpow : ∀ n : ℕ, ∀ x : H, (f ^ n) (QuotientGroup.mk x) = QuotientGroup.mk ((ρ (σ ^ n)) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, hσf, ih, pow_succ, map_mul, MulAut.mul_apply]
  have hcop : (orderOf f).Coprime n := by
    rw [hord]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn
  have hord' : orderOf (f ^ n) = p := by rw [Nat.Coprime.orderOf_pow hcop, hord]
  have hfix : fixNum (f ^ n) = fixNum f :=
    FP.fixNum_eq_of_orderOf_eq hp.pos (f₀ := f) (Subgroup.mem_zpowers f)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers f) n) hord hord'
  rw [← hfix]
  exact stOrder_core hm hK Z hZc hZ ρ good hgood hu hv hH hC hp (f ^ n) (σ ^ n) hgn (hpow n) hord'

end Core

section Action

@[expose] def stableAct {K M : Type*} [Field K] [Group M] (a : (K ≃+* K) → M →* M)
    (h1 : ∀ g, a 1 g = g) (hmul : ∀ σ τ g, a (σ * τ) g = a σ (a τ g)) (H : Subgroup M)
    (hH : ∀ σ, ∀ h ∈ H, a σ h ∈ H) : (K ≃+* K) →* MulAut H where
  toFun σ :=
    { toFun := fun h => ⟨a σ h, hH σ h h.2⟩
      invFun := fun h => ⟨a σ⁻¹ h, hH σ⁻¹ h h.2⟩
      left_inv := fun h => Subtype.ext (by
        change a σ⁻¹ (a σ (h : M)) = h
        rw [← hmul, inv_mul_cancel, h1])
      right_inv := fun h => Subtype.ext (by
        change a σ (a σ⁻¹ (h : M)) = h
        rw [← hmul, mul_inv_cancel, h1])
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  map_one' := MulEquiv.ext fun h => Subtype.ext (h1 (h : M))
  map_mul' := fun x y => MulEquiv.ext fun h => Subtype.ext (hmul x y (h : M))

theorem fixNum_stableAct {K M : Type*} [Field K] [Group M] (a : (K ≃+* K) → M →* M)
    (h1 : ∀ g, a 1 g = g) (hmul : ∀ σ τ g, a (σ * τ) g = a σ (a τ g)) (H : Subgroup M)
    (hH : ∀ σ, ∀ h ∈ H, a σ h ∈ H) (σ : K ≃+* K) :
    fixNum (stableAct a h1 hmul H hH σ) = Nat.card {g : M // g ∈ H ∧ a σ g = g} :=
  (Nat.card_congr (Equiv.subtypeEquivRight fun h => by
    rw [← Subtype.coe_inj]; rfl)).trans
    (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun g : M => g ∈ H)
      (fun g : M => a σ g = g)))

end Action

section Inner

@[expose] def InnFree (p : ℕ) {R : Type*} [Group R] (F : Set (MulAut R)) : Prop :=
  ∀ f ∈ F, orderOf f = p → f ∉ (MulAut.conj : R →* MulAut R).range

theorem congr_mem_range_conj {R S : Type*} [Group R] [Group S] (e : R ≃* S) (f : MulAut R) :
    MulAut.congr e f ∈ (MulAut.conj : S →* MulAut S).range ↔
      f ∈ (MulAut.conj : R →* MulAut R).range := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.symm q, MulEquiv.ext fun g => e.injective ?_⟩
    have h := congrArg (fun β : MulAut S => β (e g)) hq
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h ⊢
    exact h
  · rintro ⟨r, hr⟩
    refine ⟨e r, MulEquiv.ext fun s => ?_⟩
    have h := congrArg (fun β : MulAut R => β (e.symm s)) hr
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h ⊢
    rw [← h]
    simp

end Inner

end FQ

end CFSG.LocalAnalysis.GLTheoremA
