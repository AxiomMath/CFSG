module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellBig

public section

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

section Arith

theorem prime_facts' {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr1 : r ∣ p ^ 2 + 1)
    (hr2 : ¬ r ∣ p ^ 2 - 1) : ¬ r ∣ p - 1 ∧ ¬ r ∣ p ^ 3 - 1 ∧ r ≠ p := by
  have hp1 := hp.one_lt
  have hrp : r ≠ p := by
    rintro rfl
    have h1 : r ∣ 1 := (Nat.dvd_add_right (dvd_pow_self r (by norm_num))).1 hr1
    exact hr.one_lt.ne' (Nat.dvd_one.1 h1)
  have hrp1 : ¬ r ∣ p - 1 := fun h => hr2 (h.trans (by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    refine ⟨m + 2, ?_⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega))
  refine ⟨hrp1, fun h => ?_, hrp⟩
  ·
    have hfac : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : (m + 1) ^ 3 = m * ((m + 1) ^ 2 + (m + 1) + 1) + 1 := by ring
      omega
    rw [hfac] at h
    rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
    · exact hrp1 h1
    · have h2 : r ∣ p := by
        have : p ^ 2 + p + 1 = (p ^ 2 + 1) + p := by ring
        rw [this] at h1
        exact (Nat.dvd_add_right hr1).1 h1
      exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h2)

end Arith

section Restrict

variable {G : Type*} [Group G]

@[expose] noncomputable def stabAut (N : Subgroup G) [Finite N] (α : MulAut G)
    (h : ∀ x ∈ N, α x ∈ N) : MulAut N :=
  have hmap : N.map (α : G →* G) = N := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    · rw [Subgroup.card_map_of_injective α.injective]
  (α.subgroupMap N).trans (MulEquiv.subgroupCongr hmap)

theorem stabAut_apply (N : Subgroup G) [Finite N] (α : MulAut G) (h : ∀ x ∈ N, α x ∈ N)
    (x : N) : ((stabAut N α h x : N) : G) = α x := rfl

theorem stabAut_pow_apply (N : Subgroup G) [Finite N] (α : MulAut G) (h : ∀ x ∈ N, α x ∈ N)
    (m : ℕ) (x : N) : (((stabAut N α h ^ m) x : N) : G) = (α ^ m) x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih, stabAut_apply]

theorem stabAut_pow_eq_one (N : Subgroup G) [Finite N] (α : MulAut G) (h : ∀ x ∈ N, α x ∈ N)
    {m : ℕ} (hα : α ^ m = 1) : stabAut N α h ^ m = 1 :=
  MulEquiv.ext fun x => Subtype.ext (by rw [stabAut_pow_apply, hα]; rfl)

end Restrict

section Counting

theorem eq_one_of_card_pow_le_three {Q : Type*} [Group Q] [Finite Q] {p r k a : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1)
    (hrne : r ≠ p) (hQ : Nat.card Q = p ^ a) (ha : a ≤ 3) (α : MulAut Q) (hα : α ^ r ^ k = 1) :
    α = 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let A : Subgroup (MulAut Q) := Subgroup.zpowers α
  have hAcard : Nat.card A = orderOf α := Nat.card_zpowers α
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 (hAcard ▸ orderOf_dvd_of_pow_eq_one hα)
  have hA : IsPGroup r A := IsPGroup.of_card hj
  have hmod := hA.card_modEq_card_fixedPoints Q
  let F : Subgroup Q := MonoidHom.eqLocus (α : Q →* Q) (MonoidHom.id Q)
  have hFmem : ∀ x, x ∈ F ↔ α x = x := fun x => Iff.rfl
  have hfixmem : ∀ x : Q, x ∈ MulAction.fixedPoints A Q ↔ α x = x := by
    intro x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨α, Subgroup.mem_zpowers α⟩
    · intro h a
      have hst : α ∈ MulAction.stabilizer (MulAut Q) x := h
      have := (Subgroup.zpowers_le (H := MulAction.stabilizer (MulAut Q) x)).2 hst a.2
      exact this
  have hfix : Nat.card (MulAction.fixedPoints A Q) = Nat.card F :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfixmem x).trans (hFmem x).symm)
  have : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Q := IsPGroup.of_card hQ
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card.1 (hQp.to_subgroup F))
  have hba : b ≤ a := by
    have h1 : Nat.card F ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card F
    rw [hb, hQ] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1
  rw [hfix, hb, hQ] at hmod
  have hbeq : b = a := by
    by_contra hne
    have hlt : b < a := lt_of_le_of_ne hba hne
    have h1 : r ∣ p ^ b * (p ^ (a - b) - 1) := by
      have : p ^ b * (p ^ (a - b) - 1) = p ^ a - p ^ b := by
        rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hba, mul_one]
      rw [this]
      exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hp.pos hba)).1 hmod.symm
    have hd : r ∣ p ^ (a - b) - 1 :=
      (Nat.Coprime.pow_right b ((Nat.coprime_primes hr hp).2 hrne)).dvd_of_dvd_mul_left h1
    have hd3 : a - b = 1 ∨ a - b = 2 ∨ a - b = 3 := by omega
    rcases hd3 with h | h | h
    · rw [h, pow_one] at hd; exact hrp hd
    · rw [h] at hd; exact hr2 hd
    · rw [h] at hd; exact hr3 hd
  have hFtop : F = ⊤ := by
    rw [← Subgroup.card_eq_iff_eq_top, hb, hQ, hbeq]
  refine MulEquiv.ext fun x => ?_
  have : x ∈ F := hFtop ▸ Subgroup.mem_top x
  exact this

end Counting

section G1

theorem gamma_stable_subgroup_trivial {G : Type*} [CommGroup G] [Finite G] {p r k : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p) (hGp : ∀ g : G, g ^ p = 1)
    (hcard : Nat.card G = p ^ 4) (γ : MulAut G) (hγ : γ ^ r ^ k = 1) (hnt : ∃ g, γ g ≠ g)
    (W : Subgroup G) (hW : ∀ w ∈ W, γ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  have : Fact p.Prime := ⟨hp⟩
  have hGP : IsPGroup p G := IsPGroup.of_card hcard
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (hGP.to_subgroup W)
  have hWcard : Nat.card W * Nat.card (G ⧸ W) = p ^ 4 := by
    rw [← hcard, mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup W).symm
  have hQdvd : Nat.card (G ⧸ W) ∣ p ^ 4 := ⟨Nat.card W, by rw [← hWcard, mul_comm]⟩
  obtain ⟨c, hc4, hc⟩ := (Nat.dvd_prime_pow hp).1 hQdvd
  have hac : a + c = 4 := by
    rw [ha, hc, ← pow_add] at hWcard
    exact Nat.pow_right_injective hp.two_le hWcard
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hW0
    rw [pow_zero] at ha
    exact Subgroup.card_eq_one.1 ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hW1
    rw [← Subgroup.card_eq_iff_eq_top, hcard]
    rw [pow_zero] at hc
    rw [hc, mul_one] at hWcard
    exact hWcard
  have hγW : ∀ w ∈ W, γ w = w := by
    have h1 := eq_one_of_card_pow_le_three (k := k) hp hr hrp hr2 hr3 hrne (a := a)
      (Q := W) ha (by omega) (stabAut W γ hW) (stabAut_pow_eq_one W γ hW hγ)
    intro w hw
    have := congrArg (fun e : MulAut W => ((e ⟨w, hw⟩ : W) : G)) h1
    exact this
  have hmapW : W.map (γ : G →* G) = W := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hW y hy
    · rw [Subgroup.card_map_of_injective γ.injective]
  let γbar : MulAut (G ⧸ W) := QuotientGroup.congr W W γ hmapW
  have hpowbar : ∀ (n : ℕ) (y : G), (γbar ^ n) (QuotientGroup.mk y) =
      QuotientGroup.mk ((γ ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply]
      have : γbar (QuotientGroup.mk y) = QuotientGroup.mk (γ y) := rfl
      rw [this, ih]
  have hbar1 : γbar ^ r ^ k = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y => rw [hpowbar, hγ]; rfl
  have hbar := eq_one_of_card_pow_le_three (k := k) hp hr hrp hr2 hr3 hrne (a := c)
    (Q := G ⧸ W) hc (by omega) γbar hbar1
  have hγmod : ∀ g : G, γ g * g⁻¹ ∈ W := by
    intro g
    have h3 : (QuotientGroup.mk (γ g) : G ⧸ W) = QuotientGroup.mk g := by
      have := congrArg (fun e : MulAut (G ⧸ W) => e (QuotientGroup.mk g)) hbar
      exact this
    have h4 := QuotientGroup.eq.1 h3
    have h5 := inv_mem h4
    simpa [mul_comm] using h5
  have hiter : ∀ (m : ℕ) (g : G), (γ ^ m) g = g * (γ g * g⁻¹) ^ m := by
    have hfixpow : ∀ (m : ℕ) (w : G), w ∈ W → (γ ^ m) w = w := by
      intro m
      induction m with
      | zero => intro w _; rfl
      | succ m ih =>
        intro w hw
        rw [pow_succ, MulAut.mul_apply, hγW w hw, ih w hw]
    intro m g
    induction m generalizing g with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, MulAut.mul_apply]
      have hg : γ g = g * (γ g * g⁻¹) := by rw [mul_comm (γ g) g⁻¹, mul_inv_cancel_left]
      conv_lhs => rw [hg]
      rw [map_mul, hfixpow m _ (hγmod g), ih g, pow_succ]
      group
  obtain ⟨g, hg⟩ := hnt
  apply hg
  set d := γ g * g⁻¹ with hd
  have hd1 : d ^ r ^ k = 1 := by
    have := hiter (r ^ k) g
    rw [hγ] at this
    have h2 : g * d ^ r ^ k = g * 1 := by rw [mul_one]; exact this.symm
    exact mul_left_cancel h2
  have hd2 : d ^ p = 1 := hGp d
  have hcop : Nat.Coprime (r ^ k) p :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hr hp).2 hrne)
  have := (pow_gcd_eq_one (a := d)).2 ⟨hd1, hd2⟩
  rw [hcop, pow_one] at this
  have h5 : γ g = d * g := by rw [hd, inv_mul_cancel_right]
  rw [h5, this, one_mul]

end G1

section Sub

open scoped IsMulCommutative

variable {S : Type*} [Group S]

theorem stable_subgroup_trivial_sub {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup S) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (γ : MulAut S) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    (W : Subgroup Ē) (hW : ∀ (x : S) (hx : x ∈ Ē), (⟨x, hx⟩ : Ē) ∈ W →
      (⟨γ x, hγE x hx⟩ : Ē) ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have : Finite Ē := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  refine gamma_stable_subgroup_trivial (k := k) hp hr hrp hr2 hr3 hrne
    (fun g => Subtype.ext (hEp g g.2)) hcard (stabAut Ē γ hγE) (stabAut_pow_eq_one Ē γ hγE hγ)
    ?_ W fun w hw => hW w w.2 hw
  obtain ⟨x, hx, hxγ⟩ := hnt
  exact ⟨⟨x, hx⟩, fun h => hxγ (congrArg Subtype.val h)⟩

theorem hom_trivial_of_ker_stable {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p)
    (Ē : Subgroup S) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (γ : MulAut S) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    {N : Type*} [Group N] (ψ : Ē →* N) (hrange : Nat.card ψ.range ≤ p)
    (hker : ∀ (x : S) (hx : x ∈ Ē), ψ ⟨x, hx⟩ = 1 → ψ ⟨γ x, hγE x hx⟩ = 1) : ψ = 1 := by
  have : Finite Ē := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  rcases stable_subgroup_trivial_sub (k := k) hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard γ hγ hγE hnt
    ψ.ker hker with h | h
  · exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 h
    have h1 : Nat.card ψ.range = Nat.card Ē :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h1, hcard] at hrange
    have : p ^ 4 > p := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  · exact MonoidHom.ext fun x => (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))

end Sub

section Step3

open scoped IsMulCommutative

theorem hom_trivial_of_ker_stable_cyclic {S : Type*} [Group S] {p r k : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1)
    (hrne : r ≠ p) (Ē : Subgroup S) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (γ : MulAut S) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    {N : Type*} [Group N] [Finite N] [IsCyclic N] (ψ : Ē →* N) (hψp : ∀ x, ψ x ^ p = 1)
    (hker : ∀ (x : S) (hx : x ∈ Ē), ψ ⟨x, hx⟩ = 1 → ψ ⟨γ x, hγE x hx⟩ = 1) : ψ = 1 := by
  classical
  refine hom_trivial_of_ker_stable (k := k) hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard γ hγ hγE hnt
    ψ ?_ hker
  have : Fintype N := Fintype.ofFinite N
  have hle : Nat.card ψ.range ≤ Nat.card {a : N // a ^ p = 1} := by
    refine Nat.card_le_card_of_injective
      (fun a : ψ.range => (⟨a.1, ?_⟩ : {a : N // a ^ p = 1})) ?_
    · obtain ⟨x, hx⟩ := a.2
      rw [← hx]
      exact hψp x
    · intro a b hab
      exact Subtype.ext (congrArg (Subtype.val : {a : N // a ^ p = 1} → N) hab)
  refine hle.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hp.pos

theorem exists_hom_factor {H S : Type*} [Group H] [Group S] (π : H →* S) (Ē : Subgroup S)
    (hπE : ∀ x ∈ Ē, ∃ e, π e = x) {N : Type*} [Group N] (ω : ↥(Ē.comap π) →* N)
    (hω : ∀ e : ↥(Ē.comap π), π e = 1 → ω e = 1) :
    ∃ ψ : Ē →* N, ∀ (e : H) (he : π e ∈ Ē), ψ ⟨π e, he⟩ = ω ⟨e, he⟩ := by
  have hsurj : Function.Surjective (π.subgroupComap Ē) := by
    rintro ⟨x, hx⟩
    obtain ⟨e, he⟩ := hπE x hx
    exact ⟨⟨e, by rw [Subgroup.mem_comap, he]; exact hx⟩, Subtype.ext he⟩
  refine ⟨(π.subgroupComap Ē).liftOfSurjective hsurj ⟨ω, fun e he => ?_⟩, fun e he => ?_⟩
  · rw [MonoidHom.mem_ker] at he ⊢
    exact hω e (congrArg Subtype.val he)
  · exact (π.subgroupComap Ē).liftOfRightInverse_comp_apply _ _ _ ⟨e, he⟩

theorem central_of_gamma_commutes {H S : Type*} [Group H] [Finite H] [Group S] {p r k : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (hr3 : ¬ r ∣ p ^ 3 - 1) (hrne : r ≠ p) (π : H →* S) (hker : π.ker ≤ Subgroup.center H)
    (hcyc : IsCyclic π.ker) (Ē : Subgroup S) (hEc : IsMulCommutative Ē)
    (hEp : ∀ x ∈ Ē, x ^ p = 1) (hcard : Nat.card Ē = p ^ 4) (hπE : ∀ x ∈ Ē, ∃ e, π e = x)
    (y : H) (hy : y ^ p ∈ Subgroup.center H) (hyE : ∀ e, π e ∈ Ē → π (y * e * y⁻¹) = π e)
    (γ : MulAut S) (γ' : MulAut H) (hγ' : ∀ e, π (γ' e) = γ (π e)) (hγ : γ ^ r ^ k = 1)
    (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    (hγy : γ' y * y⁻¹ ∈ Subgroup.center H) :
    ∀ e, π e ∈ Ē → y * e = e * y := by
  classical
  have hC : ∀ z, π z = 1 → z ∈ Subgroup.center H := fun z hz => hker (MonoidHom.mem_ker.2 hz)
  have hcomm : ∀ z, π z = 1 → ∀ g : H, g * z = z * g :=
    fun z hz g => Subgroup.mem_center_iff.1 (hC z hz) g
  have hmem : ∀ e : H, π e ∈ Ē → π (y * e * y⁻¹ * e⁻¹) = 1 := by
    intro e he
    rw [map_mul, map_inv, hyE e he, mul_inv_cancel]
  let ω : ↥(Ē.comap π) →* ↥π.ker :=
    { toFun := fun e => ⟨y * e * y⁻¹ * e⁻¹, MonoidHom.mem_ker.2 (hmem e e.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun e f => by
        apply Subtype.ext
        have hc := hcomm _ (hmem f f.2) (e : H)⁻¹
        change y * ((e : H) * f) * y⁻¹ * ((e : H) * f)⁻¹ =
          (y * e * y⁻¹ * (e : H)⁻¹) * (y * f * y⁻¹ * (f : H)⁻¹)
        have h1 : (y * e * y⁻¹ * (e : H)⁻¹) * (y * f * y⁻¹ * (f : H)⁻¹) =
            y * e * y⁻¹ * ((e : H)⁻¹ * (y * f * y⁻¹ * (f : H)⁻¹)) := by group
        rw [h1, hc]
        group }
  have hω : ∀ e : ↥(Ē.comap π), ((ω e : π.ker) : H) = y * e * y⁻¹ * (e : H)⁻¹ := fun e => rfl
  have hω1 : ∀ e : ↥(Ē.comap π), π e = 1 → ω e = 1 := by
    intro e he
    apply Subtype.ext
    rw [hω]
    have := hcomm e he y
    rw [this]
    simp
  obtain ⟨ψ, hψ⟩ := exists_hom_factor π Ē hπE ω hω1
  have hωp : ∀ e : ↥(Ē.comap π), ω e ^ p = 1 := by
    intro e
    apply Subtype.ext
    obtain ⟨c, hcdef⟩ : ∃ c : H, c = y * e * y⁻¹ * (e : H)⁻¹ := ⟨_, rfl⟩
    have hcc : c ∈ Subgroup.center H := by rw [hcdef]; exact hker (ω e).2
    rw [Subgroup.coe_pow, Subgroup.coe_one, hω, ← hcdef]
    have hcen : ∀ j : ℕ, ∀ g : H, g * c ^ j = c ^ j * g := fun j g =>
      Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ hcc j) g
    have hyc : y * (e : H) * y⁻¹ = c * e := by rw [hcdef]; group
    have hconj : ∀ j : ℕ, y ^ j * (e : H) * (y ^ j)⁻¹ = c ^ j * e := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 : y ^ (j + 1) * (e : H) * (y ^ (j + 1))⁻¹ =
            y * (y ^ j * (e : H) * (y ^ j)⁻¹) * y⁻¹ := by group
        rw [h1, ih]
        calc y * (c ^ j * (e : H)) * y⁻¹ = (y * c ^ j) * e * y⁻¹ := by group
          _ = (c ^ j * y) * e * y⁻¹ := by rw [hcen j y]
          _ = c ^ j * (y * e * y⁻¹) := by group
          _ = c ^ (j + 1) * e := by rw [hyc, pow_succ, mul_assoc]
    have h2 := hconj p
    have h3 : y ^ p * (e : H) * (y ^ p)⁻¹ = e := by
      rw [← Subgroup.mem_center_iff.1 hy e]
      group
    rw [h3] at h2
    have h4 : c ^ p * e = 1 * e := by rw [one_mul]; exact h2.symm
    exact (mul_right_cancel h4)
  have hcomm_iff : ∀ e : H, y * e * y⁻¹ * e⁻¹ = 1 ↔ y * e = e * y := fun e => by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hψ1 : ψ = 1 := by
    refine hom_trivial_of_ker_stable_cyclic (k := k) hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard γ hγ
      hγE hnt ψ ?_ ?_
    · rintro ⟨x, hx⟩
      obtain ⟨e, rfl⟩ := hπE x hx
      rw [hψ e hx]
      exact hωp ⟨e, hx⟩
    · intro x hx h1
      obtain ⟨e, rfl⟩ := hπE x hx
      have hγe : π (γ' e) ∈ Ē := by rw [hγ']; exact hγE _ hx
      have h2 : (⟨γ (π e), hγE _ hx⟩ : Ē) = ⟨π (γ' e), hγe⟩ := Subtype.ext (hγ' e).symm
      rw [h2, hψ (γ' e) hγe]
      rw [hψ e hx] at h1
      have h3 : y * e * y⁻¹ * (e : H)⁻¹ = 1 := congrArg Subtype.val h1
      have hye : y * e = e * y := (hcomm_iff e).1 h3
      have h4 : γ' y * γ' e = γ' e * γ' y := by rw [← map_mul, ← map_mul, hye]
      have hc := Subgroup.mem_center_iff.1 hγy (γ' e)
      have hcy : (γ' y * y⁻¹) * y = γ' y := inv_mul_cancel_right _ _
      have h5 : (γ' y * y⁻¹) * (y * γ' e) = (γ' y * y⁻¹) * (γ' e * y) := by
        calc (γ' y * y⁻¹) * (y * γ' e) = ((γ' y * y⁻¹) * y) * γ' e := (mul_assoc _ _ _).symm
          _ = γ' y * γ' e := by rw [hcy]
          _ = γ' e * γ' y := h4
          _ = γ' e * ((γ' y * y⁻¹) * y) := by rw [hcy]
          _ = (γ' e * (γ' y * y⁻¹)) * y := (mul_assoc _ _ _).symm
          _ = ((γ' y * y⁻¹) * γ' e) * y := by rw [hc]
          _ = (γ' y * y⁻¹) * (γ' e * y) := mul_assoc _ _ _
      have h6 := mul_left_cancel h5
      apply Subtype.ext
      change y * γ' e * y⁻¹ * (γ' e)⁻¹ = 1
      exact (hcomm_iff _).2 h6
  intro e he
  have h1 := DFunLike.congr_fun hψ1 ⟨π e, he⟩
  rw [hψ e he] at h1
  exact (hcomm_iff e).1 (congrArg Subtype.val h1)

end Step3

section Scalars

theorem fieldAut_apply_eq_of_pow_eq_one {K : Type*} [Field K] [Finite K] [CharP K 2]
    {p r k f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hrp : ¬ r ∣ p - 1)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) (hσ : σ ^ r ^ k = 1) {a : K} (ha : a ^ p = 1) :
    σ a = a := by
  obtain ⟨m, hm, hdiv⟩ := exists_frobenius_exponent σ hK hσ
  obtain ⟨j, hj⟩ := exists_pow_modEq hp hp2 hr hrp hdiv
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ∀ n : ℕ, a ^ ((2 ^ f) ^ n) = a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_mul, ih, ← hcardK, FiniteField.pow_card]
  rw [hm, pow_eq_pow_mod _ ha, show 2 ^ m % p = (2 ^ f) ^ j % p from hj, ← pow_eq_pow_mod _ ha,
    hpow]

theorem eq_one_of_gamma_smul {H : Type*} [Group H] {p r k : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrne : r ≠ p) (γ' : MulAut H) (hγ' : γ' ^ r ^ k = 1) (y c : H) (hy : y ^ p = 1)
    (hcy : c * y = y * c) (hc : γ' y = c * y) (hfix : c ^ p = 1 → γ' c = c) : c = 1 := by
  have hcp : c ^ p = 1 := by
    have h1 : (γ' y) ^ p = 1 := by rw [← map_pow, hy, map_one]
    rw [hc, (Commute.mul_pow (show Commute c y from hcy)), hy, mul_one] at h1
    exact h1
  have hfc := hfix hcp
  have hcfix : ∀ m : ℕ, (γ' ^ m) c = c := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfc, ih]
  have hiter : ∀ m : ℕ, (γ' ^ m) y = c ^ m * y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, MulAut.mul_apply, hc, map_mul, hcfix m, ih, pow_succ' c m, mul_assoc]
  have h1 := hiter (r ^ k)
  rw [hγ'] at h1
  have h2 : c ^ r ^ k * y = 1 * y := by rw [one_mul]; exact h1.symm
  have hck : c ^ r ^ k = 1 := mul_right_cancel h2
  have hcop : Nat.Coprime (r ^ k) p := Nat.Coprime.pow_left _ ((Nat.coprime_primes hr hp).2 hrne)
  have := (pow_gcd_eq_one (a := c)).2 ⟨hck, hcp⟩
  rwa [hcop, pow_one] at this

theorem exists_unitary_pth_root {K : Type*} [Field K] [Finite K] {q p : ℕ} (hq : Even q)
    (hp : 0 < p) (hcard : Nat.card K = q ^ 2) {l : K} (hln : l ^ (q + 1) = 1)
    (hlp : ∃ μ : K, μ ^ p = l) : ∃ ν : K, ν ^ p = l ∧ ν ^ (q + 1) = 1 := by
  obtain ⟨μ, hμ⟩ := hlp
  obtain ⟨h, hh⟩ := hq
  have : Fintype K := Fintype.ofFinite K
  have hcardF : Fintype.card K = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := Fintype.card_pos (α := K)
    rw [hcardF] at this
    omega
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  have hq2 : q = 2 * g + 2 := by omega
  subst hq2
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hln
    exact zero_ne_one hln
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hl0
    rw [← hμ, zero_pow hp.ne']
  have hμn : μ ^ ((2 * g + 1) * (2 * g + 3)) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one μ hμ0
    have h2 : Fintype.card K - 1 = (2 * g + 1) * (2 * g + 3) := by
      rw [hcardF]
      have : (2 * g + 2) ^ 2 = (2 * g + 1) * (2 * g + 3) + 1 := by ring
      omega
    rwa [h2] at h1
  refine ⟨μ ^ ((2 * g + 1) * (g + 1)), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hμ]
    have : (2 * g + 1) * (g + 1) = (2 * g + 2 + 1) * g + 1 := by ring
    rw [this, pow_succ, pow_mul, hln, one_pow, one_mul]
  · rw [← pow_mul]
    have : (2 * g + 1) * (g + 1) * (2 * g + 2 + 1) = (2 * g + 1) * (2 * g + 3) * (g + 1) := by ring
    rw [this, pow_mul, hμn, one_pow]

end Scalars

section Omega

open scoped IsMulCommutative

theorem exists_Omega_big_factor {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] {H S : Type} [Group H] [Finite H] [Group S]
    {f p r k : ℕ} (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrp : ¬ r ∣ p - 1) (hr2 : ¬ r ∣ p ^ 2 - 1) (hr3 : ¬ r ∣ p ^ 3 - 1)
    (hrne : r ≠ p) (π : H →* S) (hker : π.ker ≤ Subgroup.center H) (hcyc : IsCyclic π.ker)
    (Ē : Subgroup S) (hEc : IsMulCommutative Ē) (hEp : ∀ x ∈ Ē, x ^ p = 1)
    (hcard : Nat.card Ē = p ^ 4) (hπE : ∀ x ∈ Ē, ∃ e, π e = x)
    (hab : ∀ e e' : H, π e ∈ Ē → π e' ∈ Ē → e * e' = e' * e)
    (ρ : H →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) (z : Module.End K V) (hzp : z ^ p = 1)
    (hz : ∀ e, π e ∈ Ē → Commute z ((ρ e : V ≃ₗ[K] V) : Module.End K V))
    (γ : MulAut S) (γ' : MulAut H) (hγ' : ∀ e, π (γ' e) = γ (π e)) (hγ : γ ^ r ^ k = 1)
    (hγ'k : γ' ^ r ^ k = 1) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hnt : ∃ x ∈ Ē, γ x ≠ x)
    (σ : K ≃+* K) (hσ : σ ^ r ^ k = 1) (fM : V →ₛₗ[(σ : K →+* K)] V)
    (hfbij : Function.Bijective fM)
    (hfρ : ∀ (e : H) (v : V), fM (ρ e v) = ρ (γ' e) (fM v))
    (hfz : ∀ v, fM (z v) = z (fM v)) :
    ∃ h : K[X], h ∈ primaryFactors z ∧ Irreducible h ∧ 5 ≤ primaryMultiplicity z h := by
  classical
  let Ω : Subgroup H :=
    { carrier := {e | π e ∈ Ē ∧ e ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
        refine ⟨by rw [map_mul]; exact Ē.mul_mem ha hb, ?_⟩
        rw [(Commute.mul_pow (show Commute a b from hab a b ha hb)), ha1, hb1, one_mul]
      one_mem' := ⟨by rw [map_one]; exact Ē.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha1⟩
        exact ⟨by rw [map_inv]; exact Ē.inv_mem ha, by rw [inv_pow, ha1, inv_one]⟩ }
  have hΩ : ∀ e, e ∈ Ω ↔ π e ∈ Ē ∧ e ^ p = 1 := fun e => Iff.rfl
  have hlift : ∀ x ∈ Ē, ∃ e ∈ Ω, π e = x := by
    have := hcyc
    let : CommGroup ↥π.ker := IsCyclic.commGroup
    let P : Subgroup ↥π.ker := (powMonoidHom p : ↥π.ker →* ↥π.ker).range
    have : Finite (↥π.ker ⧸ P) := inferInstance
    have : IsCyclic (↥π.ker ⧸ P) :=
      isCyclic_of_surjective (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
    have hpm : ∀ e : H, π e ∈ Ē → e ^ p ∈ π.ker := fun e he => by
      rw [MonoidHom.mem_ker, map_pow]
      exact hEp _ he
    let ψ' : ↥(Ē.comap π) →* (↥π.ker ⧸ P) :=
      { toFun := fun e => QuotientGroup.mk ⟨(e : H) ^ p, hpm e e.2⟩
        map_one' := by
          rw [← QuotientGroup.mk_one]
          congr 1
          apply Subtype.ext
          simp
        map_mul' := fun e f => by
          rw [← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          change ((e : H) * f) ^ p = (e : H) ^ p * (f : H) ^ p
          exact Commute.mul_pow (hab e f e.2 f.2) p }
    have hψ'1 : ∀ e : ↥(Ē.comap π), π e = 1 → ψ' e = 1 := by
      intro e he
      change (QuotientGroup.mk ⟨(e : H) ^ p, hpm e e.2⟩ : ↥π.ker ⧸ P) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨⟨e, MonoidHom.mem_ker.2 he⟩, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_hom_factor π Ē hπE ψ' hψ'1
    have hψp : ∀ x : Ē, ψ x ^ p = 1 := by
      rintro ⟨x, hx⟩
      obtain ⟨e, rfl⟩ := hπE x hx
      rw [hψ e hx]
      change (QuotientGroup.mk ⟨(e : H) ^ p, hpm e hx⟩ : ↥π.ker ⧸ P) ^ p = 1
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨⟨(e : H) ^ p, hpm e hx⟩, rfl⟩
    have hψ1 : ψ = 1 := by
      refine hom_trivial_of_ker_stable_cyclic (k := k) hp hr hrp hr2 hr3 hrne Ē hEc hEp hcard γ hγ
        hγE hnt ψ hψp ?_
      intro x hx h1
      obtain ⟨e, rfl⟩ := hπE x hx
      have hγe : π (γ' e) ∈ Ē := by rw [hγ']; exact hγE _ hx
      have h2 : (⟨γ (π e), hγE _ hx⟩ : Ē) = ⟨π (γ' e), hγe⟩ := Subtype.ext (hγ' e).symm
      rw [h2, hψ (γ' e) hγe]
      rw [hψ e hx] at h1
      change (QuotientGroup.mk ⟨(e : H) ^ p, hpm e hx⟩ : ↥π.ker ⧸ P) = 1 at h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨w, hw⟩ := h1
      have hw' : (w : H) ^ p = e ^ p := congrArg Subtype.val hw
      have hγw : π (γ' (w : H)) = 1 := by
        rw [hγ', MonoidHom.mem_ker.1 w.2, map_one]
      change (QuotientGroup.mk ⟨(γ' e) ^ p, hpm (γ' e) hγe⟩ : ↥π.ker ⧸ P) = 1
      rw [QuotientGroup.eq_one_iff]
      refine ⟨⟨γ' (w : H), MonoidHom.mem_ker.2 hγw⟩, ?_⟩
      apply Subtype.ext
      change (γ' (w : H)) ^ p = (γ' e) ^ p
      rw [← map_pow, ← map_pow, hw']
    intro x hx
    obtain ⟨e, rfl⟩ := hπE x hx
    have h1 := DFunLike.congr_fun hψ1 ⟨π e, hx⟩
    rw [hψ e hx] at h1
    change (QuotientGroup.mk ⟨(e : H) ^ p, hpm e hx⟩ : ↥π.ker ⧸ P) = 1 at h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨w, hw⟩ := h1
    have hw' : (w : H) ^ p = e ^ p := congrArg Subtype.val hw
    have hwc : Commute e (w : H)⁻¹ :=
      (Commute.inv_right (Subgroup.mem_center_iff.1 (hker w.2) e))
    refine ⟨e * (w : H)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [map_mul, map_inv, MonoidHom.mem_ker.1 w.2, inv_one, mul_one]
      exact hx
    · rw [Commute.mul_pow hwc, inv_pow, hw', mul_inv_cancel]
    · rw [map_mul, map_inv, MonoidHom.mem_ker.1 w.2, inv_one, mul_one]
  have hΩstab : ∀ e ∈ Ω, γ' e ∈ Ω := by
    intro e he
    obtain ⟨he1, he2⟩ := he
    exact ⟨by rw [hγ']; exact hγE _ he1, by rw [← map_pow, he2, map_one]⟩
  have : Finite Ω := inferInstance
  have : Fintype Ω := Fintype.ofFinite Ω
  obtain ⟨x, hxE, hxγ⟩ := hnt
  obtain ⟨e₀, he₀, hπe₀⟩ := hlift x hxE
  have hg₀ : γ' e₀ ≠ e₀ := fun h => hxγ (by rw [← hπe₀, ← hγ', h])
  have hGp : ∀ g : Ω, g ^ p = 1 := fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, g.2.2, Subgroup.coe_one])
  have hGK : ((Fintype.card Ω : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h0
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hGp g)
    rw [hg] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h1).symm
  let : CommGroup Ω :=
    { (inferInstance : Group Ω) with
      mul_comm := fun a b => Subtype.ext (hab a b a.2.1 b.2.1) }
  let ρΩ : Ω →* (V ≃ₗ[K] V) := ρ.comp Ω.subtype
  have hρΩ : Function.Injective ρΩ := hρ.comp Subtype.val_injective
  let γΩ : MulAut Ω := stabAut Ω γ' hΩstab
  have hγΩ : γΩ ^ r ^ k = 1 := stabAut_pow_eq_one Ω γ' hΩstab hγ'k
  refine exists_big_primary_factor (G := Ω) hK hp hp2 hr hr5 hrp hGp hGK ρΩ hρΩ z
    (fun g => hz g g.2.1) hzp γΩ hγΩ ⟨e₀, he₀⟩ (fun h => hg₀ (congrArg Subtype.val h)) σ hσ fM
    hfbij (fun e v => hfρ e v) hfz

end Omega

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
