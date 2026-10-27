module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8CaseII

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Arith

theorem r1_sep {ι κ : Type*} {r : ℕ} (m a b : ℕ) (hm : Odd m) (hh : 3 ≤ Nat.gcd a m)
    (hnd : ¬ m ∣ a) (β : ι → Fin r → ℤ) (X : ι → κ → Fin r → ℤ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (β i - β i') c)
    (hX : ∀ i j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (X i j - X i j') c)
    (i i' : ι) (j j' : κ)
    (h : ∀ c, (m : ℤ) ∣ ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c) : i = i' ∧ j = j' := by
  set g := Nat.gcd a m with hgdef
  have hgpos : 0 < g := by omega
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a m
  obtain ⟨d, hd⟩ := Nat.gcd_dvd_right a m
  have hgm : g ∣ m := Nat.gcd_dvd_right a m
  have hgodd : Odd g := Odd.of_dvd_nat hm hgm
  have hii : i = i' := by
    by_contra hne
    apply hβ i i' hne g hh
    intro c
    have h1 : (g : ℤ) ∣ (2 : ℤ) ^ b * (β i - β i') c := by
      have h2 : (g : ℤ) ∣ (a : ℤ) * (X i j - X i' j') c :=
        dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left a m)) _
      have h3 := dvd_trans (Int.natCast_dvd_natCast.2 hgm) (h c)
      have h4 : ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
          ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c =
          (a : ℤ) * (X i j - X i' j') c - (2 : ℤ) ^ b * (β i - β i') c := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [h4] at h3
      have := dvd_sub h2 h3
      rwa [sub_sub_cancel] at this
    exact (odd_coprime_two_pow hgodd b).dvd_of_dvd_mul_left h1
  subst hii
  refine ⟨rfl, ?_⟩
  by_contra hjj
  have hdodd : Odd d := Odd.of_dvd_nat hm ⟨g, by rw [hd]; ring⟩
  have hd3 : 3 ≤ d := by
    rcases hdodd with ⟨k, hk⟩
    by_contra hlt
    have : d = 1 := by omega
    apply hnd
    rw [this, mul_one] at hd
    rw [hd]
    exact Nat.gcd_dvd_left a m
  apply hX i j j' hjj d hd3
  intro c
  have h1 := h c
  have h4 : ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i j' - ((2 : ℤ) ^ b) • β i)) c = (a : ℤ) * (X i j - X i j') c := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h4] at h1
  have hcop : IsCoprime (a' : ℤ) (d : ℤ) := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := m) hgpos
    rw [show a / Nat.gcd a m = a' by rw [← hgdef, ha']; exact Nat.mul_div_cancel_left a' hgpos,
      show m / Nat.gcd a m = d by rw [← hgdef, hd]; exact Nat.mul_div_cancel_left d hgpos] at this
    exact Nat.isCoprime_iff_coprime.2 this
  have h5 : (g : ℤ) * d ∣ g * a' * (X i j - X i j') c := by
    have e1 : (m : ℤ) = g * d := by rw [hd]; push_cast; ring
    have e2 : (a : ℤ) = g * a' := by rw [ha']; push_cast; ring
    rwa [e1, e2] at h1
  have h6 : (d : ℤ) ∣ a' * (X i j - X i j') c := by
    rw [mul_assoc] at h5
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hgpos.ne')).1 h5
  exact hcop.symm.dvd_of_dvd_mul_left h6

theorem r2_sep {ι κ : Type*} {r : ℕ} (m a b : ℕ) (hm : Odd m) (h3 : 3 ≤ m) (hma : m ∣ a)
    (β : ι → Fin r → ℤ) (X : ι → κ → Fin r → ℤ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (β i - β i') c)
    (i i' : ι) (j j' : κ)
    (h : ∀ c, (m : ℤ) ∣ ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c) : i = i' := by
  by_contra hne
  apply hβ i i' hne m h3
  intro c
  have h1 := h c
  have h4 : ((a : ℤ) • X i j - ((2 : ℤ) ^ b) • β i -
      ((a : ℤ) • X i' j' - ((2 : ℤ) ^ b) • β i')) c =
      (a : ℤ) * (X i j - X i' j') c - (2 : ℤ) ^ b * (β i - β i') c := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h4] at h1
  have h2 : (m : ℤ) ∣ (2 : ℤ) ^ b * (β i - β i') c := by
    have := dvd_sub (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 hma)
      ((X i j - X i' j') c)) h1
    rwa [sub_sub_cancel] at this
  exact (odd_coprime_two_pow hm b).dvd_of_dvd_mul_left h2

theorem kpow_congr {K : Type} [Field K] {k : Type} [Field k] [Algebra K k] (t : Kˣ) {e f : ℤ}
    (h : ((Nat.card Kˣ : ℕ) : ℤ) ∣ e - f) : kpow (k := k) K t e = kpow (k := k) K t f := by
  obtain ⟨q, hq⟩ := h
  have hne : (algebraMap K k (t : K)) ≠ 0 := by simp
  have h2 : (algebraMap K k (t : K)) ^ (Nat.card Kˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  have he : e = f + (Nat.card Kˣ : ℤ) * q := by linarith
  unfold kpow
  rw [he, zpow_add₀ hne, zpow_mul, zpow_natCast, h2, one_zpow, mul_one]

end Arith

section Tensor


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem mExp_single_one (i s : Fin τ.rank) : mExp τ i (Pi.single s (1 : ℤ)) = τ.cartan i s := by
  unfold mExp
  simp [Pi.single_apply]

theorem reflect_eq_self_of_mExp {θ : Fin τ.rank → ℤ} {j : Fin τ.rank} (h : mExp τ j θ = 0) :
    reflect τ j θ = θ := by
  unfold reflect
  have h' : ∑ l, τ.cartan j l * θ l = 0 := h
  rw [h', zero_smul, sub_zero]

theorem tensor_vec {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hJ : ∀ j, j ≠ s → j ∈ J)
    {θ : Fin τ.rank → ℤ} {c c' : ℕ} (hθ : ∀ i, mExp τ i θ = if i = s then (c : ℤ) else 0)
    (hcc : ((2 ^ n - 1 : ℕ) : ℤ) ∣ (c : ℤ) * c' - 1) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      (J' = ∅ → ∀ g, ρ (rankOne τ K s g) y = y) ∧
      ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y, e ≠ 0 ∧
        e ∈ wtSpace ρ ((((∑ i ∈ J', 2 ^ i) * c' : ℕ) : ℤ) • θ -
          (2 : ℤ) ^ b • Pi.single s (1 : ℤ)) := by
  obtain ⟨J', hJ', hε, -, hJ0, hwt⟩ := string_of_highest (hw := hw) hK hρ ht s
  refine ⟨J', hJ', hε, hJ0, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  refine ⟨e, he, he0, ?_⟩
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hcard : ((Nat.card Kˣ : ℕ) : ℤ) = ((2 ^ n - 1 : ℕ) : ℤ) := by rw [Nat.card_units, hK]
  have hcong : ((Nat.card Kˣ : ℕ) : ℤ) ∣ ((a * c' : ℕ) : ℤ) * c - a := by
    rw [hcard]
    have : ((a * c' : ℕ) : ℤ) * c - a = a * ((c : ℤ) * c' - 1) := by push_cast; ring
    rw [this]
    exact dvd_mul_of_dvd_right hcc _
  set E : Fin τ.rank → ℤ := fun i => mExp τ i ((((a * c' : ℕ) : ℤ)) • θ) with hE
  have hEi : ∀ i, E i = ((a * c' : ℕ) : ℤ) * (if i = s then (c : ℤ) else 0) := by
    intro i
    simp only [hE]
    rw [mExp_smul, hθ]
  have hy : ∀ i t, ρ (dC τ K i t) y = kpow (k := k) K t (E i) • y := by
    intro i t
    rw [ht.2.2.1 _ (dC_mem_H i t)]
    congr 1
    rw [hEi]
    by_cases hi : i = s
    · subst hi
      simp only [↓reduceIte]
      rw [hε t, kpow_congr t hcong]
      unfold kpow
      rw [zpow_natCast]
    · simp only [hi, ↓reduceIte, mul_zero]
      rw [((ht.2.2.2 i).1 (hJ i hi)).1 t]
      simp [kpow]
  have hes : ∀ z : Kˣ, ρ (dC τ K s z) e = kpow (k := k) K z (E s - 2 * (2 : ℤ) ^ b) • e := by
    intro z
    rw [hed z]
    congr 1
    show kpow (k := k) K z ((a : ℤ) - 2 ^ (b + 1)) = _
    refine kpow_congr z ?_
    rw [hEi]
    simp only [↓reduceIte]
    have : (a : ℤ) - 2 ^ (b + 1) - (((a * c' : ℕ) : ℤ) * c - 2 * 2 ^ b) =
        -(((a * c' : ℕ) : ℤ) * c - a) := by ring
    rw [this]
    exact dvd_neg.2 hcong
  intro i t
  rw [weight_shift ρ s E hy ((2 : ℤ) ^ b) he hes i t, mExp_comb, mExp_single_one]
  simp only [hE]
  rw [mExp_smul]
  congr 2
  ring

theorem tensor_bound_of_vec [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hs : s ∉ J)
    {θ : Fin τ.rank → ℤ} (hθ : ∀ j, j ≠ s → mExp τ j θ = 0) {a b : ℕ} {e : V}
    (he : e ∈ orbitSpan (ρ.comp (rankOne τ K s)) y) (he0 : e ≠ 0)
    (hew : e ∈ wtSpace ρ ((a : ℤ) • θ - (2 : ℤ) ^ b • Pi.single s (1 : ℤ)))
    (h3M : 3 ≤ 2 ^ n - 1) (ha : (2 ^ n - 1) ∣ a ∨ 3 ≤ Nat.gcd a (2 ^ n - 1))
    (hU : ∀ δ : Fin τ.rank → ℤ, (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣ mExp τ i δ) →
      ∀ l, ((2 ^ n - 1 : ℕ) : ℤ) ∣ δ l)
    {N P : ℕ} (w : Fin N → WeylGroup τ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣
      (w i • (Pi.single s 1 : Fin τ.rank → ℤ) - w i' • (Pi.single s 1 : Fin τ.rank → ℤ)) l)
    (u : Fin P → WeylGroup τ) (hu : ∀ j, u j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hXu : ∀ j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣ (u j • θ - u j' • θ) l) :
    N * P ≤ Module.finrank k V := by
  classical
  set M := 2 ^ n - 1 with hM
  have hModd : Odd M := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by rw [hM, pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
  have hMcard : Nat.card Kˣ = M := by rw [Nat.card_units, hK]
  let X : Fin N → Fin P → Fin τ.rank → ℤ := fun i j => w i • (u j • θ)
  let β : Fin N → Fin τ.rank → ℤ := fun i => w i • (Pi.single s (1 : ℤ))
  let ν : Fin N × Fin P → Fin τ.rank → ℤ := fun p =>
    (a : ℤ) • X p.1 p.2 - (2 : ℤ) ^ b • β p.1
  let v : Fin N × Fin P → V := fun p =>
    ρ (nWC τ K (w p.1)) (ρ (nWC τ K (u p.2)) e)
  have hinj : ∀ g' : adjointGroup τ K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hv : ∀ p, v p ∈ wtSpace ρ (ν p) := by
    intro p
    have h1 := wt_nWC hw ρ (u p.2) hew
    have h2 := wt_nWC hw ρ (w p.1) h1
    have hνeq : w p.1 • (u p.2 • (((a : ℤ)) • θ - (2 : ℤ) ^ b • Pi.single s (1 : ℤ))) = ν p := by
      rw [weyl_smul_comb, hu, weyl_smul_comb]
    rw [← hνeq]
    exact h2
  have hv0 : ∀ p, v p ≠ 0 := by
    intro p h0
    apply he0
    apply hinj (nWC τ K (u p.2))
    apply hinj (nWC τ K (w p.1))
    rw [map_zero, map_zero]
    exact h0
  have hsepdvd : ∀ p q, wcls τ K k (ν p) = wcls τ K k (ν q) →
      ∀ l, (M : ℤ) ∣ (ν p - ν q) l := by
    intro p q h
    have h1 := dvd_of_wcls_eq h
    rw [hMcard] at h1
    refine hU (ν p - ν q) (fun i => ?_)
    rw [mExp_sub]
    exact h1 i
  have hX' : ∀ i j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣ (X i j - X i j') l := by
    intro i j j' hjj d hd hc
    apply hXu j j' hjj d hd
    have h1 : X i j - X i j' = w i • ((1 : ℤ) • (u j • θ) - (1 : ℤ) • (u j' • θ)) := by
      rw [weyl_smul_comb]; simp [X]
    rw [h1] at hc
    have := (weyl_dvd_iff (w i) d _).1 hc
    simpa using this
  have hfin : Fintype.card (Fin N × Fin P) ≤ Module.finrank k V := by
    by_cases hMa : M ∣ a
    · have hsep2 : ∀ p q, wcls τ K k (ν p) = wcls τ K k (ν q) → p.1 = q.1 := fun p q h =>
        r2_sep M a b hModd h3M hMa β X hβ p.1 q.1 p.2 q.2 (hsepdvd p q h)
      have hli : LinearIndependent k (fun j => ρ (nWC τ K (u j)) y) := by
        refine linearIndependent_translates_of_isChevType hρ ht hs (v₀ := θ)
          (fun j hj => reflect_eq_self_of_mExp (hθ j hj)) u ?_
        intro j j' hjj h
        apply hXu j j' hjj 3 le_rfl
        intro l
        simp [h]
      have hcop := copies_linearIndependent hρ ht (s := s) u hu hli he he0
      have hcop' : ∀ i : Fin N, LinearIndependent k (fun j : Fin P => v (i, j)) := fun i =>
        hcop.map' (ρ (nWC τ K (w i))) (LinearMap.ker_eq_bot.2 (hinj _))
      have hli2 : LinearIndependent k v := by
        refine linearIndependent_of_wcls hw ρ v ν hv (fun c => ?_)
        rcases isEmpty_or_nonempty {p : Fin N × Fin P // wcls τ K k (ν p) = c} with hE | ⟨⟨p0, hp0⟩⟩
        · exact linearIndependent_empty_type
        · have hf : Function.Injective
              (fun p : {p : Fin N × Fin P // wcls τ K k (ν p) = c} => p.1.2) := by
            intro p q hpq
            have h1 : p.1.1 = q.1.1 := hsep2 p.1 q.1 (p.2.trans q.2.symm)
            exact Subtype.ext (Prod.ext h1 hpq)
          have := (hcop' p0.1).comp (fun p : {p : Fin N × Fin P // wcls τ K k (ν p) = c} => p.1.2) hf
          convert this using 2 with p
          have h1 : p.1.1 = p0.1 := hsep2 p.1 p0 (p.2.trans hp0.symm)
          simp only [Function.comp]
          rw [← h1]
      exact hli2.fintype_card_le_finrank
    · have hg3 : 3 ≤ Nat.gcd a M := ha.resolve_left hMa
      have hsep : ∀ p q, wcls τ K k (ν p) = wcls τ K k (ν q) → p = q := by
        intro p q h
        have := r1_sep M a b hModd hg3 hMa β X hβ hX' p.1 q.1 p.2 q.2 (hsepdvd p q h)
        exact Prod.ext this.1 this.2
      have hli2 : LinearIndependent k v := by
        refine linearIndependent_of_wcls hw ρ v ν hv (fun c => ?_)
        have : Subsingleton {p : Fin N × Fin P // wcls τ K k (ν p) = c} :=
          ⟨fun p q => Subtype.ext (hsep p.1 q.1 (p.2.trans q.2.symm))⟩
        exact li_of_subsingleton' _ (fun p => hv0 p.1)
      exact hli2.fintype_card_le_finrank
  simpa [Fintype.card_prod] using hfin

theorem tensor_bound [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hJ : ∀ j, j ≠ s → j ∈ J) (hs : s ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC τ K s z) ^ (2 ^ g) = χ (dC τ K s z)) (ht2 : 2 ≤ n / g)
    {θ : Fin τ.rank → ℤ} {c c' : ℕ} (hθ : ∀ i, mExp τ i θ = if i = s then (c : ℤ) else 0)
    (hcc : ((2 ^ n - 1 : ℕ) : ℤ) ∣ (c : ℤ) * c' - 1)
    (hU : ∀ δ : Fin τ.rank → ℤ, (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣ mExp τ i δ) →
      ∀ l, ((2 ^ n - 1 : ℕ) : ℤ) ∣ δ l)
    {N P : ℕ} (w : Fin N → WeylGroup τ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣
      (w i • (Pi.single s 1 : Fin τ.rank → ℤ) - w i' • (Pi.single s 1 : Fin τ.rank → ℤ)) l)
    (u : Fin P → WeylGroup τ) (hu : ∀ j, u j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hXu : ∀ j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣ (u j • θ - u j' • θ) l) :
    N * P ≤ Module.finrank k V := by
  obtain ⟨J', hJ', hε, hJ0, hvec⟩ := tensor_vec hK hρ ht hJ hθ hcc
  obtain ⟨b, hb⟩ := string_nonempty hn hK ht hs hε hJ0
  obtain ⟨e, he, he0, hew⟩ := hvec b hb
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hper' := periodic_dvd hK hε hper
  have ha0 : 0 < a := Finset.sum_pos (fun i _ => by positivity) ⟨b, hb⟩
  have hg3 := gcd_ge_three hg hgn ht2 hper' ha0
  have hMpos : 0 < 2 ^ n - 1 := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h3M : 3 ≤ 2 ^ n - 1 := le_trans hg3 (Nat.gcd_le_right _ hMpos)
  have hg3' : 3 ≤ Nat.gcd (a * c') (2 ^ n - 1) := by
    have hpos : 0 < Nat.gcd (a * c') (2 ^ n - 1) := Nat.gcd_pos_of_pos_right _ hMpos
    have : Nat.gcd a (2 ^ n - 1) ∣ Nat.gcd (a * c') (2 ^ n - 1) :=
      Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _) (Nat.gcd_dvd_right _ _)
    exact le_trans hg3 (Nat.le_of_dvd hpos this)
  exact tensor_bound_of_vec hn hK hρ ht hs (fun j hj => by simp [hθ, hj]) he he0 hew h3M
    (Or.inr hg3') hU w hβ u hu hXu

end Tensor

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
