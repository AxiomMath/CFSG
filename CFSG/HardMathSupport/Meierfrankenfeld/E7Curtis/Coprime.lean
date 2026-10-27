module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.Tensor

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section Arith

theorem r0_sep {ι : Type*} {r : ℕ} (m a c : ℤ) (b b' : ℕ) (hcop : IsCoprime a m)
    (X : ι → Fin r → ℤ) (σ : ι → Fin r)
    (hm : ¬ m ∣ 2 ^ b) (hb1 : ¬ m ∣ a * c - 2 ^ b) (hb2 : ¬ m ∣ a * c + 2 ^ b)
    (hbb : m ∣ (2 : ℤ) ^ b' - 2 ^ b → b = b')
    (hfc : ∀ p q, p ≠ q → (∃ l, l ≠ σ p ∧ l ≠ σ q ∧ ¬ m ∣ (X p - X q) l) ∨
      (σ p ≠ σ q ∧ ((X p - X q) (σ p) = 0 ∨ (X p - X q) (σ p) = c ∨ (X p - X q) (σ p) = -c)))
    (p q : ι)
    (h : ∀ l, m ∣ (a • X p - (2 : ℤ) ^ b • (Pi.single (σ p) (1 : ℤ) : Fin r → ℤ) -
      (a • X q - (2 : ℤ) ^ b' • (Pi.single (σ q) (1 : ℤ) : Fin r → ℤ))) l) :
    p = q ∧ b = b' := by
  classical
  have key : ∀ l, (a • X p - (2 : ℤ) ^ b • (Pi.single (σ p) (1 : ℤ) : Fin r → ℤ) -
      (a • X q - (2 : ℤ) ^ b' • (Pi.single (σ q) (1 : ℤ) : Fin r → ℤ))) l =
      a * (X p - X q) l - 2 ^ b * (Pi.single (σ p) (1 : ℤ) : Fin r → ℤ) l +
        2 ^ b' * (Pi.single (σ q) (1 : ℤ) : Fin r → ℤ) l := by
    intro l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  by_cases hpq : p = q
  · subst hpq
    refine ⟨rfl, hbb ?_⟩
    have h1 := h (σ p)
    rw [key, Pi.single_eq_same, sub_self] at h1
    convert h1 using 1
    simp only [Pi.zero_apply]
    ring
  · exfalso
    rcases hfc p q hpq with ⟨l, hl1, hl2, hl⟩ | ⟨hσ, hx⟩
    · apply hl
      have h1 := h l
      rw [key, Pi.single_eq_of_ne hl1, Pi.single_eq_of_ne hl2, mul_zero, mul_zero, sub_zero,
        add_zero] at h1
      exact hcop.symm.dvd_of_dvd_mul_left h1
    · have h1 := h (σ p)
      rw [key, Pi.single_eq_same, Pi.single_eq_of_ne hσ, mul_zero, add_zero, mul_one] at h1
      rcases hx with h0 | h0 | h0 <;> rw [h0] at h1
      · apply hm
        have : m ∣ -(a * 0 - 2 ^ b) := dvd_neg.2 h1
        simpa using this
      · exact hb1 h1
      · apply hb2
        have : m ∣ -(a * -c - 2 ^ b) := dvd_neg.2 h1
        convert this using 1
        ring

theorem eq_of_two_pow_modEq {n b b' : ℕ} (hb : b < n) (hb' : b' < n)
    (h : ((2 ^ n - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ b' - 2 ^ b) : b = b' := by
  have hT : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℤ) ≤ 2 ^ b' := one_le_pow₀ (by norm_num)
  have h3 : (2 : ℤ) ^ b ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2 : ℤ) ^ b' ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hM : (((2 ^ n - 1 : ℕ) : ℤ)) = 2 ^ n - 1 := by push_cast [h4n]; ring
  rw [hM] at h
  have h5 : (2 : ℤ) ^ b' - 2 ^ b = 0 := by
    obtain ⟨k, hk⟩ := h
    have hlt : (2 : ℤ) ^ b' - 2 ^ b < 2 ^ n - 1 := by linarith
    have hgt : -(2 ^ n - 1) < (2 : ℤ) ^ b' - 2 ^ b := by linarith
    have hMpos : (0 : ℤ) < 2 ^ n - 1 := by linarith
    rw [hk] at hlt hgt ⊢
    have hk1 : k < 1 := by
      by_contra hk1; push Not at hk1; nlinarith
    have hk2 : -1 < k := by
      by_contra hk2; push Not at hk2; nlinarith
    have : k = 0 := by omega
    simp [this]
  have h6 : (2 : ℤ) ^ b' = 2 ^ b := by linarith
  exact (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h6)).symm

theorem sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  have := geom_two_pow 2 n (by norm_num)
  simp only [Nat.add_one_sub_one, one_mul] at this
  omega

theorem sum_two_pow_cast_sub {J : Finset ℕ} {b : ℕ} (h : 2 ^ b ≤ ∑ i ∈ J, 2 ^ i) :
    ((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) - 2 ^ b = ((∑ i ∈ J, 2 ^ i - 2 ^ b : ℕ) : ℤ) := by
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem not_dvd_sum_sub_two_pow {n : ℕ} {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) {b b' : ℕ}
    (hb : b ∈ J) (hb' : b' ∈ J) (hne : b ≠ b') :
    ¬ ((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) - 2 ^ b := by
  intro h
  have h1 : 2 ^ b + 2 ^ b' ≤ ∑ i ∈ J, 2 ^ i := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hb
      · rw [Finset.mem_singleton.1 hx]; exact hb')
  have h2 := sum_two_pow_le J hJ
  have h2b : 2 ^ b ≤ ∑ i ∈ J, 2 ^ i := le_trans (Nat.le_add_right _ _) h1
  rw [sum_two_pow_cast_sub h2b] at h
  have h5 := Int.natCast_dvd_natCast.1 h
  have hlt : 2 ^ b < ∑ i ∈ J, 2 ^ i :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right Nat.one_le_two_pow) h1
  have hpos : 0 < ∑ i ∈ J, 2 ^ i - 2 ^ b := Nat.sub_pos_of_lt hlt
  have h6 := Nat.le_of_dvd hpos h5
  have h7 : ∑ i ∈ J, 2 ^ i - 2 ^ b < ∑ i ∈ J, 2 ^ i :=
    Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le _) hlt) Nat.one_le_two_pow
  exact absurd (lt_of_le_of_lt h6 h7) (not_lt.2 h2)

theorem not_dvd_sum_add_two_pow {n : ℕ} {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) {b b' : ℕ}
    (hb : b ∈ J) (hb' : b' ∈ J) (hne : b ≠ b') :
    ¬ ((2 ^ n - 1 : ℕ) : ℤ) ∣ ((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) + 2 ^ b := by
  intro h
  have hbn := hJ b hb
  have hbn' := hJ b' hb'
  have h2 := sum_two_pow_le J hJ
  have hT : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h3 : 2 ^ b ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1n : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hcast : ((∑ i ∈ J, 2 ^ i : ℕ) : ℤ) + 2 ^ b = ((∑ i ∈ J, 2 ^ i + 2 ^ b : ℕ) : ℤ) := by
    push_cast; ring
  rw [hcast] at h
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.1 h
  have hk2 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have : (2 ^ n - 1) * 2 ≤ (2 ^ n - 1) * k := Nat.mul_le_mul_left _ hk2
    omega
  have hk1 : 1 ≤ k := by
    by_contra hk1
    push Not at hk1
    have : k = 0 := by omega
    rw [this, mul_zero] at hk
    omega
  have hk3 : k = 1 := by omega
  rw [hk3, mul_one] at hk
  have hsub : J ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hJ i hi)
  have hsd := Finset.sum_sdiff hsub (f := fun i => 2 ^ i)
  rw [sum_range_two_pow] at hsd
  have h5 : ∑ i ∈ Finset.range n \ J, 2 ^ i = ∑ i ∈ ({b} : Finset ℕ), 2 ^ i := by
    rw [Finset.sum_singleton]; omega
  have h6 := Finset.geomSum_injective (le_refl 2) h5
  have : b ∈ Finset.range n \ J := by
    have : b ∈ ({b} : Finset ℕ) := Finset.mem_singleton_self b
    rw [← h6] at this
    exact this
  exact (Finset.mem_sdiff.1 this).2 hb

end Arith

section Coprime


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem tensor_bound_coprime [Module.Finite k V]
    (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (ρ : Representation k (adjointGroup τ K) V) {s : Fin τ.rank} {θ : Fin τ.rank → ℤ}
    {c c' : ℕ} (hcc : ((2 ^ n - 1 : ℕ) : ℤ) ∣ (c : ℤ) * c' - 1)
    (hU : ∀ δ : Fin τ.rank → ℤ, (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣ mExp τ i δ) →
      ∀ l, ((2 ^ n - 1 : ℕ) : ℤ) ∣ δ l)
    {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) {b₁ b₂ : ℕ} (hb₁ : b₁ ∈ J') (hb₂ : b₂ ∈ J')
    (hb : b₁ ≠ b₂)
    (hcop : IsCoprime (((∑ i ∈ J', 2 ^ i) * c' : ℕ) : ℤ) ((2 ^ n - 1 : ℕ) : ℤ))
    {e : Fin 2 → V} (he0 : ∀ ε, e ε ≠ 0)
    (hew : ∀ ε, e ε ∈ wtSpace ρ ((((∑ i ∈ J', 2 ^ i) * c' : ℕ) : ℤ) • θ -
      (2 : ℤ) ^ (![b₁, b₂] ε) • Pi.single s (1 : ℤ)))
    {N P : ℕ} (w : Fin N → WeylGroup τ) (σ : Fin N → Fin τ.rank)
    (hσ : ∀ i, w i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single (σ i) 1)
    (u : Fin P → WeylGroup τ) (hu : ∀ j, u j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hfc : ∀ p q : Fin N × Fin P, p ≠ q →
      (∃ l, l ≠ σ p.1 ∧ l ≠ σ q.1 ∧
        ¬ ((2 ^ n - 1 : ℕ) : ℤ) ∣ (w p.1 • (u p.2 • θ) - w q.1 • (u q.2 • θ)) l) ∨
      (σ p.1 ≠ σ q.1 ∧ ((w p.1 • (u p.2 • θ) - w q.1 • (u q.2 • θ)) (σ p.1) = 0 ∨
        (w p.1 • (u p.2 • θ) - w q.1 • (u q.2 • θ)) (σ p.1) = c ∨
        (w p.1 • (u p.2 • θ) - w q.1 • (u q.2 • θ)) (σ p.1) = -c))) :
    2 * (N * P) ≤ Module.finrank k V := by
  classical
  set M : ℤ := ((2 ^ n - 1 : ℕ) : ℤ) with hM
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  set a' : ℤ := (((∑ i ∈ J', 2 ^ i) * c' : ℕ) : ℤ) with ha'
  have hn2 : 2 ≤ n := by
    have := hJ' b₁ hb₁
    have := hJ' b₂ hb₂
    omega
  have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h3M : (3 : ℤ) ≤ M := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have : (4 : ℤ) ≤ 2 ^ n := by exact_mod_cast this
    rw [hM]; push_cast [h4]; linarith
  have hModd : Odd M := by
    rw [hM]
    exact (Int.odd_coe_nat _).2 (Nat.Even.sub_odd h4 (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one)
  have hMcard : ((Nat.card Kˣ : ℕ) : ℤ) = M := by rw [Nat.card_units, hK]
  have hac : M ∣ a' * c - a := by
    have : a' * c - a = a * ((c : ℤ) * c' - 1) := by rw [ha', ha]; push_cast; ring
    rw [this]
    exact dvd_mul_of_dvd_right hcc _
  have hbε : ∀ ε, ![b₁, b₂] ε ∈ J' := fun ε => by fin_cases ε <;> simp [hb₁, hb₂]
  have hbε' : ∀ ε, ∃ b'' ∈ J', b'' ≠ ![b₁, b₂] ε := fun ε => by
    fin_cases ε
    · exact ⟨b₂, hb₂, Ne.symm hb⟩
    · exact ⟨b₁, hb₁, hb⟩
  have hm2 : ∀ b, ¬ M ∣ 2 ^ b := by
    intro b hdvd
    have hcop2 : IsCoprime M ((2 : ℤ) ^ b) := by
      obtain ⟨t, ht⟩ := hModd
      refine IsCoprime.pow_right ⟨1, -t, ?_⟩
      rw [ht]; ring
    have := hcop2.isUnit_of_dvd' (dvd_refl M) hdvd
    rw [Int.isUnit_iff] at this
    omega
  let X : Fin N × Fin P → Fin τ.rank → ℤ := fun p => w p.1 • (u p.2 • θ)
  let ν : (Fin N × Fin P) × Fin 2 → Fin τ.rank → ℤ := fun p =>
    a' • X p.1 - (2 : ℤ) ^ (![b₁, b₂] p.2) • Pi.single (σ p.1.1) (1 : ℤ)
  let v : (Fin N × Fin P) × Fin 2 → V := fun p =>
    ρ (nWC τ K (w p.1.1)) (ρ (nWC τ K (u p.1.2)) (e p.2))
  have hinj : ∀ g' : adjointGroup τ K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hv : ∀ p, v p ∈ wtSpace ρ (ν p) := by
    intro p
    have h1 := wt_nWC hw ρ (u p.1.2) (hew p.2)
    have h2 := wt_nWC hw ρ (w p.1.1) h1
    have hνeq : w p.1.1 • (u p.1.2 • (a' • θ - (2 : ℤ) ^ (![b₁, b₂] p.2) • Pi.single s (1 : ℤ))) =
        ν p := by
      rw [weyl_smul_comb, hu, weyl_smul_comb, hσ]
    rw [← hνeq]
    exact h2
  have hv0 : ∀ p, v p ≠ 0 := by
    intro p h0
    apply he0 p.2
    apply hinj (nWC τ K (u p.1.2))
    apply hinj (nWC τ K (w p.1.1))
    rw [map_zero, map_zero]
    exact h0
  have hsep : ∀ p q, wcls τ K k (ν p) = wcls τ K k (ν q) → p = q := by
    intro p q h
    have h1 := dvd_of_wcls_eq h
    rw [hMcard] at h1
    have h2 : ∀ l, M ∣ (ν p - ν q) l := hU (ν p - ν q) (fun i => by rw [mExp_sub]; exact h1 i)
    obtain ⟨b'', hb'', hne''⟩ := hbε' p.2
    have hb1 : ¬ M ∣ a' * c - 2 ^ (![b₁, b₂] p.2) := by
      intro hd
      have := dvd_sub hd hac
      rw [show a' * c - 2 ^ (![b₁, b₂] p.2) - (a' * c - a) = a - 2 ^ (![b₁, b₂] p.2) by ring]
        at this
      exact not_dvd_sum_sub_two_pow hJ' (hbε p.2) hb'' hne''.symm this
    have hb2 : ¬ M ∣ a' * c + 2 ^ (![b₁, b₂] p.2) := by
      intro hd
      have := dvd_sub hd hac
      rw [show a' * c + 2 ^ (![b₁, b₂] p.2) - (a' * c - a) = a + 2 ^ (![b₁, b₂] p.2) by ring]
        at this
      exact not_dvd_sum_add_two_pow hJ' (hbε p.2) hb'' hne''.symm this
    have hbb : M ∣ (2 : ℤ) ^ (![b₁, b₂] q.2) - 2 ^ (![b₁, b₂] p.2) →
        ![b₁, b₂] p.2 = ![b₁, b₂] q.2 :=
      fun hd => eq_of_two_pow_modEq (hJ' _ (hbε p.2)) (hJ' _ (hbε q.2)) hd
    obtain ⟨hpq, hbq⟩ := r0_sep M a' c (![b₁, b₂] p.2) (![b₁, b₂] q.2) hcop X (fun p => σ p.1)
      (hm2 _) hb1 hb2 hbb hfc p.1 q.1 h2
    refine Prod.ext hpq ?_
    revert hbq
    rcases p with ⟨p, ε⟩
    rcases q with ⟨q, ε'⟩
    fin_cases ε <;> fin_cases ε' <;> simp [hb, Ne.symm hb]
  have hli : LinearIndependent k v := by
    refine linearIndependent_of_wcls hw ρ v ν hv (fun c => ?_)
    have : Subsingleton {p : (Fin N × Fin P) × Fin 2 // wcls τ K k (ν p) = c} :=
      ⟨fun p q => Subtype.ext (hsep p.1 q.1 (p.2.trans q.2.symm))⟩
    exact li_of_subsingleton' _ (fun p => hv0 p.1)
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin] at this
  linarith

theorem node_bound [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {s : Fin τ.rank} (hJ : ∀ j, j ≠ s → j ∈ J) (hs : s ∉ J)
    {θ : Fin τ.rank → ℤ} {c c' : ℕ} (hθ : ∀ i, mExp τ i θ = if i = s then (c : ℤ) else 0)
    (hcc : ((2 ^ n - 1 : ℕ) : ℤ) ∣ (c : ℤ) * c' - 1)
    (hU : ∀ δ : Fin τ.rank → ℤ, (∀ i, ((2 ^ n - 1 : ℕ) : ℤ) ∣ mExp τ i δ) →
      ∀ l, ((2 ^ n - 1 : ℕ) : ℤ) ∣ δ l)
    {N P : ℕ} (w : Fin N → WeylGroup τ)
    (hβ : ∀ i i', i ≠ i' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣
      (w i • (Pi.single s 1 : Fin τ.rank → ℤ) - w i' • (Pi.single s 1 : Fin τ.rank → ℤ)) l)
    (u : Fin P → WeylGroup τ) (hu : ∀ j, u j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hXu : ∀ j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ l, (d : ℤ) ∣ (u j • θ - u j' • θ) l)
    {N₀ P₀ : ℕ} (w₀ : Fin N₀ → WeylGroup τ) (σ : Fin N₀ → Fin τ.rank)
    (hσ : ∀ i, w₀ i • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single (σ i) 1)
    (u₀ : Fin P₀ → WeylGroup τ)
    (hu₀ : ∀ j, u₀ j • (Pi.single s 1 : Fin τ.rank → ℤ) = Pi.single s 1)
    (hfc : 3 ≤ n → ∀ p q : Fin N₀ × Fin P₀, p ≠ q →
      (∃ l, l ≠ σ p.1 ∧ l ≠ σ q.1 ∧
        ¬ ((2 ^ n - 1 : ℕ) : ℤ) ∣ (w₀ p.1 • (u₀ p.2 • θ) - w₀ q.1 • (u₀ q.2 • θ)) l) ∨
      (σ p.1 ≠ σ q.1 ∧ ((w₀ p.1 • (u₀ p.2 • θ) - w₀ q.1 • (u₀ q.2 • θ)) (σ p.1) = 0 ∨
        (w₀ p.1 • (u₀ p.2 • θ) - w₀ q.1 • (u₀ q.2 • θ)) (σ p.1) = c ∨
        (w₀ p.1 • (u₀ p.2 • θ) - w₀ q.1 • (u₀ q.2 • θ)) (σ p.1) = -c))) :
    (∃ b < n, ∀ z : Kˣ, χ (dC τ K s z) = (algebraMap K k (z : K)) ^ (2 ^ b)) ∨
      min (N * P) (2 * (N₀ * P₀)) ≤ Module.finrank k V := by
  classical
  obtain ⟨J', hJ', hε, hJ0, hvec⟩ := tensor_vec hK hρ ht hJ hθ hcc
  have hne := string_nonempty hn hK ht hs hε hJ0
  by_cases hcard : J'.card ≤ 1
  · left
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 (le_antisymm hcard (Finset.card_pos.2 hne))
    refine ⟨b, hJ' b (by simp [hb]), fun z => ?_⟩
    rw [hε z, hb, Finset.sum_singleton]
  · right
    push Not at hcard
    obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := Finset.one_lt_card.1 hcard
    have hn2 : 2 ≤ n := by
      have := hJ' b₁ hb₁
      have := hJ' b₂ hb₂
      omega
    have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3M : 3 ≤ 2 ^ n - 1 := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hModd : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd h4 (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
    obtain ⟨e₁, he₁, he₁0, he₁w⟩ := hvec b₁ hb₁
    obtain ⟨e₂, he₂, he₂0, he₂w⟩ := hvec b₂ hb₂
    by_cases hcop : Nat.Coprime ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1)
    · refine le_trans (min_le_right _ _) ?_
      have hn3 : 3 ≤ n := by
        by_contra hn3
        have hn2' : n = 2 := by omega
        subst hn2'
        have hsub : J' ⊆ Finset.range 2 := fun i hi => Finset.mem_range.2 (hJ' i hi)
        have hJeq : J' = Finset.range 2 :=
          Finset.eq_of_subset_of_card_le hsub (by simp; omega)
        have : (2 ^ 2 - 1) ∣ (∑ i ∈ J', 2 ^ i) * c' := by
          rw [hJeq, sum_range_two_pow]
          exact dvd_mul_right _ _
        have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) this
        norm_num at h1
      refine tensor_bound_coprime hw hK ρ hcc hU hJ' hb₁ hb₂ hb
        (Nat.isCoprime_iff_coprime.2 hcop) (e := ![e₁, e₂])
        (fun ε => by fin_cases ε; exacts [he₁0, he₂0]) (fun ε => by fin_cases ε; exacts [he₁w, he₂w])
        w₀ σ hσ u₀ hu₀
        (hfc hn3)
    · refine le_trans (min_le_left _ _) ?_
      have hg : 3 ≤ Nat.gcd ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1) := by
        have hdvd := Nat.gcd_dvd_right ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1)
        have hodd : Odd (Nat.gcd ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1)) := Odd.of_dvd_nat hModd hdvd
        have hpos : 0 < Nat.gcd ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1) :=
          Nat.gcd_pos_of_pos_right _ (by omega)
        have h1 : Nat.gcd ((∑ i ∈ J', 2 ^ i) * c') (2 ^ n - 1) ≠ 1 := hcop
        rcases hodd with ⟨t, ht⟩
        omega
      exact tensor_bound_of_vec hn hK hρ ht hs (fun j hj => by simp [hθ, hj]) he₁ he₁0 he₁w h3M
        (Or.inr hg) hU w hβ u hu hXu

end Coprime

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
