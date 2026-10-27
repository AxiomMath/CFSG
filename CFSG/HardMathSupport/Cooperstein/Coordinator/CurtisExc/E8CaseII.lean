module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Sep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringWts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.DigitConds
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Family

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section CaseII


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem mExp_theta (i : Fin Tag.E8.rank) :
    mExp .E8 i e8Theta = if i = n8 then 1 else 0 := by
  revert i; decide +kernel

theorem mExp_single (i : Fin Tag.E8.rank) :
    mExp .E8 i (Pi.single n8 (1 : ℤ)) = Tag.E8.cartan i n8 := by
  unfold mExp
  simp [Pi.single_apply]

theorem mExp_comb {τ : Tag} (i : Fin τ.rank) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    mExp τ i (a • x - b • y) = a * mExp τ i x - b * mExp τ i y := by
  unfold mExp
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mExp_smul {τ : Tag} (i : Fin τ.rank) (a : ℤ) (x : Fin τ.rank → ℤ) :
    mExp τ i (a • x) = a * mExp τ i x := by
  unfold mExp
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem caseII_vec {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E8 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E8 K → k} {J : Finset (Fin Tag.E8.rank)}
    (ht : IsChevType .E8 K 2 exists_weyl_neg_E8 ρ y χ J) (hJ : ∀ s, s ≠ n8 → s ∈ J) :
    ∃ J' : Finset ℕ, (∀ i ∈ J', i < n) ∧
      (∀ z : Kˣ, χ (dC .E8 K n8 z) = (algebraMap K k (z : K)) ^ (∑ i ∈ J', 2 ^ i)) ∧
      (J' = ∅ → ∀ g, ρ (rankOne .E8 K n8 g) y = y) ∧
      ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne .E8 K n8)) y, e ≠ 0 ∧
        e ∈ wtSpace ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • e8Theta - (2 : ℤ) ^ b • Pi.single n8 (1 : ℤ)) := by
  obtain ⟨J', hJ', hε, -, hJ0, hwt⟩ := string_of_highest (hw := exists_weyl_neg_E8) hK hρ ht n8
  refine ⟨J', hJ', hε, hJ0, fun b hb => ?_⟩
  obtain ⟨e, he, he0, hed⟩ := hwt b hb
  refine ⟨e, he, he0, ?_⟩
  set a : ℤ := ((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) with ha
  have hy : ∀ i t, ρ (dC .E8 K i t) y = kpow (k := k) K t (mExp .E8 i (a • e8Theta)) • y := by
    intro i t
    have h1 := ht.2.2.1 _ (dC_mem_H i t)
    rw [h1]
    congr 1
    have : mExp .E8 i (a • e8Theta) = a * (if i = n8 then 1 else 0) := by
      rw [mExp_smul, mExp_theta]
    rw [this]
    by_cases hi : i = n8
    · subst hi
      rw [hε t]
      simp only [↓reduceIte, mul_one]
      unfold kpow
      rw [ha, zpow_natCast]
    · have hiJ := hJ i hi
      have h3 := ((ht.2.2.2 i).1 hiJ).1 t
      rw [h3]
      simp [kpow, hi]
  have hes : ∀ z : Kˣ, ρ (dC .E8 K n8 z) e =
      kpow (k := k) K z (mExp .E8 n8 (a • e8Theta) - 2 * (2 : ℤ) ^ b) • e := by
    intro z
    rw [hed z]
    have : mExp .E8 n8 (a • e8Theta) = a := by
      rw [mExp_smul, mExp_theta]; simp
    rw [this]
    congr 2
    ring
  intro i t
  have := weight_shift ρ n8 (fun i => mExp .E8 i (a • e8Theta)) hy ((2 : ℤ) ^ b) he hes i t
  rw [this]
  congr 1
  rw [mExp_comb, mExp_smul, mExp_single]
  ring_nf

theorem li_of_subsingleton' {ι : Type*} [Subsingleton ι] (v : ι → V) (h : ∀ i, v i ≠ 0) :
    LinearIndependent k v := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact linearIndependent_empty_type
  · exact LinearIndependent.of_subsingleton i (h i)

theorem mExp_sub {τ : Tag} (i : Fin τ.rank) (x y : Fin τ.rank → ℤ) :
    mExp τ i (x - y) = mExp τ i x - mExp τ i y := by
  have := mExp_comb i 1 1 x y
  simpa using this

theorem e8Omega_n8 : e8Omega n8 = e8Theta := by decide

theorem caseII_bound [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .E8 K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : adjointGroup .E8 K → k} {J : Finset (Fin Tag.E8.rank)}
    (ht : IsChevType .E8 K 2 exists_weyl_neg_E8 ρ y χ J) (hJ : ∀ s, s ≠ n8 → s ∈ J)
    (h7 : n8 ∉ J) {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (dC .E8 K n8 z) ^ (2 ^ g) = χ (dC .E8 K n8 z)) (ht2 : 2 ≤ n / g) :
    13440 ≤ Module.finrank k V := by
  classical
  obtain ⟨J', hJ', hε, hJ0, hvec⟩ := caseII_vec hK hρ ht hJ
  have hne := string_nonempty hn hK ht h7 hε hJ0
  obtain ⟨b, hb⟩ := hne
  obtain ⟨e, he, he0, hew⟩ := hvec b hb
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hper' := periodic_dvd hK hε hper
  have ha0 : 0 < a := Finset.sum_pos (fun i _ => by positivity) ⟨b, hb⟩
  have haM : a ≤ 2 ^ n - 1 := sum_two_pow_le J' hJ'
  have hg3 := gcd_ge_three hg hgn ht2 hper' ha0
  set M := 2 ^ n - 1 with hM
  have hMpos : 0 < M := by
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hModd : Odd M := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by rw [hM, pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩
  have h3M : 3 ≤ M := le_trans hg3 (Nat.gcd_le_right _ hMpos)
  have hMcard : Nat.card Kˣ = M := by rw [Nat.card_units, hK]
  obtain ⟨w, hβ⟩ := exists_betaFamily
  obtain ⟨u, hu, hXu⟩ := exists_uFamily
  let X : Fin 240 → Fin 56 → Fin Tag.E8.rank → ℤ := fun i j => w i • (u j • e8Theta)
  let β : Fin 240 → Fin Tag.E8.rank → ℤ := fun i => w i • (Pi.single n8 (1 : ℤ))
  let ν : Fin 240 × Fin 56 → Fin Tag.E8.rank → ℤ := fun p =>
    (a : ℤ) • X p.1 p.2 - (2 : ℤ) ^ b • β p.1
  let v : Fin 240 × Fin 56 → V := fun p =>
    ρ (nWC .E8 K (w p.1)) (ρ (nWC .E8 K (u p.2)) e)
  have hinj : ∀ g' : adjointGroup .E8 K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hv : ∀ p, v p ∈ wtSpace ρ (ν p) := by
    intro p
    have h1 := wt_nWC exists_weyl_neg_E8 ρ (u p.2) hew
    have h2 := wt_nWC exists_weyl_neg_E8 ρ (w p.1) h1
    have hνeq : w p.1 • (u p.2 • (((a : ℤ)) • e8Theta - (2 : ℤ) ^ b • Pi.single n8 (1 : ℤ))) = ν p := by
      rw [weyl_smul_comb, hu, weyl_smul_comb]
    rw [← hνeq]
    exact h2
  have hv0 : ∀ p, v p ≠ 0 := by
    intro p h0
    apply he0
    apply hinj (nWC .E8 K (u p.2))
    apply hinj (nWC .E8 K (w p.1))
    rw [map_zero, map_zero]
    exact h0
  have hsepdvd : ∀ p q, wcls .E8 K k (ν p) = wcls .E8 K k (ν q) → ∀ c, (M : ℤ) ∣ (ν p - ν q) c := by
    intro p q h
    have h1 := dvd_of_wcls_eq h
    rw [hMcard] at h1
    refine dvd_of_dvd_mExp (M : ℤ) (ν p - ν q) (fun c => ?_)
    rw [mExp_sub]
    exact h1 c
  have hX' : ∀ i j j', j ≠ j' → ∀ d : ℕ, 3 ≤ d → ¬ ∀ c, (d : ℤ) ∣ (X i j - X i j') c := by
    intro i j j' hjj d hd hc
    apply hXu j j' hjj d hd
    have h1 : X i j - X i j' = w i • ((1 : ℤ) • (u j • e8Theta) - (1 : ℤ) • (u j' • e8Theta)) := by
      rw [weyl_smul_comb]; simp [X]
    rw [h1] at hc
    have := (weyl_dvd_iff (w i) d _).1 hc
    simpa using this
  have hfin : Fintype.card (Fin 240 × Fin 56) ≤ Module.finrank k V := by
    by_cases hMa : M ∣ a
    · have haeq : a = M := Nat.le_antisymm haM (Nat.le_of_dvd ha0 hMa)
      have hsep2 : ∀ p q, wcls .E8 K k (ν p) = wcls .E8 K k (ν q) → p.1 = q.1 := by
        intro p q h
        have := hsepdvd p q h
        refine R2_sep M b hModd h3M β X hβ p.1 q.1 p.2 q.2 ?_
        simp only [ν] at this
        rw [haeq] at this
        exact this
      have hli : LinearIndependent k (fun j => ρ (nWC .E8 K (u j)) y) := by
        refine linearIndependent_translates_of_isChevType hρ ht h7 (v₀ := e8Theta) ?_ u ?_
        · intro j hj
          rw [← e8Omega_n8]
          exact reflect_e8Omega n8 j hj
        · intro j j' hjj h
          apply hXu j j' hjj 3 le_rfl
          intro c
          simp [h]
      have hcop := copies_linearIndependent hρ ht (s := n8) u hu hli he he0
      have hcop' : ∀ i : Fin 240, LinearIndependent k (fun j : Fin 56 => v (i, j)) := fun i =>
        hcop.map' (ρ (nWC .E8 K (w i))) (LinearMap.ker_eq_bot.2 (hinj _))
      have hli2 : LinearIndependent k v := by
        refine linearIndependent_of_wcls exists_weyl_neg_E8 ρ v ν hv (fun c => ?_)
        rcases isEmpty_or_nonempty {p : Fin 240 × Fin 56 // wcls .E8 K k (ν p) = c} with hE | ⟨⟨p0, hp0⟩⟩
        · exact linearIndependent_empty_type
        · have hf : Function.Injective
              (fun p : {p : Fin 240 × Fin 56 // wcls .E8 K k (ν p) = c} => p.1.2) := by
            intro p q hpq
            have h1 : p.1.1 = q.1.1 := hsep2 p.1 q.1 (p.2.trans q.2.symm)
            exact Subtype.ext (Prod.ext h1 hpq)
          have := (hcop' p0.1).comp (fun p : {p : Fin 240 × Fin 56 // wcls .E8 K k (ν p) = c} => p.1.2) hf
          convert this using 2 with p
          have h1 : p.1.1 = p0.1 := hsep2 p.1 p0 (p.2.trans hp0.symm)
          simp only [Function.comp]
          rw [← h1]
      exact hli2.fintype_card_le_finrank
    · have hsep : ∀ p q, wcls .E8 K k (ν p) = wcls .E8 K k (ν q) → p = q := by
        intro p q h
        have := R1_sep M a b hModd hg3 hMa β X hβ hX' p.1 q.1 p.2 q.2 (hsepdvd p q h)
        exact Prod.ext this.1 this.2
      have hli2 : LinearIndependent k v := by
        refine linearIndependent_of_wcls exists_weyl_neg_E8 ρ v ν hv (fun c => ?_)
        haveI : Subsingleton {p : Fin 240 × Fin 56 // wcls .E8 K k (ν p) = c} :=
          ⟨fun p q => Subtype.ext (hsep p.1 q.1 (p.2.trans q.2.symm))⟩
        exact li_of_subsingleton' _ (fun p => hv0 p.1)
      exact hli2.fintype_card_le_finrank
  simpa using hfin

end CaseII

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
