module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.StringWts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Weyl
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4ModWeyl
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Copies

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

section PairBound

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem dim_ge_of_sep [Module.Finite k V] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k (adjointGroup .F4 K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup .F4 K → k} {J : Finset (Fin Tag.F4.rank)}
    (ht : IsChevType .F4 K 2 exists_weyl_neg_F4' ρ y χ J) {s : Fin Tag.F4.rank} (hs : s ∉ J)
    (a : Fin Tag.F4.rank → ℕ)
    (hy : ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      ρ (dC .F4 K i t) y = kpow (k := k) K t ((a i : ℕ) : ℤ) • y)
    (B : Finset ℕ)
    (hE : ∀ b ∈ B, ∃ e ∈ orbitSpan (ρ.comp (rankOne .F4 K s)) y, e ≠ 0 ∧ ∀ z : Kˣ,
      ρ (dC .F4 K s z) e = (algebraMap K k (z : K)) ^ (((a s : ℕ) : ℤ) - 2 ^ (b + 1)) • e)
    (hsep : ∀ (i i' : Fin 12) (j j' : Fin 8) (b b' : ℕ), b ∈ B → b' ∈ B →
      (∀ c, ((2 ^ n - 1 : ℕ) : ℤ) ∣
        (((1 : ℤ) • (wF s i • (uF s j • lamF a)) - (2 : ℤ) ^ b • (wF s i • (Pi.single s (1 : ℤ) :
            Fin Tag.F4.rank → ℤ))) -
          ((1 : ℤ) • (wF s i' • (uF s j' • lamF a)) - (2 : ℤ) ^ b' • (wF s i' • (Pi.single s (1 : ℤ) :
            Fin Tag.F4.rank → ℤ)))) c) → i = i' ∧ b = b') :
    96 * B.card ≤ Module.finrank k V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hK]
  obtain ⟨hu, hΩ, -, -⟩ := family_props s
  have hE' : ∀ b : ℕ, ∃ e : V, b ∈ B → (e ∈ orbitSpan (ρ.comp (rankOne .F4 K s)) y ∧ e ≠ 0 ∧
      ∀ z : Kˣ, ρ (dC .F4 K s z) e =
        (algebraMap K k (z : K)) ^ (((a s : ℕ) : ℤ) - 2 ^ (b + 1)) • e) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨e, he, he0, hes⟩ := hE b hb
      exact ⟨e, fun _ => ⟨he, he0, hes⟩⟩
    · exact ⟨0, fun h => absurd h hb⟩
  choose Ev hEv using hE'
  have hEw : ∀ b ∈ B, Ev b ∈ wtSpace ρ ((1 : ℤ) • lamF a - (2 : ℤ) ^ b • Pi.single s (1 : ℤ)) := by
    intro b hb
    obtain ⟨he, he0, hes⟩ := hEv b hb
    have hes' : ∀ z : Kˣ, ρ (dC .F4 K s z) (Ev b) =
        kpow (k := k) K z (((a s : ℕ) : ℤ) - 2 * (2 : ℤ) ^ b) • Ev b := by
      intro z
      rw [hes z]
      unfold kpow
      congr 2
      rw [pow_succ]; ring
    intro i t
    have := weight_shift ρ s (fun i => ((a i : ℕ) : ℤ)) hy ((2 : ℤ) ^ b) he hes' i t
    rw [this, mExp_combF, mExp_lamF, mExp_singleF]
    congr 1
    simp only [one_mul]
    ring_nf
  let ι := Fin 12 × Fin 8 × {b : ℕ // b ∈ B}
  let w : Fin 12 → WeylGroup .F4 := fun i => wF s i
  let u : Fin 8 → WeylGroup .F4 := fun j => uF s j
  let γ : Fin 12 → Fin Tag.F4.rank → ℤ := fun i => w i • (Pi.single s (1 : ℤ) : Fin Tag.F4.rank → ℤ)
  let ν : ι → Fin Tag.F4.rank → ℤ := fun p =>
    (1 : ℤ) • (w p.1 • (u p.2.1 • lamF a)) - (2 : ℤ) ^ (p.2.2 : ℕ) • γ p.1
  let v : ι → V := fun p => ρ (nWC .F4 K (w p.1)) (ρ (nWC .F4 K (u p.2.1)) (Ev p.2.2))
  have hinj : ∀ g' : adjointGroup .F4 K, Function.Injective (ρ g') :=
    fun g' => (repEquiv ρ g').injective
  have hv : ∀ p, v p ∈ wtSpace ρ (ν p) := by
    intro p
    have h1 := wt_nWC exists_weyl_neg_F4' ρ (u p.2.1) (hEw p.2.2 p.2.2.2)
    have h2 := wt_nWC exists_weyl_neg_F4' ρ (w p.1) h1
    have hνeq : w p.1 • (u p.2.1 • ((1 : ℤ) • lamF a - (2 : ℤ) ^ (p.2.2 : ℕ) • Pi.single s (1 : ℤ))) =
        ν p := by
      rw [weyl_smul_combF, hu, weyl_smul_combF]
    rw [← hνeq]
    exact h2
  have hsepdvd : ∀ p q, wcls .F4 K k (ν p) = wcls .F4 K k (ν q) → ∀ c,
      (((2 ^ n - 1 : ℕ)) : ℤ) ∣ (ν p - ν q) c := by
    intro p q h
    have h1 := dvd_of_wcls_eq h
    rw [hMcard] at h1
    exact dvd_of_dvd_mExpF _ (ν p - ν q) (fun c => by rw [mExp_subF]; exact h1 c)
  have hsep' : ∀ p q, wcls .F4 K k (ν p) = wcls .F4 K k (ν q) → p.1 = q.1 ∧ p.2.2 = q.2.2 := by
    intro p q h
    have := hsep p.1 q.1 p.2.1 q.2.1 p.2.2 q.2.2 p.2.2.2 q.2.2.2 (fun c => by
      have h4 := hsepdvd p q h c
      simpa only [ν, γ, w, u, Pi.sub_apply] using h4)
    exact ⟨this.1, Subtype.ext this.2⟩
  have hli : LinearIndependent k (fun j => ρ (nWC .F4 K (u j)) y) := by
    refine linearIndependent_translates_of_isChevType hρ ht hs (v₀ := f4Omega s)
      (reflect_f4Omega s) u hΩ
  have hcop : ∀ b : {b : ℕ // b ∈ B},
      LinearIndependent k (fun j : Fin 8 => ρ (nWC .F4 K (u j)) (Ev b)) := by
    intro b
    obtain ⟨he, he0, -⟩ := hEv b b.2
    exact copies_linearIndependent hρ ht u hu hli he he0
  have hcop' : ∀ (i : Fin 12) (b : {b : ℕ // b ∈ B}),
      LinearIndependent k (fun j : Fin 8 => v (i, j, b)) := fun i b =>
    (hcop b).map' (ρ (nWC .F4 K (w i))) (LinearMap.ker_eq_bot.2 (hinj _))
  have hli2 : LinearIndependent k v := by
    refine linearIndependent_of_wcls exists_weyl_neg_F4' ρ v ν hv (fun c => ?_)
    rcases isEmpty_or_nonempty {p : ι // wcls .F4 K k (ν p) = c} with hE | ⟨⟨p0, hp0⟩⟩
    · exact linearIndependent_empty_type
    · have hkey : ∀ q : {p : ι // wcls .F4 K k (ν p) = c},
          q.1 = (p0.1, q.1.2.1, p0.2.2) := by
        intro q
        obtain ⟨h1, h2⟩ := hsep' q.1 p0 (q.2.trans hp0.symm)
        exact Prod.ext h1 (Prod.ext rfl h2)
      have hf : Function.Injective
          (fun q : {p : ι // wcls .F4 K k (ν p) = c} => q.1.2.1) := by
        intro q q' hqq'
        apply Subtype.ext
        rw [hkey q, hkey q']
        simp only at hqq'
        rw [hqq']
      have := (hcop' p0.1 p0.2.2).comp
        (fun q : {p : ι // wcls .F4 K k (ν p) = c} => q.1.2.1) hf
      convert this using 2 with q
      simp only [Function.comp]
      exact congrArg v (hkey q)
  have hcardι : Fintype.card ι = 96 * B.card := by
    simp only [ι, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    ring
  have h1 := hli2.fintype_card_le_finrank
  rw [hcardι] at h1
  exact h1

end PairBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
