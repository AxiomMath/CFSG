module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni

open CFSG.HardMathSupport.Curtis.Coordinator
open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent

theorem exists_primeFormP_of_twistedA {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (hU : UnitaryFieldData 2 f K), 3 ≤ r + 1 ∧
      ¬(r + 1 = 3 ∧ 2 ^ f = 2) ∧
      Nonempty (S ≃* primeFormP hU
        ((1 : GL (Fin (r + 1)) K) : Matrix (Fin (r + 1)) (Fin (r + 1)) K)) := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hq] at h
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e'⟩⟩ := h
  have hU : UnitaryFieldData 2 q.exponent K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ 2 ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := r + 1)) hn3 hq'
  exact ⟨q.exponent, K, inferInstance, hU, hn3, hq',
    ⟨(e'.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

section Aut

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_conj_mul_field (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K),
      α = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A *
        primeFormFieldHom h isPrimeFormGram_one σ ∧
      primeFormFieldFactor h isPrimeFormGram_one hn hne α = σ := by
  obtain ⟨⟨A, σ⟩, rfl⟩ := primeFormPsi_surjective h (isPrimeFormGram_one (n := n)) hn hne α
  exact ⟨A, σ, primeFormPsi_apply h _ A σ, primeFormFieldFactor_psi h _ hn hne _⟩

theorem pow_eq_one_conj_mul_field (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (σ : K ≃+* K) (m : ℕ)
    (hm : (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A *
      primeFormFieldHom h isPrimeFormGram_one σ) ^ m = 1) :
    σ ^ m = 1 ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      twistedNorm σ (A : GL (Fin n) K) m = GeneralLinearGroup.scalar (Fin n) c := by
  rw [conj_mul_field_pow] at hm
  have h1 : primeFormPsi h (isPrimeFormGram_one (n := n))
      ⟨⟨twistedNorm σ (A : GL (Fin n) K) m, twistedNorm_mem h σ A.2 m⟩, σ ^ m⟩ = 1 := by
    rw [primeFormPsi_apply]
    exact hm
  obtain ⟨hσ, c, hc, hcA⟩ := (primeFormPsi_eq_one_iff h (isPrimeFormGram_one (n := n)) hn _).1 h1
  exact ⟨hσ, c, hc, hcA⟩

theorem fieldFactor_pow_eq_one (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} {m : ℕ}
    (hα : α ^ m = 1) : primeFormFieldFactor h isPrimeFormGram_one hn hne α ^ m = 1 := by
  rw [← map_pow, hα, map_one]

end Aut

section Outer

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_descent (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {ζ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} (hζp : ζ ^ p = 1)
    (hout : primeFormFieldFactor h isPrimeFormGram_one hn hne ζ ≠ 1) :
    ∃ (σ : K ≃+* K) (M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      orderOf σ = p ∧ p ∣ f ∧
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ * ζ *
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M =
        primeFormFieldHom h isPrimeFormGram_one σ := by
  have : Fact p.Prime := ⟨hp⟩
  have hζ1 : ζ ≠ 1 := fun h1 => hout (by rw [h1, map_one])
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hσp : primeFormFieldFactor h isPrimeFormGram_one hn hne ζ ^ p = 1 := by
    rw [← map_pow, hζp, map_one]
  have hσord : orderOf (primeFormFieldFactor h isPrimeFormGram_one hn hne ζ) = p :=
    orderOf_eq_prime hσp hout
  obtain ⟨hpf, -, -, -, -, M, hM⟩ := unitary_prime_semilinear_field_descent h hn hne hp hp2 hpℓ ζ
    hord _ rfl hσord
  exact ⟨_, M, hσord, hpf, hM⟩

theorem mem_autFix_conj_iff {X : Type*} [Group X] (u g ζ : MulAut X) (hζ : u⁻¹ * ζ * u = g)
    (x : X) :
    ζ x = x ↔ g (u⁻¹ x) = u⁻¹ x := by
  rw [← hζ]
  change ζ x = x ↔ u⁻¹ (ζ (u (u⁻¹ x))) = u⁻¹ x
  rw [show u (u⁻¹ x) = x from by simp]
  exact ⟨fun h => by rw [h], fun h => u⁻¹.injective h⟩

theorem not_isSolvable_autFix_of_outer (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {ζ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} (hζp : ζ ^ p = 1)
    (hout : primeFormFieldFactor h isPrimeFormGram_one hn hne ζ ≠ 1)
    (hq0 : ¬(n = 3 ∧ ℓ ^ (f / p) = 2)) : ¬ Group.IsSolvable ↥(autFix ζ) := by
  intro hsolv
  obtain ⟨σ, M, hσ, hpf, hM⟩ := exists_descent h hn hne hp hp2 hpℓ hζp hout
  set u := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hu
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hinj := subfieldPSU_injective h h₀ hbar n (by omega)
  have hle := range_subfieldPSU_le h n h₀ hbar (σ := σ)
  let ψ : primeFormP h₀ ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) →* ↥(autFix ζ) :=
    { toFun := fun x => ⟨u (subfieldPSU h h₀ hbar n x), by
        rw [mem_autFix, mem_autFix_conj_iff u _ ζ hM, MulAut.inv_apply_self]
        exact hle ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψ : Function.Injective ψ := fun x y hxy =>
    hinj (u.injective (congrArg Subtype.val hxy))
  have hs : Group.IsSolvable (primeFormP h₀
      ((1 : GL (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (CFSG.LieType.Chevalley.fixSubfield σ))) :=
    Group.isSolvable_of_isSolvable_injective hψ
  have hsimple := isSimpleGroup_primeFormP_one h₀ hn hq0
  exact not_commute_primeFormP_one h₀ hn hq0 fun a b => IsSimpleGroup.comm_iff_isSolvable.mpr hs a b

theorem card_le_of_outer_exception (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hp3 : 3 < p)
    (hZ : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {ζ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} (hζp : ζ ^ p = 1)
    (hout : primeFormFieldFactor h isPrimeFormGram_one hn hne ζ ≠ 1)
    (hq0 : n = 3 ∧ ℓ ^ (f / p) = 2)
    (Ē : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hfix : ∀ x ∈ Ē, ζ x = x) : Nat.card Ē ≤ 72 := by
  obtain ⟨σ, M, hσ, hpf, hM⟩ := exists_descent h hn hne hp hp2 hpℓ hζp hout
  set u := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M with hu
  have : Finite K := h.finite
  have hZ' : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hZ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hexc⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ n hn hne hZ'
  obtain ⟨hc72, -⟩ := hexc hq0 hp3
  have hfin : Finite ↥(fieldFixedPSU h n σ) := Nat.finite_of_card_ne_zero (by rw [hc72]; norm_num)
  let ψ : Ē →* ↥(fieldFixedPSU h n σ) :=
    { toFun := fun x => ⟨u⁻¹ x, by
        have := (mem_autFix_conj_iff u _ ζ hM x).1 (hfix x x.2)
        exact this⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hψ : Function.Injective ψ := fun x y hxy =>
    Subtype.ext (u⁻¹.injective (congrArg Subtype.val hxy))
  rw [← hc72]
  exact Nat.card_le_card_of_injective ψ hψ

end Outer

section Order

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem card_primeFormD_three_dvd (h : UnitaryFieldData ℓ f K) :
    Nat.card (primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∣
      (ℓ ^ f + 1) * ((ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1)) := by
  have hsu : Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
    have e : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = unitarySU ℓ f K 3 := by
      rw [Units.val_one]
      exact (unitarySU_eq_gramSU h 3).symm
    rw [e]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h
  set D := primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner
    (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) with hI
  let φ : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    (primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).comp
      (Subgroup.inclusion (fun _ hg => hg.1))
  have hφ : φ.range = I := by
    ext α
    rw [MonoidHom.mem_range, hI, mem_inner_primeFormP]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (mem_inner_primeFormP h _ α).1 hα
    exact ⟨_, rfl⟩
  have h1 : Nat.card D = Nat.card (D ⧸ I.subgroupOf D) * Nat.card (I.subgroupOf D) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (I.subgroupOf D) = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hID).toEquiv
  have h3 : Nat.card I ∣ Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    rw [← hφ]
    exact Subgroup.card_range_dvd φ
  rw [h1, h2]
  exact mul_dvd_mul (card_primeFormD_quotient_dvd h 1) (hsu ▸ h3)

theorem eq_one_of_pow_five_eq_one (h : UnitaryFieldData 2 3 K) {k : ℕ}
    {α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}
    (hα : α ^ 5 ^ k = 1) : α = 1 := by
  have hne : ¬(3 = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have : Finite K := h.finite
  have hσ := fieldFactor_pow_eq_one h (le_refl 3) hne hα
  have hring := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hdvd1 : orderOf (primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne α) ∣ 5 ^ k :=
    orderOf_dvd_of_pow_eq_one hσ
  have hdvd2 : orderOf (primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne α) ∣ 6 := by
    have := orderOf_dvd_natCard (primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne α)
    rwa [show Nat.card (K ≃+* K) = 6 from hring] at this
  have hcop : Nat.Coprime (5 ^ k) 6 := Nat.Coprime.pow_left k (by norm_num)
  have hσ1 : primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne α = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2)
  have hD : α ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hne]
    exact hσ1
  have hdvd3 : orderOf α ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hα
  have hdvd4 : orderOf α ∣ (2 ^ 3 + 1) * ((2 ^ 3) ^ 3 * ((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 3 + 1)) :=
    (Subgroup.orderOf_dvd_natCard _ hD).trans (card_primeFormD_three_dvd h)
  have hcop' : Nat.Coprime (5 ^ k)
      ((2 ^ 3 + 1) * ((2 ^ 3) ^ 3 * ((2 ^ 3) ^ 2 - 1) * ((2 ^ 3) ^ 3 + 1))) :=
    Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' hdvd3 hdvd4)

end Order

section Cell

variable {f n p r : ℕ} {K : Type} [Field K]

theorem fieldFactor_eq_one_of_cell (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ 2 ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr1 : r ∣ p ^ 2 + 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (Ē : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ζ γ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hE : CFSG.Open.IsElemAbelian p Ē) (hcard : Nat.card Ē = p ^ 4) (hζp : ζ ^ p = 1)
    (hζE : ∀ x ∈ Ē, ζ x = x) (hsolv : Group.IsSolvable ↥(autFix ζ))
    (hγ : ∃ k : ℕ, γ ^ r ^ k = 1) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hcomm : γ * ζ = ζ * γ)
    (hnt : ∃ x ∈ Ē, γ x ≠ x) :
    primeFormFieldFactor h isPrimeFormGram_one hn hne ζ = 1 := by
  by_contra hout
  have hpℓ : p ≠ 2 := hp2
  by_cases hq0 : n = 3 ∧ 2 ^ (f / p) = 2
  · by_cases hp3 : 3 < p
    · have hZ : ¬ p ∣ Nat.gcd n (2 ^ f + 1) := fun hdvd => by
        have h3 : p ∣ 3 := by
          have := hdvd.trans (Nat.gcd_dvd_left _ _)
          rwa [hq0.1] at this
        have := Nat.le_of_dvd (by norm_num) h3
        omega
      have hle := card_le_of_outer_exception h hn hne hp hp2 hpℓ hp3 hZ hζp hout hq0 Ē hζE
      rw [hcard] at hle
      have hp5 : 5 ≤ p := by
        by_contra hlt
        obtain rfl : p = 4 := by omega
        exact absurd hp (by norm_num)
      have : 5 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp5 4
      norm_num at this
      omega
    · obtain rfl : p = 3 := by have := hp.two_le; omega
      obtain ⟨σ, M, hσ, hpf, -⟩ := exists_descent h hn hne hp hp2 hpℓ hζp hout
      have hf : f / 3 = 1 := Nat.pow_right_injective (le_refl 2) (by simpa using hq0.2)
      obtain rfl : f = 3 := by omega
      obtain rfl : n = 3 := hq0.1
      have hr5 : r = 5 := by
        have h10 : r ∣ 10 := by simpa using hr1
        have h8 : ¬ r ∣ 8 := by simpa using hr2
        have hle : r ≤ 10 := Nat.le_of_dvd (by norm_num) h10
        interval_cases r <;> first | rfl | (exfalso; revert hr h10 h8; decide)
      subst hr5
      obtain ⟨k, hk⟩ := hγ
      have h1 := eq_one_of_pow_five_eq_one h hk
      obtain ⟨x, -, hx⟩ := hnt
      exact hx (by rw [h1]; rfl)
  · exact not_isSolvable_autFix_of_outer h hn hne hp hp2 hpℓ hζp hout hq0 hsolv

theorem zeta_mem_primeFormD (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ 2 ^ f = 2)) (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hr1 : r ∣ p ^ 2 + 1) (hr2 : ¬ r ∣ p ^ 2 - 1)
    (Ē : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ζ γ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hE : CFSG.Open.IsElemAbelian p Ē) (hcard : Nat.card Ē = p ^ 4) (hζp : ζ ^ p = 1)
    (hζE : ∀ x ∈ Ē, ζ x = x) (hsolv : Group.IsSolvable ↥(autFix ζ))
    (hγ : ∃ k : ℕ, γ ^ r ^ k = 1) (hγE : ∀ x ∈ Ē, γ x ∈ Ē) (hcomm : γ * ζ = ζ * γ)
    (hnt : ∃ x ∈ Ē, γ x ≠ x) :
    ζ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hne]
  exact fieldFactor_eq_one_of_cell h hn hne hp hp2 hr hr1 hr2 Ē ζ γ hE hcard hζp hζE hsolv hγ hγE
    hcomm hnt

end Cell

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellUni
