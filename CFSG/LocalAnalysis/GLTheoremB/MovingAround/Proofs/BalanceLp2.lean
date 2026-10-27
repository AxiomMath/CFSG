module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakModel
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceFromYS

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut localDeltaIn)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idScalarKernel)
open CFSG.HardMathSupport.Timmesfeld.LocalTwo (HeisP.commutant_scalar HeisP.coe_mul_eq_of_conj_eq)
open Matrix

section Groups

variable {G : Type*} [Group G]

theorem commutator_central_mul {a b c d : G} (hc : ∀ g, c * g = g * c) (hd : ∀ g, d * g = g * d) :
    (c * a) * (d * b) * (c * a)⁻¹ * (d * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc' : ∀ g, c * g * c⁻¹ = g := fun g => by rw [hc g, mul_inv_cancel_right]
  have hd' : ∀ g, d * g * d⁻¹ = g := fun g => by rw [hd g, mul_inv_cancel_right]
  calc (c * a) * (d * b) * (c * a)⁻¹ * (d * b)⁻¹
      = c * (a * (d * b) * a⁻¹) * c⁻¹ * (d * b)⁻¹ := by group
    _ = a * (d * b) * a⁻¹ * (d * b)⁻¹ := by rw [hc']
    _ = a * (d * (b * a⁻¹ * b⁻¹) * d⁻¹) := by group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [hd']
    _ = a * b * a⁻¹ * b⁻¹ := by group

end Groups

section HeisTwo

variable {K : Type} [Field K] {p : ℕ}

theorem pow_eq_one_of_conj_eq_scalar_mul (hp0 : 0 < p) {g A : GL (Fin p) K} {u c : Kˣ}
    (h : g * A * g⁻¹ = GeneralLinearGroup.scalar (Fin p) u * A) {n : ℕ}
    (hn : g ^ n = GeneralLinearGroup.scalar (Fin p) c) : u ^ n = 1 := by
  have h1 := BalanceFromYS.conj_pow_eq h (GeneralLinearGroup.scalar_commute u g).symm n
  rw [hn, GeneralLinearGroup.scalar_commute c A, mul_inv_cancel_right, ← map_pow] at h1
  have h2 : GeneralLinearGroup.scalar (Fin p) (u ^ n) * A = 1 * A := by rw [one_mul]; exact h1.symm
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.glScalar_injective hp0
    ((mul_right_cancel h2).trans (map_one _).symm)

theorem pow_eq_one_of_conj_eq_scalar_mul' (hp0 : 0 < p) {g A : GL (Fin p) K} {u a : Kˣ}
    (h : g * A * g⁻¹ = GeneralLinearGroup.scalar (Fin p) u * A)
    (ha : A ^ p = GeneralLinearGroup.scalar (Fin p) a) : u ^ p = 1 := by
  have e1 : (g * A * g⁻¹) ^ p = g * A ^ p * g⁻¹ := conj_pow
  have e2 : (GeneralLinearGroup.scalar (Fin p) u * A) ^ p =
      GeneralLinearGroup.scalar (Fin p) (u ^ p) * A ^ p := by
    rw [(show Commute (GeneralLinearGroup.scalar (Fin p) u) A from
      GeneralLinearGroup.scalar_commute u A).mul_pow, map_pow]
  rw [h, e2, ha, (GeneralLinearGroup.scalar_commute a g).symm, mul_inv_cancel_right] at e1
  have h2 : GeneralLinearGroup.scalar (Fin p) (u ^ p) * GeneralLinearGroup.scalar (Fin p) a =
      1 * GeneralLinearGroup.scalar (Fin p) a := by rw [one_mul]; exact e1
  exact CFSG.HardMathSupport.Timmesfeld.CrossChar.glScalar_injective hp0
    ((mul_right_cancel h2).trans (map_one _).symm)

theorem eq_scalar_of_heis_two (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {A B g : GL (Fin p) K}
    {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {a b u v c : Kˣ} {k : ℕ}
    (ha : A ^ p = GeneralLinearGroup.scalar (Fin p) a) (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b)
    (hgA : g * A * g⁻¹ = GeneralLinearGroup.scalar (Fin p) u * A)
    (hgB : g * B * g⁻¹ = GeneralLinearGroup.scalar (Fin p) v * B)
    (hg : g ^ (2 ^ k) = GeneralLinearGroup.scalar (Fin p) c) :
    ∃ d : Kˣ, g = GeneralLinearGroup.scalar (Fin p) d := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  have hcop : Nat.Coprime p (2 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have key : ∀ {X : GL (Fin p) K} {x y : Kˣ}, X ^ p = GeneralLinearGroup.scalar (Fin p) x →
      g * X * g⁻¹ = GeneralLinearGroup.scalar (Fin p) y * X → y = 1 := by
    intro X x y hX hgX
    have h1 := pow_eq_one_of_conj_eq_scalar_mul' hp0 hgX hX
    have h2 := pow_eq_one_of_conj_eq_scalar_mul hp0 hgX hg
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h2))
  obtain rfl := key ha hgA
  obtain rfl := key hb hgB
  rw [map_one, one_mul] at hgA hgB
  obtain ⟨c', hc'⟩ := HeisP.commutant_scalar hω hAB hpK (g : Matrix (Fin p) (Fin p) K)
    (HeisP.coe_mul_eq_of_conj_eq hgA) (HeisP.coe_mul_eq_of_conj_eq hgB)
  have hc0 : c' ≠ 0 := by
    rintro rfl
    have h1 := g.mul_inv
    rw [hc', map_zero, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨Units.mk0 c' hc0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, hc']
  rfl

theorem conjAut_eq_one_of_heis_two {F : Type} [Field F] [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) {A B : GL (Fin p) F} {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω)
    (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1) {g : GL (Fin p) F}
    (hgA : conjAut p F g * conjAut p F A = conjAut p F A * conjAut p F g)
    (hgB : conjAut p F g * conjAut p F B = conjAut p F B * conjAut p F g) {k : ℕ}
    (hg : conjAut p F g ^ (2 ^ k) = 1) : conjAut p F g = 1 := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hA
  obtain ⟨b, hb⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hB
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hg
  obtain ⟨u, hu⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_comm_scalar hn hgA
  obtain ⟨v, hv⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_comm_scalar hn hgB
  have hu' : g * A * g⁻¹ = GeneralLinearGroup.scalar (Fin p) u * A := by
    calc g * A * g⁻¹ = GeneralLinearGroup.scalar (Fin p) u * (A * g) * g⁻¹ := by rw [hu]
      _ = GeneralLinearGroup.scalar (Fin p) u * A := by group
  have hv' : g * B * g⁻¹ = GeneralLinearGroup.scalar (Fin p) v * B := by
    calc g * B * g⁻¹ = GeneralLinearGroup.scalar (Fin p) v * (B * g) * g⁻¹ := by rw [hv]
      _ = GeneralLinearGroup.scalar (Fin p) v * B := by group
  obtain ⟨d, rfl⟩ := eq_scalar_of_heis_two hp hp2 hpF hω hAB ha hb hu' hv' hc
  exact LinearFlag.conjAut_scalar d

variable {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K)

theorem exists_scalar_of_conjHom_eq_one (hn : 3 ≤ p) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    {X : primeFormUnitary h (idGram K p)} (hX : primeFormConjHom h (idGram K p) X = 1) :
    ∃ c : Kˣ, (X : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) c := by
  obtain ⟨c, -, hc⟩ :=
    (CFSG.RankThree.PartOne.KCUnitaryModel.primeFormConjHom_eq_one_iff_of_ne hn hne X).1 hX
  exact ⟨c, hc⟩

theorem conjHom_eq_one_of_heis_two (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (hpK : (p : K) ≠ 0) {A B : primeFormUnitary h (idGram K p)} {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : (A : GL (Fin p) K) * B * (A : GL (Fin p) K)⁻¹ * (B : GL (Fin p) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin p) ω)
    (hA : primeFormConjHom h (idGram K p) A ^ p = 1) (hB : primeFormConjHom h (idGram K p) B ^ p = 1)
    {g : primeFormUnitary h (idGram K p)}
    (hgA : primeFormConjHom h (idGram K p) g * primeFormConjHom h (idGram K p) A =
      primeFormConjHom h (idGram K p) A * primeFormConjHom h (idGram K p) g)
    (hgB : primeFormConjHom h (idGram K p) g * primeFormConjHom h (idGram K p) B =
      primeFormConjHom h (idGram K p) B * primeFormConjHom h (idGram K p) g) {k : ℕ}
    (hg : primeFormConjHom h (idGram K p) g ^ (2 ^ k) = 1) : primeFormConjHom h (idGram K p) g = 1 := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a, ha⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := A ^ p) (by rw [map_pow, hA])
  obtain ⟨b, hb⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := B ^ p) (by rw [map_pow, hB])
  obtain ⟨c, hc⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := g ^ (2 ^ k)) (by rw [map_pow, hg])
  obtain ⟨u, hu⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := g * A * g⁻¹ * A⁻¹)
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgA]; group)
  obtain ⟨v, hv⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := g * B * g⁻¹ * B⁻¹)
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgB]; group)
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv] at ha hb hc hu hv
  have hu' : (g : GL (Fin p) K) * A * (g : GL (Fin p) K)⁻¹ = GeneralLinearGroup.scalar (Fin p) u * A := by
    rw [← hu]; group
  have hv' : (g : GL (Fin p) K) * B * (g : GL (Fin p) K)⁻¹ = GeneralLinearGroup.scalar (Fin p) v * B := by
    rw [← hv]; group
  obtain ⟨d, hd⟩ := eq_scalar_of_heis_two hp hp2 hpK hω hAB ha hb hu' hv' hc
  exact CFSG.HardMathSupport.Solomon.Coordinator.primeFormConjHom_eq_one_of_scalar h hn hne hd

end HeisTwo

section Unitary

variable {K : Type} [Field K] {ℓ f : ℕ} (h : UnitaryFieldData ℓ f K) {p : ℕ}

include h in
theorem ringEquiv_eq_one_of_heis (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1) {ω : Kˣ}
    (hω : IsPrimitiveRoot ω p) {φ : K ≃+* K} (hφω : φ (ω : K) = ω) {k : ℕ} (hφ : φ ^ (2 ^ k) = 1) :
    φ = 1 := by
  classical
  have := h.finite
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic h.prime K h.card
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := h.one_le; omega)
  letI : Fintype (RingAut K) := Fintype.ofFinite _
  have hinj : Function.Injective h.bar := h.bar.injective
  let barE : K ≃+* K := RingEquiv.ofBijective h.bar ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hbarE : ∀ x, barE x = x ^ ℓ ^ f := fun x => h.bar_apply x
  have hbar2 : barE ^ 2 = 1 := by
    refine RingEquiv.ext fun x => ?_
    show barE (barE x) = x
    exact h.bar_bar x
  have hbar1 : barE ≠ 1 := by
    intro e
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    have h1 : barE c = c := congrArg (fun σ : RingAut K => σ c) e
    exact hc h1
  by_contra hφ1
  obtain ⟨i, hi, hφi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hφ)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hφ1 (orderOf_eq_one_iff.1 (by simpa using hφi))
  set ψ := φ ^ (2 ^ (i - 1)) with hψ
  have hψ2 : ψ ^ 2 = 1 := by
    rw [hψ, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi0), ← hφi,
      pow_orderOf_eq_one]
  have hψ1 : ψ ≠ 1 := pow_ne_one_of_lt_orderOf (by positivity)
    (by rw [hφi]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hψbar : ψ = barE := by
    by_contra hne
    have hle := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) two_pos
    have hsub : ({1, barE, ψ} : Finset (RingAut K)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl | rfl
      · exact one_pow 2
      · exact hbar2
      · exact hψ2
    have hcard3 : ({1, barE, ψ} : Finset (RingAut K)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hbar1, Ne.symm hψ1⟩
    have := Finset.card_le_card hsub
    omega
  have hpow : ∀ n : ℕ, (φ ^ n) (ω : K) = ω := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      show (φ ^ n) (φ (ω : K)) = ω
      rw [hφω, ih]
  have hbω : barE (ω : K) = ω := by rw [← hψbar, hψ]; exact hpow _
  rw [hbarE] at hbω
  have h2 : ω ^ (ℓ ^ f - 1) = 1 := by
    have hl : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    apply Units.ext
    have h3 : (ω : K) ^ (ℓ ^ f - 1) * ω = 1 * ω := by
      rw [← pow_succ, Nat.sub_add_cancel hl, one_mul, hbω]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ (Units.ne_zero ω) h3
  have h3 : p ∣ ℓ ^ f - 1 := hω.dvd_of_pow_eq_one _ h2
  have h4 : p ∣ 2 := by
    have h5 := Nat.dvd_sub hpq h3
    have hl : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    rwa [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at h5
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)

theorem glAut_scalar (φ : K ≃+* K) (n : ℕ) (c : Kˣ) :
    glAut φ (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.scalar (Fin n) (Units.map (φ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.scalar_apply, Matrix.diagonal_map (map_zero φ)]
  rfl

theorem mem_primeFormD_of_heis_two (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (hpq : p ∣ ℓ ^ f + 1) {A B : primeFormUnitary h (idGram K p)} {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : (A : GL (Fin p) K) * B * (A : GL (Fin p) K)⁻¹ * (B : GL (Fin p) K)⁻¹ =
      GeneralLinearGroup.scalar (Fin p) ω)
    {t : MulAut (primeFormP h (idGram K p))} (htA : t * primeFormConjHom h (idGram K p) A =
      primeFormConjHom h (idGram K p) A * t)
    (htB : t * primeFormConjHom h (idGram K p) B = primeFormConjHom h (idGram K p) B * t) {k : ℕ}
    (ht : t ^ (2 ^ k) = 1) : t ∈ primeFormD h (idGram K p) := by
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hp0 := hp.pos
  have hC : IsPrimeFormGram (1 : GL (Fin p) K) := isPrimeFormGram_one
  obtain ⟨φ, ⟨A', hA'⟩, -⟩ := existsUnique_primeFormFieldFactor h hC hn hne t
  have hΦt : primeFormFieldFactor h hC hn hne t = φ := by
    rw [hA']
    exact primeFormFieldFactor_apply h hC hn hne A' φ
  rw [← ker_primeFormFieldFactor h hC hn hne, MonoidHom.mem_ker, hΦt]
  refine ringEquiv_eq_one_of_heis h hp hp2 hpq hω ?_ (k := k) ?_
  ·
    have hconj : ∀ X : primeFormUnitary h (idGram K p),
        t * primeFormConjHom h (idGram K p) X * t⁻¹ =
          primeFormConjHom h (idGram K p) (A' * primeFormFieldU h hC φ X * A'⁻¹) := by
      intro X
      rw [hA', map_mul, map_mul, map_inv, ← primeFormField_conj_eq h hC φ X]
      group
    have hrel : ∀ {X : primeFormUnitary h (idGram K p)},
        t * primeFormConjHom h (idGram K p) X = primeFormConjHom h (idGram K p) X * t →
        ∃ u : Kˣ, ((A' * primeFormFieldU h hC φ X * A'⁻¹ : primeFormUnitary h (idGram K p)) :
          GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) u * X := by
      intro X hX
      have h1 : primeFormConjHom h (idGram K p) (A' * primeFormFieldU h hC φ X * A'⁻¹ * X⁻¹) = 1 := by
        rw [map_mul, map_inv, ← hconj X, hX]
        group
      obtain ⟨u, hu⟩ := exists_scalar_of_conjHom_eq_one h hn hne h1
      refine ⟨u, ?_⟩
      rw [← hu]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    obtain ⟨u, hu⟩ := hrel htA
    obtain ⟨v, hv⟩ := hrel htB
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hu hv
    have e1 : ((A' * primeFormFieldU h hC φ A * A'⁻¹) * (A' * primeFormFieldU h hC φ B * A'⁻¹) *
        (A' * primeFormFieldU h hC φ A * A'⁻¹)⁻¹ * (A' * primeFormFieldU h hC φ B * A'⁻¹)⁻¹ :
          primeFormUnitary h (idGram K p)) =
        A' * primeFormFieldU h hC φ (A * B * A⁻¹ * B⁻¹) * A'⁻¹ := by
      simp only [map_mul, map_inv]
      group
    have e2 := congrArg (fun X : primeFormUnitary h (idGram K p) => (X : GL (Fin p) K)) e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
    rw [hu, hv, commutator_central_mul (fun g => GeneralLinearGroup.scalar_commute u g)
      (fun g => GeneralLinearGroup.scalar_commute v g), hAB, coe_primeFormFieldU] at e2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e2
    rw [hAB, glAut_scalar, ← GeneralLinearGroup.scalar_commute _ _, mul_inv_cancel_right] at e2
    have e3 := CFSG.HardMathSupport.Timmesfeld.CrossChar.glScalar_injective hp0 e2
    have e4 := congrArg Units.val e3
    simpa using e4.symm
  · rw [← hΦt, ← map_pow, ht, map_one]

theorem localDeltaTwoIn_eq_bot_unitary_heis (hp : p.Prime) (hp2 : p ≠ 2) (hne : ¬(p = 3 ∧ ℓ ^ f = 2))
    (hpq : p ∣ ℓ ^ f + 1) {A B : primeFormUnitary h (idGram K p)} (hAB : A * B ≠ B * A)
    (hA : primeFormConjHom h (idGram K p) A ^ p = 1) (hB : primeFormConjHom h (idGram K p) B ^ p = 1)
    (hcomm : primeFormConjHom h (idGram K p) A * primeFormConjHom h (idGram K p) B =
      primeFormConjHom h (idGram K p) B * primeFormConjHom h (idGram K p) A)
    (hA1 : primeFormConjHom h (idGram K p) A ≠ 1) (hB1 : primeFormConjHom h (idGram K p) B ≠ 1)
    (H : Subgroup (MulAut (primeFormP h (idGram K p)))) :
    localDeltaTwoIn H (Subgroup.closure {primeFormConjHom h (idGram K p) A,
      primeFormConjHom h (idGram K p) B}) = ⊥ := by
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite (primeFormP h (idGram K p)) := CFSG.RankThree.PartOne.KCUnitaryModel.finite_primeFormP
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hpℓ : ¬ p ∣ ℓ := by
    intro hd
    have h1 : p ∣ ℓ ^ f := hd.trans (dvd_pow_self ℓ (by have := h.one_le; omega))
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 hpq))
  have hpK : ((p : ℕ) : K) ≠ 0 := by
    refine CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp ?_
    rw [h.card]
    exact fun hd => hpℓ (hp.dvd_of_dvd_pow hd)
  obtain ⟨z, hz⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := A * B * A⁻¹ * B⁻¹)
    (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]; group)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hz
  obtain ⟨b, hb⟩ := exists_scalar_of_conjHom_eq_one h hn hne (X := B ^ p) (by rw [map_pow, hB])
  simp only [Subgroup.coe_pow] at hb
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hAB
    apply Subtype.ext
    rw [map_one] at hz
    simp only [Subgroup.coe_mul]
    calc (A : GL (Fin p) K) * B = (A * B * (A : GL (Fin p) K)⁻¹ * (B : GL (Fin p) K)⁻¹) * (B * A) := by
          group
      _ = B * A := by rw [hz, one_mul]
  have hzp : z ^ p = 1 :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.comm_scalar_pow_eq_one hn
      (A := (A : GL (Fin p) K)) (B := (B : GL (Fin p) K))
      (by rw [← hz]; group) hb
  have hω : IsPrimitiveRoot z p := by
    have := orderOf_eq_prime hzp hz1
    rw [← this]
    exact IsPrimitiveRoot.orderOf z
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have hmem : ∀ d ∈ Subgroup.closure ({primeFormConjHom h (idGram K p) A,
      primeFormConjHom h (idGram K p) B} : Set (MulAut (primeFormP h (idGram K p)))), d ≠ 1 →
      t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (primeFormP h (idGram K p))))) := by
    intro d hd hd1
    unfold localDeltaTwoIn at ht
    simp only [Subgroup.mem_iInf] at ht
    exact ht d hd hd1
  have htA := hmem _ (Subgroup.subset_closure (by simp)) hA1
  have htB := hmem _ (Subgroup.subset_closure (by simp)) hB1
  have hcA : t * primeFormConjHom h (idGram K p) A = primeFormConjHom h (idGram K p) A * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ htA).2
  have hcB : t * primeFormConjHom h (idGram K p) B = primeFormConjHom h (idGram K p) B * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ htB).2
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨t, htA⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨g, rfl⟩ := mem_primeFormD_of_heis_two h hp hp2 hne hpq hω hz hcA hcB hk'
  exact conjHom_eq_one_of_heis_two h hp hp2 hne hpK hω hz hA hB hcA hcB hk'

end Unitary

section Poly

open Polynomial

variable {K : Type} [Field K] {p : ℕ}

theorem geom_sum_eq_zero_of_pow {x : K} (hx : x ^ p = 1) (hx1 : x ≠ 1) :
    ∑ k ∈ Finset.range p, x ^ k = 0 := by
  have h := geom_sum_mul x p
  rw [hx, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hx1)

@[expose] noncomputable def conjLin : GL (Fin p) K →* Module.End K (Matrix (Fin p) (Fin p) K) where
  toFun g := (LinearMap.mulLeft K (g : Matrix (Fin p) (Fin p) K)).comp
    (LinearMap.mulRight K ((g⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))
  map_one' := by
    ext X : 1
    simp
  map_mul' g h := by
    ext X : 1
    simp [Matrix.mul_assoc]

theorem conjLin_apply (g : GL (Fin p) K) (X : Matrix (Fin p) (Fin p) K) :
    conjLin g X = (g : Matrix (Fin p) (Fin p) K) * X * ((g⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  simp [conjLin, Matrix.mul_assoc]

theorem conjLin_mul (g : GL (Fin p) K) (X Y : Matrix (Fin p) (Fin p) K) :
    conjLin g (X * Y) = conjLin g X * conjLin g Y := by
  simp only [conjLin_apply, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K), ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem conjLin_one (g : GL (Fin p) K) : conjLin g 1 = 1 := by
  rw [conjLin_apply, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjLin_pow_apply (g : GL (Fin p) K) (X : Matrix (Fin p) (Fin p) K) (n : ℕ) :
    conjLin g (X ^ n) = conjLin g X ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, conjLin_one]
  | succ n ih => rw [pow_succ, conjLin_mul, ih, pow_succ]

theorem conjLin_scalar (c : Kˣ) : conjLin (GeneralLinearGroup.scalar (Fin p) c) = 1 := by
  ext X : 1
  rw [conjLin_apply, Module.End.one_apply, GeneralLinearGroup.coe_scalar, ← map_inv,
    GeneralLinearGroup.coe_scalar, (Matrix.scalar_commute (c : K) (fun r => Commute.all _ r) X).eq,
    Matrix.mul_assoc, ← map_mul, Units.mul_inv, map_one, Matrix.mul_one]

variable {A B : GL (Fin p) K} {ω : Kˣ}

theorem conjLin_A_pow (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (i : ℕ) :
    conjLin B ((A : Matrix (Fin p) (Fin p) K) ^ i) = ((ω : K)⁻¹ ^ i) • (A : Matrix (Fin p) (Fin p) K) ^ i := by
  have h1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.rel_B_zpow hAB (i : ℤ)
  simp only [zpow_natCast] at h1
  have h2 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K)) h1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Units.val_inv_eq_inv_val] at h2
  rw [conjLin_apply, h2, ← Matrix.smul_eq_diagonal_mul]

theorem conjLin_pow_A_pow (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (k i : ℕ) :
    (conjLin B ^ k) ((A : Matrix (Fin p) (Fin p) K) ^ i) =
      (((ω : K)⁻¹ ^ i) ^ k) • (A : Matrix (Fin p) (Fin p) K) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show conjLin B ^ (k + 1) = conjLin B * conjLin B ^ k from pow_succ' _ _, Module.End.mul_apply, ih,
      map_smul, conjLin_A_pow hAB, smul_smul, pow_succ, mul_comm]

theorem conjLin_pow_eq_one {b : Kˣ} (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b) :
    conjLin B ^ p = 1 := by
  rw [← map_pow, hb, conjLin_scalar]

@[expose] noncomputable def fourier (B : GL (Fin p) K) (ζ : K) : Module.End K (Matrix (Fin p) (Fin p) K) :=
  ∑ k ∈ Finset.range p, ζ ^ k • conjLin B ^ k

theorem conjLin_mul_fourier {b : Kˣ} (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b) {ζ : K}
    (hζ : ζ ^ p = 1) (hζ0 : ζ ≠ 0) : conjLin B * fourier B ζ = ζ⁻¹ • fourier B ζ := by
  set x := ζ • conjLin B with hx
  have hF : fourier B ζ = ∑ k ∈ Finset.range p, x ^ k := by
    simp only [fourier, hx, _root_.smul_pow]
  have h1 : (x - 1) * fourier B ζ = 0 := by
    rw [hF, mul_geom_sum, hx, _root_.smul_pow, hζ, one_smul, conjLin_pow_eq_one hb, sub_self]
  have h2 : ζ • (conjLin B * fourier B ζ) = fourier B ζ := by
    rw [sub_mul, one_mul, sub_eq_zero, hx, smul_mul_assoc] at h1
    exact h1
  calc conjLin B * fourier B ζ = (ζ⁻¹ * ζ) • (conjLin B * fourier B ζ) := by
        rw [inv_mul_cancel₀ hζ0, one_smul]
    _ = ζ⁻¹ • (ζ • (conjLin B * fourier B ζ)) := by rw [smul_smul]
    _ = ζ⁻¹ • fourier B ζ := by rw [h2]

theorem sum_fourier (hp0 : 0 < p) (hω : IsPrimitiveRoot (ω : K) p) :
    ∑ j ∈ Finset.range p, fourier B ((ω : K) ^ j) = (p : K) • 1 := by
  simp only [fourier]
  rw [Finset.sum_comm, Finset.sum_eq_single 0]
  · rw [Nat.cast_smul_eq_nsmul]
    simp
  · intro k hk hk0
    rw [← Finset.sum_smul]
    have h1 : ∑ j ∈ Finset.range p, ((ω : K) ^ j) ^ k = ∑ j ∈ Finset.range p, ((ω : K) ^ k) ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul, ← pow_mul, mul_comm]
    have h2 : ((ω : K) ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have h3 : (ω : K) ^ k ≠ 1 := fun h =>
      hk0 (Nat.eq_zero_of_dvd_of_lt ((hω.pow_eq_one_iff_dvd k).1 h) (Finset.mem_range.1 hk))
    rw [h1, geom_sum_eq_zero_of_pow h2 h3, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hp0) h

theorem fourier_A_pow (hω : IsPrimitiveRoot (ω : K) p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {i j : ℕ} (hi : i < p) (hj : j < p) :
    fourier B ((ω : K) ^ j) ((A : Matrix (Fin p) (Fin p) K) ^ i) =
      (if i = j then (p : K) else 0) • (A : Matrix (Fin p) (Fin p) K) ^ i := by
  simp only [fourier, LinearMap.sum_apply, LinearMap.smul_apply, conjLin_pow_A_pow hAB, smul_smul,
    ← Finset.sum_smul]
  congr 1
  have e : ∀ k, ((ω : K) ^ j) ^ k * ((ω : K)⁻¹ ^ i) ^ k = ((ω : K) ^ j * (ω : K)⁻¹ ^ i) ^ k :=
    fun k => (mul_pow _ _ _).symm
  simp_rw [e]
  have hω0 : (ω : K) ≠ 0 := Units.ne_zero ω
  split_ifs with hij
  · subst hij
    rw [← mul_pow, mul_inv_cancel₀ hω0, one_pow]
    simp
  · apply geom_sum_eq_zero_of_pow
    · rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j p, mul_comm i p, pow_mul, pow_mul, hω.pow_eq_one, inv_pow,
        hω.pow_eq_one, one_pow, inv_one, one_pow, one_mul]
    · intro h1
      apply hij
      have h2 : (ω : K) ^ j = (ω : K) ^ i := by
        rw [inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hω0)] at h1
        exact h1
      exact (hω.pow_inj hj hi h2).symm

theorem linearIndependent_pow_of_heis (hp0 : 0 < p) (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0) :
    LinearIndependent K (fun i : Fin p => (A : Matrix (Fin p) (Fin p) K) ^ (i : ℕ)) := by
  haveI : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
  have hω' : IsPrimitiveRoot (ω : K) p := IsPrimitiveRoot.coe_units_iff.2 hω
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 := congrArg (fourier B ((ω : K) ^ (j : ℕ))) hc
  rw [map_zero, map_sum] at h1
  have h2 : ∀ i : Fin p, fourier B ((ω : K) ^ (j : ℕ)) (c i • (A : Matrix (Fin p) (Fin p) K) ^ (i : ℕ)) =
      (if i = j then c i * p else 0) • (A : Matrix (Fin p) (Fin p) K) ^ (i : ℕ) := by
    intro i
    rw [map_smul, fourier_A_pow hω' hAB i.2 j.2, smul_smul]
    by_cases hij : i = j
    · rw [if_pos (congrArg Fin.val hij), if_pos hij]
    · rw [if_neg (fun h => hij (Fin.ext h)), if_neg hij, mul_zero]
  simp only [h2] at h1
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [if_neg hij, zero_smul]) (by simp), if_pos rfl] at h1
  have hAj : (A : Matrix (Fin p) (Fin p) K) ^ (j : ℕ) ≠ 0 := by
    rw [← Units.val_pow_eq_pow_val]
    exact Units.ne_zero _
  rcases smul_eq_zero.1 h1 with h3 | h3
  · exact (mul_eq_zero.1 h3).resolve_right hpK
  · exact absurd h3 hAj

theorem eq_smul_pow_of_eigen (hp0 : 0 < p) (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0)
    {Y : Matrix (Fin p) (Fin p) K} (hYA : Y * A = A * Y) {j : ℕ}
    (hY : conjLin B Y = ((ω : K) ^ j)⁻¹ • Y) : ∃ d : K, Y = d • (A : Matrix (Fin p) (Fin p) K) ^ j := by
  haveI : NeZero p := ⟨hp0.ne'⟩
  set Ai := ((A⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) with hAi
  have hAiA : Ai * (A : Matrix (Fin p) (Fin p) K) = 1 := by
    rw [hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAAi : (A : Matrix (Fin p) (Fin p) K) * Ai = 1 := by
    rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hTAi : conjLin B Ai = (ω : K) • Ai := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.rel_BA hAB
    have h2 : B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω * A⁻¹ := by
      have e : B * A⁻¹ * B⁻¹ = (B * A * B⁻¹)⁻¹ := by group
      rw [e, h1, _root_.mul_inv_rev, ← map_inv, inv_inv, ← GeneralLinearGroup.scalar_commute ω A⁻¹]
    have h3 := congrArg (fun g : GL (Fin p) K => (g : Matrix (Fin p) (Fin p) K)) h2
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h3
    rw [hAi, conjLin_apply, h3, ← Matrix.smul_eq_diagonal_mul]
  set Z := Y * Ai ^ j with hZ
  have hTZ : conjLin B Z = Z := by
    rw [hZ, conjLin_mul, hY, conjLin_pow_apply, hTAi, _root_.smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero ω)), one_smul]
  have hZB : Z * (B : Matrix (Fin p) (Fin p) K) = (B : Matrix (Fin p) (Fin p) K) * Z := by
    have h1 := hTZ
    rw [conjLin_apply] at h1
    calc Z * (B : Matrix (Fin p) (Fin p) K)
        = ((B : Matrix (Fin p) (Fin p) K) * Z * ((B⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) *
            (B : Matrix (Fin p) (Fin p) K) := by rw [h1]
      _ = (B : Matrix (Fin p) (Fin p) K) * Z := by
          rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  have hAiA' : Ai * (A : Matrix (Fin p) (Fin p) K) = (A : Matrix (Fin p) (Fin p) K) * Ai := by
    rw [hAiA, hAAi]
  have hZA : Z * (A : Matrix (Fin p) (Fin p) K) = (A : Matrix (Fin p) (Fin p) K) * Z := by
    rw [hZ, Matrix.mul_assoc, (Commute.pow_left hAiA' j).eq, ← Matrix.mul_assoc, hYA, Matrix.mul_assoc]
  obtain ⟨d, hd⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.commutant_scalar hω hAB hpK Z hZA hZB
  refine ⟨d, ?_⟩
  have hYZ : Y = Z * (A : Matrix (Fin p) (Fin p) K) ^ j := by
    rw [hZ, Matrix.mul_assoc, ← (show Commute Ai (A : Matrix (Fin p) (Fin p) K) from hAiA').mul_pow, hAiA,
      one_pow, Matrix.mul_one]
  rw [hYZ, hd, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem exists_aeval_of_commute (hp0 : 0 < p) (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0) {b : Kˣ}
    (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b) {v : Matrix (Fin p) (Fin p) K}
    (hv : v * A = A * v) : ∃ P : K[X], v = aeval (A : Matrix (Fin p) (Fin p) K) P := by
  have hω' : IsPrimitiveRoot (ω : K) p := IsPrimitiveRoot.coe_units_iff.2 hω
  have hω0 : (ω : K) ≠ 0 := Units.ne_zero ω
  have hTkA : ∀ k : ℕ, (conjLin B ^ k) (A : Matrix (Fin p) (Fin p) K) =
      ((ω : K)⁻¹ ^ k) • (A : Matrix (Fin p) (Fin p) K) := fun k => by
    simpa using conjLin_pow_A_pow hAB k 1
  have hTk : ∀ k : ℕ, (conjLin B ^ k) v * A = A * (conjLin B ^ k) v := by
    intro k
    have h1 : (conjLin B ^ k) (v * A) = (conjLin B ^ k) (A * v) := by rw [hv]
    rw [← map_pow, conjLin_mul, conjLin_mul, map_pow, hTkA, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ (pow_ne_zero k (inv_ne_zero hω0)) h1
  have hcomp : ∀ j : ℕ, ∃ d : K, fourier B ((ω : K) ^ j) v = d • (A : Matrix (Fin p) (Fin p) K) ^ j := by
    intro j
    apply eq_smul_pow_of_eigen hp0 hω hAB hpK
    · simp only [fourier, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_mul, Finset.mul_sum,
        Matrix.smul_mul, Matrix.mul_smul, hTk]
    · rw [← Module.End.mul_apply, conjLin_mul_fourier hb (by rw [← pow_mul, mul_comm, pow_mul,
        hω'.pow_eq_one, one_pow]) (pow_ne_zero _ hω0)]
      rfl
  choose d hd using hcomp
  have hsum := congrArg (fun T : Module.End K (Matrix (Fin p) (Fin p) K) => T v) (sum_fourier (B := B) hp0 hω')
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.one_apply, hd] at hsum
  refine ⟨∑ j ∈ Finset.range p, C (d j / p) * X ^ j, ?_⟩
  have hv' : v = (p : K)⁻¹ • ∑ j ∈ Finset.range p, d j • (A : Matrix (Fin p) (Fin p) K) ^ j := by
    rw [hsum, smul_smul, inv_mul_cancel₀ hpK, one_smul]
  rw [hv', Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, map_mul, aeval_C, aeval_X_pow, ← Algebra.smul_def, div_eq_inv_mul]

theorem eq_zero_of_aeval_eq_zero_of_lt {M : Matrix (Fin p) (Fin p) K}
    (hind : LinearIndependent K (fun i : Fin p => M ^ (i : ℕ))) {g : K[X]} (hg : g.natDegree < p)
    (h0 : aeval M g = 0) : g = 0 := by
  have hsum : aeval M g = ∑ i : Fin p, g.coeff i • M ^ (i : ℕ) := by
    conv_lhs => rw [g.as_sum_range' p hg]
    rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => aeval M (monomial i (g.coeff i))) p]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [aeval_monomial, Algebra.smul_def]
  rw [hsum] at h0
  have hc := Fintype.linearIndependent_iff.1 hind _ h0
  ext n
  by_cases hn : n < p
  · simpa using hc ⟨n, hn⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]

theorem det_eq_of_pow_eq_scalar (hp : p.Prime) (hp2 : p ≠ 2) (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0) {μ : Kˣ}
    (hμ : A ^ p = GeneralLinearGroup.scalar (Fin p) μ) : (A : Matrix (Fin p) (Fin p) K).det = μ := by
  have hind := linearIndependent_pow_of_heis hp.pos hω hAB hpK
  have hM : (A : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) (μ : K) := by
    have := congrArg Units.val hμ
    rwa [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at this
  have hchar : (A : Matrix (Fin p) (Fin p) K).charpoly = X ^ p - C (μ : K) := by
    by_contra hne
    have hmon1 := (A : Matrix (Fin p) (Fin p) K).charpoly_monic
    have hmon2 : (X ^ p - C (μ : K)).Monic := monic_X_pow_sub_C _ hp.ne_zero
    have hdeg1 : (A : Matrix (Fin p) (Fin p) K).charpoly.natDegree = p := by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hdeg2 : (X ^ p - C (μ : K)).natDegree = p := natDegree_X_pow_sub_C
    have hg0 : (A : Matrix (Fin p) (Fin p) K).charpoly - (X ^ p - C (μ : K)) ≠ 0 := sub_ne_zero.2 hne
    have hlt : ((A : Matrix (Fin p) (Fin p) K).charpoly - (X ^ p - C (μ : K))).natDegree < p := by
      have h1 := degree_sub_lt (p := (A : Matrix (Fin p) (Fin p) K).charpoly) (q := X ^ p - C (μ : K))
        (by rw [degree_eq_natDegree hmon1.ne_zero, degree_eq_natDegree hmon2.ne_zero, hdeg1, hdeg2])
        hmon1.ne_zero (by rw [hmon1.leadingCoeff, hmon2.leadingCoeff])
      rw [degree_eq_natDegree hmon1.ne_zero, hdeg1] at h1
      exact (natDegree_lt_iff_degree_lt hg0).2 h1
    apply hg0
    apply eq_zero_of_aeval_eq_zero_of_lt hind hlt
    rw [map_sub, Matrix.aeval_self_charpoly, map_sub, map_pow, aeval_X, aeval_C, hM, zero_sub, neg_eq_zero,
      sub_eq_zero, Matrix.algebraMap_eq_diagonal]
    rfl
  rw [Matrix.det_eq_sign_charpoly_coeff, hchar, Fintype.card_fin, coeff_sub, coeff_X_pow, coeff_C_zero,
    if_neg hp.ne_zero.symm, zero_sub, Odd.neg_one_pow (hp.odd_of_ne_two hp2)]
  ring

theorem isUnit_det_scalar_add {M : Matrix (Fin p) (Fin p) K} {μ : K}
    (hM : M ^ p = Matrix.scalar (Fin p) μ) (hμ : ∀ c : K, c ^ p ≠ μ) (a : K) :
    IsUnit (Matrix.scalar (Fin p) a + M).det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hsc : ∀ c : K, (Matrix.scalar (Fin p) c).mulVec v = c • v := fun c => by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h1 : M.mulVec v = (-a) • v := by
    rw [Matrix.add_mulVec, hsc] at hv
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
    exact hv
  have h2 : ∀ n : ℕ, (M ^ n).mulVec v = (-a) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h3 := h2 p
  rw [hM, hsc] at h3
  have h4 : (μ - (-a) ^ p) • v = 0 := by rw [sub_smul, h3, sub_self]
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact hμ (-a) (sub_eq_zero.1 h5).symm
  · exact hv0 h5

theorem aeval_conj_unit (u : GL (Fin p) K) (M : Matrix (Fin p) (Fin p) K) (P : K[X]) :
    aeval ((u : Matrix (Fin p) (Fin p) K) * M * ((u⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) P =
      (u : Matrix (Fin p) (Fin p) K) * aeval M P * ((u⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, Matrix.mul_add, Matrix.add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, Units.conj_pow,
      Matrix.mul_smul, Matrix.smul_mul]

theorem odd_geom_sum {Q n : ℕ} (hn : Odd n) : Odd (∑ i ∈ Finset.range n, Q ^ i) := by
  rcases Nat.even_or_odd Q with hQ | hQ
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.pos; omega⟩
    rw [Finset.sum_range_succ', pow_zero]
    exact Even.add_one (Finset.even_sum _ fun i _ => hQ.pow_of_ne_zero (by omega))
  · rw [Nat.odd_iff, Finset.sum_nat_mod, Finset.sum_congr rfl fun i _ => by
      rw [Nat.pow_mod, Nat.odd_iff.1 hQ, one_pow]]
    simp [Nat.odd_iff.1 hn]

end Poly



section Outer

open Polynomial

variable {F : Type} [Field F] [Finite F] {p : ℕ}

theorem units_pow_facts (hp : p.Prime) (hpF : p ∣ Nat.card F - 1) {μ : Fˣ} (hμ : ∀ c : Fˣ, c ^ p ≠ μ) :
    μ ^ ((Nat.card F - 1) / p) ≠ 1 ∧ ∀ d : Fˣ, ∃ (i : ℕ) (c : Fˣ), d = μ ^ i * c ^ p := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hN : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  set N := Nat.card F - 1 with hNdef
  set m := N / p with hmdef
  have hog : orderOf g = N := by
    rw [← hN]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hNm : N = p * m := (Nat.mul_div_cancel' hpF).symm
  have hN0 : 0 < N := by rw [← hN]; exact Nat.card_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hNm; omega
  have hpow : ∀ x : Fˣ, ∃ u : ℕ, g ^ u = x := fun x =>
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg x))
  have crit : ∀ x : Fˣ, x ^ m = 1 → ∃ c : Fˣ, c ^ p = x := by
    intro x hx
    obtain ⟨u, rfl⟩ := hpow x
    have h1 : orderOf g ∣ u * m := orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hx)
    rw [hog, hNm, mul_comm u m, mul_comm p m] at h1
    obtain ⟨u', rfl⟩ := Nat.dvd_of_mul_dvd_mul_left hm0 h1
    exact ⟨g ^ u', by rw [← pow_mul, mul_comm]⟩
  have h1 : μ ^ m ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := crit μ h
    exact hμ c hc
  refine ⟨h1, fun d => ?_⟩
  have hcardp : ∀ x : Fˣ, (x ^ m) ^ p = 1 := fun x => by
    rw [← pow_mul, mul_comm, ← hNm, ← hN, pow_card_eq_one']
  have hζ : IsPrimitiveRoot (((μ ^ m : Fˣ)) : F) p := by
    rw [IsPrimitiveRoot.coe_units_iff]
    have := orderOf_eq_prime (hcardp μ) h1
    rw [← this]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((d ^ m : Fˣ) : F))
    (by rw [← Units.val_pow_eq_pow_val, hcardp, Units.val_one])
  have hi' : (μ ^ m) ^ i = d ^ m := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi)
  obtain ⟨c, hc⟩ := crit (d * (μ ^ i)⁻¹) (by
    rw [mul_pow, inv_pow, ← pow_mul, mul_comm i, pow_mul, hi', mul_inv_cancel])
  exact ⟨i, c, by rw [hc, mul_comm d, mul_inv_cancel_left]⟩

theorem finite_projectiveSL : Finite (projectiveSL p F) :=
  Finite.of_surjective (proj p F) (proj_surjective p F)

theorem exists_odd_conjAut_pow_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {μ b : Fˣ}
    (hμ : A ^ p = GeneralLinearGroup.scalar (Fin p) μ) (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b)
    (hζ : μ ^ ((Nat.card F - 1) / p) ≠ 1) {v : GL (Fin p) F} (hv : v * A = A * v) :
    ∃ m : ℕ, Odd m ∧ conjAut p F (v ^ m) = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  have hQF : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  have hQ1 : 1 ≤ Nat.card F := Nat.card_pos
  have hpQ : ¬ p ∣ Nat.card F := fun hd => by
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpQ
  have hcardU : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hQs : Nat.card F = p * ((Nat.card F - 1) / p) + 1 := by
    rw [Nat.mul_div_cancel' hpF]
    omega
  have hAQ : A ^ Nat.card F =
      GeneralLinearGroup.scalar (Fin p) (μ ^ ((Nat.card F - 1) / p)) * A := by
    conv_lhs => rw [hQs]
    rw [pow_succ, pow_mul, hμ, ← map_pow, (GeneralLinearGroup.scalar_commute _ A)]
  have hζp : (μ ^ ((Nat.card F - 1) / p)) ^ p = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hpF, ← hcardU, pow_card_eq_one']
  have hω' : IsPrimitiveRoot ((ω⁻¹ : Fˣ) : F) p := IsPrimitiveRoot.coe_units_iff.2 hω.inv
  obtain ⟨k, hkp, hk⟩ := hω'.eq_pow_of_pow_eq_one (ξ := ((μ ^ ((Nat.card F - 1) / p) : Fˣ) : F))
    (by rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one])
  have hk' : ω⁻¹ ^ k = μ ^ ((Nat.card F - 1) / p) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hζ (by rw [← hk', pow_zero])
  have hBk : B ^ k * A * (B ^ k)⁻¹ = A ^ Nat.card F := by
    rw [CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.conjB_pow_A hAB k, hk', hAQ]
  have hfrob : ∀ P : F[X], aeval (A : Matrix (Fin p) (Fin p) F) P ^ Nat.card F =
      ((B ^ k : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * aeval (A : Matrix (Fin p) (Fin p) F) P *
        (((B ^ k)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    intro P
    have hmat : ((B ^ k : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (A : Matrix (Fin p) (Fin p) F) *
        (((B ^ k)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = (A : Matrix (Fin p) (Fin p) F) ^ Nat.card F := by
      have := congrArg Units.val hBk
      rwa [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at this
    rw [← aeval_conj_unit, hmat, ← map_pow, ← hQF, ← FiniteField.expand_card, Polynomial.expand_aeval]
  obtain ⟨P, hP⟩ := exists_aeval_of_commute hp0 hω hAB hpK hb (v := (v : Matrix (Fin p) (Fin p) F))
    (by have := congrArg Units.val hv; simpa only [Units.val_mul] using this)
  have hvn : ∀ n : ℕ, ((v ^ n : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      aeval (A : Matrix (Fin p) (Fin p) F) (P ^ n) := fun n => by
    rw [Units.val_pow_eq_pow_val, hP, map_pow]
  have hfrobv : ∀ n : ℕ, (v ^ n) ^ Nat.card F = B ^ k * v ^ n * (B ^ k)⁻¹ := fun n => by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hvn, hfrob, Units.val_mul, Units.val_mul, hvn]
  have hiter : ∀ n j : ℕ, (v ^ n) ^ (Nat.card F ^ j) = B ^ (k * j) * v ^ n * (B ^ (k * j))⁻¹ := by
    intro n j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_mul, ih, conj_pow, hfrobv n, mul_add, mul_one, pow_add]
      group
  have hvQp : v ^ (Nat.card F ^ p) = v := by
    have h1 := hiter 1 p
    rw [pow_one, mul_comm k p, pow_mul, hb, ← map_pow] at h1
    rw [h1, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  have hQp1 : 1 ≤ Nat.card F ^ p := Nat.one_le_pow _ _ hQ1
  have hvord : v ^ (Nat.card F ^ p - 1) = 1 := by
    have h1 : v ^ (Nat.card F ^ p - 1) * v = 1 * v := by
      rw [← pow_succ, Nat.sub_add_cancel hQp1, hvQp, one_mul]
    exact mul_right_cancel h1
  have hmQ : (∑ i ∈ Finset.range p, Nat.card F ^ i) * Nat.card F + 1 =
      (∑ i ∈ Finset.range p, Nat.card F ^ i) + Nat.card F ^ p := by
    rw [Finset.sum_mul, ← Finset.sum_range_succ, Finset.sum_range_succ']
    simp [pow_succ]
  have hN : (v ^ (∑ i ∈ Finset.range p, Nat.card F ^ i)) ^ Nat.card F =
      v ^ (∑ i ∈ Finset.range p, Nat.card F ^ i) := by
    rw [← pow_mul, show (∑ i ∈ Finset.range p, Nat.card F ^ i) * Nat.card F =
      (∑ i ∈ Finset.range p, Nat.card F ^ i) + (Nat.card F ^ p - 1) by omega, pow_add, hvord, mul_one]
  set m := ∑ i ∈ Finset.range p, Nat.card F ^ i with hm
  have hNB : v ^ m * B ^ k = B ^ k * v ^ m := by
    have h1 := hfrobv m
    rw [hN] at h1
    calc v ^ m * B ^ k = (B ^ k * v ^ m * (B ^ k)⁻¹) * B ^ k := by rw [← h1]
      _ = B ^ k * v ^ m := by group
  have hkcop : Nat.Coprime k p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hkp))
  obtain ⟨k', -, hk''⟩ := Nat.exists_mul_mod_eq_one_of_coprime hkcop hp.one_lt
  obtain ⟨q, hq⟩ : ∃ q, k * k' = 1 + p * q := ⟨k * k' / p, by rw [← hk'', Nat.mod_add_div]⟩
  have hBkk : (B ^ k) ^ k' = B * GeneralLinearGroup.scalar (Fin p) (b ^ q) := by
    rw [← pow_mul, hq, pow_add, pow_one, pow_mul, hb, ← map_pow]
  have hNB1 : v ^ m * B = B * v ^ m := by
    have h1 : Commute (v ^ m) ((B ^ k) ^ k') := (show Commute (v ^ m) (B ^ k) from hNB).pow_right k'
    rw [hBkk] at h1
    have h2 : Commute (v ^ m) (GeneralLinearGroup.scalar (Fin p) (b ^ q)) :=
      (GeneralLinearGroup.scalar_commute _ _).symm
    have h3 := h1.mul_right h2.inv_right
    rw [mul_inv_cancel_right] at h3
    exact h3
  have hNA : ((v ^ m : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * A =
      A * ((v ^ m : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    have h1 : v ^ m * A = A * v ^ m := ((show Commute v A from hv).pow_left m).eq
    simpa only [Units.val_mul] using congrArg Units.val h1
  have hNB' : ((v ^ m : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * B =
      B * ((v ^ m : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    simpa only [Units.val_mul] using congrArg Units.val hNB1
  obtain ⟨c', hc'⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.HeisP.commutant_scalar hω hAB hpK _ hNA hNB'
  have hc0 : c' ≠ 0 := by
    rintro rfl
    have h1 := (v ^ m).mul_inv
    rw [hc', map_zero, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨m, odd_geom_sum (hp.odd_of_ne_two hp2), ?_⟩
  have hvm : v ^ m = GeneralLinearGroup.scalar (Fin p) (Units.mk0 c' hc0) := by
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar, hc']
    rfl
  rw [hvm]
  exact LinearFlag.conjAut_scalar _

theorem commute_conjAut_of_outer (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} {ω : Fˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) ω) {μ b : Fˣ}
    (hμ : A ^ p = GeneralLinearGroup.scalar (Fin p) μ) (hb : B ^ p = GeneralLinearGroup.scalar (Fin p) b)
    (hμp : ∀ c : Fˣ, c ^ p ≠ μ) {H : Subgroup (MulAut (projectiveSL p F))}
    (hH : innerAut (projectiveSL p F) ≤ H) {t : MulAut (projectiveSL p F)}
    (ht : t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))))
    (Θ : GL (Fin p) F →* GL (Fin p) F) (hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g))
    (hΘA : ∀ w, w * A = A * w → Θ w * A = A * Θ w) {w : GL (Fin p) F} (hw : w * A = A * w) :
    t * conjAut p F w = conjAut p F w * t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (projectiveSL p F) := finite_projectiveSL
  have hpQ : ¬ p ∣ Nat.card F := fun hd => by
    have hQ1 : 1 ≤ Nat.card F := Nat.card_pos
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpQ
  have hdetA : GeneralLinearGroup.det A = μ :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact det_eq_of_pow_eq_scalar hp hp2 hω hAB hpK hμ)
  obtain ⟨hζ, hdec⟩ := units_pow_facts hp hpF hμp
  obtain ⟨i, c, hdc⟩ := hdec (GeneralLinearGroup.det w)
  set w₀ := w * (A ^ i)⁻¹ with hw₀
  have hdet₀ : GeneralLinearGroup.det w₀ = c ^ p := by
    rw [hw₀, map_mul, map_inv, map_pow, hdc, hdetA, mul_comm (μ ^ i), mul_inv_cancel_right]
  have hw₀inn : conjAut p F w₀ ∈ innerAut (projectiveSL p F) := conjAut_mem_range_conj_of_det_eq_pow hdet₀
  have hw₀A : w₀ * A = A * w₀ :=
    ((show Commute w A from hw).mul_left ((Commute.refl A).pow_left i).inv_left).eq
  have hw₀C : conjAut p F w₀ ∈ H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F))) :=
    ⟨hH hw₀inn, Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hw₀A])⟩
  have hcO : t * conjAut p F w₀ * t⁻¹ * (conjAut p F w₀)⁻¹ ∈
      pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))) := by
    have h1 : conjAut p F w₀ * t⁻¹ * (conjAut p F w₀)⁻¹ ∈
        pCoreOf 2 (H ⊓ Subgroup.centralizer ({conjAut p F A} : Set (MulAut (projectiveSL p F)))) :=
      (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hw₀C) t⁻¹).1
        (Subgroup.inv_mem _ ht)
    have := Subgroup.mul_mem _ ht h1
    simpa [mul_assoc] using this
  have hcv : t * conjAut p F w₀ * t⁻¹ * (conjAut p F w₀)⁻¹ = conjAut p F (Θ w₀ * w₀⁻¹) := by
    rw [hΘ, ← map_inv, ← map_mul]
  rw [hcv] at hcO
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨_, hcO⟩
  have hj' : conjAut p F (Θ w₀ * w₀⁻¹) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hvA : (Θ w₀ * w₀⁻¹) * A = A * (Θ w₀ * w₀⁻¹) :=
    ((show Commute (Θ w₀) A from hΘA w₀ hw₀A).mul_left (show Commute w₀ A from hw₀A).inv_left).eq
  obtain ⟨m, hm, hm1⟩ := exists_odd_conjAut_pow_eq_one hp hp2 hpF hω hAB hμ hb hζ hvA
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have hv1 : conjAut p F (Θ w₀ * w₀⁻¹) = 1 := by
    rw [map_pow] at hm1
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj')
      (orderOf_dvd_of_pow_eq_one hm1))
  have htw₀ : t * conjAut p F w₀ = conjAut p F w₀ * t := by
    rw [← hcv, mul_inv_eq_one] at hv1
    calc t * conjAut p F w₀ = t * conjAut p F w₀ * t⁻¹ * t := by group
      _ = conjAut p F w₀ * t := by rw [hv1]
  have htA : t * conjAut p F A = conjAut p F A * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ ht).2
  have hww : w = w₀ * A ^ i := by rw [hw₀]; group
  rw [hww, map_mul, map_pow]
  exact ((show Commute t (conjAut p F w₀) from htw₀).mul_right
    ((show Commute t (conjAut p F A) from htA).pow_right i)).eq

theorem lin_three {A : Matrix (Fin p) (Fin p) F}
    (hind : LinearIndependent F (fun i : Fin p => A ^ (i : ℕ))) (hp3 : 3 ≤ p) {s t u : F}
    (h : s • A ^ 0 + t • A ^ 1 + u • A ^ 2 = 0) : s = 0 ∧ t = 0 ∧ u = 0 := by
  have h3 := hind.comp (fun j : Fin 3 => (⟨j, by omega⟩ : Fin p))
    (fun i j hij => by simpa [Fin.ext_iff] using hij)
  have := Fintype.linearIndependent_iff.1 h3 ![s, t, u] (by simpa [Fin.sum_univ_three] using h)
  exact ⟨this 0, this 1, this 2⟩

theorem coe_map_GL (σ : F →+* F) (g : GL (Fin p) F) :
    ((GeneralLinearGroup.map σ g : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      (g : Matrix (Fin p) (Fin p) F).map σ := by
  ext i j
  rfl

theorem localDeltaTwoIn_eq_bot_linear_outer (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {A B : GL (Fin p) F} (hAB : A * B ≠ B * A) (hA : conjAut p F A ^ p = 1) (hB : conjAut p F B ^ p = 1)
    (hcomm : conjAut p F A * conjAut p F B = conjAut p F B * conjAut p F A) (hA1 : conjAut p F A ≠ 1)
    (hB1 : conjAut p F B ≠ 1) (hout : conjAut p F A ∉ innerAut (projectiveSL p F))
    {H : Subgroup (MulAut (projectiveSL p F))} (hH : innerAut (projectiveSL p F) ≤ H) :
    localDeltaTwoIn H (Subgroup.closure {conjAut p F A, conjAut p F B}) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have : Finite (projectiveSL p F) := finite_projectiveSL
  have hn : 3 ≤ p := by have := hp.two_le; omega
  have hp0 := hp.pos
  have hpQ : ¬ p ∣ Nat.card F := fun hd => by
    have hQ1 : 1 ≤ Nat.card F := Nat.card_pos
    have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hd hpF
    rw [show Nat.card F - (Nat.card F - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hpK : (p : F) ≠ 0 := CFSG.RankThree.PartOne.CTP.natCast_ne_zero_of_not_dvd_card hp hpQ
  obtain ⟨z, hz⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_comm_scalar hn hcomm
  have hzrel : A * B * A⁻¹ * B⁻¹ = GeneralLinearGroup.scalar (Fin p) z := by
    rw [hz]
    group
  obtain ⟨b, hb⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hB
  obtain ⟨μ, hμ⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.exists_pow_scalar hn hA
  have hzp : z ^ p = 1 := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.comm_scalar_pow_eq_one hn hz hb
  have hz1 : z ≠ 1 := fun e => hAB (by rw [hz, e, map_one, one_mul])
  have hω : IsPrimitiveRoot z p := by
    have := orderOf_eq_prime hzp hz1
    rw [← this]
    exact IsPrimitiveRoot.orderOf z
  have hdetA : GeneralLinearGroup.det A = μ :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply]; exact det_eq_of_pow_eq_scalar hp hp2 hω hzrel hpK hμ)
  have hμp : ∀ c : Fˣ, c ^ p ≠ μ := fun c hc =>
    hout (conjAut_mem_range_conj_of_det_eq_pow (by rw [hdetA, hc]))
  have hindA := linearIndependent_pow_of_heis hp0 hω hzrel hpK
  have hM : (A : Matrix (Fin p) (Fin p) F) ^ p = Matrix.scalar (Fin p) (μ : F) := by
    have := congrArg Units.val hμ
    rwa [Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar] at this
  have hμK : ∀ c : F, c ^ p ≠ (μ : F) := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hc
      exact Units.ne_zero μ hc.symm
    exact hμp (Units.mk0 c hc0) (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc]))
  let wa : F → GL (Fin p) F := fun a =>
    Matrix.nonsingInvUnit (Matrix.scalar (Fin p) a + (A : Matrix (Fin p) (Fin p) F))
      (isUnit_det_scalar_add hM hμK a)
  have hwa : ∀ a, ((wa a : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      Matrix.scalar (Fin p) a + (A : Matrix (Fin p) (Fin p) F) := fun a => rfl
  have hwaA : ∀ a, wa a * A = A * wa a := by
    intro a
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hwa, Matrix.add_mul, Matrix.mul_add,
      (Matrix.scalar_commute a (fun r => Commute.all _ r) (A : Matrix (Fin p) (Fin p) F)).eq]
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  have hmem : ∀ d ∈ Subgroup.closure ({conjAut p F A, conjAut p F B} : Set (MulAut (projectiveSL p F))),
      d ≠ 1 → t ∈ pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (projectiveSL p F)))) := by
    intro d hd hd1
    unfold localDeltaTwoIn at ht
    simp only [Subgroup.mem_iInf] at ht
    exact ht d hd hd1
  have htA := hmem _ (Subgroup.subset_closure (by simp)) hA1
  have htB := hmem _ (Subgroup.subset_closure (by simp)) hB1
  have hcA : t * conjAut p F A = conjAut p F A * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ htA).2
  have hcB : t * conjAut p F B = conjAut p F B * t :=
    Subgroup.mem_centralizer_singleton_iff.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ htB).2
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _ ⟨t, htA⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hmult : ∀ (Θ : GL (Fin p) F →* GL (Fin p) F), (∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g)) →
      ∀ {w : GL (Fin p) F}, t * conjAut p F w = conjAut p F w * t →
        ∃ l : Fˣ, Θ w = GeneralLinearGroup.scalar (Fin p) l * w := by
    intro Θ hΘ w hw
    have h1 : conjAut p F (Θ w * w⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hΘ, hw, mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨l, hl⟩ := CFSG.HardMathSupport.Timmesfeld.LocalTwo.Heis.eq_scalar_of_conjAut_eq_one hn h1
    exact ⟨l, by rw [hl, inv_mul_cancel_right]⟩
  have hpres : ∀ (Θ : GL (Fin p) F →* GL (Fin p) F) (l : Fˣ),
      Θ A = GeneralLinearGroup.scalar (Fin p) l * A → ∀ w, w * A = A * w → Θ w * A = A * Θ w := by
    intro Θ l hl w hw
    have h1 : Θ w * Θ A = Θ A * Θ w := by rw [← map_mul, ← map_mul, hw]
    rw [hl] at h1
    have h2 : GeneralLinearGroup.scalar (Fin p) l * (Θ w * A) =
        GeneralLinearGroup.scalar (Fin p) l * (A * Θ w) := by
      calc GeneralLinearGroup.scalar (Fin p) l * (Θ w * A)
          = Θ w * (GeneralLinearGroup.scalar (Fin p) l * A) := by
            rw [← mul_assoc, GeneralLinearGroup.scalar_commute l (Θ w), mul_assoc]
        _ = GeneralLinearGroup.scalar (Fin p) l * A * Θ w := h1
        _ = GeneralLinearGroup.scalar (Fin p) l * (A * Θ w) := mul_assoc _ _ _
    exact mul_left_cancel h2
  have htrans := standard_automorphism_transport (K := F) (n := p)
  obtain ⟨A', σ, ε, hε, hteq⟩ := (automorphism_generation (K := F) hn).2 t
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hteq
    let Θ : GL (Fin p) F →* GL (Fin p) F :=
      (MulAut.conj A').toMonoidHom.comp (GeneralLinearGroup.map (σ : F →+* F))
    have hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g) := by
      intro g
      have h1 := htrans.2.2.1 σ g
      rw [hteq]
      calc conjAut p F A' * fieldAut p F σ * conjAut p F g * (conjAut p F A' * fieldAut p F σ)⁻¹
          = conjAut p F A' * (fieldAut p F σ * conjAut p F g * (fieldAut p F σ)⁻¹) *
              (conjAut p F A')⁻¹ := by group
        _ = conjAut p F (Θ g) := by
          rw [h1, ← map_inv, ← map_mul, ← map_mul]
          rfl
    obtain ⟨l, hl⟩ := hmult Θ hΘ hcA
    have hcomm' := fun w (hw : w * A = A * w) =>
      commute_conjAut_of_outer hp hp2 hpF hω hzrel hμ hb hμp hH htA Θ hΘ (hpres Θ l hl) hw
    have hΘmat : ∀ g : GL (Fin p) F, ((Θ g : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        (A' : Matrix (Fin p) (Fin p) F) * (g : Matrix (Fin p) (Fin p) F).map σ *
          ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      intro g
      show ((A' * GeneralLinearGroup.map (σ : F →+* F) g * A'⁻¹ : GL (Fin p) F) :
        Matrix (Fin p) (Fin p) F) = _
      rw [Units.val_mul, Units.val_mul, coe_map_GL]
      rfl
    have hconj1 : (A' : Matrix (Fin p) (Fin p) F) * ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hscal : ∀ c : F, Matrix.scalar (Fin p) c = c • (1 : Matrix (Fin p) (Fin p) F) := fun c => by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have key : ∀ a : F, ∃ ν : F, σ a = ν * a ∧ (l : F) = ν := by
      intro a
      obtain ⟨ν, hν⟩ := hmult Θ hΘ (hcomm' _ (hwaA a))
      refine ⟨(ν : F), ?_⟩
      have h1 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) hν
      have h2 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) hl
      rw [hΘmat, hwa, Units.val_mul, GeneralLinearGroup.coe_scalar, hwa, Matrix.map_add _ (map_add σ), Matrix.mul_add,
        Matrix.add_mul] at h1
      rw [hΘmat, Units.val_mul, GeneralLinearGroup.coe_scalar] at h2
      rw [h2] at h1
      have hsc : ∀ c : F, (A' : Matrix (Fin p) (Fin p) F) * (Matrix.scalar (Fin p) c).map σ *
          ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = Matrix.scalar (Fin p) (σ c) := by
        intro c
        rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ), ← Matrix.scalar_apply,
          (Matrix.scalar_commute (σ c) (fun r => Commute.all _ r) (A' : Matrix (Fin p) (Fin p) F)).symm.eq,
          Matrix.mul_assoc, hconj1, Matrix.mul_one]
      rw [hsc] at h1
      simp only [hscal, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul] at h1
      have h3 : (σ a - (ν : F) * a) • (A : Matrix (Fin p) (Fin p) F) ^ 0 +
          ((l : F) - ν) • (A : Matrix (Fin p) (Fin p) F) ^ 1 +
            (0 : F) • (A : Matrix (Fin p) (Fin p) F) ^ 2 = 0 := by
        have e : (σ a - (ν : F) * a) • (A : Matrix (Fin p) (Fin p) F) ^ 0 +
            ((l : F) - ν) • (A : Matrix (Fin p) (Fin p) F) ^ 1 +
              (0 : F) • (A : Matrix (Fin p) (Fin p) F) ^ 2 =
            (σ a • (1 : Matrix (Fin p) (Fin p) F) + (l : F) • (A : Matrix (Fin p) (Fin p) F)) -
              (((ν : F) * a) • (1 : Matrix (Fin p) (Fin p) F) + (ν : F) • (A : Matrix (Fin p) (Fin p) F)) := by
          simp only [pow_zero, pow_one, zero_smul, add_zero, sub_smul]
          abel
        rw [e, h1, sub_self]
      obtain ⟨h4, h5, -⟩ := lin_three hindA hn h3
      exact ⟨by linear_combination h4, by linear_combination h5⟩
    have hσ : σ = 1 := by
      refine RingEquiv.ext fun a => ?_
      obtain ⟨ν₁, h11, h12⟩ := key 1
      obtain ⟨νa, ha1, ha2⟩ := key a
      rw [map_one, mul_one] at h11
      show σ a = a
      rw [ha1, ← ha2, h12, ← h11, one_mul]
    rw [hσ, map_one, mul_one] at hteq
    rw [hteq] at hcA hcB hk' ⊢
    exact conjAut_eq_one_of_heis_two hp hp2 hpK hω hzrel hA hB hcA hcB hk'
  ·
    exfalso
    rw [pow_one] at hteq
    have hδinv : (dualAut p F)⁻¹ = dualAut p F := inv_eq_of_mul_eq_one_right htrans.2.2.2.1
    let Θ : GL (Fin p) F →* GL (Fin p) F :=
      (MulAut.conj A').toMonoidHom.comp ((GeneralLinearGroup.map (σ : F →+* F)).comp
        GeneralLinearGroup.inverseTranspose.toMonoidHom)
    have hΘ : ∀ g, t * conjAut p F g * t⁻¹ = conjAut p F (Θ g) := by
      intro g
      have h1 := htrans.2.2.2.2.1 g
      have h2 := htrans.2.2.1 σ (GeneralLinearGroup.inverseTranspose g)
      rw [hteq]
      calc conjAut p F A' * fieldAut p F σ * dualAut p F * conjAut p F g *
            (conjAut p F A' * fieldAut p F σ * dualAut p F)⁻¹
          = conjAut p F A' * (fieldAut p F σ * (dualAut p F * conjAut p F g * (dualAut p F)⁻¹) *
              (fieldAut p F σ)⁻¹) * (conjAut p F A')⁻¹ := by group
        _ = conjAut p F (Θ g) := by
          rw [hδinv, h1, h2, ← map_inv, ← map_mul, ← map_mul]
          rfl
    obtain ⟨l, hl⟩ := hmult Θ hΘ hcA
    have hcomm' := fun w (hw : w * A = A * w) =>
      commute_conjAut_of_outer hp hp2 hpF hω hzrel hμ hb hμp hH htA Θ hΘ (hpres Θ l hl) hw
    obtain ⟨ν, hν⟩ := hmult Θ hΘ (hcomm' _ (hwaA 1))
    have hΘinv : ∀ g : GL (Fin p) F, ((Θ g⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
        (A' : Matrix (Fin p) (Fin p) F) * ((g : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
          ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      intro g
      show ((A' * GeneralLinearGroup.map (σ : F →+* F) (GeneralLinearGroup.inverseTranspose g⁻¹) * A'⁻¹ :
        GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = _
      rw [Units.val_mul, Units.val_mul, coe_map_GL, GeneralLinearGroup.coe_inverseTranspose, inv_inv,
        Matrix.transpose_map]
      rfl
    have hconj1 : (A' : Matrix (Fin p) (Fin p) F) * ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hscR : ∀ (c : F) (X : Matrix (Fin p) (Fin p) F), X * Matrix.scalar (Fin p) c = c • X := fun c X => by
      rw [← (Matrix.scalar_commute c (fun r => Commute.all _ r) X).eq, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    have hAiM : ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (A : Matrix (Fin p) (Fin p) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hWiW : (((wa 1)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
        ((wa 1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hW1 : ((wa 1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 + (A : Matrix (Fin p) (Fin p) F) := by
      rw [hwa, map_one]
    have hRA : (A' : Matrix (Fin p) (Fin p) F) * ((A : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
        ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
          ((l⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [← hΘinv A, map_inv, hl, _root_.mul_inv_rev, ← map_inv, Units.val_mul, GeneralLinearGroup.coe_scalar,
        hscR]
    have hRW : (A' : Matrix (Fin p) (Fin p) F) * (((wa 1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
        ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
          ((ν⁻¹ : Fˣ) : F) • (((wa 1)⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [← hΘinv (wa 1), map_inv, hν, _root_.mul_inv_rev, ← map_inv, Units.val_mul, GeneralLinearGroup.coe_scalar,
        hscR]
    have hRW' : (A' : Matrix (Fin p) (Fin p) F) * (((wa 1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map σ)ᵀ *
        ((A'⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
          1 + ((l⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      rw [hW1, Matrix.map_add _ (map_add σ), Matrix.map_one (⇑σ) (map_zero σ) (map_one σ), Matrix.transpose_add,
        Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hconj1, hRA]
    rw [hRW'] at hRW
    have h5 : (1 + ((l⁻¹ : Fˣ) : F) • ((A⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) *
        ((wa 1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = ((ν⁻¹ : Fˣ) : F) • (1 : Matrix (Fin p) (Fin p) F) := by
      rw [hRW, Matrix.smul_mul, hWiW]
    rw [hW1, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, hAiM] at h5
    have h6 := congrArg (· * (A : Matrix (Fin p) (Fin p) F)) h5
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hAiM] at h6
    have h7 : ((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) ^ 0 +
        (1 + ((l⁻¹ : Fˣ) : F) - ((ν⁻¹ : Fˣ) : F)) • (A : Matrix (Fin p) (Fin p) F) ^ 1 +
          (1 : F) • (A : Matrix (Fin p) (Fin p) F) ^ 2 = 0 := by
      have e : ((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) ^ 0 +
          (1 + ((l⁻¹ : Fˣ) : F) - ((ν⁻¹ : Fˣ) : F)) • (A : Matrix (Fin p) (Fin p) F) ^ 1 +
            (1 : F) • (A : Matrix (Fin p) (Fin p) F) ^ 2 =
          ((A : Matrix (Fin p) (Fin p) F) + (A : Matrix (Fin p) (Fin p) F) * (A : Matrix (Fin p) (Fin p) F) +
            (((l⁻¹ : Fˣ) : F) • (1 : Matrix (Fin p) (Fin p) F) +
              ((l⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F))) -
            ((ν⁻¹ : Fˣ) : F) • (A : Matrix (Fin p) (Fin p) F) := by
        simp only [pow_zero, pow_one, pow_two, one_smul, sub_smul, add_smul]
        abel
      rw [e, h6, sub_self]
    obtain ⟨-, -, h8⟩ := lin_three hindA hn h7
    exact one_ne_zero h8

end Outer

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp
