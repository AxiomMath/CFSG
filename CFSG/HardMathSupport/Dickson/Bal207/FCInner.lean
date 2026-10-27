module

public import CFSG.HardMathSupport.Dickson.Bal207.FCStepC
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Timmesfeld.LinearRank

open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

@[expose] def conjAut {S B : Subgroup G} (h : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B) :
    S →* MulAut B where
  toFun s :=
    { toFun := fun b => ⟨(s : G) * b * (s : G)⁻¹, h s s.2 b b.2⟩
      invFun := fun b => ⟨(s : G)⁻¹ * b * s, by
        have := h _ (S.inv_mem s.2) b b.2
        rwa [inv_inv] at this⟩
      left_inv := fun b => Subtype.ext (by dsimp only; group)
      right_inv := fun b => Subtype.ext (by dsimp only; group)
      map_mul' := fun b b' => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  map_one' := MulEquiv.ext fun b => Subtype.ext (by
    show ((1 : S) : G) * b * ((1 : S) : G)⁻¹ = b
    rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])
  map_mul' s s' := MulEquiv.ext fun b => Subtype.ext (by
    show ((s * s' : S) : G) * b * ((s * s' : S) : G)⁻¹ = s * (s' * b * (s' : G)⁻¹) * (s : G)⁻¹
    rw [Subgroup.coe_mul]
    group)

theorem exists_invariant_sylow [Finite G] {p : ℕ} [Fact p.Prime] {S R : Subgroup G}
    (hS : IsPGroup p S) (hR : Nat.Coprime p (Nat.card R))
    (hSR : ∀ s ∈ S, ∀ r ∈ R, s * r * s⁻¹ ∈ R) (q : ℕ) [Fact q.Prime] :
    ∃ P : Subgroup G, P ≤ R ∧ IsPGroup q P ∧ Nat.card P = q ^ (Nat.card R).factorization q ∧
      ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
  classical
  let _ : MulAction S (Sylow q R) := MulAction.compHom _ (conjAut hSR)
  have h2 : ¬p ∣ Nat.card (Sylow q R) := by
    obtain ⟨P⟩ : Nonempty (Sylow q R) := inferInstance
    intro h
    have h1 := (Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card (P : Subgroup R))
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hR (h.trans h1)
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q R) h2
  refine ⟨(P : Subgroup R).map R.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map R.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective, Sylow.card_eq_multiplicity]
  · rintro s hs _ ⟨y, hy, rfl⟩
    have hfix : (⟨s, hs⟩ : S) • P = P := hP ⟨s, hs⟩
    have hmem : conjAut hSR ⟨s, hs⟩ y ∈ (((⟨s, hs⟩ : S) • P : Sylow q R) : Subgroup R) := by
      show conjAut hSR ⟨s, hs⟩ y ∈ conjAut hSR ⟨s, hs⟩ • (P : Subgroup R)
      exact Subgroup.smul_mem_pointwise_smul y _ _ hy
    rw [hfix] at hmem
    exact ⟨_, hmem, rfl⟩

theorem commute_of_pow_eq_one {x y : G} (hz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center G) {s m : ℕ}
    (hsm : Nat.Coprime s m) (hzm : (x * y * x⁻¹ * y⁻¹) ^ m = 1) (hxs : x ^ s = 1) :
    x * y = y * x := by
  have hzj : ∀ j : ℕ, ∀ g : G, (x * y * x⁻¹ * y⁻¹) ^ j * g = g * (x * y * x⁻¹ * y⁻¹) ^ j :=
    fun j g => (Subgroup.mem_center_iff.1 ((Subgroup.center G).pow_mem hz j) g).symm
  have key : ∀ j : ℕ, x ^ j * y * (x ^ j)⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ j * y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc x ^ (j + 1) * y * (x ^ (j + 1))⁻¹ = x * (x ^ j * y * (x ^ j)⁻¹) * x⁻¹ := by group
        _ = x * ((x * y * x⁻¹ * y⁻¹) ^ j * y) * x⁻¹ := by rw [ih]
        _ = (x * y * x⁻¹ * y⁻¹) ^ j * (x * y * x⁻¹) := by
          rw [← mul_assoc x, ← hzj j x]
          group
        _ = (x * y * x⁻¹ * y⁻¹) ^ (j + 1) * y := by rw [pow_succ]; group
  have hzs : (x * y * x⁻¹ * y⁻¹) ^ s = 1 := by
    have h1 := key s
    rw [hxs, one_mul, inv_one, mul_one] at h1
    have h2 : (x * y * x⁻¹ * y⁻¹) ^ s * y = 1 * y := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  have hz1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have h3 := (pow_gcd_eq_one (a := x * y * x⁻¹ * y⁻¹) (m := s) (n := m)).2 ⟨hzs, hzm⟩
    rwa [hsm, pow_one] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [hz1, one_mul]

@[expose] def powOneSubgroup (T : Subgroup G) (s : ℕ)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x ^ s = 1 → x * y = y * x) : Subgroup G where
  carrier := {g | g ∈ T ∧ g ^ s = 1}
  mul_mem' {a b} ha hb := ⟨T.mul_mem ha.1 hb.1, by
    rw [Commute.mul_pow (hc a ha.1 b hb.1 ha.2), ha.2, hb.2, one_mul]⟩
  one_mem' := ⟨T.one_mem, one_pow s⟩
  inv_mem' {a} ha := ⟨T.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem mem_powOneSubgroup {T : Subgroup G} {s : ℕ}
    {hc : ∀ x ∈ T, ∀ y ∈ T, x ^ s = 1 → x * y = y * x} {g : G} :
    g ∈ powOneSubgroup T s hc ↔ g ∈ T ∧ g ^ s = 1 :=
  Iff.rfl

end Generic

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

abbrev oneGram (K : Type) [Field K] (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem one_le_of_unitary (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k) :
    1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : 0 < ℓ ^ f := pow_pos h.prime.pos f
    rw [pow_zero] at hq
    omega
  · exact hk

theorem IsFullDiag.entry_cube {D : Subgroup (GL (Fin n) K)} (hD : IsFullDiag D)
    {d : GL (Fin n) K} (hd : d ∈ D) (i : Fin n) : (d : Matrix (Fin n) (Fin n) K) i i ^ 3 = 1 := by
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) (hD.cube d hd)
  simp only [Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h1
  rwa [pow_apply_diag (hD.diag d hd)] at h1

theorem IsFullDiag.mem_unitary (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    {D : Subgroup (GL (Fin n) K)} (hD : IsFullDiag D) {d : GL (Fin n) K} (hd : d ∈ D) :
    d ∈ primeFormUnitary h (oneGram K n) := by
  have hk := one_le_of_unitary h hq
  change ((d : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * oneGram K n * d = oneGram K n
  rw [oneGram, Units.val_one, Matrix.mul_one]
  ext i j
  rw [mul_diag_apply (hD.diag d hd), transpose_apply, map_apply, one_apply]
  split_ifs with hij
  · subst hij
    have h3 := hD.entry_cube hd i
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [h.bar_apply, ← pow_succ, hq, pow_succ', pow_mul, h3, one_pow]
  · rw [hD.diag d hd (Ne.symm hij), map_zero, zero_mul]

theorem pow_eq_one_of_center (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    (hn : 1 ≤ n) {z : GL (Fin n) K} (hz : z ∈ Subgroup.center (GL (Fin n) K))
    (hzU : z ∈ primeFormUnitary h (oneGram K n)) : z ^ (3 ^ k) = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, rfl⟩ := hz
  have hN := norm_eq_one_of_scalar_mem_primeFormUnitary h hn 1 hzU
  have hc : c ^ (3 ^ k) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hq, pow_succ, ← h.bar_apply, mul_comm]
    exact hN)
  rw [← map_pow, hc, map_one]

theorem eq_bot_of_le_primeFormD (h : UnitaryFieldData ℓ f K) {k : ℕ} (hq : ℓ ^ f + 1 = 3 ^ k)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) {D : Subgroup (GL (Fin n) K)} (hD : IsFullDiag D)
    {Q : Subgroup (MulAut (primeFormP h (oneGram K n)))} (hQD : Q ≤ primeFormD h (oneGram K n))
    (hQ3 : Nat.Coprime 3 (Nat.card Q))
    (hDQ : ∀ A : primeFormUnitary h (oneGram K n), (A : GL (Fin n) K) ∈ D → ∀ σ ∈ Q,
      primeFormConjHom h _ A * σ * (primeFormConjHom h _ A)⁻¹ ∈ Q) : Q = ⊥ := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (Matrix (Fin n) (Fin n) K) := inferInstanceAs (Finite (Fin n → Fin n → K))
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (Units.val : GL (Fin n) K → Matrix (Fin n) (Fin n) K)
      fun _ _ hab => Units.ext hab
  haveI : Finite (MulAut (primeFormP h (oneGram K n))) :=
    Finite.of_injective (fun e : MulAut (primeFormP h (oneGram K n)) =>
      (e : primeFormP h (oneGram K n) → primeFormP h (oneGram K n)))
      fun _ _ hab => MulEquiv.ext (congrFun hab)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn1 : 1 ≤ n := by omega
  have hk := one_le_of_unitary h hq
  by_contra hQ
  obtain ⟨r, hr, hrQ⟩ := Nat.exists_prime_and_dvd fun h1 => hQ (Subgroup.eq_bot_of_card_eq Q h1)
  haveI : Fact r.Prime := ⟨hr⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hQ3 hrQ
  set Dc : Subgroup (MulAut (primeFormP h (oneGram K n))) :=
    (D.comap (primeFormUnitary h (oneGram K n)).subtype).map
      (primeFormConjHom h (oneGram K n))
    with hDc
  have hDc3 : IsPGroup 3 Dc := by
    rintro ⟨_, A, hA, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show primeFormConjHom h (oneGram K n) A ^ 3 ^ 1 = 1
    have hA3 : A ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hD.cube _ hA)
    rw [pow_one, ← map_pow, hA3, map_one]
  have hDcQ : ∀ s ∈ Dc, ∀ σ ∈ Q, s * σ * s⁻¹ ∈ Q := by
    rintro _ ⟨A, hA, rfl⟩ σ hσ
    exact hDQ A hA σ hσ
  obtain ⟨S, hSQ, hSr, hScard, hSD⟩ := exists_invariant_sylow hDc3 hQ3 hDcQ r
  have hS1 : 1 < Nat.card S := by
    rw [hScard]
    exact Nat.one_lt_pow (Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrQ).ne'
      hr.one_lt
  haveI : Nontrivial S := Finite.one_lt_card_iff_nontrivial.1 hS1
  haveI := hSr.center_nontrivial
  obtain ⟨z₀, hz₀⟩ := exists_ne (1 : Subgroup.center S)
  set Z : Subgroup (MulAut (primeFormP h (oneGram K n))) :=
    S ⊓ Subgroup.centralizer (S : Set (MulAut (primeFormP h (oneGram K n)))) with hZ
  have hz₀Z : ((z₀ : S) : MulAut (primeFormP h (oneGram K n))) ∈ Z := by
    refine Subgroup.mem_inf.2 ⟨(z₀ : S).2, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    have := Subgroup.mem_center_iff.1 z₀.2 ⟨τ, hτ⟩
    exact congrArg Subtype.val this
  have hz₀1 : ((z₀ : S) : MulAut (primeFormP h (oneGram K n))) ≠ 1 := by
    intro h1
    apply hz₀
    exact Subtype.ext (Subtype.ext h1)
  have hZc : ∀ σ ∈ Z, ∀ τ ∈ Z, σ * τ = τ * σ := fun σ hσ τ hτ =>
    (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hτ).2 σ (Subgroup.mem_inf.1 hσ).1)
  have hZD : ∀ s ∈ Dc, ∀ σ ∈ Z, s * σ * s⁻¹ ∈ Z := by
    intro s hs σ hσ
    obtain ⟨hσS, hσC⟩ := Subgroup.mem_inf.1 hσ
    refine Subgroup.mem_inf.2 ⟨hSD s hs σ hσS, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    have hτ' : s⁻¹ * τ * s⁻¹⁻¹ ∈ S := hSD s⁻¹ (Dc.inv_mem hs) τ hτ
    have hcomm := Subgroup.mem_centralizer_iff.1 hσC _ hτ'
    calc τ * (s * σ * s⁻¹) = s * ((s⁻¹ * τ * s⁻¹⁻¹) * σ) * s⁻¹ := by group
      _ = s * (σ * (s⁻¹ * τ * s⁻¹⁻¹)) * s⁻¹ := by rw [hcomm]
      _ = s * σ * s⁻¹ * τ := by group
  have hZs : ∀ σ ∈ Z, σ ^ Nat.card S = 1 := by
    intro σ hσ
    have := pow_card_eq_one' (x := (⟨σ, (Subgroup.mem_inf.1 hσ).1⟩ : S))
    exact congrArg Subtype.val this
  have hscop : Nat.Coprime (Nat.card S) (3 ^ k) := by
    rw [hScard]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have h3s : Nat.Coprime 3 (Nat.card S) := by
    rw [hScard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3))
  set T : Subgroup (GL (Fin n) K) :=
    (Z.comap (primeFormConjHom h (oneGram K n))).map
      (primeFormUnitary h (oneGram K n)).subtype
    with hT
  have hcomT : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (GL (Fin n) K) ∧
      (x * y * x⁻¹ * y⁻¹) ^ (3 ^ k) = 1 := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    have h1 : primeFormConjHom h (oneGram K n) (A * B * A⁻¹ * B⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hZc _ hA _ hB, mul_inv_cancel_right,
        mul_inv_cancel]
    have h2 := (primeFormConjHom_eq_one_iff_center h hn hne _).1 h1
    exact ⟨h2, pow_eq_one_of_center h hq hn1 h2 (A * B * A⁻¹ * B⁻¹).2⟩
  have hc : ∀ x ∈ T, ∀ y ∈ T, x ^ Nat.card S = 1 → x * y = y * x := fun x hx y hy hxs =>
    commute_of_pow_eq_one (hcomT x hx y hy).1 hscop (hcomT x hx y hy).2 hxs
  set A := powOneSubgroup T (Nat.card S) hc with hA
  have hAbot : A = ⊥ := by
    refine eq_bot_of_full h hq hD (fun x hx y hy => hc x hx.1 y hy.1 hx.2) ?_ ?_ ?_
    · intro d hd x hx
      obtain ⟨⟨B, hB, hBx⟩, hxs⟩ := (mem_powOneSubgroup).1 hx
      have hdU : d ∈ primeFormUnitary h (oneGram K n) := hD.mem_unitary h hq hd
      have hBZ : primeFormConjHom h (oneGram K n) (⟨d, hdU⟩ * B * ⟨d, hdU⟩⁻¹) ∈ Z := by
        rw [map_mul, map_mul, map_inv]
        exact hZD _ ⟨⟨d, hdU⟩, hd, rfl⟩ _ (Subgroup.mem_comap.1 hB)
      have hx' : (primeFormUnitary h (oneGram K n)).subtype (⟨d, hdU⟩ * B * ⟨d, hdU⟩⁻¹) =
          d * x * d⁻¹ := by
        rw [map_mul, map_mul, map_inv, hBx]
        rfl
      refine (mem_powOneSubgroup).2 ⟨⟨_, Subgroup.mem_comap.2 hBZ, hx'⟩, ?_⟩
      rw [conj_pow, hxs, mul_one, mul_inv_cancel]
    · intro x hx
      obtain ⟨⟨B, -, rfl⟩, -⟩ := (mem_powOneSubgroup).1 hx
      simpa only [oneGram, Units.val_one, Matrix.mul_one, Subgroup.coe_subtype] using
        mem_primeFormUnitary.1 B.2
    · intro x hx
      exact Nat.Coprime.coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one ((mem_powOneSubgroup).1 hx).2) h3s
  apply hz₀1
  obtain ⟨g, hg⟩ := hQD (hSQ (Subgroup.mem_inf.1 hz₀Z).1)
  set σ := ((z₀ : S) : MulAut (primeFormP h (oneGram K n))) with hσ
  set l := g ^ Nat.card S with hl
  have hlc : primeFormConjHom h (oneGram K n) l = 1 := by
    rw [hl, map_pow, hg]
    exact hZs σ hz₀Z
  have hlZ : (l : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) :=
    (primeFormConjHom_eq_one_iff_center h hn hne _).1 hlc
  have hl3 : l ^ (3 ^ k) = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_eq_one_of_center h hq hn1 hlZ l.2)
  have h3k : 1 < 3 ^ k := Nat.one_lt_pow (by omega) (by norm_num)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hscop h3k
  set μ := (l ^ u)⁻¹ with hμ
  have hμc : (μ : GL (Fin n) K) ∈ Subgroup.center (GL (Fin n) K) := by
    rw [hμ, InvMemClass.coe_inv, SubgroupClass.coe_pow]
    exact (Subgroup.center _).inv_mem ((Subgroup.center _).pow_mem hlZ u)
  have hμZ : ∀ y : primeFormUnitary h (oneGram K n), μ * y = y * μ := by
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (Subgroup.mem_center_iff.1 hμc (y : GL (Fin n) K)).symm
  have hlsu : l ^ (Nat.card S * u) = l := by
    have e := Nat.div_add_mod (Nat.card S * u) (3 ^ k)
    rw [hu] at e
    rw [← e, pow_add, pow_mul, hl3, one_pow, one_mul, pow_one]
  have hμs : μ ^ Nat.card S * l = 1 := by
    rw [hμ, inv_pow, ← pow_mul, mul_comm u, hlsu, inv_mul_cancel]
  have hcμ : primeFormConjHom h (oneGram K n) μ = 1 :=
    (primeFormConjHom_eq_one_iff_center h hn hne _).2 hμc
  have hμgZ : primeFormConjHom h (oneGram K n) (μ * g) ∈ Z := by
    rw [map_mul, hcμ, one_mul, hg]
    exact hz₀Z
  have hmem : ((μ * g : primeFormUnitary h (oneGram K n)) : GL (Fin n) K) ∈ A := by
    refine (mem_powOneSubgroup).2 ⟨⟨μ * g, Subgroup.mem_comap.2 hμgZ, rfl⟩, ?_⟩
    rw [← SubgroupClass.coe_pow, Commute.mul_pow (hμZ g), ← hl, hμs, OneMemClass.coe_one]
  rw [hAbot] at hmem
  have h1 : μ * g = 1 := Subtype.ext (Subgroup.mem_bot.1 hmem)
  rw [← hg, eq_inv_of_mul_eq_one_right h1, map_inv, hcμ, inv_one]

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
