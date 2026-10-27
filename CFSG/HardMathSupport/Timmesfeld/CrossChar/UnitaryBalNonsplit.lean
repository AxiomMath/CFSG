module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBlockOrder

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryNonsplit
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryBlock CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryPair CFSG.RankThree.PartOne.KCUnitaryGt
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCLinComm
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

section Order

theorem mul_dvd_pow_sq_sub_one {q : ℕ} (hp : p.Prime) (hpq : p ∣ q + 1) :
    ((p * (q + 1) : ℕ) : ℤ) ∣ ((q ^ p : ℕ) : ℤ) ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum : (p : ℤ) ∣ ∑ i ∈ Finset.range p, ((q : ℤ) ^ 2) ^ i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hq : (q : ZMod p) = -1 := by
      have := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr hpq
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    push_cast
    simp only [hq]
    have h1 : ((-1 : ZMod p) ^ 2) = 1 := neg_one_sq
    simp [h1]
  obtain ⟨s, hs⟩ := hsum
  have hgeom := geom_sum_mul ((q : ℤ) ^ 2) p
  have e1 : ((q ^ p : ℕ) : ℤ) ^ 2 - 1 = ((q : ℤ) ^ 2) ^ p - 1 := by
    push_cast; ring
  rw [e1, ← hgeom, hs]
  refine ⟨s * ((q : ℤ) - 1), ?_⟩
  push_cast
  ring

theorem card_idScalarKernel_dvd [Finite K] : Nat.card (idScalarKernel h n) ∣ ℓ ^ f + 1 := by
  classical
  set Z := idScalarKernel h n with hZ
  have hmem : ∀ z : Z, ∃ c : Kˣ, ((z : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      GeneralLinearGroup.scalar (Fin n) c ∧ c ^ (ℓ ^ f + 1) = 1 := by
    intro z
    obtain ⟨c, hc, hz⟩ := z.2
    exact ⟨c, hz, hc⟩
  let g : Z →* GL (Fin n) K := (primeFormUnitary h (idGram K n)).subtype.comp Z.subtype
  have hrange : ∀ z : Z, g z ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range := by
    intro z
    obtain ⟨c, hc, -⟩ := hmem z
    exact ⟨c, hc.symm⟩
  let g' : Z →* (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range :=
    g.codRestrict _ hrange
  have hinj : Function.Injective g' := by
    intro z z' hzz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y => ((y : (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range) :
      GL (Fin n) K)) hzz
  have : IsCyclic ((GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range) :=
    isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have hcyc : IsCyclic Z := isCyclic_of_injective g' hinj
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun z => ?_
  obtain ⟨c, hc, hc1⟩ := hmem z
  apply Subtype.ext
  apply Subtype.ext
  change ((z : primeFormUnitary h (idGram K n)) : GL (Fin n) K) ^ (ℓ ^ f + 1) = 1
  rw [hc, ← map_pow, hc1, map_one]


theorem dvd_card_map_of_mul_dvd [Finite K] (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {F : Subgroup (primeFormUnitary h (idGram K n))}
    (hdvd : p * (ℓ ^ f + 1) ∣ Nat.card F) :
    p ∣ Nat.card (F.map (primeFormConjHom h (idGram K n))) := by
  classical
  let φ : F →* MulAut (primeFormP h (idGram K n)) :=
    (primeFormConjHom h (idGram K n)).comp F.subtype
  have hrange : φ.range = F.map (primeFormConjHom h (idGram K n)) := by
    ext y
    constructor
    · rintro ⟨Y, rfl⟩
      exact ⟨Y, Y.2, rfl⟩
    · rintro ⟨Y, hY, rfl⟩
      exact ⟨⟨Y, hY⟩, rfl⟩
  have hsplit : Nat.card F = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hkerle : φ.ker.map F.subtype ≤ idScalarKernel h n := by
    rintro _ ⟨y, hy, rfl⟩
    exact (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp hy
  have hkdvd : Nat.card φ.ker ∣ ℓ ^ f + 1 := by
    have h1 : Nat.card (φ.ker.map F.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective F.subtype_injective
    rw [← h1]
    exact (Subgroup.card_dvd_of_le hkerle).trans card_idScalarKernel_dvd
  obtain ⟨t, ht⟩ := hkdvd
  rw [hsplit, ht, show p * (Nat.card φ.ker * t) = Nat.card φ.ker * (p * t) by ring,
    mul_comm (Nat.card φ.range)] at hdvd
  have h2 : p * t ∣ Nat.card φ.range :=
    (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hdvd
  rw [← hrange]
  exact (Dvd.intro t rfl).trans h2

theorem exists_ne_mem_primaryFactors' (hn : 0 < n) (hp : p ≠ 0) (hpF : (p : K) ≠ 0) {ω : K}
    (hω : IsPrimitiveRoot ω p) {S : GL (Fin n) K} (hS : S ^ p = 1)
    (hS1 : ∀ d : Kˣ, S ≠ GeneralLinearGroup.scalar (Fin n) d) :
    ∃ a ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) K)),
      ∃ a' ∈ primaryFactors (Matrix.toLin' (S : Matrix (Fin n) (Fin n) K)), a ≠ a' := by
  classical
  set xS := Matrix.toLin' (S : Matrix (Fin n) (Fin n) K) with hxS
  have hsq : Squarefree (minpoly K xS) := squarefree_minpoly_of_pow_eq_one hpF
    (toLin'_pow_eq_one hS)
  have hsum := sum_primaryProjection hsq
  by_contra hall
  push Not at hall
  obtain ⟨a₀, ha₀⟩ : (primaryFactors xS).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.sum_empty] at hsum
    have h2 := congrFun (LinearMap.congr_fun hsum (Pi.single ⟨0, hn⟩ 1)) ⟨0, hn⟩
    simp at h2
  have hsingle : primaryFactors xS = {a₀} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨ha₀, fun a ha => hall a ha a₀ ha₀⟩
  obtain ⟨ζ, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp hω hS ha₀
  rw [hsingle, Finset.sum_singleton] at hsum
  have hxv : ∀ v, xS v = ζ • v := by
    intro v
    have hPv : primaryProjection xS (X - C ζ) v = v := by rw [hsum]; rfl
    have h1 := mem_primaryComponent.1 (primaryProjection_mem hsq ha₀ v)
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      hPv] at h1
    exact sub_eq_zero.1 h1
  have hSmat : (S : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) ζ := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [← hxS, hxv]
    ext i
    simp [Matrix.mulVec_diagonal]
  have hζ : ζ ≠ 0 := by
    rintro rfl
    have h1 : ((S * S⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩ = 1 := by
      rw [mul_inv_cancel]; simp
    rw [Units.val_mul, hSmat] at h1
    simp at h1
  apply hS1 (Units.mk0 ζ hζ)
  ext i j
  rw [hSmat, GeneralLinearGroup.coe_scalar]
  rfl


theorem dualPoly_X_sub_C_self {μ : K} (hμ : h.bar μ * μ = 1) :
    dualPoly h.bar (X - C μ) = X - C μ := by
  have hbar0 : h.bar μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ
    exact zero_ne_one hμ
  rw [dualPoly_X_sub_C hbar0]
  congr 2
  exact (inv_eq_of_mul_eq_one_right hμ)

end Order


theorem psi_refl_eq (M : primeFormUnitary h (idGram K n)) :
    primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, RingEquiv.refl K⟩ =
      primeFormConjHom h (idGram K n) M := by
  rw [primeFormPsi_apply]
  have : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) (RingEquiv.refl K) = 1 :=
    map_one _
  rw [this, mul_one]

theorem exists_scalar_of_conj_commute (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {A B : primeFormUnitary h (idGram K n)}
    (hAB : primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) B =
      primeFormConjHom h (idGram K n) B * primeFormConjHom h (idGram K n) A) :
    ∃ d : Kˣ, (A : GL (Fin n) K) * (B : GL (Fin n) K) =
      (B : GL (Fin n) K) * (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) d := by
  have h1 : primeFormConjHom h (idGram K n) ((B * A)⁻¹ * (A * B)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hAB, inv_mul_cancel]
  obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne _).mp h1
  refine ⟨d, ?_⟩
  have hd' : ((B : GL (Fin n) K) * (A : GL (Fin n) K))⁻¹ * ((A : GL (Fin n) K) * B) =
      GeneralLinearGroup.scalar (Fin n) d := by simpa using hd
  rw [← hd', mul_inv_cancel_left]

theorem eq_one_of_scalar_commutator {A B : primeFormUnitary h (idGram K n)} {d : Kˣ}
    (hAB : (A : GL (Fin n) K) * (B : GL (Fin n) K) =
      (B : GL (Fin n) K) * (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) d)
    {w : Fin n → K} {α : K} (hα : α ≠ 0)
    (hw : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w = α • w)
    (hBw : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      α • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w))
    (hBw0 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ≠ 0) : d = 1 := by
  have h1 := congrArg (fun g : GL (Fin n) K => ((g : Matrix (Fin n) (Fin n) K)) *ᵥ w) hAB
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
  rw [← Matrix.mulVec_mulVec, hBw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h1
  have h2 : (Matrix.scalar (Fin n) (d : K)) *ᵥ w = (d : K) • w := by
    simp [Matrix.scalar_apply]
  rw [h2, Matrix.mulVec_smul, hw, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul] at h1
  have h3 : (α * (1 - (d : K))) • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) = 0 := by
    rw [show α * (1 - (d : K)) = α - (d : K) * α by ring, sub_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 hα
    · exact Units.ext (by have := sub_eq_zero.mp h5; simpa using this.symm)
  · exact absurd h4 hBw0

section Nonsplit

theorem scalar_pow_eq_one_of_eq {S : GL (Fin n) K} {d : Kˣ} (hn : 0 < n) {k : ℕ}
    (hS : S ^ k = 1) (hd : S = GeneralLinearGroup.scalar (Fin n) d) : d ^ k = 1 := by
  apply glScalar_injective hn (F := K)
  rw [map_pow, ← hd, hS, map_one]

theorem localDeltaIn_eq_bot_of_unitary_nonsplit (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hq3 : 3 < ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {R S : primeFormUnitary h (idGram K n)} (hRS : R * S = S * R) {c : Kˣ}
    (hR : (R : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ d : Kˣ, d ^ p ≠ c) (hS : S ^ p = 1)
    (hS1 : primeFormConjHom h (idGram K n) S ≠ 1)
    {E H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H)
    (hRE : primeFormConjHom h (idGram K n) R ∈ E)
    (hSE : primeFormConjHom h (idGram K n) S ∈ E) : localDeltaIn p H E = ⊥ := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have hpℓ := ne_char_of_dvd_add_one hp hpq h.one_le
  have hn0 : 0 < n := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq h.prime hp).mp this).symm
  obtain ⟨ω, hω⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
  obtain ⟨ζ, hζ, hζn⟩ := exists_norm_one_primitiveRoot (h := h) hp hpq
  have hζ' := exists_norm_one_ne_one_sq_ne_one (h := h) hp hp2 hpq
  have hirr : Irreducible (X ^ p - C (c : K)) := by
    refine X_pow_sub_C_irreducible_of_prime hp fun b hb => ?_
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp0] at hb
      exact c.ne_zero hb.symm
    exact hc (Units.mk0 b hb0) (Units.ext (by simpa using hb))
  have hRSgl : (R : GL (Fin n) K) * (S : GL (Fin n) K) = (S : GL (Fin n) K) * R :=
    congrArg Subtype.val hRS
  have hSgl : (S : GL (Fin n) K) ^ p = 1 := by
    have := congrArg (fun y : primeFormUnitary h (idGram K n) => (y : GL (Fin n) K)) hS
    simpa using this
  have hSs : (S : GL (Fin n) K) ^ p = GeneralLinearGroup.scalar (Fin n) (1 : Kˣ) := by
    rw [hSgl, map_one]
  have H0S := primaryData_of_pow_eq_scalar hp hpℓ hSs
  have H0R := primaryData_of_pow_eq_scalar hp hpℓ hR
  have hsqS := H0S.squarefree
  have hSnsc : ∀ d : Kˣ, (S : GL (Fin n) K) ≠ GeneralLinearGroup.scalar (Fin n) d := by
    intro d hd
    apply hS1
    have hdp := scalar_pow_eq_one_of_eq hn0 hSgl hd
    have hdn : h.norm (d : K) = 1 := by
      change (d : K) * h.bar (d : K) = 1
      rw [mul_comm]
      exact bar_eq_inv_of_pow_eq_one h hpq (by
        rw [← Units.val_pow_eq_pow_val, hdp, Units.val_one])
    exact (primeFormConjHom_eq_one_iff_of_ne hn hne S).mpr
      ⟨d, (pow_succ_eq_one_iff_norm h d).mpr hdn, hd⟩
  have hρR1 : primeFormConjHom h (idGram K n) R ≠ 1 := by
    intro h1
    obtain ⟨d, -, hd⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne R).mp h1
    apply hc d
    apply glScalar_injective hn0 (F := K)
    rw [map_pow, ← hd, hR]
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha, a', ha', haa'⟩ := exists_ne_mem_primaryFactors' hn0 hp0 hpK hω hSgl hSnsc
  obtain ⟨ν₀, rfl⟩ := exists_eq_X_sub_C_of_mem_primaryFactors hp0 hω hSgl ha
  have hdim := le_finrank_primaryComponent hn0 hp0 hRSgl hirr hR hsqS ha
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsqS ha)
  have hv₀eig := mem_primaryComponent_X_sub_C.mp hv₀
  have hν₀p : ν₀ ^ p = 1 := eigenvalue_pow_eq_one hS hv₀0 hv₀eig
  have hν₀bar : h.bar ν₀ * ν₀ = 1 := bar_eq_inv_of_pow_eq_one h hpq hν₀p
  have hν₀0 : ν₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp0] at hν₀p
    exact zero_ne_one hν₀p
  have hsep := separatingLeft_primaryComponent_selfDual H0S ha (dualPoly_X_sub_C_self hν₀bar)
  obtain ⟨e, he_mem, he_on⟩ := exists_orthonormal_triple hsep (le_trans hp3 hdim)
  have hSe : ∀ i, ((toLinU h n S : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) (e i) = ν₀ • e i := fun i =>
    mem_primaryComponent_X_sub_C.mp (he_mem i)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  obtain ⟨hmemS, hgoodS⟩ := isGoodBlock_of_eigenpair (h := h) hq3 (he_on.pair h01) (hSe 0) (hSe 1)
  have hJpS := dvd_card_map_gBlock_of_torus hp hp2 hn hne H0S hν₀bar hmemS (he_on.pair h01)
    (hSe 0) (hSe 1) hζ hζn
  have hcommS := commute_of_mem_localDeltaIn_gBlock hp hn hne hq2 H0S ⟨X - C ν₀, hmemS⟩ hgoodS hH
    hg hSE hS1 hJpS
  have hh := mem_primaryFactors_X_pow_sub_C hn0 hp0 hirr hR
  have hRone : ∀ b ∈ primaryFactors (Matrix.toLin' ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      b = X ^ p - C (c : K) := by
    intro b hb
    have hirr' := irreducible_of_mem_primaryFactors hb
    have hdvd : b ∣ X ^ p - C (c : K) := (mem_primaryFactors.mp hb).2.2.trans
      (minpoly.dvd K _ (aeval_X_pow_sub_C_eq_zero hR))
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hb)
      (monic_X_pow_sub_C _ hp0) (associated_of_dvd_dvd hdvd (hirr'.dvd_symm hirr hdvd))
  have hselfR : dualPoly h.bar (X ^ p - C (c : K)) = X ^ p - C (c : K) :=
    hRone _ (dualPoly_mem_primaryFactors H0R hh)
  obtain ⟨-, -, -, -, -, hmultR⟩ :=
    exists_mixing_mem_blockImage hn0 hp0 hRSgl hirr hR hsqS ha ha' haa'
  have hgoodR : IsGoodBlock h (toLinU h n R) ⟨X ^ p - C (c : K), hh⟩ := by
    refine ⟨hmultR, fun _ => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    rw [natDegree_X_pow_sub_C]
    have : ℓ ^ f ≤ ℓ ^ (f * p) :=
      Nat.pow_le_pow_right h.prime.pos (by nlinarith [h.one_le, hp.two_le])
    omega
  have hJpR : p ∣ Nat.card ((gBlock h R (X ^ p - C (c : K))).map
      (primeFormConjHom h (idGram K n))) := by
    refine dvd_card_map_of_mul_dvd hn hne ?_
    have hd := dvd_card_specialBlock_selfDual H0R ⟨X ^ p - C (c : K), hh⟩ hselfR
      (p := p * (ℓ ^ f + 1)) (j := 2) le_rfl hmultR (by
        rw [natDegree_X_pow_sub_C]
        simpa using mul_dvd_pow_sq_sub_one (q := ℓ ^ f) hp hpq)
    have hcard : Nat.card (gBlock h R (X ^ p - C (c : K))) =
        Nat.card (specialBlock (idForm h n) (toLinU h n R) (X ^ p - C (c : K))) := by
      rw [← map_toLinU_gBlock]
      exact (Subgroup.card_map_of_injective toLinU_injective).symm
    rw [hcard]
    exact hd
  have hcommR := commute_of_mem_localDeltaIn_gBlock hp hn hne hq2 H0R ⟨X ^ p - C (c : K), hh⟩
    hgoodR hH hg hRE hρR1 hJpR
  obtain ⟨⟨M', τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn hne g
  have hmat1 := hmat_refl (n := n) (K := K)
  have hMunit : IsUnit ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (M' : GL (Fin n) K).isUnit
  have hTC01 : TorusComm h ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) τ (e 0) (e 1) :=
    torusComm_of_block hn hne hq2 H0S hν₀bar hmemS hgoodS (he_on.pair h01) (hSe 0) (hSe 1) M' τ
      hcommS
  obtain ⟨hmem02, hgood02⟩ := isGoodBlock_of_eigenpair (h := h) hq3 (he_on.pair h02) (hSe 0) (hSe 2)
  have hTC02 : TorusComm h ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) τ (e 0) (e 2) :=
    torusComm_of_block hn hne hq2 H0S hν₀bar hmem02 hgood02 (he_on.pair h02) (hSe 0) (hSe 2) M' τ
      hcommS
  have hτ : τ = RingEquiv.refl K :=
    tau_eq_one_of_torus h hMunit (he_on.pair h01) (he_on.pair h02)
      (he_on.linearIndependent_triple h01 h02 h12) hTC01 hTC02
  subst hτ
  have he0 : e 0 ≠ 0 := (he_on.pair h01).ne_zero_left
  have hmulinj := Matrix.mulVec_injective_iff_isUnit.mpr hMunit
  have hmulinjR : Function.Injective
      (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (R : GL (Fin n) K).isUnit
  have hmulinjS : Function.Injective
      (((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec) :=
    Matrix.mulVec_injective_iff_isUnit.mpr (S : GL (Fin n) K).isUnit
  obtain ⟨dM, hdM⟩ := (exists_smul_of_torusComm (he_on.pair h01) hTC01 hζ').1
  have hdM0 : dM ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hdM
    exact he0 (hmulinj (hdM.trans (Matrix.mulVec_zero _).symm))
  have hSv : ∀ i, ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e i = ν₀ • e i :=
    fun i => hSe i
  have hSe0 : ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0 ≠ 0 := by
    rw [hSv]
    exact smul_ne_zero hν₀0 he0
  have hρS : primeFormConjHom h (idGram K n) M' * primeFormConjHom h (idGram K n) S =
      primeFormConjHom h (idGram K n) S * primeFormConjHom h (idGram K n) M' := by
    have := commute_of_mem_localDeltaIn hg hSE
    rwa [psi_refl_eq] at this
  obtain ⟨dS, hdS⟩ := exists_scalar_of_conj_commute hn hne hρS
  have hdS1 : dS = 1 := by
    refine eq_one_of_scalar_commutator hdS hdM0 hdM ?_ hSe0
    rw [hSv, Matrix.mulVec_smul, hdM, smul_comm]
  have hMS : M' * S = S * M' := by
    apply Subtype.ext
    rw [hdS1, map_one, mul_one] at hdS
    exact hdS
  have hFS : Group.IsPerfect (gBlock h S (X - C ν₀)) :=
    (isQuasisimple_gBlock hq2 H0S ⟨X - C ν₀, hmemS⟩ hgoodS).1
  have hblockS : ∀ Y ∈ gBlock h S (X - C ν₀), M' * Y = Y * M' := by
    intro Y hY
    have := matrix_comm_of_perfect hn hne hFS M' (RingEquiv.refl K) hcommS Y hY
    rw [hmat1] at this
    exact Subtype.ext (Units.ext this)
  obtain ⟨cS, hcS⟩ := exists_scalar_of_commute_gBlock_X_sub_C hq2 H0S hmemS hgoodS M' hMS hblockS
  have hcS0' : ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0 = cS • e 0 :=
    hcS (e 0) (hSe 0)
  have hcS0 : cS ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcS0'
    exact he0 (hmulinj (hcS0'.trans (Matrix.mulVec_zero _).symm))
  have hρR : primeFormConjHom h (idGram K n) M' * primeFormConjHom h (idGram K n) R =
      primeFormConjHom h (idGram K n) R * primeFormConjHom h (idGram K n) M' := by
    have := commute_of_mem_localDeltaIn hg hRE
    rwa [psi_refl_eq] at this
  obtain ⟨dR, hdR⟩ := exists_scalar_of_conj_commute hn hne hρR
  have hReS : ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0) =
      ν₀ • (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0) := by
    have hmm : ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((S : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul, ← Units.val_mul, hRSgl]
    rw [Matrix.mulVec_mulVec, hmm, ← Matrix.mulVec_mulVec, hSv, Matrix.mulVec_smul]
  have hRe0 : ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0 ≠ 0 := fun h0 =>
    he0 (hmulinjR (h0.trans (Matrix.mulVec_zero _).symm))
  have hcSR : ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0) =
      cS • (((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ e 0) :=
    hcS _ (by rw [toLinU_apply_eq]; exact hReS)
  have hdR1 : dR = 1 := eq_one_of_scalar_commutator hdR hcS0 hcS0' hcSR hRe0
  have hMR : M' * R = R * M' := by
    apply Subtype.ext
    rw [hdR1, map_one, mul_one] at hdR
    exact hdR
  have hFR : Group.IsPerfect (gBlock h R (X ^ p - C (c : K))) :=
    (isQuasisimple_gBlock hq2 H0R ⟨X ^ p - C (c : K), hh⟩ hgoodR).1
  have hblockR : ∀ Y ∈ gBlock h R (X ^ p - C (c : K)), M' * Y = Y * M' := by
    intro Y hY
    have := matrix_comm_of_perfect hn hne hFR M' (RingEquiv.refl K) hcommR Y hY
    rw [hmat1] at this
    exact Subtype.ext (Units.ext this)
  have : Fact (Irreducible (X ^ p - C (c : K))) := ⟨hirr⟩
  obtain ⟨cR, hcR⟩ := exists_eScalar_of_commute_gBlock hq2 H0R ⟨X ^ p - C (c : K), hh⟩ hgoodR M' hMR
    hblockR
  have hmemR : ∀ v : Fin n → K, v ∈ primaryComponent ((toLinU h n R :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
      (X ^ p - C (c : K)) := fun v => mem_primaryComponent_X_pow_sub_C hR v
  have hcReq : cR = algebraMap K (AdjoinRoot (X ^ p - C (c : K))) cS := by
    have hu0 : (⟨e 0, hmemR (e 0)⟩ : primaryComponent ((toLinU h n R :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
        (X ^ p - C (c : K))) ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    refine smul_left_injective (AdjoinRoot (X ^ p - C (c : K))) hu0 ?_
    refine Subtype.ext ?_
    have h1 := hcR ⟨e 0, hmemR (e 0)⟩
    rw [coe_algebraMap_smul_primaryComponent]
    show ((cR • (⟨e 0, hmemR (e 0)⟩ : primaryComponent _ _) : primaryComponent _ _) :
      Fin n → K) = cS • e 0
    rw [← h1, toLinU_apply_eq]
    exact hcS0'
  have hall : ∀ v : Fin n → K, ((M' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      cS • v := by
    intro v
    have h1 := hcR ⟨v, hmemR v⟩
    rw [hcReq, coe_algebraMap_smul_primaryComponent] at h1
    rw [← toLinU_apply_eq]
    exact h1
  exact psi_eq_one_of_scalar hn hne M' cS hall

end Nonsplit

end CFSG.HardMathSupport.Timmesfeld.CrossChar
