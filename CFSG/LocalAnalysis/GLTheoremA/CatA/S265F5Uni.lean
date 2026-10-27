module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F5UniBlk
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F5

open Matrix
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.Classical
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.LocalAnalysis.GLTheoremA.HDescUniRes

section Lift

private theorem mul_comm_of_eq_conj_mul_central_odd {G : Type*} [Group G] {n : ℕ} (hn : Odd n)
    {x u s : G} (hu2 : u * u = 1) (hs : ∀ g, s * g = g * s) (hsn : s ^ n = 1)
    (h : u = x * u * x⁻¹ * s) : x * u = u * x := by
  have hs2 : s * s = 1 := by
    have h1 : u * u = (x * u * x⁻¹) * (x * u * x⁻¹) * (s * s) := by
      conv_lhs => rw [h]
      rw [show x * u * x⁻¹ * s * (x * u * x⁻¹ * s) = x * u * x⁻¹ * (s * (x * u * x⁻¹)) * s by
        group]
      rw [hs (x * u * x⁻¹)]
      group
    have h2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
      calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [h2, one_mul, hu2] at h1
    exact h1.symm
  have hs1 : s = 1 := by
    obtain ⟨m, hm⟩ := hn
    have key : s ^ n = (s ^ 2) ^ m * s := by rw [← pow_mul, ← pow_succ, ← hm]
    rw [hsn, sq, hs2, one_pow, one_mul] at key
    exact key.symm
  rw [hs1, mul_one] at h
  calc x * u = x * u * x⁻¹ * x := by group
    _ = u * x := by rw [← h]

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem exists_lift_sq_eq_one_primeFormP {n : ℕ} (hn : Odd n) {t : primeFormP h (idGram K n)}
    (ht : t ^ 2 = 1) :
    ∃ U : gramSU h (idGram K n), (U : primeFormP h (idGram K n)) = t ∧ U ^ 2 = 1 := by
  obtain ⟨U₀, rfl⟩ := QuotientGroup.mk_surjective t
  have hs : U₀ ^ 2 ∈ normOneScalars h (gramSU h (idGram K n)) n := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact ht
  obtain ⟨c, -, hcn, hcU⟩ := hs
  refine ⟨U₀ ^ n, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hn
    have e1 : U₀ ^ n = (U₀ ^ 2) ^ m * U₀ := by rw [← pow_mul, ← pow_succ, ← hm]
    rw [e1, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow, ht, one_pow, one_mul]
  · apply Subtype.ext
    rw [← pow_mul, show n * 2 = 2 * n from Nat.mul_comm n 2, pow_mul, Subgroup.coe_pow, hcU,
      ← map_pow, hcn, map_one, Subgroup.coe_one]

theorem mul_comm_of_primeFormConjHom_fix_odd {n : ℕ} (hn : Odd n)
    {X : primeFormUnitary h (idGram K n)} {U : gramSU h (idGram K n)} (hU2 : U ^ 2 = 1)
    (hfix : primeFormConjHom h (idGram K n) X (U : primeFormP h (idGram K n)) = U) :
    (X : GL (Fin n) K) * U = U * X := by
  rw [primeFormConjHom_mk, QuotientGroup.eq] at hfix
  obtain ⟨c, -, hcn, hc⟩ := hfix
  have hW : ((⟨(X : GL (Fin n) K) * U * (X : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h (idGram K n) X.2 U.2⟩ : gramSU h (idGram K n))⁻¹ * U :
        gramSU h (idGram K n)) =
      ((X : GL (Fin n) K) * U * (X : GL (Fin n) K)⁻¹)⁻¹ * (U : GL (Fin n) K) := rfl
  rw [hW] at hc
  refine mul_comm_of_eq_conj_mul_central_odd hn (s := GeneralLinearGroup.scalar (Fin n) c) ?_
    (fun g => GeneralLinearGroup.scalar_commute c g) (by rw [← map_pow, hcn, map_one]) ?_
  · rw [← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  · rw [← hc, mul_inv_cancel_left]

end Lift

section FieldPart

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem card_le_mul_card_inf_primeFormD (h : UnitaryFieldData ℓ f K) {n p : ℕ} (hn : 3 ≤ n)
    (hne : ¬ (n = 3 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    {B : Subgroup (MulAut (primeFormP h (idGram K n)))} (hB : ∀ b ∈ B, b ^ p = 1) :
    Nat.card B ≤ p * Nat.card (B ⊓ primeFormD h (idGram K n) :
      Subgroup (MulAut (primeFormP h (idGram K n)))) := by
  classical
  have := h.finite
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := n)) hn hne
  let φ : B →* (K ≃+* K) :=
    (primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).comp B.subtype
  have hkerφ : Nat.card φ.ker = Nat.card (B ⊓ primeFormD h (idGram K n) :
      Subgroup (MulAut (primeFormP h (idGram K n)))) := by
    have h1 : φ.ker = (primeFormD h (idGram K n)).subgroupOf B := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
      rfl
    rw [h1, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  haveI : IsCyclic (K ≃+* K) := by
    obtain ⟨σ₀, -, -, htop, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality h.prime
        (by have := h.one_le; omega) h.card
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩
  have hrange : Nat.card φ.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨y, hy⟩ := x
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
    apply Subtype.ext
    show φ b ^ p = 1
    rw [← map_pow, show b ^ p = 1 from Subtype.ext (hB b b.2), map_one]
  rw [← Subgroup.card_ker_mul_card_range φ, hkerφ, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos hrange)

end FieldPart

section Subfield

variable {ℓ f e : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {k : Subfield K}
  {h₀ : UnitaryFieldData ℓ e k} (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c)

include hbar in
private theorem subfieldGL_mem_primeFormUnitary_aux {n : ℕ} {g : GL (Fin n) k}
    (hg : g ∈ primeFormUnitary h₀ (idGram k n)) :
    subfieldGL k n g ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul, hg,
    Matrix.map_one _ (map_zero _) (map_one _)]

include hbar in
private theorem mem_primeFormUnitary_of_subfieldGL_aux {n : ℕ} {g : GL (Fin n) k}
    (hg : subfieldGL k n g ∈ primeFormUnitary h (idGram K n)) :
    g ∈ primeFormUnitary h₀ (idGram k n) := by
  rw [mem_primeFormUnitary] at hg ⊢
  simp only [idGram, Units.val_one, Matrix.mul_one] at hg ⊢
  rw [coe_subfieldGL, map_subtype_map_bar h h₀ hbar, ← transpose_map, ← Matrix.map_mul] at hg
  refine Matrix.map_injective (f := (k.subtype : k → K)) Subtype.val_injective ?_
  change (((g : Matrix (Fin n) (Fin n) k).map h₀.bar)ᵀ * g).map k.subtype =
    (1 : Matrix (Fin n) (Fin n) k).map k.subtype
  rw [hg, Matrix.map_one _ (map_zero _) (map_one _)]

omit h in
private theorem glAut_subfieldGL_aux (σ : K ≃+* K) (n : ℕ) (g : GL (Fin n) (fixSubfield σ)) :
    glAut σ (subfieldGL (fixSubfield σ) n g) = subfieldGL (fixSubfield σ) n g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (((g : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

end Subfield

section Reduction

variable {f : ℕ} {K : Type} [Field K] [CharP K 2]

theorem glaPLayer_ne_bot_of_fieldHom_conjHom_prime (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hpe : p ∣ 2 ^ (f / p) + 1) (he2 : 2 ≤ f / p) {M : primeFormUnitary h (idGram K p)}
    (hM1 : primeFormConjHom h (idGram K p) M ≠ 1)
    (hMp : primeFormConjHom h (idGram K p) M ^ p = 1)
    (hcomm : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
        primeFormConjHom h (idGram K p) M =
      primeFormConjHom h (idGram K p) M *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ)
    {t : primeFormP h (idGram K p)} (ht : orderOf t = 2)
    (hfix : primeFormConjHom h (idGram K p) M t = t) :
    GLAPLayer p (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K p) M)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have := h.finite
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hn2p : p < 2 * p := by
    have := hp.pos
    omega
  obtain ⟨hpf, hK₀card⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  set e := f / p with he
  have hfe : f = p * e := (Nat.mul_div_cancel' hpf).symm
  have hf2 : 2 ≤ f := le_trans he2 (Nat.div_le_self f p)
  have hne : ¬ (p = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h2] at h4
    norm_num at h4
  have hpq : p ∣ 2 ^ f + 1 := by
    have h1 := Odd.nat_add_dvd_pow_add_pow (2 ^ e) 1 hpodd
    rw [one_pow, ← pow_mul, show e * p = f by rw [hfe, mul_comm]] at h1
    exact hpe.trans h1
  set K₀ := fixSubfield σ with hK₀def
  have hσK₀ : ∀ c ∈ K₀, σ c = c := fun c hc => RingHom.mem_eqLocusField.mp hc
  have h₀ : UnitaryFieldData 2 e K₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar₀ : ∀ c : K₀, (h₀.bar c : K) = h.bar c := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hK₀card' : Nat.card K₀ = (2 ^ e) ^ 2 := by rw [hK₀card, pow_mul']
  have hpK₀ : p ∣ Nat.card K₀ - 1 := by
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ e = y + 1 := ⟨2 ^ e - 1, by have := @Nat.one_le_two_pow e; omega⟩
    have hsq : (y + 1) ^ 2 = y * (y + 1 + 1) + 1 := by ring
    rw [hK₀card', hy, hsq, Nat.add_sub_cancel]
    rw [hy] at hpe
    exact Dvd.dvd.mul_left hpe y
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.CTP.exists_primitiveRoot_of_dvd (F := K₀) hp hpK₀
  have hζK : IsPrimitiveRoot (ζ : K) p := hζ.map_of_injective K₀.subtype.injective
  have hμp : ∀ x : K, x ^ p = 1 → σ x = x := by
    intro x hx
    obtain ⟨m, -, rfl⟩ := hζK.eq_pow_of_pow_eq_one hx
    rw [map_pow, hσK₀ _ ζ.2]
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht] at this
  obtain ⟨U, rfl, hU2⟩ := exists_lift_sq_eq_one_primeFormP hpodd ht2
  set u : GL (Fin p) K := (U : GL (Fin p) K) with hu
  have hu1 : u ≠ 1 := by
    intro h1
    have hU : U = 1 := Subtype.ext h1
    rw [hU, QuotientGroup.mk_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hu2 : u * u = 1 := by
    rw [hu, ← Subgroup.coe_mul, ← sq, hU2, Subgroup.coe_one]
  obtain ⟨A, α, hαn, hAp, hAM⟩ := exists_pow_scalar_of_mem_primeFormD hp3 ⟨M, rfl⟩ hMp
  rw [hAM] at hM1 hcomm hfix ⊢
  have hAu := mul_comm_of_primeFormConjHom_fix_odd hpodd hU2 hfix
  obtain ⟨μ, hμ⟩ := exists_pow_eq_of_comm_involution hp hn2p hu1 hu2 hAu hAp
  have hμn : h.norm (μ : K) = 1 :=
    norm_eq_one_of_pow_norm hp hp2 hpq (by rw [hμ]; exact hαn)
  have hμ'n : h.norm ((μ⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_inv_eq_inv_val] using
      CFSG.HardMathSupport.Timmesfeld.CrossChar.norm_inv_eq_one hμn
  obtain ⟨A', hA'⟩ : ∃ A' : primeFormUnitary h (idGram K p), A' = scalarU h p μ⁻¹ hμ'n * A :=
    ⟨_, rfl⟩
  have hA'c : primeFormConjHom h (idGram K p) A' = primeFormConjHom h (idGram K p) A := by
    rw [hA', map_mul, conjHom_scalarU hp3 hne, one_mul]
  have hA'p : A' ^ p = 1 := by
    rw [hA']
    exact rescale_pow_eq_one hp3 hne hμ'n (by rw [hμ]; exact hAp)
  have hA'pg : (A' : GL (Fin p) K) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hA'p, Subgroup.coe_one]
  have ha'e : (A' : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) μ⁻¹ * A := by
    rw [hA', Subgroup.coe_mul, coe_scalarU]
  have hA'u : (A' : GL (Fin p) K) * u = u * A' := by
    rw [ha'e, mul_assoc, hAu, ← mul_assoc, ← mul_assoc,
      GeneralLinearGroup.scalar_commute μ⁻¹ u]
  rw [← hA'c] at hM1 hcomm ⊢
  have hσc : primeFormConjHom h (idGram K p)
      (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := p)) σ A') =
      primeFormConjHom h (idGram K p) A' := by
    have e1 : primeFormConjHom h (idGram K p)
        (primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := p)) σ A') =
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
          primeFormConjHom h (idGram K p) A' *
          (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ)⁻¹ :=
      (primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := p)) σ A').symm
    rw [e1, hcomm, mul_inv_cancel_right]
  have hz : primeFormConjHom h (idGram K p)
      (A'⁻¹ * primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := p)) σ A') = 1 := by
    rw [map_mul, map_inv, hσc, inv_mul_cancel]
  obtain ⟨lam, -, hlam⟩ := (primeFormConjHom_eq_one_iff_of_ne hp3 hne _).1 hz
  have hσA : glAut σ (A' : GL (Fin p) K) =
      (A' : GL (Fin p) K) * GeneralLinearGroup.scalar (Fin p) lam := by
    rw [← hlam, Subgroup.coe_mul, Subgroup.coe_inv, coe_primeFormFieldU, mul_inv_cancel_left]
  have hσM : GeneralLinearGroup.map (σ : K →+* K) (A' : GL (Fin p) K) =
      (A' : GL (Fin p) K) * GeneralLinearGroup.scalar (Fin p) lam := by
    rw [← hσA]
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, coe_glAut, Matrix.map_apply]
    rfl
  have hlam1 : lam = 1 := eq_one_of_map_eq_mul_scalar hp hn2p hζK hμp hu1 hu2 hA'u hA'pg hσM
  have hσA' : glAut σ (A' : GL (Fin p) K) = A' := by
    rw [hσA, hlam1, map_one, mul_one]
  obtain ⟨M₀, hM₀⟩ := exists_subfieldGL_eq_of_fixed p hσA'
  have hM₀U : M₀ ∈ primeFormUnitary h₀ (idGram K₀ p) :=
    mem_primeFormUnitary_of_subfieldGL_aux h hbar₀ (by rw [hM₀]; exact A'.2)
  have hM₀p : M₀ ^ p = 1 :=
    subfieldGL_injective K₀ p (by rw [map_pow, hM₀, hA'pg, map_one])
  set A₀ : primeFormUnitary h₀ (idGram K₀ p) := ⟨M₀, hM₀U⟩ with hA₀
  have hA₀p : A₀ ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hM₀p)
  obtain ⟨b, ν, -, hb, hν, -⟩ := exists_orthonormal_eigenbasis_pair (h := h₀) hp
    hpe (A := A₀) (B := A₀) rfl hA₀p hA₀p
  have hν' : ∀ i, (M₀ : Matrix (Fin p) (Fin p) K₀) *ᵥ b i = ν i • b i := fun i =>
    (CFSG.RankThree.PartOne.KCUnitaryBlock.toLinU_apply_eq h₀ A₀ (b i)).symm.trans (hν i)
  obtain ⟨R₀, hR₀U, hR₀⟩ := exists_unitary_conj_eq_diagonal h₀ hb hν'
  have hXg : ((subfieldGL K₀ p R₀ * (A' : GL (Fin p) K) * (subfieldGL K₀ p R₀)⁻¹ :
      GL (Fin p) K) : Matrix (Fin p) (Fin p) K) = diagonal (fun l => (ν l : K)) := by
    rw [← hM₀, ← map_inv, ← map_mul, ← map_mul, coe_subfieldGL, hR₀]
    exact Matrix.diagonal_map (map_zero _)
  obtain ⟨Q, hQ⟩ : ∃ Q : primeFormUnitary h (idGram K p),
      (Q : GL (Fin p) K) = subfieldGL K₀ p R₀ :=
    ⟨⟨_, subfieldGL_mem_primeFormUnitary_aux h hbar₀ hR₀U⟩, rfl⟩
  have hX : (((Q * A' * Q⁻¹ : primeFormUnitary h (idGram K p)) : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) = diagonal (fun l => (ν l : K)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hQ]
    exact hXg
  obtain ⟨a, a', hda, haa'⟩ := Function.not_injective_iff.1
    (not_injective_of_conj_eq_diagonal hu1 hu2 hA'u hXg)
  have hd0p : ∀ l, (ν l : K) ^ p = 1 := diagonal_pow_eq_one hA'pg hXg
  obtain ⟨c, hdc⟩ : ∃ c, (ν c : K) ≠ ν a := by
    by_contra hcon
    have hcon' : ∀ l, (ν l : K) = ν a := fun l => by_contra fun h' => hcon ⟨l, h'⟩
    apply hM1
    have hda0 : (ν a : K) ≠ 0 := by
      intro h0
      have h1 := hd0p a
      rw [h0, zero_pow hp.ne_zero] at h1
      exact zero_ne_one h1
    have hsc : (Q : GL (Fin p) K) * A' * (Q : GL (Fin p) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ hda0) := by
      apply Units.ext
      rw [hQ, hXg, GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
      congr 1
      funext l
      exact hcon' l
    have hA'sc : (A' : GL (Fin p) K) = GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ hda0) := by
      calc (A' : GL (Fin p) K) = (Q : GL (Fin p) K)⁻¹ *
            ((Q : GL (Fin p) K) * A' * (Q : GL (Fin p) K)⁻¹) * Q := by group
        _ = _ := by
          rw [hsc, ← GeneralLinearGroup.scalar_commute _ (Q : GL (Fin p) K)⁻¹,
            inv_mul_cancel_right]
    exact primeFormConjHom_eq_one_of_coe_eq_scalar hA'sc
  have hcore := glaPLayer_ne_bot_of_unitary_diagonal_block h hp hp2 h₀ hbar₀ he2 hpe hX haa'
    hda hdc
  have hσQ : primeFormFieldU h (isPrimeFormGram_idGram (K := K) (n := p)) σ Q = Q :=
    Subtype.ext (by rw [coe_primeFormFieldU, hQ]; exact glAut_subfieldGL_aux σ p R₀)
  have e2 : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
      primeFormConjHom h (idGram K p) Q *
      (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ)⁻¹ =
      primeFormConjHom h (idGram K p) Q := by
    have := primeFormField_conj_eq h (isPrimeFormGram_idGram (K := K) (n := p)) σ Q
    rwa [hσQ] at this
  have hfconj : primeFormConjHom h (idGram K p) Q *
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
      (primeFormConjHom h (idGram K p) Q)⁻¹ =
      primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ := by
    calc primeFormConjHom h (idGram K p) Q *
          primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
          (primeFormConjHom h (idGram K p) Q)⁻¹
        = (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
            primeFormConjHom h (idGram K p) Q *
            (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ)⁻¹) *
          primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
          (primeFormConjHom h (idGram K p) Q)⁻¹ := by rw [e2]
      _ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ := by group
  have hcX : primeFormConjHom h (idGram K p) (Q * A' * Q⁻¹) =
      primeFormConjHom h (idGram K p) Q * primeFormConjHom h (idGram K p) A' *
        (primeFormConjHom h (idGram K p) Q)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  apply HDescLinRes.glaPLayer_ne_bot_of_conj hp (primeFormConjHom h (idGram K p) Q)
  rw [hfconj, ← hcX]
  exact hcore

end Reduction

section UniModel

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem glaPLayer_ne_bot_of_field_unitary_prime {f : ℕ} (h : UnitaryFieldData 2 f K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpe : p ∣ 2 ^ (f / p) + 1) (he2 : 2 ≤ f / p)
    {x c : MulAut (primeFormP h (idGram K p))} (hxp : x ^ p = 1)
    (hxD : x ∉ primeFormD h (idGram K p)) (hcD : c ∈ primeFormD h (idGram K p)) (hc1 : c ≠ 1)
    (hcp : c ^ p = 1) (hcomm : x * c = c * x) {t : primeFormP h (idGram K p)} (ht : orderOf t = 2)
    (hct : c t = t) : GLAPLayer p (fixSubgroup x ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hf2 : 2 ≤ f := le_trans he2 (Nat.div_le_self f p)
  have hne : ¬ (p = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h2] at h4
    norm_num at h4
  obtain ⟨σ, hσdef⟩ : ∃ σ : K ≃+* K, primeFormFieldFactor h
      (isPrimeFormGram_idGram (K := K) (n := p)) hp3 hne x = σ := ⟨_, rfl⟩
  have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := p)) hp3 hne
  have hσp : σ ^ p = 1 := by rw [← hσdef, ← map_pow, hxp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hxD
    rw [← hker, MonoidHom.mem_ker, hσdef, h1]
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hxo : orderOf x = p := orderOf_eq_prime hxp (fun h0 => hxD (h0 ▸ Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, N, hN⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hp3 hne
      hp hp2 x hxo σ hσdef hσo
  obtain ⟨M, rfl⟩ := hcD
  obtain ⟨g, hg⟩ : ∃ g : MulAut (primeFormP h (idGram K p)),
      g = primeFormConjHom h (idGram K p) N := ⟨_, rfl⟩
  have hcM' : primeFormConjHom h (idGram K p) (N⁻¹ * M * N) =
      g⁻¹ * primeFormConjHom h (idGram K p) M * g := by
    rw [hg, map_mul, map_mul, map_inv]
  have hfσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ = g⁻¹ * x * g := by
    rw [hg]
    exact hN.symm
  have hM1 : primeFormConjHom h (idGram K p) (N⁻¹ * M * N) ≠ 1 := by
    rw [hcM']
    intro h1
    apply hc1
    calc primeFormConjHom h (idGram K p) M =
          g * (g⁻¹ * primeFormConjHom h (idGram K p) M * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hMp : primeFormConjHom h (idGram K p) (N⁻¹ * M * N) ^ p = 1 := by
    rw [hcM']
    have := conj_pow (a := g⁻¹) (b := primeFormConjHom h (idGram K p) M) (i := p)
    rw [inv_inv] at this
    rw [this, hcp]
    group
  have hcomm' : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ *
      primeFormConjHom h (idGram K p) (N⁻¹ * M * N) =
      primeFormConjHom h (idGram K p) (N⁻¹ * M * N) *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ := by
    rw [hfσ, hcM']
    calc g⁻¹ * x * g * (g⁻¹ * primeFormConjHom h (idGram K p) M * g)
        = g⁻¹ * (x * primeFormConjHom h (idGram K p) M) * g := by group
      _ = g⁻¹ * (primeFormConjHom h (idGram K p) M * x) * g := by rw [hcomm]
      _ = g⁻¹ * primeFormConjHom h (idGram K p) M * g * (g⁻¹ * x * g) := by group
  have ht' : orderOf (g⁻¹ t) = 2 :=
    (orderOf_injective (g⁻¹ : MulAut (primeFormP h (idGram K p))).toMonoidHom
      (MulEquiv.injective _) t).trans ht
  have hfix' : primeFormConjHom h (idGram K p) (N⁻¹ * M * N) (g⁻¹ t) = g⁻¹ t := by
    rw [hcM']
    simp only [MulAut.mul_apply, MulAut.apply_inv_self, hct]
  have hred := glaPLayer_ne_bot_of_fieldHom_conjHom_prime h hp hp2 hσo hpe he2 hM1 hMp hcomm' ht'
    hfix'
  apply HDescLinRes.glaPLayer_ne_bot_of_conj hp g⁻¹
  rw [show g⁻¹ * x * g⁻¹⁻¹ = primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := p)) σ by
      rw [hfσ, inv_inv],
    show g⁻¹ * primeFormConjHom h (idGram K p) M * g⁻¹⁻¹ =
      primeFormConjHom h (idGram K p) (N⁻¹ * M * N) by rw [hcM', inv_inv]]
  exact hred

theorem exists_layer_of_unitary_model_prime {T : Type} [Group T] [Finite T] {f : ℕ}
    (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpe : p ∣ 2 ^ (f / p) + 1) (he2 : 2 ≤ f / p) (eT : T ≃* primeFormP h (idGram K p))
    {β : MulAut T} (hβp : β ^ p = 1) (hβD : MulAut.congr eT β ∉ primeFormD h (idGram K p))
    (Eb : Subgroup (MulAut T)) (hEp : ∀ c ∈ Eb, c ^ p = 1)
    (hEcomm : ∀ c ∈ Eb, β * c = c * β) (hpE : p ^ 2 ≤ Nat.card Eb) {t : T} (ht : orderOf t = 2)
    (hEt : ∀ c ∈ Eb, c t = t) :
    ∃ c ∈ Eb, c ∉ Subgroup.zpowers β ∧ GLAPLayer p (fixSubgroup β ⊓ fixSubgroup c) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut (primeFormP h (idGram K p))) :=
    Finite.of_injective
      (fun (g : MulAut (primeFormP h (idGram K p))) (w : primeFormP h (idGram K p)) => g w)
      (fun g g' hgg' => MulEquiv.ext (congrFun hgg'))
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hf2 : 2 ≤ f := le_trans he2 (Nat.div_le_self f p)
  have hne : ¬ (p = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h2] at h4
    norm_num at h4
  have hφinj : Function.Injective (MulAut.congr eT).toMonoidHom := (MulAut.congr eT).injective
  have hcard' : Nat.card (Eb.map (MulAut.congr eT).toMonoidHom) = Nat.card Eb :=
    Subgroup.card_map_of_injective hφinj
  have hEp' : ∀ c ∈ Eb.map (MulAut.congr eT).toMonoidHom, c ^ p = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hEp c hc, map_one]
  have hbound := card_le_mul_card_inf_primeFormD h hp3 hne hp
    (B := Eb.map (MulAut.congr eT).toMonoidHom) hEp'
  have hne' : (Eb.map (MulAut.congr eT).toMonoidHom ⊓ primeFormD h (idGram K p) :
      Subgroup (MulAut (primeFormP h (idGram K p)))) ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, hcard'] at hbound
    have h2 : p * p ≤ p * 1 := by
      rw [← sq]
      exact hpE.trans hbound
    have h3 := Nat.le_of_mul_le_mul_left h2 hp.pos
    have h4 := hp.one_lt
    omega
  obtain ⟨⟨c', hc'⟩, hc'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne'
  obtain ⟨hc'E, hc'D⟩ := Subgroup.mem_inf.1 hc'
  obtain ⟨c, hcE, rfl⟩ := hc'E
  have hcD : MulAut.congr eT c ∈ primeFormD h (idGram K p) := hc'D
  have hc1 : MulAut.congr eT c ≠ 1 := fun h0 => hc'1 (Subtype.ext h0)
  have hxp : MulAut.congr eT β ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hcp : MulAut.congr eT c ^ p = 1 := by rw [← map_pow, hEp c hcE, map_one]
  have hxc : MulAut.congr eT β * MulAut.congr eT c = MulAut.congr eT c * MulAut.congr eT β := by
    rw [← map_mul, ← map_mul, hEcomm c hcE]
  have hxo : Nat.card (Subgroup.zpowers (MulAut.congr eT β)) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hxp (fun h0 => hβD (h0 ▸ Subgroup.one_mem _))
  have hxD := CFSG.LocalAnalysis.GLTheoremA.S265.s265_inf_zpowers_bot hp hxo hβD
  refine ⟨c, hcE, ?_, ?_⟩
  · intro hcβ
    apply hc1
    have hmem : MulAut.congr eT c ∈
        (primeFormD h (idGram K p) ⊓ Subgroup.zpowers (MulAut.congr eT β) : Subgroup _) := by
      refine Subgroup.mem_inf.2 ⟨hcD, ?_⟩
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hcβ
      exact Subgroup.mem_zpowers_iff.2 ⟨i, (map_zpow (MulAut.congr eT) β i).symm⟩
    rw [hxD] at hmem
    exact Subgroup.mem_bot.1 hmem
  · apply S265F3.glaPLayer_ne_bot_of_congr hp eT
    have ht' : orderOf (eT t) = 2 := (orderOf_injective eT.toMonoidHom eT.injective t).trans ht
    have hct : MulAut.congr eT c (eT t) = eT t := by
      show eT (c (eT.symm (eT t))) = eT t
      rw [MulEquiv.symm_apply_apply, hEt c hcE]
    exact glaPLayer_ne_bot_of_field_unitary_prime h hp hp2 hpe he2 hxp hβD hcD hc1 hcp hxc ht' hct

end UniModel

end CFSG.LocalAnalysis.GLTheoremA.S265F5

end
