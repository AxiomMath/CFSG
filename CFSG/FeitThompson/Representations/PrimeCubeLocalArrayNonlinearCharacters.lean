module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
import CFSG.FeitThompson.Representations.JoinedLayersStrictBoundRemainingChars
import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.PGroupIrreducibleDegreePower
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import CFSG.FeitThompson.Representations.QuotientLayerDegreeSquareSum
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Local.PrimeCubeNonabelianCommutatorCentre
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalLinearInduced NormalInduction

private noncomputable def degOf {X : Type*} [Group X] (θ : X → ℂ) : ℕ := ⌊(θ 1).re⌋₊

private theorem coe_degOf {X : Type*} [Group X] [Finite X] {θ : X → ℂ} (hθ : θ ∈ Irr X) :
    θ 1 = (degOf θ : ℂ) := by
  obtain ⟨k, -, hk, -⟩ := Irr.exists_degree hθ
  rw [degOf, hk]
  norm_num

private theorem degOf_pos {X : Type*} [Group X] [Finite X] {θ : X → ℂ} (hθ : θ ∈ Irr X) :
    0 < degOf θ := by
  obtain ⟨k, hk, hk1, -⟩ := Irr.exists_degree hθ
  have h1 : (degOf θ : ℂ) = (k : ℂ) := by rw [← coe_degOf hθ, hk1]
  have : degOf θ = k := by exact_mod_cast h1
  omega

private theorem degOf_eq_one_iff {X : Type*} [Group X] [Finite X] {θ : X → ℂ} (hθ : θ ∈ Irr X) :
    degOf θ = 1 ↔ θ 1 = 1 := by
  refine ⟨fun hd => by rw [coe_degOf hθ, hd, Nat.cast_one], fun h1 => ?_⟩
  have : (degOf θ : ℂ) = ((1 : ℕ) : ℂ) := by rw [← coe_degOf hθ, h1]; norm_num
  exact_mod_cast this

private theorem sum_sq_degOf (X : Type*) [Group X] [Finite X] :
    ∑ θ ∈ irrFinset X, degOf θ ^ 2 = Nat.card X := by
  have h : ((∑ θ ∈ irrFinset X, degOf θ ^ 2 : ℕ) : ℂ) = (Nat.card X : ℂ) := by
    push_cast
    rw [← sum_character_one_sq' (G := X)]
    exact Finset.sum_congr rfl fun θ hθ => by rw [coe_degOf (mem_irrFinset.1 hθ)]
  exact_mod_cast h

private theorem card_filter_apply_one (X : Type*) [Group X] [Finite X] :
    ((irrFinset X).filter (fun θ => θ 1 = 1)).card = Nat.card (X ⧸ commutator X) := by
  classical
  have hset : (irrFinset X).filter (fun θ => θ 1 = 1) = irrTrivialOnFinset (commutator X) := by
    ext θ
    rw [Finset.mem_filter, mem_irrFinset, mem_irrTrivialOnFinset,
      ← Irr.setOf_apply_one_eq_one_eq_irrTrivialOn_commutator, Set.mem_sep_iff]
  have hsum : ∑ θ ∈ irrTrivialOnFinset (commutator X), θ 1 ^ 2
      = (Nat.card (X ⧸ commutator X) : ℂ) := sum_sq_degree_irrTrivialOn
  have hone : ∀ θ ∈ irrTrivialOnFinset (commutator X), θ 1 ^ 2 = (1 : ℂ) := by
    intro θ hθ
    rw [mem_irrTrivialOnFinset, ← Irr.setOf_apply_one_eq_one_eq_irrTrivialOn_commutator,
      Set.mem_sep_iff] at hθ
    rw [hθ.2, one_pow]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact_mod_cast hset ▸ hsum

private theorem card_nonprincipalLinearIrr (X : Type*) [Group X] [Finite X] :
    (finite_nonprincipalLinearIrr (K := X)).toFinset.card = Nat.card (X ⧸ commutator X) - 1 := by
  classical
  have hset : (finite_nonprincipalLinearIrr (K := X)).toFinset
      = ((irrFinset X).filter (fun θ => θ 1 = 1)).erase 1 := by
    ext θ
    rw [Set.Finite.mem_toFinset, mem_nonprincipalLinearIrr, Finset.mem_erase, Finset.mem_filter,
      mem_irrFinset]
    tauto
  have h1mem : (1 : X → ℂ) ∈ (irrFinset X).filter (fun θ => θ 1 = 1) :=
    Finset.mem_filter.2 ⟨mem_irrFinset.2 one_mem_Irr, rfl⟩
  rw [hset, Finset.card_erase_of_mem h1mem, card_filter_apply_one X]

private theorem prime_cube_exhaust {X : Type*} [Group X] [Finite X] {p d : ℕ}
    (hp : p.Prime) (hX : Nat.card X = p ^ 3) (hnab : ¬ IsMulCommutative X)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = p - 1)
    (χ : ι → X → ℂ) (hχirr : ∀ i, χ i ∈ Irr X) (hχinj : Function.Injective χ)
    (hdeg : ∀ i, χ i 1 = (d : ℂ)) (hd1 : 1 < d) :
    d = p ∧ ∀ θ ∈ Irr X, θ 1 ≠ 1 → ∃ i, χ i = θ := by
  classical
  have hp2 := hp.two_le
  have hcomm : Nat.card ↥(commutator X) = p :=
    card_commutator_of_card_eq_prime_cube hp hX hnab
  have hquot : Nat.card (X ⧸ commutator X) = p ^ 2 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator X)
    rw [hX, hcomm] at hc
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    rw [h3] at hc
    exact (Nat.eq_of_mul_eq_mul_right hp.pos hc).symm
  have hpsub : p ^ 3 - p ^ 2 = (p - 1) * p ^ 2 := by
    rw [Nat.sub_mul, one_mul]
    congr 1
    ring
  have hsplit : ∑ θ ∈ (irrFinset X).filter (fun θ => θ 1 = 1), degOf θ ^ 2
      + ∑ θ ∈ (irrFinset X).filter (fun θ => ¬ θ 1 = 1), degOf θ ^ 2 = p ^ 3 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_sq_degOf, hX]
  have hlin : ∑ θ ∈ (irrFinset X).filter (fun θ => θ 1 = 1), degOf θ ^ 2 = p ^ 2 := by
    have hterm : ∀ θ ∈ (irrFinset X).filter (fun θ => θ 1 = 1), degOf θ ^ 2 = 1 := by
      intro θ hθ
      obtain ⟨hmem, h1⟩ := Finset.mem_filter.1 hθ
      rw [(degOf_eq_one_iff (mem_irrFinset.1 hmem)).2 h1, one_pow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_filter_apply_one X, hquot,
      smul_eq_mul, mul_one]
  have hnonlin : ∑ θ ∈ (irrFinset X).filter (fun θ => ¬ θ 1 = 1), degOf θ ^ 2
      = p ^ 3 - p ^ 2 := by omega
  set F : Finset (X → ℂ) := Finset.image χ Finset.univ with hF
  have hFcard : F.card = p - 1 := by
    rw [hF, Finset.card_image_of_injective _ hχinj, Finset.card_univ, hι]
  have hFsub : F ⊆ (irrFinset X).filter (fun θ => ¬ θ 1 = 1) := by
    intro θ hθ
    rw [hF, Finset.mem_image] at hθ
    obtain ⟨i, -, rfl⟩ := hθ
    refine Finset.mem_filter.2 ⟨mem_irrFinset.2 (hχirr i), ?_⟩
    rw [hdeg i]
    intro hc
    have : d = 1 := by exact_mod_cast hc
    omega
  have hFdeg : ∀ θ ∈ F, degOf θ = d := by
    intro θ hθ
    rw [hF, Finset.mem_image] at hθ
    obtain ⟨i, -, rfl⟩ := hθ
    have : (degOf (χ i) : ℂ) = (d : ℂ) := by rw [← coe_degOf (hχirr i), hdeg i]
    exact_mod_cast this
  have hFsum : ∑ θ ∈ F, degOf θ ^ 2 = (p - 1) * d ^ 2 := by
    rw [Finset.sum_congr rfl fun θ hθ => by rw [hFdeg θ hθ], Finset.sum_const, hFcard,
      smul_eq_mul]
  have hle : (p - 1) * d ^ 2 ≤ (p - 1) * p ^ 2 := by
    rw [← hpsub, ← hFsum, ← hnonlin]
    exact Finset.sum_le_sum_of_subset hFsub
  have hd_le : d ≤ p :=
    Nat.pow_le_pow_iff_left (n := 2) (by norm_num) |>.1
      (Nat.le_of_mul_le_mul_left hle (by omega))
  have hne : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hι]
    omega
  obtain ⟨i⟩ := hne
  obtain ⟨b, -, hb⟩ := Irr.exists_one_eq_pow_of_card_eq_prime_pow hp hX (hχirr i)
  rw [hdeg i] at hb
  have hbn : d = p ^ b := by exact_mod_cast hb
  have hd_ge : p ≤ d := by
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · rw [pow_zero] at hbn; omega
    · rw [hbn]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos hbpos
  have hdp : d = p := le_antisymm hd_le hd_ge
  refine ⟨hdp, fun θ hθ hθ1 => ?_⟩
  have hFsum' : ∑ θ ∈ F, degOf θ ^ 2 = p ^ 3 - p ^ 2 := by rw [hFsum, hdp, hpsub]
  have heq : F = (irrFinset X).filter (fun θ => ¬ θ 1 = 1) := by
    by_contra hcon
    obtain ⟨x, hx, hxn⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hFsub hcon)
    have hxmem : x ∈ irrFinset X := (Finset.mem_filter.1 hx).1
    have hpos : 0 < degOf x ^ 2 := by
      have := degOf_pos (mem_irrFinset.1 hxmem)
      positivity
    have hlt := Finset.sum_lt_sum_of_subset (f := fun θ => degOf θ ^ 2) hFsub hx hxn hpos
      (fun _ _ _ => Nat.zero_le _)
    rw [hFsum', hnonlin] at hlt
    omega
  have hmem : θ ∈ F := by
    rw [heq]
    exact Finset.mem_filter.2 ⟨mem_irrFinset.2 hθ, hθ1⟩
  rw [hF, Finset.mem_image] at hmem
  obtain ⟨i', -, hi'⟩ := hmem
  exact ⟨i', hi'⟩

private theorem card_indFamLinearFinset_mul {L : Type*} [Group L] [Fintype L] {K : Subgroup L}
    [K.Normal] (hirr : indFamLinear K ⊆ Irr L) :
    (indFamLinearFinset K).card * K.index
      = (finite_nonprincipalLinearIrr (K := ↥K)).toFinset.card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun θ : ↥K → ℂ => indClassFun K θ)
    (s := (finite_nonprincipalLinearIrr (K := ↥K)).toFinset) (t := indFamLinearFinset K)
    (fun θ hθ => mem_indFamLinearFinset.2
      (indClassFun_mem_indFamLinear K (Set.Finite.mem_toFinset _ |>.1 hθ)))]
  have hfiber : ∀ f ∈ indFamLinearFinset K,
      (((finite_nonprincipalLinearIrr (K := ↥K)).toFinset).filter
        (fun ψ => indClassFun K ψ = f)).card = K.index := by
    intro f hf
    obtain ⟨θ, hθ, rfl⟩ := (mem_indFamLinear K).1 (mem_indFamLinearFinset.1 hf)
    have hfib : ((finite_nonprincipalLinearIrr (K := ↥K)).toFinset).filter
        (fun ψ => indClassFun K ψ = indClassFun K θ) = conjOrbit K θ := by
      ext ψ
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, mem_conjOrbit]
      refine ⟨fun hψ => (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun K
          (nonprincipalLinearIrr_subset_Irr hψ.1) (nonprincipalLinearIrr_subset_Irr hθ)).1 hψ.2,
        ?_⟩
      rintro ⟨t, rfl⟩
      have hmem : conjClassFun K t θ ∈ nonprincipalLinearIrr ↥K := by
        obtain ⟨hirr', h1, hne⟩ := mem_nonprincipalLinearIrr.1 hθ
        refine mem_nonprincipalLinearIrr.2 ⟨conjClassFun_mem_Irr K t hirr', ?_, ?_⟩
        · rw [conjClassFun_apply, map_one, h1]
        · intro hc
          refine hne (funext fun x => ?_)
          have hx := congrFun hc ((MulAut.conjNormal t⁻¹).symm x)
          rw [conjClassFun_apply, MulEquiv.apply_symm_apply] at hx
          simpa using hx
      exact ⟨hmem, (NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun K
        (nonprincipalLinearIrr_subset_Irr hmem)
        (nonprincipalLinearIrr_subset_Irr hθ)).2 ⟨t, rfl⟩⟩
    rw [hfib]
    have hind : indClassFun K θ ∈ Irr L := hirr (indClassFun_mem_indFamLinear K hθ)
    have hnorm : cfInner (indClassFun K θ) (indClassFun K θ) = 1 := cfInner_self_of_mem_Irr hind
    have hrel := cfInner_self_indClassFun K (nonprincipalLinearIrr_subset_Irr hθ)
    rw [hnorm] at hrel
    have h1 : K.relIndex (inertiaGroup K θ) = 1 := by
      have : ((K.relIndex (inertiaGroup K θ) : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
        rw [← hrel]; norm_num
      exact_mod_cast this
    have hle : inertiaGroup K θ ≤ K := Subgroup.relIndex_eq_one.1 h1
    have hge : K ≤ inertiaGroup K θ :=
      le_inertiaGroup K (Irr_subset_classFun (nonprincipalLinearIrr_subset_Irr hθ))
    rw [card_conjOrbit, le_antisymm hle hge]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]

variable {L : Type*} [Group L] [Fintype L] {K W₁ W₂ : Subgroup L} [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)]

structure IsPrimeCubeArrayHyp (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (ζ : L → ℂ) (p d n : ℕ) (δ : ℂ) : Prop where
  isometry : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ
  zeta_mem_indFam : ζ ∈ indFam K (Irr ↥K \ {1})
  zeta_mem_Irr : ζ ∈ Irr L
  zeta_one : ζ 1 = (Nat.card ↥W₁ : ℂ)
  one_lt_d : 1 < d
  two_le_n : 2 ≤ n
  sign : δ = 1 ∨ δ = -1
  primeTIirr_one_eq : ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)), j ≠ principalIrr ↥W₂ →
    h.primeTIirr σ i j 1 = (d : ℂ)
  primeTISign_eq : ∀ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ → h.primeTISign σ j = δ
  degree_eq : (d : ℂ) - δ = (n : ℂ) * (Nat.card ↥W₁ : ℂ)
  prime : p.Prime
  odd : Odd p
  card_K : Nat.card ↥K = p ^ 3
  not_isMulCommutative : ¬ IsMulCommutative ↥K
  card_W₂ : Nat.card ↥W₂ = p
  le_commutator : W₂ ≤ (⁅K, K⁆ : Subgroup L)

noncomputable def alphaArray (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) (ζ : L → ℂ) (n : ℕ) (δ : ℂ)
    (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)) : L → ℂ :=
  h.primeTIirr σ i j - δ • h.primeTIirr σ i (principalIrr ↥W₂) - (n : ℂ) • ζ

omit [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem alphaArray_apply (h : IsPrimeCyclicTIHyp K W₁ W₂)
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} (ζ : L → ℂ) (n : ℕ) (δ : ℂ)
    (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)) (x : L) :
    alphaArray h σ ζ n δ i j x =
      h.primeTIirr σ i j x - δ * h.primeTIirr σ i (principalIrr ↥W₂) x - (n : ℂ) * ζ x := (rfl)

noncomputable def primeTIrowFam (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L) : Set (L → ℂ) :=
  h.primeTIrow σ '' {j : ↑(Irr ↥W₂) | j ≠ principalIrr ↥W₂}

omit [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₂)] in
theorem mem_primeTIrowFam {h : IsPrimeCyclicTIHyp K W₁ W₂}
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} {f : L → ℂ} :
    f ∈ primeTIrowFam h σ ↔ ∃ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ ∧ h.primeTIrow σ j = f :=
  Iff.rfl

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem IsPrimeCyclicTIHyp.apply_one_of_mem_indFamLinear (h : IsPrimeCyclicTIHyp K W₁ W₂)
    {f : L → ℂ} (hf : f ∈ indFamLinear K) : f 1 = (Nat.card ↥W₁ : ℂ) := by
  rw [NormalLinearInduced.apply_one_of_mem_indFamLinear K hf,
    h.isComplement'_left.index_eq_card]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem indFamLinear_subset_indFam :
    indFamLinear K ⊆ indFam K (Irr ↥K \ {1}) := by
  rw [NormalLinearInduced.indFamLinear_eq_indFam]
  refine indFam_mono K fun θ hθ => ?_
  obtain ⟨hirr, -, hne⟩ := mem_nonprincipalLinearIrr.1 hθ
  exact ⟨hirr, hne⟩

namespace IsPrimeCubeArrayHyp

variable {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} {ζ : L → ℂ} {p d n : ℕ} {δ : ℂ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂} (hA : IsPrimeCubeArrayHyp h σ ζ p d n δ)

include hA

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem three_le_prime : 3 ≤ p := by
  have h2 := hA.prime.two_le
  rcases eq_or_ne p 2 with rfl | hne
  · exact absurd hA.odd (by decide)
  · omega

omit [Fintype ↑(Irr ↥W₁)] in
theorem card_Irr_right : Fintype.card ↑(Irr ↥W₂) = p := by
  have := h.isCyclicTIPair.isMulCommutative_right
  rw [← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative, hA.card_W₂]

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem nontrivial_K : Nontrivial ↥K := by
  refine Finite.one_lt_card_iff_nontrivial.1 ?_
  rw [hA.card_K]
  exact one_lt_pow₀ hA.prime.one_lt (by norm_num)

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem isSolvable_K : Group.IsSolvable ↥K := by
  have : Fact p.Prime := ⟨hA.prime⟩
  have hpg : IsPGroup p ↥K := IsPGroup.of_card hA.card_K
  have := hpg.isNilpotent
  infer_instance

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↑(Irr ↥W₂)] in
theorem primeTIres_apply_one (j : ↑(Irr ↥W₂)) (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIres σ j 1 = (d : ℂ) := by
  rw [h.primeTIres_one j, hA.primeTIirr_one_eq _ j hj]

theorem d_eq_prime_and_exists_primeTIres_eq :
    d = p ∧ ∀ θ ∈ Irr ↥K, θ 1 ≠ 1 →
      ∃ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ ∧ h.primeTIres σ j = θ := by
  classical
  have hcard : Fintype.card {j : ↑(Irr ↥W₂) // j ≠ principalIrr ↥W₂} = p - 1 := by
    rw [Fintype.card_subtype_compl (p := fun j => j = principalIrr ↥W₂),
      Fintype.card_subtype_eq, hA.card_Irr_right]
  obtain ⟨hd, hex⟩ := prime_cube_exhaust (X := ↥K) hA.prime hA.card_K hA.not_isMulCommutative
    hcard (fun j => h.primeTIres σ j.1)
    (fun j => h.primeTIres_mem_Irr hA.isometry j.1)
    (fun j k hjk => Subtype.ext (h.primeTIres_injective hA.isometry hjk))
    (fun j => hA.primeTIres_apply_one j.1 j.2) hA.one_lt_d
  refine ⟨hd, fun θ hθ hθ1 => ?_⟩
  obtain ⟨j, hj⟩ := hex θ hθ hθ1
  exact ⟨j.1, j.2, hj⟩

theorem d_eq_prime : d = p := hA.d_eq_prime_and_exists_primeTIres_eq.1

theorem exists_primeTIres_eq {θ : ↥K → ℂ} (hθ : θ ∈ Irr ↥K) (hθ1 : θ 1 ≠ 1) :
    ∃ j : ↑(Irr ↥W₂), j ≠ principalIrr ↥W₂ ∧ h.primeTIres σ j = θ :=
  hA.d_eq_prime_and_exists_primeTIres_eq.2 θ hθ hθ1

theorem indFamLinear_subset_Irr : indFamLinear K ⊆ Irr L := by
  have hnormal := h.normal
  have := hA.nontrivial_K
  have := hA.isSolvable_K
  exact indFamLinear_subset_Irr_of_centralizer_le h.isComplement'_left.symm h.coprime_natCard
    fun u hu hu1 => by rw [h.centralizer_eq u hu hu1]; exact hA.le_commutator

theorem ncard_indFamLinear_mul :
    (indFamLinear K).ncard * Nat.card ↥W₁ = p ^ 2 - 1 := by
  have hnormal := h.normal
  have hcoe : ((indFamLinearFinset K : Finset (L → ℂ)) : Set (L → ℂ)) = indFamLinear K := by
    ext f
    rw [Finset.mem_coe, mem_indFamLinearFinset]
  have hncard : (indFamLinear K).ncard = (indFamLinearFinset K).card := by
    rw [← hcoe, Set.ncard_coe_finset]
  have hquot : Nat.card (↥K ⧸ commutator ↥K) = p ^ 2 := by
    have hcomm : Nat.card ↥(commutator ↥K) = p :=
      card_commutator_of_card_eq_prime_cube hA.prime hA.card_K hA.not_isMulCommutative
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥K)
    rw [hA.card_K, hcomm] at hc
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    rw [h3] at hc
    exact (Nat.eq_of_mul_eq_mul_right hA.prime.pos hc).symm
  rw [hncard, ← h.isComplement'_left.index_eq_card,
    card_indFamLinearFinset_mul hA.indFamLinear_subset_Irr,
    card_nonprincipalLinearIrr ↥K, hquot]

theorem apply_one_of_mem_primeTIrowFam {f : L → ℂ} (hf : f ∈ primeTIrowFam h σ) :
    f 1 = (Nat.card ↥W₁ : ℂ) * (p : ℂ) := by
  obtain ⟨j, hj, rfl⟩ := mem_primeTIrowFam.1 hf
  rw [h.primeTIrow_one j, hA.primeTIres_apply_one j hj, hA.d_eq_prime]

theorem cfInner_self_of_mem_primeTIrowFam {f : L → ℂ} (hf : f ∈ primeTIrowFam h σ) :
    cfInner f f = (Nat.card ↥W₁ : ℂ) := by
  obtain ⟨j, -, rfl⟩ := mem_primeTIrowFam.1 hf
  exact h.cfInner_self_primeTIrow hA.isometry j

theorem primeTIrow_injective {j k : ↑(Irr ↥W₂)} (hjk : h.primeTIrow σ j = h.primeTIrow σ k) :
    j = k := by
  by_contra hne
  have h1 := h.cfInner_primeTIrow_primeTIirr hA.isometry k
  rw [← hjk, h.cfInner_primeTIrow_primeTIirr_of_ne hA.isometry hne] at h1
  exact zero_ne_one h1

theorem ncard_primeTIrowFam : (primeTIrowFam h σ).ncard = p - 1 := by
  classical
  have hinj : Set.InjOn (h.primeTIrow σ) {j : ↑(Irr ↥W₂) | j ≠ principalIrr ↥W₂} :=
    fun j _ k _ hjk => hA.primeTIrow_injective hjk
  rw [primeTIrowFam, hinj.ncard_image]
  have hcompl : {j : ↑(Irr ↥W₂) | j ≠ principalIrr ↥W₂} = ({principalIrr ↥W₂} : Set _)ᶜ := by
    ext j; simp
  rw [hcompl, Set.ncard_eq_toFinset_card', Set.toFinset_compl, Finset.card_compl]
  simp [hA.card_Irr_right]

theorem primeTIrowFam_subset_indFam : primeTIrowFam h σ ⊆ indFam K (Irr ↥K \ {1}) := by
  intro f hf
  obtain ⟨j, hj, rfl⟩ := mem_primeTIrowFam.1 hf
  refine (mem_indFam K).2 ⟨h.primeTIres σ j, ⟨h.primeTIres_mem_Irr hA.isometry j, ?_⟩,
    h.indClassFun_primeTIres hA.isometry j⟩
  intro hc
  have h1 : h.primeTIres σ j 1 = (d : ℂ) := hA.primeTIres_apply_one j hj
  rw [Set.mem_singleton_iff.1 hc] at h1
  have h2 : (1 : ℂ) = (d : ℂ) := by simpa using h1
  have : d = 1 := by exact_mod_cast h2.symm
  have := hA.one_lt_d
  omega

private theorem degree_ne_aux (h2 : (Nat.card ↥W₁ : ℂ) = (Nat.card ↥W₁ : ℂ) * (p : ℂ)) :
    False := by
  have hm : (Nat.card ↥W₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h3 : (Nat.card ↥W₁ : ℂ) * 1 = (Nat.card ↥W₁ : ℂ) * (p : ℂ) := by rw [mul_one]; exact h2
  have h4 : (1 : ℂ) = (p : ℂ) := mul_left_cancel₀ hm h3
  have h5 : 1 = p := by exact_mod_cast h4
  have := hA.three_le_prime
  omega

theorem disjoint_indFamLinear_primeTIrowFam :
    Disjoint (indFamLinear K) (primeTIrowFam h σ) := by
  rw [Set.disjoint_left]
  intro f hf1 hf2
  have h1 := h.apply_one_of_mem_indFamLinear hf1
  have h2 := hA.apply_one_of_mem_primeTIrowFam hf2
  rw [h1] at h2
  exact hA.degree_ne_aux h2

theorem indFam_eq_union :
    indFam K (Irr ↥K \ {1}) = indFamLinear K ∪ primeTIrowFam h σ := by
  refine Set.Subset.antisymm (fun f hf => ?_) (Set.union_subset indFamLinear_subset_indFam
    hA.primeTIrowFam_subset_indFam)
  obtain ⟨θ, ⟨hθ, hθ1⟩, rfl⟩ := (mem_indFam K).1 hf
  by_cases hlin : θ 1 = 1
  · refine Or.inl ((mem_indFamLinear K).2 ⟨θ, ?_, rfl⟩)
    exact mem_nonprincipalLinearIrr.2 ⟨hθ, hlin, fun hc => hθ1 (by simp [hc])⟩
  · obtain ⟨j, hj, hji⟩ := hA.exists_primeTIres_eq hθ hlin
    refine Or.inr (mem_primeTIrowFam.2 ⟨j, hj, ?_⟩)
    rw [← h.indClassFun_primeTIres hA.isometry j, hji]

theorem zeta_mem_indFamLinear : ζ ∈ indFamLinear K := by
  rcases (hA.indFam_eq_union ▸ hA.zeta_mem_indFam : ζ ∈ indFamLinear K ∪ primeTIrowFam h σ) with
    hz | hz
  · exact hz
  · exact absurd (hA.zeta_one ▸ hA.apply_one_of_mem_primeTIrowFam hz)
      fun hc => hA.degree_ne_aux hc

end IsPrimeCubeArrayHyp

end CFSG.FeitThompson
