module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

open CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Defs

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def twIncl (σ : K ≃+* K) :
    ↥(twistedE6RootGroup K σ) →* ↥(adjointGroup Tag.E6 K) :=
  Subgroup.inclusion ((graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom).trans
    (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom))

noncomputable abbrev twR (σ η : K ≃+* K) : Subgroup ↥(twistedE6RootGroup K σ) :=
  fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)

noncomputable abbrev twRP (σ η : K ≃+* K) : Subgroup ↥(adjointGroup Tag.E6 K) :=
  (twR σ η).map (twIncl σ)

structure TwE6Setup (K : Type) [Field K] [Finite K] (σ η : K ≃+* K) (p : ℕ) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  ne_char : p ≠ ringChar K
  order_eta : orderOf η = p
  frob : ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card K = (ℓ ^ f) ^ 2 ∧ ∀ c, σ c = c ^ (ℓ ^ f)

theorem TwE6Setup.two_lt {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}
    (hS : TwE6Setup K σ η p) : 2 < p :=
  lt_of_le_of_ne hS.prime.two_le (Ne.symm hS.ne_two)

noncomputable abbrev xE6 {K : Type} [Field K] (γ : Fin Tag.E6.rank → ℤ) (c : K) :
    ↥(adjointGroup Tag.E6 K) :=
  xPar (rootOperatorFamily Tag.E6) γ c

structure TwGens (σ η : K ≃+* K) (R' : Subgroup ↥(adjointGroup Tag.E6 K)) : Prop where
  fixedX : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c → xE6 (Pi.single i 1) c ∈ R'
  fixedY : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c → xE6 (-Pi.single i 1) c ∈ R'
  orbX : ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)), ∀ c : K, η c = c →
    xE6 (Pi.single ij.1 1) c * xE6 (Pi.single ij.2 1) (σ c) ∈ R'
  orbY : ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)), ∀ c : K, η c = c →
    xE6 (-Pi.single ij.1 1) c * xE6 (-Pi.single ij.2 1) (σ c) ∈ R'

structure TwFull (σ : K ≃+* K) (R' : Subgroup ↥(adjointGroup Tag.E6 K)) : Prop where
  fixedX : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → xE6 (Pi.single i 1) c ∈ R'
  fixedY : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → xE6 (-Pi.single i 1) c ∈ R'
  orbX : ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)), ∀ c : K,
    xE6 (Pi.single ij.1 1) c * xE6 (Pi.single ij.2 1) (σ c) ∈ R'
  orbY : ∀ ij ∈ ({(0, 5), (2, 4)} : Finset (Fin 6 × Fin 6)), ∀ c : K,
    xE6 (-Pi.single ij.1 1) c * xE6 (-Pi.single ij.2 1) (σ c) ∈ R'

end Defs

section Basic

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

theorem twIncl_injective (σ : K ≃+* K) : Function.Injective (twIncl σ) :=
  Subgroup.inclusion_injective _

theorem coe_twIncl (σ : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    ((twIncl σ g : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) = (g : ModGL TwistTag.E6.tag K) :=
  rfl

theorem twIncl_fieldActor (σ η : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    twIncl σ (fieldActor (t := TwistTag.E6) σ η g) = entrywiseAdjointAut Tag.E6 η (twIncl σ g) := by
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut]
  exact coe_fieldActor σ η g

theorem mem_twR_iff (σ η : K ≃+* K) (g : ↥(twistedE6RootGroup K σ)) :
    g ∈ twR σ η ↔ entrywiseAdjointAut Tag.E6 η (twIncl σ g) = twIncl σ g := by
  rw [mem_fixedSubgroup, ← twIncl_fieldActor]
  exact (twIncl_injective σ).eq_iff.symm

theorem TwGens.mono {σ η : K ≃+* K} {R' R'' : Subgroup ↥(adjointGroup Tag.E6 K)} (h : TwGens σ η R')
    (hle : R' ≤ R'') : TwGens σ η R'' :=
  ⟨fun i hi c h1 h2 => hle (h.fixedX i hi c h1 h2), fun i hi c h1 h2 => hle (h.fixedY i hi c h1 h2),
    fun ij hij c h1 => hle (h.orbX ij hij c h1), fun ij hij c h1 => hle (h.orbY ij hij c h1)⟩

private theorem twGens_pow_comm (hc : ∀ x : K, η (σ x) = σ (η x)) (k : ℕ) (x : K) :
    η ((σ ^ k) x) = (σ ^ k) (η x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ', RingAut.mul_apply, RingAut.mul_apply, hc, ih]

private theorem twGens_hom_pow (τ : K ≃+* K) (k : ℕ) (x : K) :
    (τ.toRingHom ^ k) x = (τ ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, RingAut.mul_apply]
    exact ih (τ x)

private theorem twGens_sigma_sq (hS : TwE6Setup K σ η p) : σ ^ 2 = 1 := by
  obtain ⟨_, _, -, -, hK, hσ⟩ := hS.frob
  ext c
  haveI := Fintype.ofFinite K
  rw [pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card,
    FiniteField.pow_card] <;> rfl

private theorem twGens_xE6_single (i : Fin Tag.E6.rank) (c : K) :
    xPar (rootOperatorFamily Tag.E6) (Pi.single i 1) c = xElement i c :=
  endHom_injective (by rw [xPar_simple, endHom_xElt]; rfl)

private theorem twGens_xE6_neg_single (i : Fin Tag.E6.rank) (c : K) :
    xPar (rootOperatorFamily Tag.E6) (-Pi.single i 1) c = yElement i c :=
  endHom_injective (by rw [xPar_neg_simple, endHom_yElt]; rfl)

private theorem twGens_xE6_congr {i j : Fin 6} {x y : K} (hi : i.val = j.val) (hx : x = y) :
    xE6 (Pi.single i 1) x = xE6 (Pi.single j 1) y := by
  obtain rfl : i = j := Fin.ext hi
  subst hx; rfl

private theorem twGens_xE6_congr_neg {i j : Fin 6} {x y : K} (hi : i.val = j.val) (hx : x = y) :
    xE6 (-Pi.single i 1) x = xE6 (-Pi.single j 1) y := by
  obtain rfl : i = j := Fin.ext hi
  subst hx; rfl

private theorem twGens_entry_xE6 (γ : Fin Tag.E6.rank → ℤ) (x : K) (hx : η x = x) :
    entrywiseAdjointAut Tag.E6 η (xE6 γ x) = xE6 γ x := by
  have h := CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar (τ := Tag.E6)
    (F := rootOperatorFamily Tag.E6) η γ x
  rw [hx] at h
  exact h

private theorem twGens_orbitX (τ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K τ.toRingHom a) :
    twIncl τ (fixedOrbitX TwistTag.E6 K τ.toRingHom a c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        xE6 (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((τ ^ k) (c : K))).prod := by
  have h1 : twIncl τ (fixedOrbitX TwistTag.E6 K τ.toRingHom a c) =
      orbitX TwistTag.E6 K τ.toRingHom a c := rfl
  rw [h1, orbitX]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [twGens_hom_pow]
  exact (twGens_xE6_single _ _).symm

private theorem twGens_orbitY (τ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K τ.toRingHom a) :
    twIncl τ (fixedOrbitY TwistTag.E6 K τ.toRingHom a c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        xE6 (-Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((τ ^ k) (c : K))).prod := by
  have h1 : twIncl τ (fixedOrbitY TwistTag.E6 K τ.toRingHom a c) =
      orbitY TwistTag.E6 K τ.toRingHom a c := rfl
  rw [h1, orbitY]
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [twGens_hom_pow]
  exact (twGens_xE6_neg_single _ _).symm

private theorem twGens_orbitX_mem (hc : ∀ x : K, η (σ x) = σ (η x))
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a)
    (hη : η (c : K) = c) :
    fixedOrbitX TwistTag.E6 K σ.toRingHom a c ∈ twR σ η := by
  rw [mem_twR_iff, twGens_orbitX, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact twGens_entry_xE6 _ _ (by rw [twGens_pow_comm hc, hη])

private theorem twGens_orbitY_mem (hc : ∀ x : K, η (σ x) = σ (η x))
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a)
    (hη : η (c : K) = c) :
    fixedOrbitY TwistTag.E6 K σ.toRingHom a c ∈ twR σ η := by
  rw [mem_twR_iff, twGens_orbitY, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  exact twGens_entry_xE6 _ _ (by rw [twGens_pow_comm hc, hη])

theorem twR_gens (hS : TwE6Setup K σ η p) : TwGens σ η (twRP σ η) := by
  have hσ2 : σ ^ 2 = 1 := twGens_sigma_sq hS
  have hc : ∀ x : K, η (σ x) = σ (η x) := ringEquiv_comm_of_finite σ η
  have hcard0 : (TwistTag.E6.orbit (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 2 := by
    decide
  have hcard1 : (TwistTag.E6.orbit (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 2 := by
    decide
  have hcard2 : (TwistTag.E6.orbit (⟨2, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 1 := by
    decide
  have hcard3 : (TwistTag.E6.orbit (⟨3, by decide⟩ : Fin TwistTag.E6.foldedTag.rank)).card = 1 := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi c h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        twGens_orbitX_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitX, hcard3, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twGens_xE6_congr (by decide) rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        twGens_orbitX_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitX, hcard2, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twGens_xE6_congr (by decide) rfl
  · intro i hi c h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        twGens_orbitY_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitY, hcard3, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twGens_xE6_congr_neg (by decide) rfl
    · refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩
        ⟨c, mem_orbitField_of_fixed (σ := σ.toRingHom) (c := c) h1 _⟩,
        twGens_orbitY_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitY, hcard2, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact twGens_xE6_congr_neg (by decide) rfl
  · intro ij hij c h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard0, twGens_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc2⟩,
        twGens_orbitX_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitX, hcard0, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twGens_xE6_congr (by decide) rfl) (twGens_xE6_congr (by decide) rfl)
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard1, twGens_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitX TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ ⟨c, hc2⟩,
        twGens_orbitX_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitX, hcard1, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twGens_xE6_congr (by decide) rfl) (twGens_xE6_congr (by decide) rfl)
  · intro ij hij c h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨0, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard0, twGens_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc2⟩,
        twGens_orbitY_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitY, hcard0, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twGens_xE6_congr_neg (by decide) rfl)
        (twGens_xE6_congr_neg (by decide) rfl)
    · have hc2 : c ∈ orbitField TwistTag.E6 K σ.toRingHom
          (⟨1, by decide⟩ : Fin TwistTag.E6.foldedTag.rank) :=
        mem_orbitField.2 (by rw [hcard1, twGens_hom_pow, hσ2] <;> rfl)
      refine Subgroup.mem_map.2 ⟨fixedOrbitY TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ ⟨c, hc2⟩,
        twGens_orbitY_mem hc _ _ h2, ?_⟩
      rw [twGens_orbitY, hcard1, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact congrArg₂ (· * ·) (twGens_xE6_congr_neg (by decide) rfl)
        (twGens_xE6_congr_neg (by decide) rfl)

private theorem twE6_sigma_ne_one (hS : TwE6Setup K σ η p) : σ ≠ 1 := by
  obtain ⟨ℓ, f, hℓ, hf, hK, hσ⟩ := hS.frob
  intro h1
  haveI := Fintype.ofFinite K
  have hall : ∀ c : K, c ^ (ℓ ^ f) = c := fun c => by
    have h2 := hσ c
    rw [h1, RingAut.one_apply] at h2
    exact h2.symm
  have hq : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hq
  have hP0 : (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hP0]
    show Polynomial.eval c (Polynomial.X ^ (ℓ ^ f) - Polynomial.X : Polynomial K) = 0
    simp [hall c]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at hcard
  nlinarith

private theorem twE6_orderOf_sigma (hS : TwE6Setup K σ η p) : orderOf σ = 2 := by
  have hsq : σ ^ 2 = 1 := by
    obtain ⟨ℓ, f, hℓ, hf, hK, hσ⟩ := hS.frob
    ext c
    haveI := Fintype.ofFinite K
    rw [pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  exact orderOf_eq_prime hsq (twE6_sigma_ne_one hS)

private theorem twE6_fix_closure_iff (S : Set (K ≃+* K)) (a : K) :
    (∀ τ ∈ Subgroup.closure S, τ a = a) ↔ ∀ τ ∈ S, τ a = a := by
  refine ⟨fun h τ hτ => h τ (Subgroup.subset_closure hτ), fun h τ hτ => ?_⟩
  induction hτ using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rfl
  | mul x y _ _ hx hy => rw [RingAut.mul_apply, hy, hx]
  | inv x _ hx =>
    rw [RingAut.inv_apply]
    conv_lhs => rw [← hx]
    exact RingEquiv.symm_apply_apply x a

private theorem twE6_fix_zpowers_iff (g : K ≃+* K) (a : K) :
    (∀ τ ∈ Subgroup.zpowers g, τ a = a) ↔ g a = a := by
  rw [Subgroup.zpowers_eq_closure, twE6_fix_closure_iff]
  simp

private theorem twE6_fix_pair_iff (g h : K ≃+* K) (a : K) :
    (∀ τ ∈ Subgroup.closure ({g, h} : Set (K ≃+* K)), τ a = a) ↔ g a = a ∧ h a = a := by
  rw [twE6_fix_closure_iff]
  simp

private theorem twE6_card_fixSet {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n) (hK : Nat.card K = ℓ ^ n)
    (A : Subgroup (K ≃+* K)) :
    Nat.card {a : K | ∀ τ ∈ A, τ a = a} = ℓ ^ (n / Nat.card A) ∧ Nat.card A ∣ n := by
  obtain ⟨-, -, -, -, -, h⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hn hK
  obtain ⟨hdvd, S, hS, hcard⟩ := h A
  refine ⟨?_, hdvd⟩
  rw [← hS, SetLike.coe_sort_coe]
  exact hcard

private theorem twE6_eq_of_div {n x y : ℕ} (hn : 0 < n) (hx : x ∣ n) (hy : y ∣ n)
    (h : n / x = n / y) : x = y := by
  have hx' : x * (n / x) = n := Nat.mul_div_cancel' hx
  have hy' : y * (n / y) = n := Nat.mul_div_cancel' hy
  rw [h] at hx'
  have hpos : 0 < n / y := by
    rcases Nat.eq_zero_or_pos (n / y) with h0 | h0
    · rw [h0, mul_zero] at hy'
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hpos (hx'.trans hy'.symm)

theorem TwE6Setup.orderOf_restrict (hS : TwE6Setup K σ η p) : orderOf (fixSubfieldRestrict η σ) = p := by
  obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := hS.frob
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ 2 * f := by omega
  have hKn : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hσ2 : Nat.card (Subgroup.zpowers σ) = 2 :=
    (Nat.card_zpowers σ).trans (twE6_orderOf_sigma hS)
  have hηp : η ^ p = 1 := by
    rw [← hS.order_eta]
    exact pow_orderOf_eq_one η
  apply orderOf_eq_prime (fixSubfieldRestrict_pow_eq_one σ hηp)
  intro h1
  have hsub : ∀ a : K, σ a = a → η a = a := by
    intro a ha
    have ha' : a ∈ fixSubfield σ := (mem_fixSubfield σ).2 ha
    have h2 : (fixSubfieldRestrict η σ ⟨a, ha'⟩ : K) =
        ((1 : fixSubfield σ ≃+* fixSubfield σ) ⟨a, ha'⟩ : K) :=
      congrArg (fun x : fixSubfield σ ≃+* fixSubfield σ => (x ⟨a, ha'⟩ : K)) h1
    exact h2
  have hset : {a : K | ∀ τ ∈ Subgroup.closure ({η, σ} : Set (K ≃+* K)), τ a = a} =
      {a : K | ∀ τ ∈ Subgroup.zpowers σ, τ a = a} := by
    ext a
    simp only [Set.mem_setOf_eq, twE6_fix_pair_iff, twE6_fix_zpowers_iff]
    exact ⟨fun h => h.2, fun h => ⟨hsub a h, h⟩⟩
  obtain ⟨hB, hBd⟩ := twE6_card_fixSet hℓ hn hKn (Subgroup.closure ({η, σ} : Set (K ≃+* K)))
  obtain ⟨hZ, -⟩ := twE6_card_fixSet hℓ hn hKn (Subgroup.zpowers σ)
  rw [hset] at hB
  rw [hσ2] at hZ
  have e2 := Nat.pow_right_injective hℓ.two_le (hB.symm.trans hZ)
  have hBcard : Nat.card (Subgroup.closure ({η, σ} : Set (K ≃+* K))) = 2 :=
    twE6_eq_of_div (by omega) hBd (dvd_mul_right 2 f) e2
  have hηmem : η ∈ Subgroup.closure ({η, σ} : Set (K ≃+* K)) :=
    Subgroup.subset_closure (by simp)
  have hpd : Nat.card (Subgroup.zpowers η) ∣
      Nat.card (Subgroup.closure ({η, σ} : Set (K ≃+* K))) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hηmem)
  rw [Nat.card_zpowers, hS.order_eta, hBcard] at hpd
  have hle := Nat.le_of_dvd (by norm_num) hpd
  have := hS.two_lt
  omega

theorem TwE6Setup.exists_fixEta_not_fixSigma (hS : TwE6Setup K σ η p) : ∃ u : K, η u = u ∧ σ u ≠ u := by
  obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := hS.frob
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ 2 * f := by omega
  have hKn : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hσ2 : Nat.card (Subgroup.zpowers σ) = 2 :=
    (Nat.card_zpowers σ).trans (twE6_orderOf_sigma hS)
  by_contra hcon
  push Not at hcon
  have hset : {a : K | ∀ τ ∈ Subgroup.closure ({η, σ} : Set (K ≃+* K)), τ a = a} =
      {a : K | ∀ τ ∈ Subgroup.zpowers η, τ a = a} := by
    ext a
    simp only [Set.mem_setOf_eq, twE6_fix_pair_iff, twE6_fix_zpowers_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hcon a h⟩⟩
  obtain ⟨hB, hBd⟩ := twE6_card_fixSet hℓ hn hKn (Subgroup.closure ({η, σ} : Set (K ≃+* K)))
  obtain ⟨hZ, hZd⟩ := twE6_card_fixSet hℓ hn hKn (Subgroup.zpowers η)
  rw [hset] at hB
  have e2 := Nat.pow_right_injective hℓ.two_le (hB.symm.trans hZ)
  rw [Nat.card_zpowers, hS.order_eta] at e2 hZd
  have hBp : Nat.card (Subgroup.closure ({η, σ} : Set (K ≃+* K))) = p :=
    twE6_eq_of_div (by omega) hBd hZd e2
  have hσmem : σ ∈ Subgroup.closure ({η, σ} : Set (K ≃+* K)) :=
    Subgroup.subset_closure (by simp)
  have hσd : Nat.card (Subgroup.zpowers σ) ∣
      Nat.card (Subgroup.closure ({η, σ} : Set (K ≃+* K))) :=
    Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hσmem)
  rw [hσ2, hBp] at hσd
  have h2p : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hσd
  have := hS.two_lt
  omega

theorem TwE6Setup.four_le_card (hS : TwE6Setup K σ η p) : 4 ≤ Nat.card K := by
  obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := hS.frob
  rw [hK]
  have h2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ (ℓ ^ f) ^ 2 := Nat.pow_le_pow_left h2 2

theorem TwE6Setup.sigma_sq (hS : TwE6Setup K σ η p) : σ ^ 2 = 1 := by
  obtain ⟨ℓ, f, hℓ, hf, hK, hσ⟩ := hS.frob
  ext c
  haveI := Fintype.ofFinite K
  rw [pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card,
    FiniteField.pow_card]
  rfl

theorem TwE6Setup.sigma_ne_one (hS : TwE6Setup K σ η p) : σ ≠ 1 :=
  twE6_sigma_ne_one hS

theorem isMaxHeightRoot_perm_fixed {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    permLattice TwistTag.E6.perm θ = θ := by
  have key : ∀ t ∈ rootFinset Tag.E6, (∀ γ ∈ rootFinset Tag.E6, height γ ≤ height t) →
      permLattice (τ := Tag.E6) TwistTag.E6.perm t = t := by
    decide +kernel
  exact key θ (mem_rootFinset.2 hθ.1) fun γ hγ => hθ.2 γ (mem_rootFinset.1 hγ)

private theorem twE6_xPar_fixed_root_smul_single {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) :
    ∃ w ∈ relWeylTwist TwistTag.E6, ∃ j : Fin TwistTag.E6.tag.rank,
      TwistTag.E6.perm j = j ∧ w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = γ := by
  haveI : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩
  obtain ⟨w, hw, a, ha⟩ := TwistTag.exists_diagramOrbit_eq TwistTag.E6 hγ
  have hO : TwistTag.E6.diagramOrbit γ = ({γ} : Finset (Fin TwistTag.E6.tag.rank → ℤ)) :=
    diagramOrbit_eq_singleton_of_fixed hρ
  have hmem : ∀ i ∈ TwistTag.E6.orbit a,
      w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) = γ := by
    intro i hi
    have h : w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ∈
        TwistTag.E6.diagramOrbit γ := by
      rw [ha]
      exact Finset.mem_image_of_mem (fun k => w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) hi
    rw [hO] at h
    exact Finset.eq_of_mem_singleton h
  fin_cases a
  · exfalso
    have hp : (Pi.single (0 : Fin TwistTag.E6.tag.rank) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        Pi.single (5 : Fin TwistTag.E6.tag.rank) 1 :=
      MulAction.injective w ((hmem 0 (Finset.mem_insert_self (0 : Fin TwistTag.E6.tag.rank) {5})).trans
        (hmem 5 (Finset.mem_insert_of_mem (Finset.mem_singleton_self (5 : Fin TwistTag.E6.tag.rank)))).symm)
    exact absurd (congrFun hp 0) (by simp [Pi.single_apply])
  · exfalso
    have hp : (Pi.single (2 : Fin TwistTag.E6.tag.rank) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        Pi.single (4 : Fin TwistTag.E6.tag.rank) 1 :=
      MulAction.injective w ((hmem 2 (Finset.mem_insert_self (2 : Fin TwistTag.E6.tag.rank) {4})).trans
        (hmem 4 (Finset.mem_insert_of_mem (Finset.mem_singleton_self (4 : Fin TwistTag.E6.tag.rank)))).symm)
    exact absurd (congrFun hp 2) (by simp [Pi.single_apply])
  · exact ⟨w, hw, 3, rfl, hmem 3 (Finset.mem_singleton_self (3 : Fin TwistTag.E6.tag.rank))⟩
  · exact ⟨w, hw, 1, rfl, hmem 1 (Finset.mem_singleton_self (1 : Fin TwistTag.E6.tag.rank))⟩

private theorem twE6_xPar_fixed_eq_pinnedX {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (c : K) :
    ((xE6 γ c : ↥(adjointGroup Tag.E6 K)) : ModGL Tag.E6 K) =
      pinnedX Tag.E6 K γ (((rootOperatorFamily Tag.E6).pinnedFamilySign γ : K) * c) := by
  have hss := (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K γ
  rw [(rootOperatorFamily Tag.E6).pinnedX_eq_eltUnit K hγ, ← mul_assoc, hss, one_mul, xE6,
    xPar_of_isRoot hγ, (rootOperatorFamily Tag.E6).coe_eltElement]

private theorem twE6_xPar_fixed_pinnedX_mem {γ : Fin Tag.E6.rank → ℤ} {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) {j : Fin TwistTag.E6.tag.rank}
    (hj : TwistTag.E6.perm j = j)
    (hwj : w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) = γ) {σ' : K ≃+* K} {c : K}
    (hc : σ' c = c) {u : K} (hu : u * u = 1) :
    pinnedX Tag.E6 K γ (u * c) ∈ twistedE6RootGroup K σ' := by
  obtain ⟨ε, hε, hconj⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single TwistTag.E6.tag j)
  have hn : canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈
      graphFixedRootGroup TwistTag.E6 K σ'.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup hw
  have hv : (ε * u) * (ε * u) = 1 := by linear_combination (u * u) * hε + hu
  have hd : σ'.toRingHom ((ε * u) * c) = (ε * u) * c := by
    rcases mul_self_eq_one_iff.1 hv with h | h <;> simp [h, hc, RingEquiv.coe_toRingHom]
  have hx : pinnedX TwistTag.E6.tag K (Pi.single j 1) ((ε * u) * c) ∈
      graphFixedRootGroup TwistTag.E6 K σ'.toRingHom := by
    rw [pinnedX_single]
    exact graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.E6 K σ'.toRingHom
      (xUnit_mem_graphFixedPosUnipotent hj hd)
  have key := hconj ((ε * u) * c)
  have e : ε * ((ε * u) * c) = u * c := by linear_combination (u * c) * hε
  rw [e] at key
  have hkey : pinnedX Tag.E6 K γ (u * c) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K w * pinnedX TwistTag.E6.tag K (Pi.single j 1)
        ((ε * u) * c) * (canonicalRep (coxeterSystem TwistTag.E6.tag) K w)⁻¹ := by
    rw [← hwj]
    exact key.symm
  rw [hkey]
  exact mul_mem (mul_mem hn hx) (inv_mem hn)

private theorem twE6_xPar_fixed_range (σ : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {c : K} (hc : σ c = c) :
    ∃ x : ↥(twistedE6RootGroup K σ), twIncl σ x = xE6 γ c := by
  obtain ⟨w, hw, j, hj, hwj⟩ := twE6_xPar_fixed_root_smul_single hγ hρ
  have hu : ((rootOperatorFamily Tag.E6).pinnedFamilySign γ : K) *
      ((rootOperatorFamily Tag.E6).pinnedFamilySign γ : K) = 1 :=
    (rootOperatorFamily Tag.E6).pinnedFamilySign_mul_self K γ
  refine ⟨⟨pinnedX Tag.E6 K γ (((rootOperatorFamily Tag.E6).pinnedFamilySign γ : K) * c),
    twE6_xPar_fixed_pinnedX_mem hw hj hwj hc hu⟩, ?_⟩
  apply Subtype.ext
  rw [coe_twIncl]
  exact (twE6_xPar_fixed_eq_pinnedX hγ c).symm

private theorem twE6_xPar_fixed_twR (σ η : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {c : K} (hc : σ c = c) (hηc : η c = c) :
    ∃ x ∈ twR σ η, twIncl σ x = xE6 γ c := by
  obtain ⟨x, hx⟩ := twE6_xPar_fixed_range σ hγ hρ hc
  refine ⟨x, ?_, hx⟩
  rw [mem_twR_iff, hx, CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar, hηc]

theorem xPar_fixed_mem_twIncl_range (σ : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {c : K} (hc : σ c = c) :
    ∃ x : ↥(twistedE6RootGroup K σ),
      twIncl σ x = xE6 γ c := by
  exact twE6_xPar_fixed_range σ hγ hρ hc

theorem xPar_fixed_mem_twR (σ η : K ≃+* K) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hρ : permLattice TwistTag.E6.perm γ = γ) {c : K} (hc : σ c = c) (hηc : η c = c) :
    ∃ x ∈ twR σ η, twIncl σ x = xE6 γ c := by
  exact twE6_xPar_fixed_twR σ η hγ hρ hc hηc

theorem twIncl_fixedOrbitX (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    twIncl σ (fixedOrbitX TwistTag.E6 K σ.toRingHom a c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        xE6 (Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((σ ^ k) (c : K))).prod := by
  exact twGens_orbitX σ a c

theorem twIncl_fixedOrbitY (σ : K ≃+* K) (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    twIncl σ (fixedOrbitY TwistTag.E6 K σ.toRingHom a c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k =>
        xE6 (-Pi.single ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) 1) ((σ ^ k) (c : K))).prod := by
  exact twGens_orbitY σ a c

theorem twE6_eq_top_of_twFull (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (h : TwFull σ (H.map (twIncl σ))) : H = ⊤ := by
  clear hσ2
  have hfin : ∀ a : Fin TwistTag.E6.foldedTag.rank, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by decide
  have hX : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      fixedOrbitX TwistTag.E6 K σ.toRingHom a c ∈ H := by
    intro a c
    have hP : twIncl σ (fixedOrbitX TwistTag.E6 K σ.toRingHom a c) ∈ H.map (twIncl σ) := by
      rw [twIncl_fixedOrbitX]
      rcases hfin a with rfl | rfl | rfl | rfl
      · rw [show (TwistTag.E6.orbit 0).card = 2 by decide, show List.range 2 = [0, 1] by decide]
        have e0 : TwistTag.E6.orbitMin 0 = 0 := by decide
        have e1 : TwistTag.E6.perm 0 = 5 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          pow_one, e0, e1, Equiv.Perm.one_apply]
        exact h.orbX (0, 5) (by decide) (c : K)
      · rw [show (TwistTag.E6.orbit 1).card = 2 by decide, show List.range 2 = [0, 1] by decide]
        have e0 : TwistTag.E6.orbitMin 1 = 2 := by decide
        have e1 : TwistTag.E6.perm 2 = 4 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          pow_one, e0, e1, Equiv.Perm.one_apply]
        exact h.orbX (2, 4) (by decide) (c : K)
      · have hσc : σ (c : K) = c := (mem_orbitField_iff_of_card_eq_one (by decide)).1 c.2
        rw [show (TwistTag.E6.orbit 2).card = 1 by decide, show List.range 1 = [0] by decide]
        have e0 : TwistTag.E6.orbitMin 2 = 3 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          e0, Equiv.Perm.one_apply]
        exact h.fixedX 3 (by decide) (c : K) hσc
      · have hσc : σ (c : K) = c := (mem_orbitField_iff_of_card_eq_one (by decide)).1 c.2
        rw [show (TwistTag.E6.orbit 3).card = 1 by decide, show List.range 1 = [0] by decide]
        have e0 : TwistTag.E6.orbitMin 3 = 1 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          e0, Equiv.Perm.one_apply]
        exact h.fixedX 1 (by decide) (c : K) hσc
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hP
    rwa [twIncl_injective σ hyeq] at hy
  have hY : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      fixedOrbitY TwistTag.E6 K σ.toRingHom a c ∈ H := by
    intro a c
    have hP : twIncl σ (fixedOrbitY TwistTag.E6 K σ.toRingHom a c) ∈ H.map (twIncl σ) := by
      rw [twIncl_fixedOrbitY]
      rcases hfin a with rfl | rfl | rfl | rfl
      · rw [show (TwistTag.E6.orbit 0).card = 2 by decide, show List.range 2 = [0, 1] by decide]
        have e0 : TwistTag.E6.orbitMin 0 = 0 := by decide
        have e1 : TwistTag.E6.perm 0 = 5 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          pow_one, e0, e1, Equiv.Perm.one_apply]
        exact h.orbY (0, 5) (by decide) (c : K)
      · rw [show (TwistTag.E6.orbit 1).card = 2 by decide, show List.range 2 = [0, 1] by decide]
        have e0 : TwistTag.E6.orbitMin 1 = 2 := by decide
        have e1 : TwistTag.E6.perm 2 = 4 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          pow_one, e0, e1, Equiv.Perm.one_apply]
        exact h.orbY (2, 4) (by decide) (c : K)
      · have hσc : σ (c : K) = c := (mem_orbitField_iff_of_card_eq_one (by decide)).1 c.2
        rw [show (TwistTag.E6.orbit 2).card = 1 by decide, show List.range 1 = [0] by decide]
        have e0 : TwistTag.E6.orbitMin 2 = 3 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          e0, Equiv.Perm.one_apply]
        exact h.fixedY 3 (by decide) (c : K) hσc
      · have hσc : σ (c : K) = c := (mem_orbitField_iff_of_card_eq_one (by decide)).1 c.2
        rw [show (TwistTag.E6.orbit 3).card = 1 by decide, show List.range 1 = [0] by decide]
        have e0 : TwistTag.E6.orbitMin 3 = 1 := by decide
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_zero,
          e0, Equiv.Perm.one_apply]
        exact h.fixedY 1 (by decide) (c : K) hσc
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hP
    rwa [twIncl_injective σ hyeq] at hy
  have hsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hle : ⨆ a, (orbitRankOneHomFixed TwistTag.E6 K σ.toRingHom a).range ≤ H := by
    refine iSup_le fun a => ?_
    rw [range_eq_sl2RootX_sup_sl2RootY]
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      dsimp only
      rw [orbitRankOneHomFixed_sl2Upper]
      exact hX a c
    · rintro _ ⟨c, rfl⟩
      dsimp only
      rw [orbitRankOneHomFixed_sl2Lower]
      exact hY a c
  rw [iSup_range_orbitRankOneHomFixed hsurj] at hle
  exact eq_top_iff.2 hle

theorem isRoot_sub_single_one {θ : Fin Tag.E6.rank → ℤ} (hθ : IsMaxHeightRoot Tag.E6 θ) :
    IsRoot Tag.E6 (θ - Pi.single 1 1) ∧ permLattice TwistTag.E6.perm (θ - Pi.single 1 1) = θ - Pi.single 1 1 := by
  have key : ∀ t ∈ rootFinset Tag.E6, (∀ γ ∈ rootFinset Tag.E6, height γ ≤ height t) →
      (t - Pi.single 1 1 ∈ rootFinset Tag.E6 ∧
        permLattice (τ := Tag.E6) TwistTag.E6.perm (t - Pi.single 1 1) = t - Pi.single 1 1) := by
    decide +kernel
  obtain ⟨h1, h2⟩ := key θ (mem_rootFinset.2 hθ.1) fun γ hγ => hθ.2 γ (mem_rootFinset.1 hγ)
  exact ⟨mem_rootFinset.1 h1, h2⟩

theorem TwE6Setup.of_data {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hη : orderOf η = p) : TwE6Setup K σ η p := by
  haveI := Fintype.ofFinite K
  have hK' : Fintype.card K = ℓ ^ (f * 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow hK'
  have hc : ringChar K = ℓ := ringChar.eq K ℓ
  exact ⟨hp, hp2, by rw [hc]; exact hpℓ, hη, ⟨ℓ, f, hℓ, hf, hK, hσ⟩⟩

end Basic

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
