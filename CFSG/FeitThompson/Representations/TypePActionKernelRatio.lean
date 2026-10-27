module

public import CFSG.FeitThompson.Representations.TypePThreeFittingNormBounds
import CFSG.FeitThompson.Representations.PairedFittingWitnessExcludesPartner
import CFSG.FeitThompson.Local.PairedFittingSaturationsDisjoint
import CFSG.FeitThompson.Representations.PairedSupportingKernelCollapse
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
public import CFSG.FeitThompson.Representations.TwoTISaturationsFourRegionAverage

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open CFSG.FeitThompson.Prep03
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd hallCoreOf fittingOf
  centralizerIn)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

namespace ActionKernelRatio

variable {G : Type*} [Group G]

noncomputable def partnerIndex (p q : ℕ) : ℚ := ((q : ℚ) ^ p - 1) / ((q : ℚ) - 1)

noncomputable def partnerDeficit (p q : ℕ) : ℚ :=
  ((q : ℚ) ^ p * partnerIndex p q - partnerIndex p q ^ 2 - ((q : ℚ) ^ p - 1)) /
    ((q : ℚ) ^ p * partnerIndex p q * (p : ℚ))

theorem mul_partnerDeficit {p q : ℕ} (hp : p ≠ 0) (hq : 2 ≤ q) :
    (p : ℚ) * partnerDeficit p q
      = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
          + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hQ : ((q : ℚ) - 1) ≠ 0 := by intro h; linarith [h]
  have hk1 : (1 : ℚ) < (q : ℚ) ^ p := one_lt_pow₀ (by linarith) hp
  have hK : ((q : ℚ) ^ p) ≠ 0 := by intro h; rw [h] at hk1; linarith
  have hK1 : ((q : ℚ) ^ p - 1) ≠ 0 := by intro h; linarith [h]
  have hP : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [partnerDeficit, partnerIndex]
  field_simp
  ring

theorem lt_div_of_div_lt {m : ℚ} {p q u c : ℕ} (hp : 0 < p) (hq : 0 < q) (hc : 0 < c)
    (h : m / (p : ℚ) < ((q : ℚ) * (u : ℚ)) / ((p : ℚ) ^ q * (c : ℚ))) :
    m * (p : ℚ) ^ (q - 1) / (q : ℚ) < (u : ℚ) / (c : ℚ) := by
  have hP : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hC : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc
  have hpow : ((p : ℚ)) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hfac : (0 : ℚ) < (p : ℚ) ^ q / (q : ℚ) := div_pos (pow_pos hP q) hQ
  have h2 := mul_lt_mul_of_pos_right h hfac
  have e1 : m / (p : ℚ) * ((p : ℚ) ^ q / (q : ℚ)) = m * (p : ℚ) ^ (q - 1) / (q : ℚ) := by
    rw [hpow]; field_simp
  have e2 : ((q : ℚ) * (u : ℚ)) / ((p : ℚ) ^ q * (c : ℚ)) * ((p : ℚ) ^ q / (q : ℚ))
      = (u : ℚ) / (c : ℚ) := by
    have hk : ((p : ℚ)) ^ q ≠ 0 := ne_of_gt (pow_pos hP q)
    field_simp
  rwa [e1, e2] at h2

theorem hallCoreIn_eq (M : Subgroup G) : Prep03.hallCoreIn M = hallCoreOf M := (rfl)

theorem fittingIn_eq [Finite G] (M : Subgroup G) : Prep03.fittingIn M = fittingOf M := (rfl)

theorem cent_eq (U M : Subgroup G) :
    cent U (Prep03.hallCoreIn M : Set G) = centralizerIn U (hallCoreOf M) := (rfl)

theorem isMinimalSimpleOdd_of_isAmbient [Fintype G] (hG : IsAmbient G) : IsMinimalSimpleOdd G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩

theorem primes_of_elementary_core_structure
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (hcfg : IsPConfigSetup G M U W₁ W₂) {p q : ℕ} (hp : p = Nat.card ↥W₂)
    (hq : q = Nat.card ↥W₁) : p.Prime ∧ q.Prime ∧ Odd p ∧ Odd q ∧ p ≠ q := by
  obtain ⟨-, hpp, hqp, hop, hoq, hpq, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isAmbient hG) M U W₁ W₂ hcfg.isCoatom hcfg.config p q hp hq
  exact ⟨hpp, hqp, hop, hoq, hpq⟩

theorem natCard_M_eq (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (hcfg : IsPConfigSetup G M U W₁ W₂) {p q : ℕ} (hp : p = Nat.card ↥W₂)
    (hq : q = Nat.card ↥W₁) :
    Nat.card ↥M = p ^ q * Nat.card ↥U * q := by
  obtain ⟨-, -, -, -, -, -, -, -, hsemi1, hsemi2, -, -, -, hcardH, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isAmbient hG) M U W₁ W₂ hcfg.isCoatom hcfg.config p q hp hq
  rw [hsemi1.natCard_eq_mul, hsemi2.natCard_eq_mul, hcardH, hq, mul_assoc]

theorem natCard_fittingIn_eq
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (hcfg : IsPConfigSetup G M U W₁ W₂) {p q c : ℕ} (hp : p = Nat.card ↥W₂)
    (hq : q = Nat.card ↥W₁) (hc : c = Nat.card ↥(cent U (Prep03.hallCoreIn M : Set G))) :
    Nat.card ↥(Prep03.fittingIn M) = p ^ q * c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcardH, -, -, -, -, -, -, hdir, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isAmbient hG) M U W₁ W₂ hcfg.isCoatom hcfg.config p q hp hq
  rw [fittingIn_eq, hdir.card_eq_mul, hcardH, hc, cent_eq]

theorem exists_partner (h₃ : CFSG.FeitThompson.Statements.FNI_type_p_prime_factors.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (hcfg : IsPConfigSetup G M U W₁ W₂) :
    ∃ N : Subgroup G, IsCoatom N ∧ N ≠ M ∧ ∃ V₀ : Subgroup G, V₀ ≤ N ∧
      IsWitnessedPConfiguration N V₀ W₂ W₁ ∧ M ⊓ N = W₁ ⊔ W₂ := by
  obtain ⟨-, -, -, -, -, N, hN, hNM, V₀, hV₀N, hV₀cfg, hint, -⟩ :=
    h₃ G (isMinimalSimpleOdd_of_isAmbient hG) M U W₁ W₂ hcfg.isCoatom hcfg.config _ _ rfl rfl
  exact ⟨N, hN, hNM, V₀, hV₀N, hV₀cfg, hint⟩

theorem sat_eq_conjugatesOfSet (A : Set G) : Prep03.sat A = Group.conjugatesOfSet A := by
  ext x
  simp only [Prep03.sat, conjSet, Set.mem_iUnion, Set.mem_image, Group.mem_conjugatesOfSet_iff,
    isConj_iff]
  constructor
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨a, ha, g⁻¹, by group⟩
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨c⁻¹, a, ha, by group⟩

theorem satSet_eq_conjugatesOfSet (A : Set G) :
    CFSG.FeitThompson.satSet A = Group.conjugatesOfSet A := by
  ext x
  simp only [CFSG.FeitThompson.satSet, CFSG.FeitThompson.conjSet, Set.mem_iUnion, Set.mem_image,
    Group.mem_conjugatesOfSet_iff, isConj_iff]
  constructor
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨a, ha, g⁻¹, by group⟩
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨c⁻¹, a, ha, by group⟩

omit [Group G] in
theorem sum_indicator_one [Fintype G] (s : Set G) :
    ∑ x : G, s.indicator (fun _ => (1 : ℝ)) x = (s.ncard : ℝ) := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.indicator_apply, Finset.sum_boole]

theorem sum_norm_sq_eq_of_cfInner_self_eq_one [Fintype G] {f : G → ℂ}
    (hf : cfInner f f = 1) : ∑ x : G, ‖f x‖ ^ 2 = (Nat.card G : ℝ) := by
  rw [cfInner_def] at hf
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : ∑ g : G, f g * (starRingEnd ℂ) (f g) = (Nat.card G : ℂ) := by
    field_simp at hf; linear_combination hf
  have h2 : ∀ g : G, f g * (starRingEnd ℂ) (f g) = ((‖f g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h2] at h1
  exact_mod_cast h1

theorem one_le_norm_apply_one_of_mem_signedIrr {f : G → ℂ} (hf : f ∈ signedIrr G) :
    1 ≤ ‖f 1‖ := by
  rcases mem_signedIrr.1 hf with h | h
  · obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr h
    rw [hd1, Complex.norm_natCast]; exact_mod_cast hd
  · obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr h
    have : f 1 = -(d : ℂ) := by rw [← hd1]; simp
    rw [this, norm_neg, Complex.norm_natCast]; exact_mod_cast hd

theorem isClassFun_norm_sq_add {ρ η : G → ℂ} (hρ : ρ ∈ classFun G) (hη : η ∈ classFun G) :
    IsClassFun (fun x => ‖ρ x‖ ^ 2 + ‖η x‖ ^ 2) := by
  rw [isClassFun_iff]; intro x g
  have hc : IsConj (x * g * x⁻¹) g := isConj_iff.2 ⟨x⁻¹, by group⟩
  simp only [mem_classFun.1 hρ _ _ hc, mem_classFun.1 hη _ _ hc]

theorem sum_eq_of_isTIWithNormalizer [Fintype G] {X Y A B : Subgroup G}
    (hX : IsTIWithNormalizer ((X : Set G) \ {1}) A)
    (hY : IsTIWithNormalizer ((Y : Set G) \ {1}) B)
    (hXY : (Group.conjugatesOfSet (X : Set G) \ {1}) ∩
      (Group.conjugatesOfSet (Y : Set G) \ {1}) = ∅)
    {f : G → ℝ} (hf : IsClassFun f) :
    ∑ x, f x = f 1 + A.index • ∑ x, ((X : Set G) \ {1}).indicator f x
      + B.index • ∑ x, ((Y : Set G) \ {1}).indicator f x
      + ∑ x, (Group.conjugatesOfSet (X : Set G) ∪
          Group.conjugatesOfSet (Y : Set G))ᶜ.indicator f x := by
  set P := Group.conjugatesOfSet (X : Set G) \ {1} with hP
  set Q := Group.conjugatesOfSet (Y : Set G) \ {1} with hQ
  have hone : Group.conjugatesOfSet (X : Set G) ∪ Group.conjugatesOfSet (Y : Set G)
      = ({1} : Set G) ∪ (P ∪ Q) := by
    rw [hP, hQ]
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    by_cases hx : x = 1 <;>
      simp [hx, one_mem_conjugatesOfSet_coe X, one_mem_conjugatesOfSet_coe Y]
  have h1P : (1 : G) ∉ P := by simp [hP]
  have h1Q : (1 : G) ∉ Q := by simp [hQ]
  have hPQ : Disjoint P Q := Set.disjoint_iff_inter_eq_empty.mpr hXY
  have huniv : (Set.univ : Set G) = (({1} : Set G) ∪ (P ∪ Q)) ∪
      (Group.conjugatesOfSet (X : Set G) ∪ Group.conjugatesOfSet (Y : Set G))ᶜ := by
    rw [← hone, Set.union_compl_self]
  have hsatX : ∑ᶠ x ∈ P, f x = A.index • ∑ᶠ x ∈ (X : Set G) \ {1}, f x := by
    rw [hP, ← conjugatesOfSet_sdiff_one X]
    exact hX.finsum_mem_conjugatesOfSet hf
  have hsatY : ∑ᶠ x ∈ Q, f x = B.index • ∑ᶠ x ∈ (Y : Set G) \ {1}, f x := by
    rw [hQ, ← conjugatesOfSet_sdiff_one Y]
    exact hY.finsum_mem_conjugatesOfSet hf
  have key : ∑ᶠ x : G, f x = f 1 + A.index • ∑ᶠ x ∈ (X : Set G) \ {1}, f x
      + B.index • ∑ᶠ x ∈ (Y : Set G) \ {1}, f x
      + ∑ᶠ x ∈ (Group.conjugatesOfSet (X : Set G) ∪
          Group.conjugatesOfSet (Y : Set G))ᶜ, f x := by
    rw [← finsum_mem_univ, huniv,
      finsum_mem_union (by rw [hone]; exact disjoint_compl_right) (Set.toFinite _)
        (Set.toFinite _),
      finsum_mem_union (by
          simp only [Set.disjoint_union_right, Set.disjoint_singleton_left]
          exact ⟨h1P, h1Q⟩) (Set.toFinite _) (Set.toFinite _),
      finsum_mem_union hPQ (Set.toFinite _) (Set.toFinite _), finsum_mem_singleton,
      hsatX, hsatY]
    ring
  have hconv : ∀ s : Set G, ∑ᶠ x ∈ s, f x = ∑ x, s.indicator f x := fun s => by
    rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  rw [hconv, hconv, hconv, finsum_eq_sum_of_fintype] at key
  exact key

theorem exists_irrEnum (X : Type*) [Group X] [Finite X] :
    ∃ (n : ℕ) (α : Fin n → X → ℂ) (i0 : Fin n) (bar : Fin n → Fin n),
      (∀ i, α i ∈ Irr X) ∧ Function.Injective α ∧ (∀ χ ∈ Irr X, ∃ i, α i = χ) ∧ α i0 = 1 ∧
      (∀ i, α (bar i) = fun y => (starRingEnd ℂ) (α i y)) := by
  classical
  let e := Finite.equivFin (Irr X)
  refine ⟨Nat.card (Irr X), fun i => (e.symm i : X → ℂ), e (principalIrr X),
    fun i => e (starIrr (e.symm i)), fun i => (e.symm i).2, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  · intro χ hχ
    exact ⟨e ⟨χ, hχ⟩, show ((e.symm (e ⟨χ, hχ⟩) : Irr X) : X → ℂ) = χ by
      rw [Equiv.symm_apply_apply]⟩
  · change ((e.symm (e (principalIrr X)) : Irr X) : X → ℂ) = 1
    rw [Equiv.symm_apply_apply, coe_principalIrr]
  · intro i
    change ((e.symm (e (starIrr (e.symm i))) : Irr X) : X → ℂ) = _
    rw [Equiv.symm_apply_apply, coe_starIrr_eq]

theorem prodChar_apply_of_coe_eq {A B : Subgroup G} (hW : IsCyclicTIPair (A ⊔ B) A B)
    (lam : ↥A → ℂ) (mu : ↥B → ℂ) (x : ↥A) (y : ↥B) (z : ↥(A ⊔ B))
    (hz : (z : G) = (x : G) * (y : G)) : hW.prodChar lam mu z = lam x * mu y := by
  have : z = ⟨(x : G) * (y : G), hz ▸ z.2⟩ := Subtype.ext hz
  rw [this, hW.prodChar_apply_mul lam mu x.2 y.2]

theorem exists_rowData [Fintype G] {M U A B : Subgroup G} (hodd : Odd (Nat.card G))
    (hc : IsWitnessedPConfiguration M U A B) (hW : IsCyclicTIPair (A ⊔ B) A B)
    {I J : Type} (α : I → ↥A → ℂ) (β : J → ↥B → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥A) (hαinj : Function.Injective α)
    (hαsurj : ∀ χ ∈ Irr ↥A, ∃ i, α i = χ) (hβ : ∀ j, β j ∈ Irr ↥B)
    {w : I → J → ↥(A ⊔ B) → ℂ}
    (hw : ∀ i j, ∀ x : ↥A, ∀ y : ↥B, ∀ z : ↥(A ⊔ B), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y) (i0 : I) :
    ∃ σ : (↥(A ⊔ B) → ℂ) → (↥M → ℂ), IsTIExtension A B M σ ∧
      ∃ δj : J → ℂ, (∀ j, δj j = 1 ∨ δj j = -1) ∧ (∀ j, δj j • σ (w i0 j) ∈ Irr ↥M) ∧
      ∃ ell : I → ↥M → ℂ, ∀ (i : I) (k : ↥(⁅M, M⁆ : Subgroup G)) (x : ↥A) (z : ↥M),
        (z : G) = (k : G) * (x : G) → ell i z = α i x := by
  classical
  have h1 := hc.le_M_W₁
  have h2 := hc.le_M_W₂
  obtain ⟨τl, hτl⟩ := (hc.isPrimeCyclicTIHyp_subgroupOf hodd).exists_isCyclicTIIsometry
  have hσ : IsTIExtension A B M ⇑(CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hW.isCyclic τl) :=
    CFSG.FeitThompson.Proofs.isTIExtension_sigma (sup_le h1 h2)
      (CFSG.FeitThompson.Proofs.Recip.isSigmaMap_sigmaT h1 h2 hW.isCyclic hτl)
  refine ⟨_, hσ, ?_⟩
  have hirr : ∀ j, w i0 j ∈ Irr ↥(A ⊔ B) := fun j => by
    rw [prodChar_eq_of_tensor hW (fun x y z hz => hw i0 j x y z hz)]
    exact hW.prodChar_mem_Irr (hα i0) (hβ j)
  have hsign : ∀ j, ∃ δ : ℂ, (δ = 1 ∨ δ = -1) ∧
      δ • (CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hW.isCyclic τl) (w i0 j) ∈ Irr ↥M := by
    intro j
    have hf := hirr j
    have h1' : (CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hW.isCyclic τl) (w i0 j)
        ∈ Submodule.span ℤ (Irr ↥M) :=
      mem_span_Irr_of_mem_virtualChars (hσ.maps_virtualChars _ (Irr_subset_virtualChars hf))
    have h2' : cfInner ((CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hW.isCyclic τl) (w i0 j))
        ((CFSG.FeitThompson.Proofs.Recip.sigmaT h1 h2 hW.isCyclic τl) (w i0 j)) = 1 := by
      rw [hσ.inner_eq]; exact cfInner_self_of_mem_Irr hf
    rcases mem_signedIrr.1 (mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one h1' h2') with
      h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  choose δj hδj hδjIrr using hsign
  refine ⟨δj, hδj, hδjIrr, ?_⟩
  have hP := OrientedCoreFamily.isPrimeCyclicTIHyp_commutator hodd hc
  refine ⟨fun i => hP.inflateLeft (OrientedCoreFamily.localIrrEquiv h1 α hα hαinj hαsurj i), ?_⟩
  intro i k x z hz
  have hkM : ((k : G)) ∈ M := Subgroup.commutator_le_self M k.2
  have hk : (⟨(k : G), hkM⟩ : ↥M) ∈ commutator ↥M := by
    rw [commutator_eq_subgroupOf_commutator]; exact Subgroup.mem_subgroupOf.2 k.2
  have hx : (⟨(x : G), h1 x.2⟩ : ↥M) ∈ A.subgroupOf M := Subgroup.mem_subgroupOf.2 x.2
  have hzz : z = (⟨(k : G), hkM⟩ : ↥M) * ⟨(x : G), h1 x.2⟩ := Subtype.ext hz
  simp only
  rw [hzz, hP.inflateLeft_apply_mul _ hk hx, OrientedCoreFamily.coe_localIrrEquiv]
  simp only [Function.comp_apply]
  congr 1

theorem bar_ne {X : Type*} {J : Type*} {β : J → X → ℂ} (hβinj : Function.Injective β)
    {j0 : J} (hβ0 : β j0 = 1) {bar : J → J}
    (hbar : ∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) {j : J} (hj : j ≠ j0) :
    bar j ≠ j0 := by
  intro h
  apply hj
  apply hβinj
  have h1 := hbar j
  rw [h, hβ0] at h1
  rw [hβ0]
  funext y
  have := congrFun h1 y
  simp only [Pi.one_apply] at this
  have h2 := congrArg (starRingEnd ℂ) this
  simpa using h2.symm

theorem bar_bar {X : Type*} {J : Type*} {β : J → X → ℂ} (hβinj : Function.Injective β)
    {bar : J → J} (hbar : ∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y)) (j : J) :
    bar (bar j) = j := by
  apply hβinj
  rw [hbar, hbar]
  funext y; simp

theorem exists_side_bounds
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₇ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    {G : Type u} [Group G] [Fintype G] (hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (hcfg : IsPConfigSetup G M U W₁ W₂)
    {I J : Type} [Finite I] [Finite J] (i0 : I) (j0' : J)
    (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ)
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    (hα0 : α i0 = 1) (hβ0 : β j0' = 1) (bar : J → J)
    (hbar : ∀ j, β (bar j) = fun y => (starRingEnd ℂ) (β j y))
    (w : I → J → ↥(W₁ ⊔ W₂) → ℂ)
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ))
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    (η : I → J → G → ℂ) (hη : ∀ i j, η i j = ω (w i j)) :
    ∃ ν : (↥M → ℂ) → (G → ℂ),
      IsAdditiveIsometryOn (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) ν ∧
      detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M) ⊆
        (Submodule.span ℤ (detectInd M (⁅M, M⁆ : Subgroup G) (Prep03.hallCoreIn M)) : Set (↥M → ℂ)) ∧
      (∀ i0' : I, i0' ≠ i0 → ∀ j₀ : J, j₀ ≠ j0' →
        ((Nat.card ↥(Prep03.fittingIn M) : ℝ) - 1 ≤ sumSqOn (Prep03.sharp (Prep03.fittingIn M)) (η i0' j0')) ∧
        ((Nat.card ↥(⁅M, M⁆ : Subgroup G) : ℝ) -
            ((cent U (Prep03.hallCoreIn M : Set G)).relIndex U : ℝ) ^ 2 ≤
          sumSqOn (Prep03.sharp (Prep03.fittingIn M)) (η i0 j₀)) ∧
        ∀ lam ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M) ∩ Irr ↥M,
          ((Nat.card ↥M : ℝ) - ((Nat.card ↥W₁ : ℝ) *
              ((cent U (Prep03.hallCoreIn M : Set G)).relIndex U : ℝ)) ^ 2 ≤
            sumSqOn (Prep03.sharp (Prep03.fittingIn M)) (ν lam))) ∧
      (∀ (Q : Subgroup G) (G0 : Set G),
        G0 = Set.univ \ (Prep03.sat (Prep03.fittingIn M : Set G) ∪ Prep03.sat (Q : Set G)) →
        ∀ lam ∈ detectInd M (Prep03.fittingIn M) (Prep03.hallCoreIn M), ∀ iStar : I, iStar ≠ i0 →
          (G0.ncard : ℝ) ≤
            ∑ x : G, Set.indicator G0 (fun y => ‖ν lam y‖ ^ 2 + ‖η iStar j0' y‖ ^ 2) x) := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have : Fintype J := Fintype.ofFinite J
  have hc := hcfg.config
  have hW := hc.isCyclicTIPair_sup_of_isAmbient h₂ hG hcfg.isCoatom
  obtain ⟨σ, hσ, δj, hδj, hδjIrr, ell, hell⟩ :=
    exists_rowData hG.odd_natCard hc hW α β hα hαinj hαsurj hβ hw i0
  set u := (cent U (Prep03.hallCoreIn M : Set G)).relIndex U with hu
  obtain ⟨-, ν, δ, e, hδ, he, hνiso, hTS, hdeg, hνind, -, hrow, -, hSirr, hcolorth, hdist⟩ :=
    CFSG.FeitThompson.Proofs.FCH_type_p_oriented_core_family h₁ h₂ h₄ h₅ h₆ h₇ G hG M U W₁ W₂ hcfg
      u rfl I J inferInstance inferInstance i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0
      bar hbar w hw σ ω hσ hω δj (fun j => δj j • σ (w i0 j)) ell
      (fun i j => ell i * (δj j • σ (w i0 j))) (fun j => ∑ i : I, ell i * (δj j • σ (w i0 j))) η
      hδj (fun _ => rfl) hδjIrr hell (fun _ _ => rfl) (fun _ => rfl) hη _ _ rfl rfl
  refine ⟨ν, hνiso, hTS, ?_, ?_⟩
  · intro i0' hi0' j₀ hj₀
    exact CFSG.FeitThompson.Proofs.FCH_type_p_three_fitting_norm_bounds h₂ G hG M U W₁ W₂ hcfg u rfl
      I J inferInstance inferInstance i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0
      bar hbar w hw σ ω hσ hω δj (fun j => δj j • σ (w i0 j)) ell
      (fun i j => ell i * (δj j • σ (w i0 j))) (fun j => ∑ i : I, ell i * (δj j • σ (w i0 j))) η
      hδj (fun _ => rfl) hδjIrr hell (fun _ _ => rfl) (fun _ => rfl) hη _ _ ν δ e rfl rfl hδ he
      hνiso hTS hdeg hνind
      (fun ξ hξ => ⟨(hSirr ξ hξ).1, (hSirr ξ hξ).2.1, (hSirr ξ hξ).2.2.2.2,
        (hSirr ξ hξ).2.2.2.1⟩)
      hrow hcolorth (fun j hj => ⟨(hdist j hj).1, (hdist j hj).2.2.1, (hdist j hj).2.2.2⟩)
      (fun j hj => (hdist j hj).2.1) i0' hi0' j₀ hj₀
  · intro Q G0 hG0 lam hlam iStar hiStar
    obtain ⟨χ, hχ⟩ := exists_ne_principalIrr hc.ne_bot_W₂ hc.isCyclic_W₂
    obtain ⟨j₀, hj₀⟩ := hβsurj (χ : ↥W₂ → ℂ) χ.2
    have hj₀ne : j₀ ≠ j0' := by
      intro h; apply hχ; apply Subtype.ext; rw [← hj₀, h, hβ0, coe_principalIrr]
    set j₁ := if e = 0 then j₀ else bar j₀ with hj₁
    have hj₁ne : j₁ ≠ j0' := by
      rw [hj₁]; split_ifs
      · exact hj₀ne
      · exact bar_ne hβinj hβ0 hbar hj₀ne
    have hkk : (if e = 0 then j₁ else bar j₁) = j₀ := by
      rw [hj₁]; split_ifs
      · rfl
      · exact bar_bar hβinj hbar j₀
    have hrow1 := hrow j₁ hj₁ne
    rw [hkk] at hrow1
    have hε : ((-1 : ℂ) ^ e * δ) = 1 ∨ ((-1 : ℂ) ^ e * δ) = -1 := by
      rcases he with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num
    exact CFSG.FeitThompson.Proofs.FCH_type_p_complementary_fitting_norm h₂ G hG M U W₁ W₂ hcfg u rfl
      I J inferInstance inferInstance i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0
      w hw σ ω hσ hω δj (fun j => δj j • σ (w i0 j)) ell
      (fun i j => ell i * (δj j • σ (w i0 j))) (fun j => ∑ i : I, ell i * (δj j • σ (w i0 j))) η
      hδj (fun _ => rfl) hδjIrr hell (fun _ _ => rfl) (fun _ => rfl) hη _ _ rfl rfl Q G0 hG0
      ν hνiso hTS hdeg hνind j₁ j₀ ((-1 : ℂ) ^ e * δ) hj₁ne hj₀ne hε (hdist j₀ hj₀ne).1
      (by rw [hrow1]) lam hlam iStar hiStar

theorem partnerDeficit_lt_of_real {p q u c v : ℕ} (hq : 2 ≤ q) (hp : 0 < p) (hu : 0 < u)
    (hc : 0 < c) (hv : v * (q - 1) = q ^ p - 1)
    (h : (((q : ℝ) ^ p * v - (v : ℝ) ^ 2 - ((q : ℝ) ^ p - 1)) / ((q : ℝ) ^ p * v * p))
      < ((q : ℝ) * u) ^ 2 / ((p : ℝ) ^ q * ((u : ℝ) * c) * q)) :
    partnerDeficit p q < ((q : ℚ) * (u : ℚ)) / ((p : ℚ) ^ q * (c : ℚ)) := by
  have hq1 : (1 : ℚ) < q := by exact_mod_cast hq
  have hvq : (v : ℚ) * ((q : ℚ) - 1) = (q : ℚ) ^ p - 1 := by
    have h1 : 1 ≤ q ^ p := Nat.one_le_pow _ _ (by omega)
    have := congrArg (fun n : ℕ => (n : ℚ)) hv
    push_cast [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub h1] at this
    exact this
  have hPI : partnerIndex p q = v := by
    rw [partnerIndex, div_eq_iff (by linarith), hvq]
  have hL : partnerDeficit p q = ((q : ℚ) ^ p * v - (v : ℚ) ^ 2 - ((q : ℚ) ^ p - 1)) /
      ((q : ℚ) ^ p * v * p) := by rw [partnerDeficit, hPI]
  have hR : ((q : ℝ) * u) ^ 2 / ((p : ℝ) ^ q * ((u : ℝ) * c) * q)
      = ((q : ℝ) * u) / ((p : ℝ) ^ q * c) := by
    have : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
    have : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  rw [hR] at h
  rw [hL, ← Rat.cast_lt (K := ℝ)]
  push_cast
  exact h

theorem ncard_sdiff_one_eq [Finite G] (X : Subgroup G) :
    ((((X : Set G) \ {1}).ncard : ℕ) : ℝ) = (Nat.card X : ℝ) - 1 := by
  have h : ((X : Set G)).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set G)).symm
  have hpos : 1 ≤ Nat.card X := Nat.card_pos
  rw [Set.ncard_sdiff_singleton_of_mem (SetLike.mem_coe.2 X.one_mem), h, Nat.cast_sub hpos,
    Nat.cast_one]

theorem averaging_lt {g s t iM iN hF kN K' v d f1 SF SN S0 n0 : ℝ} (hg : 0 < g) (hs : 0 < s)
    (ht : 0 < t) (hiM : iM * s = g) (hiN : iN * t = g)
    (hsum : 2 * g = f1 + iM * SF + iN * SN + S0)
    (hone : g = 1 + iM * (hF - 1) + iN * (kN - 1) + n0)
    (hSF : (s - d ^ 2) + (hF - 1) ≤ SF) (hSN : K' - v ^ 2 ≤ SN) (hS0 : n0 ≤ S0)
    (hf1 : 2 ≤ f1) : (K' - v ^ 2 - kN + 1) / t < d ^ 2 / s := by
  have hiM0 : 0 < iM := by
    by_contra h; push Not at h; nlinarith
  have hiN0 : 0 < iN := by
    by_contra h; push Not at h; nlinarith
  have h1 : iM * ((s - d ^ 2) + (hF - 1)) ≤ iM * SF := mul_le_mul_of_nonneg_left hSF hiM0.le
  have h2 : iN * (K' - v ^ 2) ≤ iN * SN := mul_le_mul_of_nonneg_left hSN hiN0.le
  have h3 : iN * (K' - v ^ 2 - kN + 1) < iM * d ^ 2 := by nlinarith
  rw [div_lt_div_iff₀ ht hs]
  have h4 : (iN * (K' - v ^ 2 - kN + 1)) * (s * t) < (iM * d ^ 2) * (s * t) :=
    mul_lt_mul_of_pos_right h3 (mul_pos hs ht)
  have h5 : g * ((K' - v ^ 2 - kN + 1) * s) < g * (d ^ 2 * t) := by
    calc g * ((K' - v ^ 2 - kN + 1) * s) = (iN * t) * ((K' - v ^ 2 - kN + 1) * s) := by
          rw [hiN]
      _ = (iN * (K' - v ^ 2 - kN + 1)) * (s * t) := by ring
      _ < (iM * d ^ 2) * (s * t) := h4
      _ = (iM * s) * (d ^ 2 * t) := by ring
      _ = g * (d ^ 2 * t) := by rw [hiM]
  exact lt_of_mul_lt_mul_left h5 hg.le

private theorem partnerDeficit_lt_aux
    (_h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (_h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₃ : CFSG.FeitThompson.Statements.FNI_type_p_prime_factors.{u})
    (_h₄ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (_h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (_h₆ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (_h₇ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    {G : Type u} [Group G] [Fintype G] (_hG : IsAmbient G) {M U W₁ W₂ : Subgroup G}
    (_hcfg : IsPConfigSetup G M U W₁ W₂) {p q u c : ℕ} (_hp : p = Nat.card ↥W₂)
    (_hq : q = Nat.card ↥W₁) (_hu : u = (cent U (Prep03.hallCoreIn M : Set G)).relIndex U)
    (_hc : c = Nat.card ↥(cent U (Prep03.hallCoreIn M : Set G)))
    (_hwit : ∃ ψ ∈ Irr ↥(fittingRaw ↥M), ψ 1 = 1 ∧
      indClassFun (fittingRaw ↥M) ψ ∈ Irr ↥M ∧
      ¬ ∀ x : ↥M, (x : G) ∈ Prep03.hallCoreIn M →
        indClassFun (fittingRaw ↥M) ψ x = indClassFun (fittingRaw ↥M) ψ 1) :
    partnerDeficit p q < ((q : ℚ) * (u : ℚ)) / ((p : ℚ) ^ q * (c : ℚ)) := by
  classical
  subst _hp _hq _hu _hc
  have hM := _hcfg.isCoatom
  have hcM := _hcfg.config
  have hG5 := isMinimalSimpleOdd_of_isAmbient _hG
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨_hG.odd_natCard, _hG.isSimpleGroup, _hG.not_isMulCommutative, _hG.forall_isSolvable⟩
  obtain ⟨hpp, hqp, -, -, -⟩ := primes_of_elementary_core_structure _h₂ _hG _hcfg rfl rfl
  obtain ⟨N, hN, hNM, V₀, hV₀N, hcN, -⟩ := exists_partner _h₃ _hG _hcfg
  have hcfgN : IsPConfigSetup G N V₀ W₂ W₁ := ⟨_hG, hN, hcN⟩
  have hwit' := (PairedFittingWitness.exists_fittingWitness_iff M).2 _hwit
  obtain ⟨-, -, -, hcardV, hcount, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FCH_paired_fitting_witness_excludes_partner _h₁ _h₂ _h₄ _h₅ _h₆ _h₇ G hG2
      M U W₁ W₂ hM hcM _ _ _ rfl rfl rfl _ _ _ rfl rfl rfl N V₀ hN hNM hV₀N hcN _ _ _ rfl rfl rfl
      _ rfl hwit'
  have hdisj := CFSG.FeitThompson.Proofs.FCH_paired_fitting_saturations_disjoint _h₂ G hG2 M U W₁ W₂
    hM hcM _ _ _ rfl rfl rfl _ _ _ rfl rfl rfl N V₀ hN hNM hV₀N hcN _ _ _ rfl rfl rfl _ rfl
  rw [satSet_eq_conjugatesOfSet, satSet_eq_conjugatesOfSet] at hdisj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcardHN, -, -, -, -, -, -, -, -, -, hTIN⟩ :=
    _h₂ G hG5 N V₀ W₂ W₁ hN hcN _ _ rfl rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTIM⟩ :=
    _h₂ G hG5 M U W₁ W₂ hM hcM _ _ rfl rfl
  obtain ⟨ξ, hξIrr, hξT⟩ := PairedFittingWitness.exists_mem_Irr_mem_detectInd_fittingIn hwit'
  obtain ⟨n₁, α, i0, barα, hα, hαinj, hαsurj, hα0, hbarα⟩ := exists_irrEnum ↥W₁
  obtain ⟨n₂, β, j0', barβ, hβ, hβinj, hβsurj, hβ0, hbarβ⟩ := exists_irrEnum ↥W₂
  obtain ⟨χ, hχ⟩ := exists_ne_principalIrr hcM.ne_bot_W₁ hcM.isCyclic_W₁
  obtain ⟨iStar, hiStar⟩ := hαsurj (χ : ↥W₁ → ℂ) χ.2
  have hiStar0 : iStar ≠ i0 := by
    intro h; apply hχ; apply Subtype.ext; rw [← hiStar, h, hα0, coe_principalIrr]
  have hW := hcM.isCyclicTIPair_sup_of_isAmbient _h₂ _hG hM
  obtain ⟨τ, hτ⟩ := hW.exists_isCyclicTIIsometry
  set ω₀ := PairedSupportingKernel.omegaUnbundled hW.isCyclic τ with hω₀
  have hωM : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω₀ f (x : G)) :=
    CFSG.FeitThompson.Proofs.isTIExtension_omega
      (PairedSupportingKernel.isOmegaMap_omegaUnbundled hW.isCyclic hτ)
  have hωN : IsTIExtension W₂ W₁ (⊤ : Subgroup G)
      (fun f x => CFSG.FeitThompson.Proofs.Recip.omegaR ω₀ f (x : G)) :=
    CFSG.FeitThompson.Proofs.isTIExtension_omega (CFSG.FeitThompson.Proofs.Recip.isOmegaMap_omegaR
      (PairedSupportingKernel.isOmegaMap_omegaUnbundled hW.isCyclic hτ))
  set w : Fin n₁ → Fin n₂ → ↥(W₁ ⊔ W₂) → ℂ := fun i j => hW.prodChar (α i) (β j) with hwdef
  have hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y := fun i j x y z hz => prodChar_apply_of_coe_eq hW _ _ x y z hz
  set wN : Fin n₂ → Fin n₁ → ↥(W₂ ⊔ W₁) → ℂ :=
    fun j i z => w i j (MulEquiv.subgroupCongr (sup_comm W₂ W₁) z) with hwNdef
  have hwN : ∀ j i, ∀ x : ↥W₂, ∀ y : ↥W₁, ∀ z : ↥(W₂ ⊔ W₁), (z : G) = (x : G) * (y : G) →
      wN j i z = β j x * α i y := by
    intro j i x y z hz
    rw [hwNdef]
    simp only
    rw [hw i j y x _ (by
      simp only [MulEquiv.subgroupCongr_apply]
      rw [hz]; exact ((hcM.commute_W₁_W₂ y.2 x.2).eq).symm)]
    ring
  set η : Fin n₁ → Fin n₂ → G → ℂ := fun i j => ω₀ (w i j) with hηdef
  obtain ⟨νM, hνMiso, hTSM, hbM, hcompl⟩ := exists_side_bounds _h₁ _h₂ _h₄ _h₅ _h₆ _h₇ _hG
    _hcfg i0 j0' α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0 barβ hbarβ w hw ω₀ hωM η
    (fun _ _ => rfl)
  obtain ⟨νN, -, -, hbN, -⟩ := exists_side_bounds _h₁ _h₂ _h₄ _h₅ _h₆ _h₇ _hG hcfgN
    j0' i0 β α hβ hα hβinj hαinj hβsurj hαsurj hβ0 hα0 barα hbarα wN hwN
    (CFSG.FeitThompson.Proofs.Recip.omegaR ω₀) hωN (fun j i => η i j) (fun _ _ => rfl)
  obtain ⟨χ₂, hχ₂⟩ := exists_ne_principalIrr hcM.ne_bot_W₂ hcM.isCyclic_W₂
  obtain ⟨jStar, hjStar⟩ := hβsurj (χ₂ : ↥W₂ → ℂ) χ₂.2
  have hjStar0 : jStar ≠ j0' := by
    intro h; apply hχ₂; apply Subtype.ext; rw [← hjStar, h, hβ0, coe_principalIrr]
  obtain ⟨hbM1, -, hbM3⟩ := hbM iStar hiStar0 jStar hjStar0
  obtain ⟨-, hbN2, -⟩ := hbN jStar hjStar0 iStar hiStar0
  have hρ3 := hbM3 ξ ⟨hξT, hξIrr⟩
  have hG0 := hcompl (Prep03.fittingIn N) _ rfl ξ hξT iStar hiStar0
  set ρ := νM ξ with hρdef
  set η' := η iStar j0' with hη'def
  have hξS := hTSM hξT
  have hρv : ρ ∈ virtualChars G := hνMiso.2.1 ξ hξS
  have hρ1 : cfInner ρ ρ = 1 := by
    rw [hνMiso.2.2 ξ hξS ξ hξS]; exact cfInner_self_of_mem_Irr hξIrr
  have hwIrr : w iStar j0' ∈ Irr ↥(W₁ ⊔ W₂) := hW.prodChar_mem_Irr (hα iStar) (hβ j0')
  have hη'v : η' ∈ virtualChars G :=
    mem_virtualChars_of_mem_virtualChars_top
      (hωM.maps_virtualChars _ (Irr_subset_virtualChars hwIrr))
  have hη'1 : cfInner η' η' = 1 := by
    have h := hωM.inner_eq (w iStar j0') (w iStar j0')
    rw [cfInner_top_eq] at h
    rw [hη'def, hηdef]; simp only; rw [h]; exact cfInner_self_of_mem_Irr hwIrr
  have hρs : ρ ∈ signedIrr G :=
    mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (mem_span_Irr_of_mem_virtualChars hρv)
      hρ1
  have hη's : η' ∈ signedIrr G :=
    mem_signedIrr_of_mem_span_Irr_of_cfInner_self_eq_one (mem_span_Irr_of_mem_virtualChars hη'v)
      hη'1
  have hρc : ρ ∈ classFun G := virtualChars_le_classFun hρv
  have hη'c : η' ∈ classFun G := virtualChars_le_classFun hη'v
  set f : G → ℝ := fun x => ‖ρ x‖ ^ 2 + ‖η' x‖ ^ 2 with hfdef
  have hfc : IsClassFun f := isClassFun_norm_sq_add hρc hη'c
  have hTIM' : IsTIWithNormalizer (((Prep03.fittingIn M : Subgroup G) : Set G) \ {1}) M := hTIM
  have hTIN' : IsTIWithNormalizer (((Prep03.fittingIn N : Subgroup G) : Set G) \ {1}) N := hTIN
  have hdisj' : (Group.conjugatesOfSet ((Prep03.fittingIn M : Subgroup G) : Set G) \ {1}) ∩
      (Group.conjugatesOfSet ((Prep03.fittingIn N : Subgroup G) : Set G) \ {1}) = ∅ := hdisj
  have hsum := sum_eq_of_isTIWithNormalizer hTIM' hTIN' hdisj' hfc
  have hone := sum_eq_of_isTIWithNormalizer hTIM' hTIN' hdisj' (f := fun _ => (1 : ℝ))
    (isClassFun_const 1)
  simp only [sum_indicator_one, ncard_sdiff_one_eq] at hone
  have hconst : ∑ _x : G, (1 : ℝ) = (Nat.card G : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]
  rw [hconst] at hone
  have htot : ∑ x, f x = 2 * (Nat.card G : ℝ) := by
    rw [hfdef]; simp only
    rw [Finset.sum_add_distrib, sum_norm_sq_eq_of_cfInner_self_eq_one hρ1,
      sum_norm_sq_eq_of_cfInner_self_eq_one hη'1]; ring
  rw [htot] at hsum
  have hsplit : ∀ X : Subgroup G, ∑ x, ((X : Set G) \ {1}).indicator f x
      = sumSqOn (Prep03.sharp X) ρ + sumSqOn (Prep03.sharp X) η' := by
    intro X
    rw [hfdef, Set.indicator_add]
    exact Finset.sum_add_distrib
  have hnonneg : ∀ (A : Set G) (h : G → ℂ), 0 ≤ sumSqOn A h := fun A h =>
    Finset.sum_nonneg fun x _ => Set.indicator_nonneg (fun y _ => by positivity) x
  rw [hsplit, hsplit] at hsum
  have hGset : Set.univ \ (Prep03.sat ((Prep03.fittingIn M : Subgroup G) : Set G) ∪
      Prep03.sat ((Prep03.fittingIn N : Subgroup G) : Set G)) = (Group.conjugatesOfSet
        ((Prep03.fittingIn M : Subgroup G) : Set G) ∪
      Group.conjugatesOfSet ((Prep03.fittingIn N : Subgroup G) : Set G))ᶜ := by
    rw [sat_eq_conjugatesOfSet, sat_eq_conjugatesOfSet, Set.compl_eq_univ_sdiff]
  rw [hGset] at hG0
  have hf1 : 2 ≤ f 1 := by
    have h1 := one_le_norm_apply_one_of_mem_signedIrr hρs
    have h2 := one_le_norm_apply_one_of_mem_signedIrr hη's
    rw [hfdef]; simp only; nlinarith
  have hcardM := natCard_M_eq _h₂ _hG _hcfg rfl rfl
  have hcardN := natCard_M_eq _h₂ _hG hcfgN rfl rfl
  have hcommN := natCard_W₁_mul_natCard_commutator hcN
  have hUc := relIndex_mul_card_of_le (inf_le_left : cent U (Prep03.hallCoreIn M : Set G) ≤ U)
  have hvv : (cent V₀ (Prep03.hallCoreIn N : Set G)).relIndex V₀ = Nat.card V₀ := hcardV.symm
  have hFN' : Nat.card ↥(Prep03.fittingIn N) = Nat.card W₁ ^ Nat.card W₂ := by
    have hFH : Prep03.fittingIn N = CFSG.FeitThompson.Prep05.hallCoreOf N := by
      obtain ⟨-, -, hFN, -⟩ := CFSG.FeitThompson.Proofs.FCH_paired_fitting_witness_excludes_partner
        _h₁ _h₂ _h₄ _h₅ _h₆ _h₇ G hG2 M U W₁ W₂ hM hcM _ _ _ rfl rfl rfl _ _ _ rfl rfl rfl N V₀
        hN hNM hV₀N hcN _ _ _ rfl rfl rfl _ rfl hwit'
      exact hFN
    rw [hFH, hcardHN]
  have hGpos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  have hMpos : (0 : ℝ) < Nat.card M := by exact_mod_cast Nat.card_pos
  have hNpos : (0 : ℝ) < Nat.card N := by exact_mod_cast Nat.card_pos
  have hiM : (M.index : ℝ) * Nat.card M = Nat.card G := by exact_mod_cast M.index_mul_card
  have hiN : (N.index : ℝ) * Nat.card N = Nat.card G := by exact_mod_cast N.index_mul_card
  simp only [nsmul_eq_mul] at hsum hone
  have hSF : ((Nat.card M : ℝ) - ((Nat.card ↥W₁ : ℝ) *
      ((cent U (Prep03.hallCoreIn M : Set G)).relIndex U : ℝ)) ^ 2) +
      ((Nat.card ↥(Prep03.fittingIn M) : ℝ) - 1) ≤
      sumSqOn (Prep03.sharp (Prep03.fittingIn M)) ρ + sumSqOn (Prep03.sharp (Prep03.fittingIn M)) η' := by
    linarith [hρ3, hbM1]
  have hSN : (Nat.card ↥(⁅N, N⁆ : Subgroup G) : ℝ) -
      ((cent V₀ (Prep03.hallCoreIn N : Set G)).relIndex V₀ : ℝ) ^ 2 ≤
      sumSqOn (Prep03.sharp (Prep03.fittingIn N)) ρ + sumSqOn (Prep03.sharp (Prep03.fittingIn N)) η' :=
    le_trans hbN2 (le_add_of_nonneg_left (hnonneg _ _))
  have key := averaging_lt hGpos hMpos hNpos hiM hiN hsum hone hSF hSN hG0 hf1
  have hu0 : 0 < (cent U (Prep03.hallCoreIn M : Set G)).relIndex U := by
    rw [Subgroup.relIndex]; exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine partnerDeficit_lt_of_real (v := Nat.card V₀) hqp.two_le hpp.pos hu0 Nat.card_pos
    (by rw [hcardV]; exact hcount) ?_
  have hK' : (Nat.card ↥(⁅N, N⁆ : Subgroup G) : ℝ)
      = (Nat.card W₁ : ℝ) ^ Nat.card W₂ * Nat.card V₀ := by
    have h : (Nat.card W₂ : ℝ) * Nat.card ↥(⁅N, N⁆ : Subgroup G)
        = (Nat.card W₁ : ℝ) ^ Nat.card W₂ * Nat.card V₀ * Nat.card W₂ := by
      exact_mod_cast hcommN.trans hcardN
    have hp0 : (Nat.card W₂ : ℝ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
    apply mul_left_cancel₀ hp0
    rw [h]; ring
  rw [hK', hFN', hvv] at key
  have hN' : (Nat.card N : ℝ) = (Nat.card W₁ : ℝ) ^ Nat.card W₂ * Nat.card V₀ * Nat.card W₂ := by
    exact_mod_cast hcardN
  have hM' : (Nat.card M : ℝ) = (Nat.card W₂ : ℝ) ^ Nat.card W₁ *
      (((cent U (Prep03.hallCoreIn M : Set G)).relIndex U : ℝ) *
        Nat.card ↥(cent U (Prep03.hallCoreIn M : Set G))) * Nat.card W₁ := by
    have h : Nat.card M = Nat.card W₂ ^ Nat.card W₁ *
        ((cent U (Prep03.hallCoreIn M : Set G)).relIndex U * Nat.card ↥(cent U (Prep03.hallCoreIn M : Set G)))
        * Nat.card W₁ := by
      rw [hcardM, ← hUc]
      rfl
    exact_mod_cast h
  rw [hN', hM'] at key
  push_cast at key ⊢
  convert key using 2
  ring

theorem actionKernelRatio_aux
    (h₁ : CFSG.FeitThompson.Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FNI_type_p_prime_factors.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₆ : CFSG.FeitThompson.Statements.FTS_canonical_signalizer_structure.{u})
    (h₇ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u}) :
    CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u} := by
  intro G _ _ hG M U W₁ W₂ hcfg p q u c hp hq hu hc m hm hwit
  obtain ⟨hpp, hqp, -, -, -⟩ := primes_of_elementary_core_structure h₂ hG hcfg hp hq
  have hpne : p ≠ 0 := hpp.pos.ne'
  have hcpos : 0 < c := by rw [hc]; exact Nat.card_pos
  have hkey := partnerDeficit_lt_aux h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hcfg hp hq hu hc hwit
  have hmL : m = (p : ℚ) * partnerDeficit p q := by
    rw [hm, mul_partnerDeficit hpne hqp.two_le]
  have hdiv : m / (p : ℚ) = partnerDeficit p q := by
    rw [hmL, mul_comm, mul_div_assoc, div_self (Nat.cast_ne_zero.2 hpne), mul_one]
  refine lt_div_of_div_lt hpp.pos hqp.pos hcpos ?_
  rw [hdiv]
  exact hkey

end ActionKernelRatio

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson

universe u

theorem FCH_type_p_action_kernel_ratio
    (h₁ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FNI_type_p_prime_factors.{u})
    (h₄ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₆ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₇ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FCH_type_p_action_kernel_ratio.{u} :=
  ActionKernelRatio.actionKernelRatio_aux h₁ h₂ h₃ h₄ h₅ h₆ h₇

end CFSG.FeitThompson.Proofs

end
