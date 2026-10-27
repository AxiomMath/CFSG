module

public import CFSG.FeitThompson.Representations.QuotientLayerDegreeSquareSum
public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
public import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
public import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open NormalInduction (conjClassFun conjClassFun_apply)
open scoped ComplexOrder

theorem cfInner_comp_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f h : B → ℂ) :
    cfInner (f ∘ e) (h ∘ e) = cfInner f h := by
  rw [cfInner_def, cfInner_def, Nat.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

variable {L : Type*} [Group L]

theorem isMulCommutative_subgroup_of_le {A B : Subgroup L} [IsMulCommutative ↥B] (hAB : A ≤ B) :
    IsMulCommutative ↥A :=
  IsMulCommutative.of_setLike_mul_comm fun a ha b hb => setLike_mul_comm (hAB ha) (hAB hb)

theorem mem_Irr_comp_inclusion_of_isMulCommutative {B : Subgroup L} [IsMulCommutative ↥B]
    {A : Subgroup L} (hAB : A ≤ B) {ψ : ↥B → ℂ} (hψ : ψ ∈ Irr ↥B) :
    ψ ∘ Subgroup.inclusion hAB ∈ Irr ↥A := by
  obtain ⟨h, rfl⟩ := exists_monoidHom_coe_eq_of_mem_Irr hψ
  have : IsMulCommutative ↥A := isMulCommutative_subgroup_of_le hAB
  exact mem_Irr_of_monoidHom (h.comp (Subgroup.inclusion hAB))

theorem resClassFun_comp_inclusion {A B : Subgroup L} (hAB : A ≤ B) (χ : L → ℂ) :
    resClassFun B χ ∘ Subgroup.inclusion hAB = resClassFun A χ := by
  funext x
  rw [Function.comp_apply, resClassFun_apply, resClassFun_apply, Subgroup.coe_inclusion]

theorem mem_normalizer_sup' {A B : Subgroup L} {g : L} (hA : g ∈ normalizer (A : Set L))
    (hB : g ∈ normalizer (B : Set L)) : g ∈ normalizer ((A ⊔ B : Subgroup L) : Set L) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_coe_of_normal (N : Subgroup L) [N.Normal] (g : L) :
    g ∈ normalizer (N : Set L) :=
  Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top g)

def conjAutSubgroupOf {A B : Subgroup L} {t : L} (hA : t ∈ normalizer (A : Set L))
    (hB : t ∈ normalizer (B : Set L)) : MulAut ↥(A.subgroupOf B) where
  toFun x := ⟨⟨t * ((x : ↥B) : L) * t⁻¹, (mem_normalizer_iff.mp hB _).mp (x : ↥B).2⟩,
    mem_subgroupOf.2 ((mem_normalizer_iff.mp hA _).mp (mem_subgroupOf.1 x.2))⟩
  invFun x := ⟨⟨t⁻¹ * ((x : ↥B) : L) * t, (mem_normalizer_iff''.mp hB _).mp (x : ↥B).2⟩,
    mem_subgroupOf.2 ((mem_normalizer_iff''.mp hA _).mp (mem_subgroupOf.1 x.2))⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
  right_inv x := by apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
  map_mul' x y := by apply Subtype.ext; apply Subtype.ext; push_cast; group

@[simp] theorem coe_conjAutSubgroupOf_apply {A B : Subgroup L} {t : L}
    (hA : t ∈ normalizer (A : Set L)) (hB : t ∈ normalizer (B : Set L))
    (x : ↥(A.subgroupOf B)) :
    (((conjAutSubgroupOf hA hB x : ↥(A.subgroupOf B)) : ↥B) : L) = t * ((x : ↥B) : L) * t⁻¹ :=
  (rfl)

def conjAutSubgroupOfHom (A B : Subgroup L) :
    ↥(normalizer (A : Set L) ⊓ normalizer (B : Set L)) →* MulAut ↥(A.subgroupOf B) where
  toFun t := conjAutSubgroupOf (mem_inf.mp t.2).1 (mem_inf.mp t.2).2
  map_one' := by
    ext x
    rw [coe_conjAutSubgroupOf_apply, MulAut.one_apply, Subgroup.coe_one, one_mul, inv_one, mul_one]
  map_mul' s t := by
    ext x
    rw [coe_conjAutSubgroupOf_apply, MulAut.mul_apply, coe_conjAutSubgroupOf_apply,
      coe_conjAutSubgroupOf_apply, Subgroup.coe_mul]
    group

@[simp] theorem coe_conjAutSubgroupOfHom_apply_apply (A B : Subgroup L)
    (t : ↥(normalizer (A : Set L) ⊓ normalizer (B : Set L))) (x : ↥(A.subgroupOf B)) :
    (((conjAutSubgroupOfHom A B t x : ↥(A.subgroupOf B)) : ↥B) : L)
      = (t : L) * ((x : ↥B) : L) * (t : L)⁻¹ :=
  coe_conjAutSubgroupOf_apply (mem_inf.mp t.2).1 (mem_inf.mp t.2).2 x

theorem resClassFun_comp_conjAutSubgroupOfHom {A B : Subgroup L} {χ : ↥B → ℂ}
    (hχ : ∀ t : L, ∀ x y : ↥B, (y : L) = t⁻¹ * (x : L) * t → χ y = χ x)
    (t : ↥(normalizer (A : Set L) ⊓ normalizer (B : Set L))) :
    resClassFun (A.subgroupOf B) χ ∘ conjAutSubgroupOfHom A B t
      = resClassFun (A.subgroupOf B) χ := by
  funext x
  rw [Function.comp_apply, resClassFun_apply, resClassFun_apply]
  refine hχ (t : L)⁻¹ _ _ ?_
  rw [coe_conjAutSubgroupOfHom_apply_apply, inv_inv]

theorem index_subgroupOf_sup_eq_card {A B : Subgroup L} [A.Normal] (hAB : A ⊓ B = ⊥) :
    (A.subgroupOf (A ⊔ B)).index = Nat.card B := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hB : B ≤ A ⊔ B := le_sup_right
  have : (A.subgroupOf (A ⊔ B)).Normal := ‹A.Normal›.subgroupOf _
  have hsup : A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA hB, Subgroup.subgroupOf_self]
  have hinf : A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B) = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hAB]
    simp
  rw [(isComplement'_of_sup_eq_top_of_inf_eq_bot hsup hinf).index_eq_card]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv

theorem conjClassFun_comp_inclusion {A B : Subgroup L} [A.Normal] [B.Normal] (hAB : A ≤ B)
    (t : L) (f : ↥B → ℂ) :
    conjClassFun B t f ∘ Subgroup.inclusion hAB
      = conjClassFun A t (f ∘ Subgroup.inclusion hAB) := by
  funext y
  rw [Function.comp_apply, conjClassFun_apply, conjClassFun_apply, Function.comp_apply]
  congr 1

theorem inertiaGroup_le_inertiaGroup_comp_inclusion {A B : Subgroup L} [A.Normal] [B.Normal]
    (hAB : A ≤ B) (ψ : ↥B → ℂ) :
    inertiaGroup B ψ ≤ inertiaGroup A (ψ ∘ Subgroup.inclusion hAB) := by
  intro t ht
  rw [mem_inertiaGroup] at ht ⊢
  rw [← conjClassFun_comp_inclusion hAB, ht]

theorem exists_forall_smul_eq_of_not_dvd_natCard {X : Type*} {P : Type*} [Group P] {q a : ℕ}
    (hq : q.Prime) (hP : Nat.card P = q ^ a) (smul : P → X → X)
    (hone : ∀ x, smul 1 x = x) (hmul : ∀ p p' x, smul (p * p') x = smul p (smul p' x))
    {S : Set X} (hstable : ∀ p : P, ∀ x ∈ S, smul p x ∈ S)
    (hcard : ¬ q ∣ Nat.card S) : ∃ x ∈ S, ∀ p : P, smul p x = x := by
  have : Fact q.Prime := ⟨hq⟩
  let _ : MulAction P ↥S :=
    { smul := fun p x => ⟨smul p (x : X), hstable p (x : X) x.2⟩
      one_smul := fun x => Subtype.ext (hone (x : X))
      mul_smul := fun p p' x => Subtype.ext (hmul p p' (x : X)) }
  obtain ⟨x, hx⟩ := nonempty_fixedPoints_of_not_dvd_natCard (P := P) (X := ↥S) hP hcard
  exact ⟨(x : X), x.2, fun p => congrArg Subtype.val (hx p)⟩

theorem exists_mem_resConstituents_comp_eq {K : Type*} [Group K] {M : Subgroup K}
    [Fintype ↥M] {χ : K → ℂ} {P : Type*} [Group P] {q a : ℕ} (hq : q.Prime)
    (hP : Nat.card P = q ^ a) (γ : P →* MulAut ↥M)
    (hinv : ∀ t : P, resClassFun M χ ∘ γ t = resClassFun M χ)
    (hcard : ¬ q ∣ (resConstituents M χ).card) :
    ∃ lam ∈ resConstituents M χ, ∀ t : P, lam ∘ γ t = lam := by
  classical
  have hstable : ∀ t : P, ∀ lam ∈ (resConstituents M χ : Set (↥M → ℂ)),
      lam ∘ ⇑(γ t⁻¹) ∈ (resConstituents M χ : Set (↥M → ℂ)) := by
    intro t lam hlam
    simp only [Finset.mem_coe] at hlam ⊢
    obtain ⟨hIrr, hpos⟩ := mem_resConstituents.1 hlam
    refine mem_resConstituents.2 ⟨mem_Irr_comp_mulAut hIrr (γ t⁻¹), ?_⟩
    have h1 : cfInner (resClassFun M χ ∘ ⇑(γ t⁻¹)) (lam ∘ ⇑(γ t⁻¹))
        = cfInner (resClassFun M χ) lam := cfInner_comp_equiv (γ t⁻¹).toEquiv _ _
    rw [hinv t⁻¹] at h1
    rw [h1]
    exact hpos
  obtain ⟨lam, hlamS, hlamfix⟩ :=
    exists_forall_smul_eq_of_not_dvd_natCard (X := ↥M → ℂ) hq hP
      (fun t lam => lam ∘ ⇑(γ t⁻¹)) (fun lam => by simp)
      (fun t t' lam => by funext x; simp [mul_inv_rev, map_mul]) hstable (by simpa using hcard)
  refine ⟨lam, by simpa using hlamS, fun t => ?_⟩
  have h4 := hlamfix t⁻¹
  rwa [inv_inv] at h4

theorem card_resConstituents_dvd_index {K : Type*} [Group K] (M : Subgroup K)
    [M.Normal] [Fintype ↥M] [Fintype K] {χ : K → ℂ} (hχ : χ ∈ Irr K) :
    (resConstituents M χ).card ∣ M.index := by
  classical
  obtain ⟨lam₀, hlam₀⟩ := resConstituents_nonempty (N := M) hχ
  have hSorb : resConstituents M χ = NormalInduction.conjOrbit M lam₀ := by
    ext mu
    rw [NormalInduction.mem_conjOrbit,
      mem_resConstituents_iff_exists_conjClassFun (N := M) hχ hlam₀]
  rw [hSorb, card_conjOrbit]
  exact Subgroup.index_dvd_of_le
    (le_inertiaGroup M (Irr_subset_classFun (mem_resConstituents.1 hlam₀).1))

theorem exists_mem_Irr_comp_inclusion_eq {G : Type*} [Group G] [Finite G] {A T : Subgroup G}
    (hAT : A ≤ T) [Fintype ↥T] [Fintype ↥A] [IsMulCommutative ↥T] {χ : G → ℂ} (hχ : χ ∈ Irr G)
    {lam : ↥A → ℂ} (hlam : lam ∈ Irr ↥A) (hpos : 0 < cfInner (resClassFun A χ) lam) :
    ∃ ψ, ψ ∈ Irr ↥T ∧ 0 < cfInner (resClassFun T χ) ψ ∧
      ψ ∘ Subgroup.inclusion hAT = lam := by
  classical
  obtain ⟨m, hm⟩ := exists_multiplicities_resClassFun (N := T) hχ
  have hA : resClassFun A χ
      = ∑ φ : irrFinset ↥T, (m φ : ℂ) • ((φ : ↥T → ℂ) ∘ Subgroup.inclusion hAT) := by
    rw [← resClassFun_comp_inclusion hAT χ, hm]
    funext x
    simp [Finset.sum_apply]
  have hsum : cfInner (resClassFun A χ) lam
      = ∑ φ : irrFinset ↥T, (m φ : ℂ) *
        cfInner ((φ : ↥T → ℂ) ∘ Subgroup.inclusion hAT) lam := by
    rw [hA, cfInner_sum_left]
    exact Finset.sum_congr rfl fun φ _ => cfInner_smul_left _ _ _
  rw [hsum] at hpos
  obtain ⟨φ, -, hφ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
  have hφI : (φ : ↥T → ℂ) ∈ Irr ↥T := mem_irrFinset.1 φ.2
  have hres : (φ : ↥T → ℂ) ∘ Subgroup.inclusion hAT = lam := by
    by_contra hne
    rw [cfInner_eq_zero_of_mem_Irr
      (mem_Irr_comp_inclusion_of_isMulCommutative hAT hφI) hlam hne, mul_zero] at hφ
    exact hφ rfl
  refine ⟨(φ : ↥T → ℂ), hφI, ?_, hres⟩
  have hmult : cfInner (resClassFun T χ) (φ : ↥T → ℂ) = (m φ : ℂ) := cfInner_eq_multiplicity hm φ
  have hm0 : m φ ≠ 0 := by
    intro h
    rw [h] at hφ
    simp at hφ
  rw [hmult]
  exact_mod_cast Nat.pos_of_ne_zero hm0

@[simp] theorem conjClassFun_one_fun {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (t : G) :
    conjClassFun N t (1 : ↥N → ℂ) = 1 := by
  funext n
  rw [conjClassFun_apply, Pi.one_apply, Pi.one_apply]

theorem resClassFun_eq_const_of_one_mem_resConstituents {K : Type*} [Group K] [Finite K]
    {M : Subgroup K} [M.Normal] [Fintype ↥M] {χ : K → ℂ} (hχ : χ ∈ Irr K)
    (h1 : (1 : ↥M → ℂ) ∈ resConstituents M χ) (x : ↥M) :
    resClassFun M χ x = resClassFun M χ 1 := by
  classical
  obtain ⟨e, -, -, hres⟩ := exists_pos_resClassFun_eq_nsmul_sum (N := M) hχ
  have hall : ∀ mu ∈ resConstituents M χ, mu = (1 : ↥M → ℂ) := by
    intro mu hmu
    obtain ⟨g, hg⟩ := (mem_resConstituents_iff_exists_conjClassFun hχ h1).1 hmu
    rw [← hg, conjClassFun_one_fun]
  have hval : ∀ y : ↥M, (∑ mu ∈ resConstituents M χ, mu) y
      = ((resConstituents M χ).card : ℂ) := by
    intro y
    rw [Finset.sum_apply,
      Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun mu hmu => by rw [hall mu hmu, Pi.one_apply]]
    simp
  have hx := congrFun hres x
  have h11 := congrFun hres 1
  rw [Pi.smul_apply, hval x] at hx
  rw [Pi.smul_apply, hval 1] at h11
  rw [hx, h11]

end CFSG.FeitThompson
