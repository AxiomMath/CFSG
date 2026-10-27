module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma35

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma39

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem solvAbSylow_quotient {B X : Subgroup G} {t : G} (htB : t ∈ centralizer (B : Set G))
    (hXN : X ≤ normalizer (B : Set G)) (hXt : X ≤ centralizer ({t} : Set G))
    (hS : Group.IsSolvable ↥(centralizer (B : Set G) ⊓ centralizer ({t} : Set G)))
    (hK : ∀ P : Sylow 2 ↥(centralizer (B : Set G)),
      IsMulCommutative (P : Subgroup ↥(centralizer (B : Set G))))
    {Q' : Type} [Group Q'] [Finite Q'] (φ : ↥(normalizer (B : Set G)) →* Q')
    (hφB : ∀ x : ↥(normalizer (B : Set G)), (x : G) ∈ B → φ x = 1)
    (hφker : ∀ x : ↥(normalizer (B : Set G)), φ x = 1 → (x : G) ∈ B ⊔ centralizer (B : Set G))
    {H : Subgroup Q'} (hH : Odd (Nat.card H)) (hXH : ∀ x (hx : x ∈ X), φ ⟨x, hXN hx⟩ ∈ H)
    [((X ⊓ B).subgroupOf X).Normal] : SolvAbSylow (X ⧸ (X ⊓ B).subgroupOf X) := by
  have hBP : B ≤ normalizer (B : Set G) := le_normalizer
  have hBn : (B.subgroupOf (normalizer (B : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBP).mpr le_rfl
  let π := QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G)))
  have hπ : ∀ p, π p = QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G))) p := fun _ => rfl
  let f : ↥X →* ↥(normalizer (B : Set G)) ⧸ B.subgroupOf (normalizer (B : Set G)) :=
    π.comp (Subgroup.inclusion hXN)
  have hf : ∀ x : ↥X, f x = π (Subgroup.inclusion hXN x) := fun _ => rfl
  have hfker : f.ker = (X ⊓ B).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, hf, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf, mem_subgroupOf, coe_inclusion, mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  refine SolvAbSylow.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
    (QuotientGroup.quotientKerEquivRange f)) ?_
  have hBφ : B.subgroupOf (normalizer (B : Set G)) ≤ φ.ker := fun x hx => hφB x hx
  let φb : ↥(normalizer (B : Set G)) ⧸ B.subgroupOf (normalizer (B : Set G)) →* Q' :=
    QuotientGroup.lift (B.subgroupOf (normalizer (B : Set G))) φ hBφ
  have hφb : ∀ p, φb (π p) = φ p := fun _ => rfl
  let ψ : ↥f.range →* Q' := φb.comp f.range.subtype
  have hψ : ∀ x : ↥X, ∀ w : ↥f.range, (w : _) = f x → ψ w = φ (Subgroup.inclusion hXN x) := by
    intro x w hw
    change φb (w : _) = _
    rw [hw, hf, hφb]
  have hincl : ∀ x : ↥X, ((Subgroup.inclusion hXN x : ↥(normalizer (B : Set G))) : G) = x :=
    fun _ => rfl
  refine SolvAbSylow.of_ker ψ ?_ ?_
  ·
    have hKP : centralizer (B : Set G) ≤ normalizer (B : Set G) := centralizer_le_normalizer _
    have hSP : centralizer (B : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (B : Set G) :=
      inf_le_left.trans hKP
    have hBt : B ≤ centralizer ({t} : Set G) := by
      intro b hb
      rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp htB b hb
    have hZ : ψ.ker.map f.range.subtype ≤
        ((centralizer (B : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
          (normalizer (B : Set G))).map π ⊓
        ((centralizer (B : Set G)).subgroupOf (normalizer (B : Set G))).map π := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx⟩ := w.2
      have hφx : φ (Subgroup.inclusion hXN x) = 1 := by
        rw [← hψ x w hx.symm]
        exact hw
      obtain ⟨b, hb, k, hk, hbk⟩ :=
        exists_mul_of_mem_sup_of_le_normalizer (centralizer_le_normalizer _) (hφker _ hφx)
      rw [hincl] at hbk
      have hkP : k ∈ normalizer (B : Set G) := hKP hk
      have hkt : k ∈ centralizer ({t} : Set G) := by
        have h1 : k = b⁻¹ * (x : G) := by
          rw [hbk]
          group
        rw [h1]
        exact mul_mem (inv_mem (hBt hb)) (hXt x.2)
      have hwk : (w : ↥(normalizer (B : Set G)) ⧸ B.subgroupOf (normalizer (B : Set G))) =
          π ⟨k, hkP⟩ := by
        rw [← hx, hf, hπ, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          mem_subgroupOf]
        have h2 : (((Subgroup.inclusion hXN x)⁻¹ * ⟨k, hkP⟩ : ↥(normalizer (B : Set G))) : G) =
            (x : G)⁻¹ * k := rfl
        have hkb : b⁻¹ * k = k * b⁻¹ := mem_centralizer_iff.mp hk b⁻¹ (inv_mem hb)
        have h3 : (b * k)⁻¹ * k = b⁻¹ := by
          calc (b * k)⁻¹ * k = k⁻¹ * (b⁻¹ * k) := by group
            _ = k⁻¹ * (k * b⁻¹) := by rw [hkb]
            _ = b⁻¹ := by group
        rw [h2, hbk, h3]
        exact inv_mem hb
      change (w : ↥(normalizer (B : Set G)) ⧸ B.subgroupOf (normalizer (B : Set G))) ∈ _
      rw [hwk]
      exact mem_inf.mpr ⟨⟨⟨k, hkP⟩, mem_inf.mpr ⟨hk, hkt⟩, rfl⟩, ⟨⟨k, hkP⟩, hk, rfl⟩⟩
    have hSs : Group.IsSolvable ↥(((centralizer (B : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (normalizer (B : Set G))).map π) := by
      have : Group.IsSolvable ↥((centralizer (B : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
          (normalizer (B : Set G))) :=
        Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hSP).toMonoidHom)
          (subgroupOfEquivOfLe hSP).injective
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    have hKs : ∀ Q : Sylow 2 ↥(((centralizer (B : Set G)).subgroupOf (normalizer (B : Set G))).map π),
        IsMulCommutative (Q : Subgroup ↥(((centralizer (B : Set G)).subgroupOf
          (normalizer (B : Set G))).map π)) := by
      refine absSylow_of_surjective ((π.subgroupMap _).comp
        (subgroupOfEquivOfLe hKP).symm.toMonoidHom) ?_ hK
      exact (π.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hKP).symm.surjective
    exact SolvAbSylow.of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ f.range.subtype_injective)
      (SolvAbSylow.of_le (hZ.trans inf_le_left) hSs (hZ.trans inf_le_right) hKs)
  ·
    have hle : ψ.range ≤ H := by
      rintro _ ⟨w, rfl⟩
      obtain ⟨x, hx⟩ := w.2
      rw [hψ x w hx.symm]
      exact hXH x x.2
    exact Odd.of_dvd_nat hH (card_dvd_of_le hle)

@[expose] noncomputable def normConj (A : Subgroup G) : ↥(normalizer (A : Set G)) →* MulAut ↥A where
  toFun n :=
    { toFun := fun a => ⟨(n : G) * a * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 a).mp a.2⟩
      invFun := fun a => ⟨(n : G)⁻¹ * a * n, by
        have := (mem_normalizer_iff.mp (inv_mem n.2) a).mp a.2
        simpa using this⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext a
    simp
  map_mul' := fun m n => by
    ext a
    simp [mul_assoc]

omit [Finite G] in
theorem normConj_apply (A : Subgroup G) (n : ↥(normalizer (A : Set G))) (a : ↥A) :
    ((normConj A n a : ↥A) : G) = (n : G) * a * (n : G)⁻¹ :=
  rfl

@[expose] def conjNormalizer (A : Subgroup G) (g : G) :
    ↥(normalizer (rightConjugate A g : Set G)) →* ↥(normalizer (A : Set G)) where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_rightConjugate_iff A g x).mp x.2⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [coe_mul]
    group

@[expose] noncomputable def outerMap (A : Subgroup G) (g : G) :
    ↥(normalizer (rightConjugate A g : Set G)) →* outerAutomorphismGroup ↥A :=
  (outerAutomorphismMap ↥A).comp ((normConj A).comp (conjNormalizer A g))

omit [Finite G] in
theorem outerMap_eq_one (A : Subgroup G) (g : G) (x : ↥(normalizer (rightConjugate A g : Set G)))
    (hx : (x : G) ∈ rightConjugate A g) : outerMap A g x = 1 := by
  rw [mem_rightConjugate_iff] at hx
  change outerAutomorphismMap ↥A (normConj A (conjNormalizer A g x)) = 1
  rw [← MonoidHom.mem_ker, outerAutomorphismMap_ker]
  refine ⟨⟨g * x * g⁻¹, hx⟩, ?_⟩
  ext a
  rfl

omit [Finite G] in
theorem mem_sup_of_outerMap_eq_one (A : Subgroup G) (g : G)
    (x : ↥(normalizer (rightConjugate A g : Set G))) (hx : outerMap A g x = 1) :
    (x : G) ∈ rightConjugate A g ⊔ centralizer (rightConjugate A g : Set G) := by
  change outerAutomorphismMap ↥A (normConj A (conjNormalizer A g x)) = 1 at hx
  rw [← MonoidHom.mem_ker, outerAutomorphismMap_ker] at hx
  obtain ⟨a, ha⟩ := hx
  have hk : (a : G)⁻¹ * (g * x * g⁻¹) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro b hb
    have h1 := congrArg (fun e : MulAut ↥A => ((e ⟨b, hb⟩ : ↥A) : G)) ha
    simp only [MulAut.conj_apply] at h1
    change (a : G) * b * (a : G)⁻¹ = g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹ at h1
    calc b * ((a : G)⁻¹ * (g * x * g⁻¹))
        = (a : G)⁻¹ * ((a : G) * b * (a : G)⁻¹) * (g * x * g⁻¹) := by group
      _ = (a : G)⁻¹ * (g * x * g⁻¹ * b * (g * x * g⁻¹)⁻¹) * (g * x * g⁻¹) := by rw [h1]
      _ = (a : G)⁻¹ * (g * x * g⁻¹) * b := by group
  have h1 : (g⁻¹ * a * g : G) ∈ rightConjugate A g := by
    rw [mem_rightConjugate_iff]
    simp [mul_assoc]
  have h2 : (g⁻¹ * ((a : G)⁻¹ * (g * x * g⁻¹)) * g : G) ∈
      centralizer (rightConjugate A g : Set G) := by
    rw [centralizer_rightConjugate, mem_rightConjugate_iff]
    simpa [mul_assoc] using hk
  have h3 : (x : G) = (g⁻¹ * a * g) * (g⁻¹ * ((a : G)⁻¹ * (g * x * g⁻¹)) * g) := by group
  rw [h3]
  exact mul_mem (mem_sup_left h1) (mem_sup_right h2)

end Lemma39

end CFSG.ComponentClassification.AS76b
