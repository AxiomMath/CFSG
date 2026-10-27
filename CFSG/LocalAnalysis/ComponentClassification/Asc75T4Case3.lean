module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Local
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

theorem oUpperTwoPrime_map {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    (oUpperTwoPrime X).map f = oUpperTwoPrime (X.map f) := by
  rw [oUpperTwoPrime, oUpperTwoPrime, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    exact ⟨x, ⟨hx, k, hf (by rw [map_pow, hk, map_one])⟩, rfl⟩

theorem exists_surjective_map {G G' P : Type*} [Group G] [Group G'] [Group P] [Finite G]
    (f : G →* G') (hf : Function.Injective f) {Q T : Subgroup G} {Q' T' : Subgroup G'}
    (hQ : Q.map f = Q') (hT : T.map f = T') (φ : oUpperTwoPrime (Q ⊔ T) →* P)
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (oddCoreIn Q).subgroupOf (oUpperTwoPrime (Q ⊔ T))) :
    ∃ φ' : oUpperTwoPrime (Q' ⊔ T') →* P, Function.Surjective φ' ∧
      φ'.ker = (oddCoreIn Q').subgroupOf (oUpperTwoPrime (Q' ⊔ T')) := by
  subst hQ hT
  have heq : (oUpperTwoPrime (Q ⊔ T)).map f = oUpperTwoPrime (Q.map f ⊔ T.map f) := by
    rw [oUpperTwoPrime_map f hf, Subgroup.map_sup]
  let e := ((oUpperTwoPrime (Q ⊔ T)).equivMapOfInjective f hf).trans
    (MulEquiv.subgroupCongr heq)
  refine ⟨φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective, ?_⟩
  ext x
  have hx : f (e.symm x) = x := by
    have h := congrArg Subtype.val (e.apply_symm_apply x)
    exact h
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_subgroupOf,
    mem_subgroupOf, oddCoreIn_map f hf, ← hx]
  exact (mem_map_iff_mem hf).symm

variable {G : Type} [Group G] [Finite G]

theorem thm4Case3_subgroupOf {M Y : Subgroup G} (hYM : Y ≤ M) (h : Thm4Case3 (Y.subgroupOf M)) :
    ∃ g ∈ M, g ∉ normalizer (Y : Set G) ∧ ∃ T : Subgroup G, T ≤ M ∧
      IsSylowOf 2 T (rightConjugate Y g) ∧ T ≤ normalizer (Y : Set G) ∧
      ∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (Y ⊔ T) →*
          Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧ φ.ker = (oddCoreIn Y).subgroupOf (oUpperTwoPrime (Y ⊔ T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩ := h
  have hN : ∀ x : M, x ∈ normalizer ((Y.subgroupOf M : Subgroup M) : Set M) ↔
      (x : G) ∈ normalizer (Y : Set G) := fun x => by
    rw [← subgroupOf_normalizer_eq hYM, mem_subgroupOf]
  have hYg : rightConjugate Y g ≤ M := fun y hy => by
    have h1 := hYM ((mem_rightConjugate_iff Y g y).mp hy)
    have h2 : y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem g.2) h1) g.2
  have hmap : (rightConjugate (Y.subgroupOf M) g).map M.subtype = rightConjugate Y g := by
    rw [← AschbacherTheorem5.SectionSix.subgroupOf_rightConjugate,
      map_subtype_subgroupOf_of_le hYg]
  refine ⟨g, g.2, fun h' => hg ((hN g).mpr h'), T.map M.subtype, map_subtype_le T, ?_, ?_, n, hn,
    exists_surjective_map M.subtype M.subtype_injective (map_subtype_subgroupOf_of_le hYM) rfl
      φ hφ hker⟩
  · rw [← hmap]
    exact (isSylowOf_map_subtype_iff M).mpr hT
  · rintro _ ⟨t, ht, rfl⟩
    exact (hN t).mp (hTN ht)

theorem Thm4Case3.rightConjugate {Q : Subgroup G} (h : Thm4Case3 Q) (a : G) :
    Thm4Case3 (rightConjugate Q a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩ := h
  set f := (MulAut.conj a⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj a⁻¹).injective
  refine ⟨a⁻¹ * g * a, ?_, AschbacherTightEmbedding.rightConjugate T a, ?_, ?_, n, hn,
    exists_surjective_map f hf rfl rfl φ hφ hker⟩
  · rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
    simpa [mul_assoc] using hg
  · have h1 := AschbacherTheorem3.IsSylowOf.map hT f
    rwa [show (AschbacherTightEmbedding.rightConjugate Q g).map f =
        AschbacherTightEmbedding.rightConjugate (AschbacherTightEmbedding.rightConjugate Q a)
          (a⁻¹ * g * a) by
      change AschbacherTightEmbedding.rightConjugate (AschbacherTightEmbedding.rightConjugate Q g)
        a = _
      rw [rightConjugate_mul, rightConjugate_mul]
      group] at h1
  · rw [← AschbacherTheorem3.rightConjugate_normalizer]
    exact map_mono hTN

theorem not_thm4Case3_rightConjugate {Q : Subgroup G} (h : ¬ Thm4Case3 Q) (a : G) :
    ¬ Thm4Case3 (rightConjugate Q a) := fun h' => h (by
  have := h'.rightConjugate a⁻¹
  rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this)

end CFSG.ComponentClassification.Asc75T4
