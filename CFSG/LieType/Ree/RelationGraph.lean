module

public import CFSG.LieType.Ree.FixedSubgroupData

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank

namespace ReeTag

theorem relationExponent_mul_relationExponent_perm
    (t : ReeTag) (a : ℕ) (i : Fin t.tag.rank) :
    t.relationExponent a i * t.relationExponent a (t.perm i) = t.prime ^ (2 * a + 1) := by
  rw [relationExponent, relationExponent, relationExponent_eq, relationExponent_eq]
  calc t.prime ^ a * t.exponent i * (t.prime ^ a * t.exponent (t.perm i)) =
        t.prime ^ a * t.prime ^ a * (t.exponent i * t.exponent (t.perm i)) := by ring
    _ = t.prime ^ (2 * a + 1) := by rw [exponent_mul_exponent_perm]; ring

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem finiteReeAut_xElement
    (i : Fin t.tag.rank) (c : K) :
    t.finiteReeAut K a (xElement i c) = xElement (t.perm i) (c ^ t.relationExponent a i) :=
  (DFunLike.congr_fun (finiteReeAut_toMonoidHom a) (xElement i c)).trans
    (reeEndo_xElement _ a i c)

theorem finiteReeAut_yElement
    (i : Fin t.tag.rank) (c : K) :
    t.finiteReeAut K a (yElement i c) = yElement (t.perm i) (c ^ t.relationExponent a i) :=
  (DFunLike.congr_fun (finiteReeAut_toMonoidHom a) (yElement i c)).trans
    (reeEndo_yElement _ a i c)

theorem finiteReeAut_mul_self
    (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    t.finiteReeAut K a * t.finiteReeAut K a = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ (t.prime ^ (2 * a + 1)) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  refine MulEquiv.ext fun g => ?_
  have h := adjointGroup_hom_ext (f := (t.finiteReeAut K a * t.finiteReeAut K a).toMonoidHom)
    (g := (1 : MulAut (adjointGroup t.tag K)).toMonoidHom)
    (fun i c => by
      change t.finiteReeAut K a (t.finiteReeAut K a (xElement i c)) = xElement i c
      rw [finiteReeAut_xElement, finiteReeAut_xElement, perm_perm, ← pow_mul,
        relationExponent_mul_relationExponent_perm, hpow])
    (fun i c => by
      change t.finiteReeAut K a (t.finiteReeAut K a (yElement i c)) = yElement i c
      rw [finiteReeAut_yElement, finiteReeAut_yElement, perm_perm, ← pow_mul,
        relationExponent_mul_relationExponent_perm, hpow])
  exact DFunLike.congr_fun h g

theorem reeRelationGroup_eq_graph_finiteReeAut :
    reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) =
      ((adjointGroup t.tag K).subtype.prod
        ((adjointGroup t.tag K).subtype.comp (t.finiteReeAut K a).toMonoidHom)).range := by
  rw [finiteReeAut_toMonoidHom]
  exact reeRelationGroup_eq_graph _ a

theorem pair_mem_reeRelationGroup_iff_mem_reeGamma
    {g : ModGL t.tag K} :
    (g, g) ∈ reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) ↔ g ∈ t.reeGamma K a := by
  rw [pair_mem_reeRelationGroup_iff (shortFaithful (CharP.cast_eq_zero K t.prime)) a,
    mem_reeGamma]
  refine exists_congr fun hg => ?_
  rw [← DFunLike.congr_fun (finiteReeAut_toMonoidHom (t := t) (K := K) a) ⟨g, hg⟩]
  rfl

end ReeTag

open ReeTag

theorem reeTitsRelationModel_iff
    (t : ReeTag) (G : Type) [Group G] (f a : ℕ) :
    ReeTitsRelationModel G t.tag t.perm t.longSet t.prime f a ↔
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K t.prime),
        Nat.card K = t.prime ^ f ∧ Nonempty (G ≃* DerivedCentralQuotient (t.reeGamma K a)) := by
  constructor
  · rintro ⟨K, _, _, hK, ⟨e⟩⟩
    have : Fintype K := Fintype.ofFinite K
    have : CharP K t.prime := charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK])
    refine ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨e.trans ?_⟩⟩
    rw [reeGamma_eq_reeFixedGroup]
  · rintro ⟨K, _, _, _, hK, ⟨e⟩⟩
    refine ⟨K, inferInstance, inferInstance, hK, ⟨e.trans ?_⟩⟩
    rw [reeGamma_eq_reeFixedGroup]

theorem ree_tits_relation_graph_identification :
    (∀ (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K t.prime],
      Nat.card K = t.prime ^ (2 * a + 1) →
        t.finiteReeAut K a * t.finiteReeAut K a = 1 ∧
        reeRelationGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
            else t.prime ^ (a + 1)) =
          ((adjointGroup t.tag K).subtype.prod
            ((adjointGroup t.tag K).subtype.comp (t.finiteReeAut K a).toMonoidHom)).range ∧
        ∀ g : ModGL t.tag K, (g, g) ∈ reeRelationGroup t.tag K t.perm
          (fun i => if i ∈ t.longSet then t.prime ^ a else t.prime ^ (a + 1)) ↔
            g ∈ t.reeGamma K a) ∧
    ∀ (G : Type) [Group G] (p f : ℕ),
      (ReeTitsModel G .twistedG2 p f ↔ StatedLieAdmissible .twistedG2 0 p f ∧
        ∃ a : ℕ, f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (_ : CharP K ReeTag.G2.prime), Nat.card K = p ^ f ∧
            Nonempty (G ≃* DerivedCentralQuotient (ReeTag.G2.reeGamma K a))) ∧
      (ReeTitsModel G .twistedF4 p f ↔ StatedLieAdmissible .twistedF4 0 p f ∧
        ∃ a : ℕ, f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (_ : CharP K ReeTag.F4.prime), Nat.card K = p ^ f ∧
            Nonempty (G ≃* DerivedCentralQuotient (ReeTag.F4.reeGamma K a))) ∧
      (ReeTitsModel G .Tits p f ↔ StatedLieAdmissible .Tits 0 p f ∧
        ∃ a : ℕ, f = 2 * a + 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (_ : CharP K ReeTag.F4.prime), Nat.card K = p ^ f ∧
            Nonempty (G ≃* DerivedCentralQuotient (ReeTag.F4.reeGamma K a))) := by
  refine ⟨fun t a K _ _ _ hK => ⟨finiteReeAut_mul_self hK, reeRelationGroup_eq_graph_finiteReeAut,
    fun g => pair_mem_reeRelationGroup_iff_mem_reeGamma⟩, fun G _ p f => ⟨?_, ?_, ?_⟩⟩
  · constructor
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .G2 G f a).1 hmodel⟩
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .G2 G f a).2 hmodel⟩
  · constructor
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .F4 G f a).1 hmodel⟩
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .F4 G f a).2 hmodel⟩
  · constructor
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .F4 G f a).1 hmodel⟩
    · rintro ⟨hadm, a, hf, hmodel⟩
      have hp := hadm.2.2.2.1
      subst hp
      exact ⟨hadm, a, hf, (reeTitsRelationModel_iff .F4 G f a).2 hmodel⟩

end CFSG.LieType.Ree
