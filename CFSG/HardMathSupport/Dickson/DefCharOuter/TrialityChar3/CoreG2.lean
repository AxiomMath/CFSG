module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Bruhat
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.UnipotentCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

section Transport

private theorem pPrimeCore_map_eq_bot_iff {G G' : Type*} [Group G] [Group G'] (p : ℕ)
    (f : G →* G') (hf : Function.Injective f) (A : Subgroup G) :
    CFSG.pPrimeCore p ↥(A.map f) = ⊥ ↔ CFSG.pPrimeCore p ↥A = ⊥ := by
  have h := CFSG.pPrimeCore_map_iso p (Subgroup.equivMapOfInjective A f hf)
  rw [← h]
  exact Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.equivMapOfInjective A f hf).injective

private theorem glaPPrimeCoreOf_eq_bot_iff_pPrimeCore {S : Type*} [Group S] (p : ℕ)
    (H : Subgroup S) :
    CFSG.Open.GLAPPrimeCoreOf p H = ⊥ ↔ CFSG.pPrimeCore p ↥H = ⊥ := by
  unfold CFSG.Open.GLAPPrimeCoreOf CFSG.Open.GLAPPrimeCore
  exact Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective H)

private theorem pPrimeCore_inf_centralizer_eq_bot {S T : Type*} [Group S] [Group T] (p : ℕ)
    (J : Subgroup S) (e : J ≃* T) (z : S) (hzJ : z ∈ J)
    (hT : CFSG.pPrimeCore p ↥(Subgroup.centralizer ({e ⟨z, hzJ⟩} : Set T)) = ⊥) :
    CFSG.pPrimeCore p ↥(J ⊓ Subgroup.centralizer ({z} : Set S)) = ⊥ := by
  have hAH : (Subgroup.centralizer ({(⟨z, hzJ⟩ : J)} : Set J)).map J.subtype =
      J ⊓ Subgroup.centralizer ({z} : Set S) := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ha
      refine Subgroup.mem_inf.2 ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ha
    · intro hg
      obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hgC
      refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hgC
  have hAB : (Subgroup.centralizer ({(⟨z, hzJ⟩ : J)} : Set J)).map e.toMonoidHom =
      Subgroup.centralizer ({e ⟨z, hzJ⟩} : Set T) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h' := congrArg e ha
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using h'
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨e.symm x, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  rw [← hAH, pPrimeCore_map_eq_bot_iff p J.subtype J.subtype_injective,
    ← pPrimeCore_map_eq_bot_iff p e.toMonoidHom e.injective, hAB]
  exact hT

end Transport


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem glaPPrimeCoreOf_fixSubgroup_conj_mul_fieldActor {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
        fieldActor (t := TwistTag.D4) σ σ)) = ⊥ := by
  rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0, glaPPrimeCoreOf_eq_bot_iff_pPrimeCore]
  generalize hzdef : longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc = z
  have hmap : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K rootD c) =
      pinnedX TwistTag.D4.tag K rootD c := by
    rw [show Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K rootD c) =
        pinnedX TwistTag.D4.tag K rootD (σ c) from
      Units.ext (entrywise_pinnedX σ.toRingHom rootD c), hc]
  have hzcoe : (z : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K rootD c := by
    rw [← hzdef]
    rfl
  have hzJ : z ∈ fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    apply Subtype.ext
    rw [coe_fieldActor, hzcoe, hmap]
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : (z : ModGL TwistTag.D4.tag K) = 1 := by simp [h]
    apply hc0
    apply pinnedX_injective TwistTag.D4.tag K rootD
    rw [pinnedX_zero, ← hzcoe]
    exact h1
  have hzpow : z ^ 3 = 1 := by
    have h3K : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
    have h0 : c + (c + c) = 0 := by linear_combination c * h3K
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzcoe, pow_three, ← pinnedX_add, ← pinnedX_add, h0, pinnedX_zero]
    rfl
  have hz3 : orderOf z = 3 := orderOf_eq_prime hzpow hz1
  have hzJo : orderOf (⟨z, hzJ⟩ : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))) = 3 :=
    (orderOf_injective (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).subtype
      (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)).subtype_injective _).symm.trans hz3
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard, CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ]
    exact_mod_cast Nat.le_self_pow (by omega) 3
  have hσ3 : ∀ x : K, σ (σ (σ x)) = x := ringEquiv_cube_apply_eq hK hσ
  let e := (fixSubgroupFieldActorEquiv K σ hσ3).trans
    (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivG2 σ hk3)
  have hz2 : orderOf (e ⟨z, hzJ⟩) = 3 :=
    (orderOf_injective e.toMonoidHom e.injective _).trans hzJo
  have hcore := glaPPrimeCoreOf_centralizer_adjointG2 3 (fixSubfield σ) (by norm_num) _ hz2
  exact pPrimeCore_inf_centralizer_eq_bot 3 _ e z hzJ
    ((glaPPrimeCoreOf_eq_bot_iff_pPrimeCore 3 _).1 hcore)

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
