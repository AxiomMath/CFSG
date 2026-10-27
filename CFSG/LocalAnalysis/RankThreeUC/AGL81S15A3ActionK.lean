module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.HardMathSupport.Curtis.Proving.BlockUZModule
public import CFSG.LinearAlgebra.SL2MinimalFaithfulSection
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A3Perfect
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Block
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.C1
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
open CFSG.HardMathSupport.Curtis.Proving
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem conjAction_mem_blockZ_subgroupOf (K : Subgroup X) (k : K) {z : blockU K}
    (hz : z ∈ (blockZ K).subgroupOf (blockU K)) :
    (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) z ∈
      (blockZ K).subgroupOf (blockU K) := by
  have hzZ : (z : X) ∈ blockZ K := hz
  have hzC : (z : X) ∈ Subgroup.centralizer (K : Set X) := by
    rw [blockZ, Subgroup.mem_inf] at hzZ
    exact hzZ.2
  have hzk : (k : X) * (z : X) = (z : X) * (k : X) :=
    Subgroup.mem_centralizer_iff.mp hzC (k : X) k.2
  have hfix : (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) z = z := by
    apply Subtype.ext
    rw [CFSG.SL2MinimalFaithful.conjAction_apply]
    change (k : X) * (z : X) * (k : X)⁻¹ = (z : X)
    rw [hzk]
    group
  rwa [hfix]

@[expose] noncomputable def conjEndUZ (K : Subgroup X) (k : K) : UZ K →* UZ K :=
  QuotientGroup.map ((blockZ K).subgroupOf (blockU K))
    ((blockZ K).subgroupOf (blockU K))
    (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k).toMonoidHom
    (fun z hz => conjAction_mem_blockZ_subgroupOf K k hz)

@[simp] theorem conjEndUZ_mk (K : Subgroup X) (k : K) (u : blockU K) :
    conjEndUZ K k (QuotientGroup.mk u) =
      QuotientGroup.mk ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) u) :=
  rfl

@[expose] noncomputable def conjAutUZ (K : Subgroup X) (k : K) : MulAut (UZ K) where
  toFun := conjEndUZ K k
  invFun := conjEndUZ K k⁻¹
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H u =>
      change conjEndUZ K k⁻¹ (conjEndUZ K k (QuotientGroup.mk u)) = QuotientGroup.mk u
      rw [conjEndUZ_mk, conjEndUZ_mk]
      have h : (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k⁻¹)
          ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) u) = u := by
        apply Subtype.ext
        rw [CFSG.SL2MinimalFaithful.conjAction_apply,
          CFSG.SL2MinimalFaithful.conjAction_apply]
        push_cast
        group
      rw [h]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H u =>
      change conjEndUZ K k (conjEndUZ K k⁻¹ (QuotientGroup.mk u)) = QuotientGroup.mk u
      rw [conjEndUZ_mk, conjEndUZ_mk]
      have h : (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k)
          ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k⁻¹) u) = u := by
        apply Subtype.ext
        rw [CFSG.SL2MinimalFaithful.conjAction_apply,
          CFSG.SL2MinimalFaithful.conjAction_apply]
        push_cast
        group
      rw [h]
  map_mul' := fun a b => map_mul (conjEndUZ K k) a b

@[simp] theorem conjAutUZ_apply_mk (K : Subgroup X) (k : K) (u : blockU K) :
    conjAutUZ K k (QuotientGroup.mk u) =
      QuotientGroup.mk ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) u) :=
  conjEndUZ_mk K k u

@[expose] noncomputable def conjAction_UZ (K : Subgroup X) : K →* MulAut (UZ K) where
  toFun k := conjAutUZ K k
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [conjAutUZ_apply_mk]
      simp
  map_mul' k l := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H u =>
      simp only [conjAutUZ_apply_mk, MulAut.mul_apply]
      have h : (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) (k * l)) u =
          (CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k)
            ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) l) u) := by
        apply Subtype.ext
        rw [CFSG.SL2MinimalFaithful.conjAction_apply,
          CFSG.SL2MinimalFaithful.conjAction_apply,
          CFSG.SL2MinimalFaithful.conjAction_apply]
        push_cast
        group
      rw [h]

@[simp] theorem conjAction_UZ_mk (K : Subgroup X) (k : K) (u : blockU K) :
    conjAction_UZ K k (QuotientGroup.mk u) =
      QuotientGroup.mk ((CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k) u) :=
  rfl

theorem exists_threeCycle_action_ne_one {K : Subgroup X} (h : IsAltType K 3) :
    ∃ (k : X) (hk : k ∈ K), conjAction_UZ K ⟨k, hk⟩ ≠ 1 := by
  classical
  obtain ⟨α, hαsurj, hαker, β, hβsurj, hβker, hβint⟩ := h
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2
  have hσ3 : Equiv.Perm.IsThreeCycle σ := by
    refine Equiv.Perm.isThreeCycle_swap_mul_swap_same ?_ ?_ ?_ <;> decide
  let y : alternatingGroup (Fin 3) := ⟨σ, hσ3.mem_alternatingGroup⟩
  obtain ⟨k, hk⟩ := hαsurj y
  let x : evenWeight 3 :=
    ⟨![(1 : ZMod 2), 1, 0], by
      rw [evenWeight]
      decide⟩
  obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd x)
  let v : blockU K :=
    CFSG.SL2MinimalFaithful.conjAction (le_normalizer_blockU K) k u
  have hv : (v : X) = (k : X) * (u : X) * (k : X)⁻¹ :=
    CFSG.SL2MinimalFaithful.conjAction_apply _ _ _
  have hβvune : β v ≠ β u := by
    intro hβvu
    have hrel := hβint k u v hv 1
    rw [hβvu] at hrel
    have hαk : ((α k : alternatingGroup (Fin 3)) : Equiv.Perm (Fin 3)) = σ := by
      rw [hk]
    rw [hαk] at hrel
    rw [hu] at hrel
    simp only [toAdd_ofAdd] at hrel
    have hinv : (σ⁻¹) 1 = 2 := by decide
    rw [hinv] at hrel
    norm_num [x] at hrel
  have hclass : (QuotientGroup.mk v : UZ K) ≠ QuotientGroup.mk u := by
    intro heq
    apply hβvune
    have hmem : v⁻¹ * u ∈ (blockZ K).subgroupOf (blockU K) := QuotientGroup.eq.mp heq
    have hker : v⁻¹ * u ∈ β.ker := by
      rw [hβker]
      exact hmem
    have hdiv : (β v)⁻¹ * β u = 1 := by
      simpa [map_mul, map_inv] using MonoidHom.mem_ker.mp hker
    have h' : β u = β v := by
      have := congrArg (fun z => β v * z) hdiv
      simpa [mul_assoc] using this
    exact h'.symm
  refine ⟨k, k.2, ?_⟩
  intro hk1
  apply hclass
  have hstep : conjAction_UZ K k (QuotientGroup.mk u) = QuotientGroup.mk v := rfl
  have hone : conjAction_UZ K k (QuotientGroup.mk u) = QuotientGroup.mk u := by
    rw [hk1]
    rfl
  rw [hstep] at hone
  exact hone

theorem card_UZ_eq_four {K : Subgroup X} (h : IsAltType K 3) : Nat.card (UZ K) = 4 := by
  obtain ⟨-, -, -, β, hβsurj, hβker, -⟩ := h
  have eA : UZ K ≃* Multiplicative ↥(evenWeight 3) :=
    (QuotientGroup.quotientMulEquivOfEq hβker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβsurj)
  rw [Nat.card_congr eA.toEquiv]
  exact CFSG.Quasithin.EmptyFaithfulMultiple.L1547.card_evenWeight_three

theorem a3_final {K : Subgroup X} (h : IsAltType K 3)
    {L : Type*} [Group L] (hperf : Group.IsPerfect L)
    (ρ : L →* MulAut (UZ K)) (φ : K →* L)
    (hfac : conjAction_UZ K = ρ.comp φ) : False := by
  have hcard : Nat.card (UZ K) = 4 := card_UZ_eq_four h
  have hbot : ρ.range = ⊥ := action_trivial_of_perfect hcard hperf ρ
  have hρ : ρ = 1 := by
    apply MonoidHom.ext
    intro l
    have hmem : ρ l ∈ ρ.range := ⟨l, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  obtain ⟨k, hk, hne⟩ := exists_threeCycle_action_ne_one h
  apply hne
  rw [hfac]
  simp [hρ]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
