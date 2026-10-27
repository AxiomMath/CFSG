module

public import CFSG.LieType.Ree.LargeReeMinimalBorel
public import CFSG.LieType.Ree.LargeReeSimplePairGeneration
public import CFSG.LieType.Ree.LargeReeSylowOpposition

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.BorelTits

theorem exists_conj_normalizer_le_proper_of_holds {X : Type*} [Group X] [Finite X] {r : ℕ}
    [Fact r.Prime] (hH : Holds X r) (T : Sylow r X) {B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer ((T : Subgroup X) : Set X)) {U : Subgroup X} (hU : U ≠ ⊥)
    (hUr : IsPGroup r U) :
    ∃ g : X, ∃ Q : Subgroup X, Q ≠ ⊤ ∧ B ≤ Q ∧
      (Subgroup.normalizer (U : Set X)).map (MulAut.conj g).toMonoidHom ≤ Q := by
  obtain ⟨S, P, hP, hNU, -, -, hNS⟩ := hH U hU hUr
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S T
  have hT : (T : Subgroup X) = (S : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    subst hg
    rfl
  refine ⟨g, P.map (MulAut.conj g).toMonoidHom, ?_, ?_, Subgroup.map_mono hNU⟩
  · intro htop
    exact hP (Subgroup.map_injective (MulAut.conj g).injective
      (htop.trans (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm))
  · intro b hb
    have hb' : b ∈ Subgroup.normalizer
        ((S.map (MulAut.conj g).toMonoidHom : Subgroup X) : Set X) := by
      have := hB hb
      rwa [hT] at this
    rw [← Subgroup.map_equiv_normalizer_eq] at hb'
    exact Subgroup.map_mono hNS hb'


section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem exists_le_reeLocalParabolic_of_proper (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A : Subgroup (ModGL F4.tag K)} (hBA : F4.reeFixedBorel K a ≤ A)
    (hAΓ : A ≤ F4.reeGamma K a) (hne : A ≠ F4.reeGamma K a) :
    ∃ j, A ≤ F4.reeLocalParabolic K a j := by
  obtain ⟨hA, -⟩ := ree_Borel_overgroup_classification F4 a K A hBA hAΓ
  by_cases hall : ∀ j : Fin F4.fixedOrbitCount,
      canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ A
  · exfalso
    refine hne (le_antisymm hAΓ ?_)
    rw [large_Ree_simple_pair_generation a K hK]
    exact sup_le ((reeLocalBlock_le _).trans (reeLocalParabolic_le_of_mem hBA (hall _)))
      ((reeLocalBlock_le _).trans (reeLocalParabolic_le_of_mem hBA (hall _)))
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have hcomb : ∀ j : Fin F4.fixedOrbitCount, ∃ i : Fin F4.fixedOrbitCount,
        ∀ k, k ≠ j → k = i := by decide
    obtain ⟨i, hi⟩ := hcomb j
    refine ⟨i, ?_⟩
    rw [← reeParabolic_singleton i, hA]
    refine sup_le_sup_left (Subgroup.closure_mono (Set.image_mono fun k hk => ?_)) _
    exact hi k fun h => hj (h ▸ hk)


theorem exists_conj_le_reeLocalParabolic (hK : Nat.card K = 2 ^ (2 * a + 1))
    {A R : Subgroup (ModGL F4.tag K)} (hAΓ : A ≤ F4.reeGamma K a) (hRΓ : R ≤ F4.reeGamma K a)
    (hR : R ≠ ⊥) (hRp : IsPGroup 2 R)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL F4.tag K))) :
    ∃ y ∈ F4.reeGamma K a, ∃ j,
      A.map (MulAut.conj y).toMonoidHom ≤ F4.reeLocalParabolic K a j := by
  have := finite_modGL (τ := F4.tag) (K := K)
  have : Fact (Nat.Prime F4.prime) := ⟨by decide⟩
  have hH : Holds ↥(F4.reeGamma K a) F4.prime := by
    have h := holds_reeFixedGroup F4 K a
    rwa [← reeGamma_eq_reeFixedGroup] at h
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  obtain ⟨T, hT⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hU : R.subgroupOf (F4.reeGamma K a) ≠ ⊥ := fun h =>
    hR ((Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hRΓ)
  have hUp : IsPGroup F4.prime ↥(R.subgroupOf (F4.reeGamma K a)) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRΓ).symm
  have hB : (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) ≤
      Subgroup.normalizer ((T : Subgroup ↥(F4.reeGamma K a)) : Set ↥(F4.reeGamma K a)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1
      (reeFixedBorel_le_normalizer_reeFixedPosUnipotent (Subgroup.mem_subgroupOf.1 hb)) x
  obtain ⟨g, Q, hQ, hBQ, hNQ⟩ := exists_conj_normalizer_le_proper_of_holds hH T hB hU hUp
  set Q' : Subgroup (ModGL F4.tag K) := Q.map (F4.reeGamma K a).subtype with hQ'
  have hQ'Γ : Q' ≤ F4.reeGamma K a := Subgroup.map_subtype_le Q
  have hBQ' : F4.reeFixedBorel K a ≤ Q' := fun b hb =>
    ⟨⟨b, (Subgroup.mem_inf.1 hb).2⟩, hBQ (Subgroup.mem_subgroupOf.2 hb), rfl⟩
  have hQ'ne : Q' ≠ F4.reeGamma K a := by
    intro h
    refine hQ (eq_top_iff.2 fun x _ => ?_)
    have hx : (x : ModGL F4.tag K) ∈ Q' := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subtype.ext hyx] at hy
  obtain ⟨j, hj⟩ := exists_le_reeLocalParabolic_of_proper hK hBQ' hQ'Γ hQ'ne
  refine ⟨(g : ModGL F4.tag K), g.2, j, fun y hy => hj ?_⟩
  obtain ⟨x, hx, rfl⟩ := hy
  have hxN : (⟨x, hAΓ hx⟩ : ↥(F4.reeGamma K a)) ∈
      Subgroup.normalizer ((R.subgroupOf (F4.reeGamma K a) : Subgroup _) : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 (hAR hx) z
  exact ⟨_, hNQ ⟨_, hxN, rfl⟩, rfl⟩

end Ree

end CFSG.LieType.SeitzGeneration
