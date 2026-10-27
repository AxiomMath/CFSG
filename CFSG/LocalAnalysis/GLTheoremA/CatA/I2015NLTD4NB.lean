module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTD4N
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Levi

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Res417Seven
open scoped commutatorElement

section Cert


theorem td4n_graphFixedRootTorus_comm {K : Type} [Field K] (σ : K →+* K)
    {x y : ModGL TwistTag.D4.tag K} (hx : x ∈ graphFixedRootTorus TwistTag.D4 K σ)
    (hy : y ∈ graphFixedRootTorus TwistTag.D4 K σ) : x * y = y * x := by
  obtain ⟨⟨hxT, -, -⟩, -⟩ := hx
  obtain ⟨⟨hyT, -, -⟩, -⟩ := hy
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyT
  change rootDiagUnitHom TwistTag.D4.tag K l * rootDiagUnitHom TwistTag.D4.tag K l' =
    rootDiagUnitHom TwistTag.D4.tag K l' * rootDiagUnitHom TwistTag.D4.tag K l
  rw [← map_mul, ← map_mul, mul_comm]

theorem td4n_commutator_torus_sup_le {K : Type} [Field K] (σ : K →+* K)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    ⁅graphFixedRootTorus TwistTag.D4 K σ ⊔ (orbitRankOneHom TwistTag.D4 K σ a).range,
      graphFixedRootTorus TwistTag.D4 K σ ⊔ (orbitRankOneHom TwistTag.D4 K σ a).range⁆ ≤
        (orbitRankOneHom TwistTag.D4 K σ a).range := by
  set H := graphFixedRootTorus TwistTag.D4 K σ
  set M := (orbitRankOneHom TwistTag.D4 K σ a).range
  have hHM : H ≤ Subgroup.normalizer (M : Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedRootTorus_le_normalizer σ a
  have hdecomp : ∀ g ∈ H ⊔ M, ∃ m ∈ M, ∃ h ∈ H, g = m * h := by
    intro g hg
    have hg' : g ∈ ((M ⊔ H : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := by
      rw [sup_comm]
      exact hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M H hHM] at hg'
    obtain ⟨m, hm, h, hh, rfl⟩ := hg'
    exact ⟨m, hm, h, hh, rfl⟩
  have hc : ∀ h ∈ H, ∀ n ∈ M, h * n * h⁻¹ ∈ M := fun h hh n hn =>
    (Subgroup.mem_normalizer_iff.1 (hHM hh) n).1 hn
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨m₁, hm₁, h₁, hh₁, rfl⟩ := hdecomp g₁ hg₁
  obtain ⟨m₂, hm₂, h₂, hh₂, rfl⟩ := hdecomp g₂ hg₂
  have hhh : h₁ * h₂ = h₂ * h₁ := td4n_graphFixedRootTorus_comm σ hh₁ hh₂
  have hxy : (m₁ * h₁) * (m₂ * h₂) = (m₁ * (h₁ * m₂ * h₁⁻¹)) * (h₁ * h₂) := by group
  have hyx : (m₂ * h₂) * (m₁ * h₁) = (m₂ * (h₂ * m₁ * h₂⁻¹)) * (h₂ * h₁) := by group
  have hform : ⁅m₁ * h₁, m₂ * h₂⁆ = ((m₁ * h₁) * (m₂ * h₂)) * ((m₂ * h₂) * (m₁ * h₁))⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hform, hxy, hyx, hhh]
  have e : (m₁ * (h₁ * m₂ * h₁⁻¹)) * (h₂ * h₁) * ((m₂ * (h₂ * m₁ * h₂⁻¹)) * (h₂ * h₁))⁻¹ =
      (m₁ * (h₁ * m₂ * h₁⁻¹)) * (m₂ * (h₂ * m₁ * h₂⁻¹))⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hm₁ (hc h₁ hh₁ m₂ hm₂))
    (M.inv_mem (M.mul_mem hm₂ (hc h₂ hh₂ m₁ hm₁)))

theorem td4n_embedding_of_le_parabolic_singleton {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) (a : Fin TwistTag.D4.foldedTag.rank)
    {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEP : E ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
    (hs : IsSimpleGroup ↥E) (hna : ∃ x y : ↥E, x * y ≠ y * x) :
    ∃ ι : ↥E →* SL2 (orbitField TwistTag.D4 K σ.toRingHom a), Function.Injective ι := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, huniq, -, -, -, -, hQ2, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.D4 K σ {a}
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} with hQdef
  set L := graphFixedParabolicLevi TwistTag.D4 K σ.toRingHom {a} with hLdef
  set P := graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} with hPdef
  set H := graphFixedRootTorus TwistTag.D4 K σ.toRingHom with hHdef
  set M := (orbitRankOneHom TwistTag.D4 K σ.toRingHom a).range with hMdef
  have hPQ : P ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hdisj : Q ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgQ, hgL⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨_, -, hu⟩ := huniq g (hQP hgQ)
    have h1 := hu (g, 1) ⟨hgQ, L.one_mem, (mul_one g).symm⟩
    have h2 := hu (1, g) ⟨Q.one_mem, hgL, (one_mul g).symm⟩
    have := congrArg Prod.fst (h1.trans h2.symm)
    simpa using this
  have hfac : ∀ g ∈ P, ∃ q ∈ Q, ∃ l ∈ L, g = q * l := by
    intro g hg
    obtain ⟨⟨q, l⟩, ⟨hq, hl, h⟩, -⟩ := huniq g hg
    exact ⟨q, hq, l, hl, h⟩
  obtain ⟨ρ, hρL, hρQ⟩ := td4n_exists_hom_complement hPQ hdisj hfac hEP
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · exact h
    · exfalso
      have hEQ : E ≤ Q := by
        intro x hx
        have hx' : (⟨x, hx⟩ : ↥E) ∈ ρ.ker := h ▸ Subgroup.mem_top _
        have h1 := hρQ ⟨x, hx⟩
        rw [MonoidHom.mem_ker.1 hx', inv_one, mul_one] at h1
        exact h1
      have hE2 : IsPGroup 2 ↥E := (hQ2 2).to_le hEQ
      haveI : Finite ↥E := Subtype.finite
      haveI := hE2.isNilpotent
      haveI : Group.IsSolvable ↥E := inferInstance
      obtain ⟨x, y, hxy⟩ := hna
      exact hxy (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance x y)
  have hcommE : commutator ↥E = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h0 | h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna
      apply hxy
      have hmem : ⁅x, y⁆ ∈ commutator ↥E :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h0
  have hrange : ρ.range = ⁅ρ.range, ρ.range⁆ := by
    have h1 : Subgroup.map ρ ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ =
        ⁅Subgroup.map ρ ⊤, Subgroup.map ρ ⊤⁆ := Subgroup.map_commutator _ _ _
    have h2 : ⁅(⊤ : Subgroup ↥E), (⊤ : Subgroup ↥E)⁆ = ⊤ := by
      rw [← commutator_def]
      exact hcommE
    rw [h2, ← MonoidHom.range_eq_map] at h1
    exact h1
  have hρHM : ρ.range ≤ H ⊔ M := by
    rintro _ ⟨x, rfl⟩
    exact graphFixedParabolicLevi_singleton_le_sup σ a (hρL x)
  have hρM : ρ.range ≤ M := by
    calc ρ.range = ⁅ρ.range, ρ.range⁆ := hrange
      _ ≤ ⁅H ⊔ M, H ⊔ M⁆ := Subgroup.commutator_mono hρHM hρHM
      _ ≤ M := td4n_commutator_torus_sup_le σ.toRingHom a
  have hinj : Function.Injective (orbitRankOneHom TwistTag.D4 K σ.toRingHom a) :=
    orbitRankOneHom_injective_D4 hσ a
  let ρ' : ↥E →* ↥M := ρ.codRestrict M fun x => hρM ⟨x, rfl⟩
  refine ⟨((MonoidHom.ofInjective hinj).symm : ↥M ≃* _).toMonoidHom.comp ρ', ?_⟩
  intro x y hxy
  have h1 : ρ' x = ρ' y := (MonoidHom.ofInjective hinj).symm.injective hxy
  exact hρinj (congrArg Subtype.val h1)

theorem td4n_sl2_embedding {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ 3 = 1)
    {E U : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEC : E ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hUC : U ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hU2 : IsPGroup 2 U) (hU : U ≠ ⊥)
    (hEU : E ≤ Subgroup.normalizer (U : Set (ModGL TwistTag.D4.tag K)))
    (hs : IsSimpleGroup ↥E) (hna : ∃ x y : ↥E, x * y ≠ y * x) :
    ∃ a : Fin TwistTag.D4.foldedTag.rank,
      ∃ ι : ↥E →* SL2 (orbitField TwistTag.D4 K σ.toRingHom a), Function.Injective ι := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, -, J, hJ, hle⟩ := td4n_exists_conj_le_graphFixedParabolic TwistTag.D4 (r := 2) σ hσ
    hEC hUC hU2 hU hEU
  obtain ⟨a, haJ⟩ := exists_subset_singleton_of_ne_univ hJ
  have hmono : graphFixedParabolic TwistTag.D4 K σ.toRingHom J ≤
      graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    sup_le_sup_left (Subgroup.closure_mono (Set.image_mono haJ)) _
  set E' := E.map (MulAut.conj x).toMonoidHom with hE'
  let eE : ↥E ≃* ↥E' := E.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  obtain ⟨ι, hι⟩ := td4n_embedding_of_le_parabolic_singleton σ hσ a (hle.trans hmono)
    (eE.isSimpleGroup_congr.1 hs)
    (by
      obtain ⟨u, v, huv⟩ := hna
      exact ⟨eE u, eE v, fun h => huv (eE.injective (by rw [map_mul, map_mul]; exact h))⟩)
  exact ⟨a, ι.comp eE.toMonoidHom, hι.comp eE.injective⟩

theorem td4n_no_normalized_two {S : Type} [Group S] {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) (e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {E : Subgroup S} (hs : IsSimpleGroup ↥E) (hna : ∃ x y : ↥E, x * y ≠ y * x)
    (hN : TD4NoSL2 (Nat.card K) ↥E) :
    ∀ U : Subgroup S, U ≠ ⊥ → IsPGroup 2 ↥U → ¬ E ≤ Subgroup.normalizer (U : Set S) := by
  intro U hU hU2 hEU
  set ψ : S →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom with hψdef
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hψC : ∀ x, ψ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x => (e x).2
  have hE'C : E.map ψ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hU'C : U.map ψ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rintro _ ⟨x, -, rfl⟩
    exact hψC x
  have hU'1 : U.map ψ ≠ ⊥ := fun h =>
    hU ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hE'U' : E.map ψ ≤ Subgroup.normalizer ((U.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
      Set (ModGL TwistTag.D4.tag K)) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map ψ)
  let eE : ↥E ≃* ↥(E.map ψ) := E.equivMapOfInjective ψ hψ
  obtain ⟨a, ι, hι⟩ := td4n_sl2_embedding σ hσ hE'C hU'C (hU2.map ψ) hU'1 hE'U'
    (eE.isSimpleGroup_congr.1 hs)
    (by
      obtain ⟨u, v, huv⟩ := hna
      exact ⟨eE u, eE v, fun h => huv (eE.injective (by rw [map_mul, map_mul]; exact h))⟩)
  have hcard : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) ≤ Nat.card K :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  exact hN ↥(orbitField TwistTag.D4 K σ.toRingHom a) hcard (ι.comp eE.toMonoidHom)
    (hι.comp eE.injective)

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
