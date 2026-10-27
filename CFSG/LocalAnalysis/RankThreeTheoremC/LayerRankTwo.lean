module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer perfect_action_inner
  solvable_of_centerQuotient)
open scoped commutatorElement

theorem eq_or_eq_of_isComponentOf_of_pRank_le_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Type*} [Group X] [Finite X] (hcore : primeComplementCore (G := X) p = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {L₁ L₂ L : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hL : IsComponentOf L ⊤) : L = L₁ ∨ L = L₂ := by
  have hp : p.Prime := Fact.out
  by_contra h
  push Not at h
  obtain ⟨t₁, ht₁, ho₁, -⟩ := exists_mem_sylow_inf_component hp hp2 hcore default h₁
  obtain ⟨t₂, ht₂, ho₂, hc₂⟩ := exists_mem_sylow_inf_component hp hp2 hcore default h₂
  obtain ⟨t, ht, ho, hc⟩ := exists_mem_sylow_inf_component hp hp2 hcore default hL
  have ht₁L : t₁ ∈ L₁ := (Subgroup.mem_inf.mp ht₁).2
  have h₁₂ := le_centralizer_of_component_ne h₁ h₂ hne
  have h2 : 2 ≤ CFSG.Open.pRank p (L₁ ⊔ L₂) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ho₁ (ho₂ ▸ pow_orderOf_eq_one t₂)
      (fun h => hc₂ (h₁₂ (Subgroup.zpowers_le.mpr ht₁L h)))
      (Subgroup.mem_centralizer_iff.mp (h₁₂ ht₁L) t₂ (Subgroup.mem_inf.mp ht₂).2).symm
      (Subgroup.mem_sup_left ht₁L) (Subgroup.mem_sup_right (Subgroup.mem_inf.mp ht₂).2)
  obtain ⟨E, hE, hEab, hEcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h2
  have hEC : E ≤ Subgroup.centralizer (L : Set X) :=
    hE.trans (sup_le (le_centralizer_of_component_ne h₁ hL (Ne.symm h.1))
      (le_centralizer_of_component_ne h₂ hL (Ne.symm h.2)))
  have h3 := three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hp hEab hEcard ho
    (fun h => hc (hEC h)) (Subgroup.le_centralizer_iff.mp hEC (Subgroup.mem_inf.mp ht).2)
    le_top (Subgroup.mem_top t)
  omega

private theorem le_sup_centralizer_of_isSolvable_outer {X : Type*} [Group X] {I Z : Subgroup X}
    (hZ : Group.IsPerfect Z) (hZN : Z ≤ Subgroup.normalizer (I : Set X))
    (hOut : Group.IsSolvable (Outer I)) : Z ≤ I ⊔ Subgroup.centralizer (I : Set X) := by
  intro z hz
  obtain ⟨i, hi⟩ := perfect_action_inner (I.normalizerMonoidHom.comp (Subgroup.inclusion hZN))
    ⟨z, hz⟩
  have hconj : ∀ x ∈ I, z * x * z⁻¹ = (i : X) * x * (i : X)⁻¹ := fun x hx => by
    simpa using congrArg (fun a : MulAut I => ((a ⟨x, hx⟩ : I) : X)) hi
  have hc : (i : X)⁻¹ * z ∈ Subgroup.centralizer (I : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * ((i : X)⁻¹ * z) = (i : X)⁻¹ * ((i : X) * x * (i : X)⁻¹) * z := by group
      _ = (i : X)⁻¹ * (z * x * z⁻¹) * z := by rw [hconj x hx]
      _ = (i : X)⁻¹ * z * x := by group
  rw [show z = (i : X) * ((i : X)⁻¹ * z) by group]
  exact Subgroup.mul_mem_sup i.2 hc

theorem le_normalizer_component_of_isPerfect {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*}
    [Group X] [Finite X] (hcore : primeComplementCore (G := X) p = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {Z : Subgroup X} (hZ : Group.IsPerfect Z)
    {L : Subgroup X} (hL : IsComponentOf L ⊤) : Z ≤ Subgroup.normalizer (L : Set X) := by
  have hconj : ∀ (g : X) {K : Subgroup X}, IsComponentOf K ⊤ →
      IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ := fun g K hK =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK
  by_cases h : ∃ L' : Subgroup X, IsComponentOf L' ⊤ ∧ L' ≠ L
  swap
  ·
    push Not at h
    exact fun z _ => mem_normalizer_of_conj_map_le (h _ (hconj z hL)).le
  obtain ⟨L', hL', hne'⟩ := h
  have hperm : ∀ (g : X) (K : Subgroup X), (K = L ∨ K = L') →
      K.map (MulAut.conj g).toMonoidHom = L ∨ K.map (MulAut.conj g).toMonoidHom = L' := by
    intro g K hK
    have hKc : IsComponentOf K ⊤ := by rcases hK with rfl | rfl <;> assumption
    exact eq_or_eq_of_isComponentOf_of_pRank_le_two hp2 hcore hrank hL hL' (Ne.symm hne')
      (hconj g hKc)
  have hmap : ∀ (k : X) (A B : Subgroup X), A.map (MulAut.conj k).toMonoidHom = B →
      (∀ x ∈ A, k * x * k⁻¹ ∈ B) ∧ (∀ x ∈ B, k⁻¹ * x * k ∈ A) := by
    intro k A B e
    refine ⟨fun x hx => e ▸ ⟨x, hx, rfl⟩, fun x hx => ?_⟩
    rw [← e] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [mul_assoc] using hy
  have hswap : ∀ g : X, (L.map (MulAut.conj g).toMonoidHom = L ∧
        L'.map (MulAut.conj g).toMonoidHom = L') ∨
      (L.map (MulAut.conj g).toMonoidHom = L' ∧ L'.map (MulAut.conj g).toMonoidHom = L) := by
    intro g
    have hinj : ∀ {A B C : Subgroup X}, A.map (MulAut.conj g).toMonoidHom = C →
        B.map (MulAut.conj g).toMonoidHom = C → A = B := by
      intro A B C eA eB
      refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
      · have := (hmap g B C eB).2 _ ((hmap g A C eA).1 x hx)
        simpa [mul_assoc] using this
      · have := (hmap g A C eA).2 _ ((hmap g B C eB).1 x hx)
        simpa [mul_assoc] using this
    rcases hperm g L (Or.inl rfl) with h0 | h0 <;> rcases hperm g L' (Or.inr rfl) with h1 | h1
    · exact absurd (hinj h0 h1) (Ne.symm hne')
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (hinj h0 h1) (Ne.symm hne')
  have hcomm : ∀ g h : X, ∀ x ∈ L, ⁅g, h⁆ * x * ⁅g, h⁆⁻¹ ∈ L := by
    intro g h x hx
    have e : ⁅g, h⁆ * x * ⁅g, h⁆⁻¹ = g * (h * (g⁻¹ * (h⁻¹ * x * h) * g) * h⁻¹) * g⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    rcases hswap g with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;> rcases hswap h with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h0).1 _
        ((hmap g _ _ g0).2 _ ((hmap h _ _ h0).2 _ hx)))
    · exact (hmap g _ _ g0).1 _ ((hmap h _ _ h1).1 _
        ((hmap g _ _ g1).2 _ ((hmap h _ _ h1).2 _ hx)))
    · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h1).1 _
        ((hmap g _ _ g1).2 _ ((hmap h _ _ h0).2 _ hx)))
    · exact (hmap g _ _ g1).1 _ ((hmap h _ _ h0).1 _
        ((hmap g _ _ g0).2 _ ((hmap h _ _ h1).2 _ hx)))
  rw [← Subgroup.isPerfect_iff.mp hZ, Subgroup.commutator_le]
  exact fun g _ h _ => Subgroup.mem_normalizer_fintype fun x hx => hcomm g h x hx

theorem le_layer_sup_centralizer_of_isPerfect {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Type*}
    [Group X] [Finite X] (hcore : primeComplementCore (G := X) p = ⊥)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hout : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥L ⧸ Subgroup.center ↥L)))
    {Z : Subgroup X} (hZ : Group.IsPerfect Z) :
    Z ≤ CFSG.layer X ⊔ Subgroup.centralizer (CFSG.layer X : Set X) := by
  have hZL : ∀ L : Subgroup X, IsComponentOf L ⊤ →
      Z ≤ L ⊔ Subgroup.centralizer (L : Set X) := by
    intro L hL
    have : Group.IsPerfect L := ⟨hL.2.2.1⟩
    have := hout L hL
    exact le_sup_centralizer_of_isSolvable_outer hZ
      (le_normalizer_component_of_isPerfect hp2 hcore hrank hZ hL) (solvable_of_centerQuotient L)
  by_cases h₀ : ∃ L : Subgroup X, IsComponentOf L ⊤
  swap
  ·
    push Not at h₀
    rw [CFSG.LocalCores.layer_eq_bot_of_forall fun K hK =>
      h₀ K ((CFSG.isComponent_iff_open K).mp hK)]
    refine fun z _ => Subgroup.mem_sup_right (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  obtain ⟨L, hL⟩ := h₀
  have hLE : L ∈ {K : Subgroup X | CFSG.IsComponent K} := (CFSG.isComponent_iff_open L).mpr hL
  by_cases h₁ : ∃ L' : Subgroup X, IsComponentOf L' ⊤ ∧ L' ≠ L
  swap
  ·
    push Not at h₁
    have hE : CFSG.layer X = L := by
      rw [CFSG.layer.eq_sSup]
      exact le_antisymm (sSup_le fun K hK => (h₁ K ((CFSG.isComponent_iff_open K).mp hK)).le)
        (le_sSup hLE)
    rw [hE]
    exact hZL L hL
  obtain ⟨L', hL', hne'⟩ := h₁
  have hne : L ≠ L' := Ne.symm hne'
  have hE : CFSG.layer X = L ⊔ L' := by
    rw [CFSG.layer.eq_sSup]
    refine le_antisymm (sSup_le fun K hK => ?_)
      (sup_le (le_sSup hLE) (le_sSup ((CFSG.isComponent_iff_open L').mpr hL')))
    rcases eq_or_eq_of_isComponentOf_of_pRank_le_two hp2 hcore hrank hL hL' hne
      ((CFSG.isComponent_iff_open K).mp hK) with h | h
    · exact h.le.trans le_sup_left
    · exact h.le.trans le_sup_right
  have h0 := hZL L hL
  have h1 := hZL L' hL'
  have h₁₀ := le_centralizer_of_component_ne hL' hL hne'
  have h₀₁ := le_centralizer_of_component_ne hL hL' hne
  have hdec : ∀ K : Subgroup X, ∀ z ∈ K ⊔ Subgroup.centralizer (K : Set X),
      ∃ a ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set X), z = a * c := by
    intro K z hz
    have hcomm : ∀ (a : K) (c : Subgroup.centralizer (K : Set X)),
        Commute (K.subtype a) ((Subgroup.centralizer (K : Set X)).subtype c) := fun a c =>
      Subgroup.mem_centralizer_iff.mp c.2 a a.2
    have hrange : (MonoidHom.noncommCoprod K.subtype
        (Subgroup.centralizer (K : Set X)).subtype hcomm).range =
        K ⊔ Subgroup.centralizer (K : Set X) := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    obtain ⟨⟨a, c⟩, hac⟩ : z ∈ (MonoidHom.noncommCoprod K.subtype
        (Subgroup.centralizer (K : Set X)).subtype hcomm).range := hrange ▸ hz
    rw [MonoidHom.noncommCoprod_apply] at hac
    exact ⟨a, a.2, c, c.2, by simpa using hac.symm⟩
  rw [hE]
  intro z hz
  obtain ⟨a, ha, c, hc, rfl⟩ := hdec L _ (h0 hz)
  obtain ⟨b, hb, d, hd, hbd⟩ := hdec L' _ (h1 hz)
  have hab : a⁻¹ * b = b * a⁻¹ :=
    (Subgroup.mem_centralizer_iff.mp (h₀₁ (L.inv_mem ha)) b hb).symm
  set e := a⁻¹ * d with he
  have hce : c = b * e := by
    calc c = a⁻¹ * (a * c) := by group
      _ = a⁻¹ * (b * d) := by rw [hbd]
      _ = b * (a⁻¹ * d) := by rw [← mul_assoc, hab, mul_assoc]
  have he₁ : e ∈ Subgroup.centralizer (L' : Set X) :=
    Subgroup.mul_mem _ (h₀₁ (L.inv_mem ha)) hd
  have he₀ : e ∈ Subgroup.centralizer (L : Set X) := by
    have : e = b⁻¹ * c := by rw [hce]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (h₁₀ hb)) hc
  have heC : e ∈ Subgroup.centralizer ((L ⊔ L' : Subgroup X) : Set X) := by
    have hle : Subgroup.zpowers e ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup X) : Set X) := by
      rw [Subgroup.le_centralizer_iff]
      refine sup_le ?_ ?_
      · rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr he₀
      · rw [← Subgroup.le_centralizer_iff]
        exact Subgroup.zpowers_le.mpr he₁
    exact hle (Subgroup.mem_zpowers e)
  rw [hce, ← mul_assoc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _
    (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb))) (Subgroup.mem_sup_right heC)

private theorem normal_centralizer_layer (X : Type*) [Group X] :
    (Subgroup.centralizer (CFSG.layer X : Set X)).Normal :=
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  Subgroup.normal_centralizer

theorem primeComplementCore_centralizer_layer_eq_bot {p : ℕ} [Fact p.Prime] {X : Type*}
    [Group X] [Finite X] (hcore : primeComplementCore (G := X) p = ⊥) :
    primeComplementCore (G := Subgroup.centralizer (CFSG.layer X : Set X)) p = ⊥ :=
  cfsg_subnormal_primeComplementCore_eq_bot p _
    (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (normal_centralizer_layer X).isSubnormal) hcore

theorem layer_centralizer_layer_eq_bot {X : Type*} [Group X] [Finite X] :
    CFSG.layer (Subgroup.centralizer (CFSG.layer X : Set X)) = ⊥ := by
  set C := Subgroup.centralizer (CFSG.layer X : Set X)
  refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => ?_
  set K' := K.map C.subtype
  have hK' : CFSG.IsComponent K' :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective _ C.subtype_injective)
      hK.1, hK.2.trans' (normal_centralizer_layer X).isSubnormal⟩
  have hcomm : ∀ a b : K', a * b = b * a := fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (Subgroup.map_subtype_le K b.2) a
      (CFSG.LocalCores.component_le_layer hK' a.2))
  have : Nontrivial K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  have : Group.IsPerfect K' := hK'.1.1
  exact Group.IsPerfect.not_isSolvable K' (Group.isSolvable_of_comm hcomm)

end CFSG.LocalAnalysis.RankThreeTheoremC
