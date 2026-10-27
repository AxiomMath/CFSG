module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLongRoot
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLeviAbstract

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open scoped commutatorElement
open CFSG.Open CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Pure

@[expose] def twistedA5Index (Q : TauCeti.PrimePower) : TauCeti.ValidLieTypeIndex :=
  ⟨.twistedA 5 Q, by simp⟩

@[expose] def IsPSU6Cover {G : Type*} [Group G] (J : Subgroup G) (Q : TauCeti.PrimePower) : Prop :=
  ⁅J, J⁆ = J ∧ (Nat.card (Subgroup.center J)).Coprime 3 ∧
    Nonempty (J ⧸ Subgroup.center J ≃* Cat (twistedA5Index Q))

theorem IsPSU6Cover.of_mulEquiv {G G' : Type*} [Group G] [Group G'] {J : Subgroup G}
    {J' : Subgroup G'} (e : J ≃* J') {Q : TauCeti.PrimePower} (h : IsPSU6Cover J Q) :
    IsPSU6Cover J' Q := by
  obtain ⟨hperf, hZ, ⟨φ⟩⟩ := h
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr (Subgroup.center J) (Subgroup.center J') e
    (Subgroup.map_center_eq e)).symm.trans φ⟩⟩
  ·
    have h1 : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
      apply Subgroup.map_injective (Subgroup.subtype_injective J)
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hperf
    have h2 : ⁅(⊤ : Subgroup J'), (⊤ : Subgroup J')⁆ = ⊤ := by
      have h3 := congrArg (Subgroup.map e.toMonoidHom) h1
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective] at h3
      exact h3
    have h4 : ⁅J', J'⁆ = J' := by
      have h5 := congrArg (Subgroup.map J'.subtype) h2
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h5
      exact h5
    exact h4
  · have h1 : Nat.card (Subgroup.center J') = Nat.card (Subgroup.center J) := by
      rw [← Subgroup.map_center_eq e]
      exact Subgroup.card_map_of_injective e.injective
    rw [h1]
    exact hZ

theorem map_centralizer_eq_of_mulAut {G : Type*} [Group G] (e : MulAut G) (S : Subgroup G) :
    (Subgroup.centralizer (S : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup G) : Set G) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩ t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 ht
    have := Subgroup.mem_centralizer_iff.1 hc s hs
    change e s * e c = e c * e s
    rw [← map_mul, ← map_mul, this]
  · intro h
    refine ⟨e.symm g, Subgroup.mem_centralizer_iff.2 fun s hs => ?_, e.apply_symm_apply g⟩
    apply e.injective
    have := h (e s) (Subgroup.mem_map_of_mem _ hs)
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact this

theorem commutator_centralizer_invariant {G : Type*} [Group G] (S : Subgroup G) (e : MulAut G)
    (hS : S.map e.toMonoidHom = S) {u : G}
    (hu : u ∈ ⁅Subgroup.centralizer (S : Set G), Subgroup.centralizer (S : Set G)⁆) :
    e u ∈ ⁅Subgroup.centralizer (S : Set G), Subgroup.centralizer (S : Set G)⁆ := by
  have hC : (Subgroup.centralizer (S : Set G)).map e.toMonoidHom = Subgroup.centralizer (S : Set G) := by
    rw [map_centralizer_eq_of_mulAut, hS]
  have hJ : (⁅Subgroup.centralizer (S : Set G), Subgroup.centralizer (S : Set G)⁆).map e.toMonoidHom =
      ⁅Subgroup.centralizer (S : Set G), Subgroup.centralizer (S : Set G)⁆ := by
    rw [Subgroup.map_commutator, hC]
  rw [← hJ]
  exact Subgroup.mem_map_of_mem _ hu

end Pure

section Levi


theorem twE6LongRootSL2_map {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (e : MulAut (twistedE6RootGroup K σ)) (X Xm : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootSL2 (X.map e.toMonoidHom) (Xm.map e.toMonoidHom) =
      (twE6LongRootSL2 X Xm).map e.toMonoidHom := by
  unfold twE6LongRootSL2
  rw [MonoidHom.map_closure, Set.image_union]
  rfl

theorem twE6LongRootLevi_map {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (e : MulAut (twistedE6RootGroup K σ)) (X Xm : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootLevi (X.map e.toMonoidHom) (Xm.map e.toMonoidHom) =
      (twE6LongRootLevi X Xm).map e.toMonoidHom := by
  unfold twE6LongRootLevi
  rw [twE6LongRootSL2_map, Subgroup.map_commutator, map_centralizer_eq_of_mulAut]

@[expose] def TwE6LeviCatalogue : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → ∀ Q : TauCeti.PrimePower, Q.card = q →
      IsPSU6Cover (twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot))) Q

section FromCatalogue


theorem twE6LeviPlaneGeneration_of_catalogue (hcat : TwE6LeviCatalogue) :
    TwE6LeviPlaneGeneration := by
  intro K _ _ σ q hK3 hσ hK X Xm hpair E hEab hcard hSinv
  classical
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨hpr, f, hf1, hqf⟩ := twE6_exists_pow_ringChar_of_card_sq K q hK hq2
  let Q : TauCeti.PrimePower := ⟨ringChar K, f, hpr, hf1⟩
  have hQcard : Q.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  obtain ⟨g, hX, hXm⟩ := hpair
  have hJ : IsPSU6Cover (twE6LongRootLevi X Xm) Q := by
    have h0 := hcat K σ q hK3 hσ hK Q hQcard
    rw [hX, hXm, twE6LongRootLevi_map]
    exact IsPSU6Cover.of_mulEquiv ((MulAut.conj g).subgroupMap _) h0
  obtain ⟨hperf, hZ, ⟨φ⟩⟩ := hJ
  haveI := hEab
  refine levi_le_planeClosure (twE6LongRootLevi X Xm) E CFSG.Open.isElemAbelian_of_isElementaryAbelian
    hcard (fun ε hε u hu => ?_) hperf hZ (twistedA5Index Q) ?_ ?_ trivial ?_ φ
  · exact commutator_centralizer_invariant _ ε (hSinv ε hε) hu
  · simpa [twistedA5Index, TauCeti.LieTypeIndex.characteristic_twistedA, Q] using
      Ne.symm hK3
  · simp [twistedA5Index, IsD2SeitzException]
  · rintro ⟨q', h⟩
    simp [twistedA5Index] at h

end FromCatalogue

end Levi

end CFSG.LieType.SeitzGeneration.ExcWideThree
