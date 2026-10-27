module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Open CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Transport

variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']

theorem LeviFacts.map {P Q : Subgroup G} (hL : LeviFacts P Q) (f : G →* G')
    (hf : Function.Injective f) : LeviFacts (P.map f) (Q.map f) := by
  rcases hL with hPQ | ⟨hgen, T, instT, g, hT, hg, hker⟩
  · left
    rw [← CFSG.Quasithin.map_perfectCore f P]
    exact Subgroup.map_mono hPQ
  · right
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.map_mono (f := f) hgen
      rw [Subgroup.map_commutator, CFSG.Quasithin.map_perfectCore f P] at h1
      exact h1
    · let E : ↥(CFSG.Quasithin.perfectCore P) ≃* ↥(CFSG.Quasithin.perfectCore (P.map f)) :=
        ((CFSG.Quasithin.perfectCore P).equivMapOfInjective f hf).trans
          (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore f P))
      refine ⟨T, instT, g.comp E.symm.toMonoidHom, hT, hg.comp E.symm.surjective, ?_⟩
      intro x hx
      have h1 := hker (E.symm x) hx
      have hxe : (x : G') = f ((E.symm x : ↥(CFSG.Quasithin.perfectCore P)) : G) := by
        conv_lhs => rw [← E.apply_symm_apply x]
        rfl
      rw [hxe]
      exact ⟨_, h1, rfl⟩

theorem LeviFacts.of_map {P Q : Subgroup G} (f : G →* G') (hf : Function.Injective f)
    (hL : LeviFacts (P.map f) (Q.map f)) : LeviFacts P Q := by
  rcases hL with hPQ | ⟨hgen, T, instT, g, hT, hg, hker⟩
  · left
    rw [← CFSG.Quasithin.map_perfectCore f P] at hPQ
    exact (Subgroup.map_le_map_iff_of_injective hf).1 hPQ
  · right
    refine ⟨?_, ?_⟩
    · rw [← CFSG.Quasithin.map_perfectCore f P, ← Subgroup.map_commutator] at hgen
      exact (Subgroup.map_le_map_iff_of_injective hf).1 hgen
    · let E : ↥(CFSG.Quasithin.perfectCore P) ≃* ↥(CFSG.Quasithin.perfectCore (P.map f)) :=
        ((CFSG.Quasithin.perfectCore P).equivMapOfInjective f hf).trans
          (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore f P))
      refine ⟨T, instT, g.comp E.toMonoidHom, hT, hg.comp E.surjective, ?_⟩
      intro x hx
      have h1 := hker (E x) hx
      have hxe : ((E x : ↥(CFSG.Quasithin.perfectCore (P.map f))) : G') = f (x : G) := rfl
      rw [hxe, Subgroup.mem_map_iff_mem hf] at h1
      exact h1

theorem ParabolicFacts.map {P Q : Subgroup G} (hF : ParabolicFacts P Q) (f : G →* G')
    (hf : Function.Injective f) : ParabolicFacts (P.map f) (Q.map f) where
  le := Subgroup.map_mono hF.le
  normalizes := (Subgroup.map_mono hF.normalizes).trans (Subgroup.le_normalizer_map f)
  pGroup := hF.pGroup.map f
  selfCentralizing := by
    rintro x ⟨⟨p, hp, rfl⟩, hx⟩
    have hpC : p ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := Subgroup.mem_centralizer_iff.1 hx (f q) ⟨q, hq, rfl⟩
      exact hf (by rw [map_mul, map_mul]; exact h1)
    exact ⟨p, hF.selfCentralizing ⟨hp, hpC⟩, rfl⟩
  center_le := by
    rintro x ⟨⟨q, hq, rfl⟩, hx⟩
    have hqC : q ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q' hq'
      have h1 := Subgroup.mem_centralizer_iff.1 hx (f q') ⟨q', hq', rfl⟩
      exact hf (by rw [map_mul, map_mul]; exact h1)
    have h2 := hF.center_le ⟨hq, hqC⟩
    rw [← Subgroup.map_commutator]
    exact ⟨q, h2, rfl⟩
  nonabelian := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    refine ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, fun h => hxy (hf ?_)⟩
    rw [map_mul, map_mul]
    exact h
  levi := hF.levi.map f hf

theorem ParabolicFacts.of_map {P Q : Subgroup G} (f : G →* G') (hf : Function.Injective f)
    (hF : ParabolicFacts (P.map f) (Q.map f)) : ParabolicFacts P Q where
  le := (Subgroup.map_le_map_iff_of_injective hf).1 hF.le
  normalizes := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro q
    have hpf : f p ∈ Subgroup.normalizer ((Q.map f : Subgroup G') : Set G') :=
      hF.normalizes ⟨p, hp, rfl⟩
    have h1 := Subgroup.mem_normalizer_iff.1 hpf (f q)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hf,
      Subgroup.mem_map_iff_mem hf] at h1
    exact h1
  pGroup := hF.pGroup.of_equiv (Q.equivMapOfInjective f hf).symm
  selfCentralizing := by
    intro p ⟨hp, hpC⟩
    have h1 : f p ∈ (P.map f) ⊓ Subgroup.centralizer ((Q.map f : Subgroup G') : Set G') := by
      refine ⟨⟨p, hp, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hpC q hq]
    have h2 := hF.selfCentralizing h1
    rwa [Subgroup.mem_map_iff_mem hf] at h2
  center_le := by
    intro q ⟨hq, hqC⟩
    have h1 : f q ∈ (Q.map f) ⊓ Subgroup.centralizer ((Q.map f : Subgroup G') : Set G') := by
      refine ⟨⟨q, hq, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨q', hq', rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hqC q' hq']
    have h2 := hF.center_le h1
    rw [← Subgroup.map_commutator, Subgroup.mem_map_iff_mem hf] at h2
    exact h2
  nonabelian := by
    obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hF.nonabelian
    exact ⟨x, hx, y, hy, fun h => hxy (by rw [← map_mul, ← map_mul, h])⟩
  levi := LeviFacts.of_map f hf hF.levi

end Transport

section Pair

@[expose] def HasParabolicPair (X : Type*) [Group X] (U : Subgroup X) : Prop :=
  ∃ Q₁ Q₂ : Subgroup X, Q₁ ≠ ⊤ ∧ Q₂ ≠ ⊤ ∧ Q₁ ⊔ Q₂ = ⊤ ∧
    (∀ α : MulAut X, U.map α.toMonoidHom = U →
      Q₁.map α.toMonoidHom = Q₁ ∧ Q₂.map α.toMonoidHom = Q₂) ∧
    (∃ R₁ : Subgroup X, ParabolicFacts Q₁ R₁) ∧ (∃ R₂ : Subgroup X, ParabolicFacts Q₂ R₂)

theorem HasParabolicPair.map {X X' : Type*} [Group X] [Group X'] [Finite X] [Finite X']
    {U : Subgroup X} (h : HasParabolicPair X U) (e : X ≃* X') :
    HasParabolicPair X' (U.map e.toMonoidHom) := by
  obtain ⟨Q₁, Q₂, h1, h2, hsup, hinv, ⟨R₁, hF₁⟩, ⟨R₂, hF₂⟩⟩ := h
  have hne : ∀ Q : Subgroup X, Q ≠ ⊤ → Q.map e.toMonoidHom ≠ ⊤ := by
    intro Q hQ hQ'
    apply hQ
    have := congrArg (Subgroup.map e.symm.toMonoidHom) hQ'
    rwa [map_symm_map, Subgroup.map_top_of_surjective _ e.symm.surjective] at this
  refine ⟨Q₁.map e.toMonoidHom, Q₂.map e.toMonoidHom, hne _ h1, hne _ h2, ?_, ?_,
    ⟨R₁.map e.toMonoidHom, hF₁.map e.toMonoidHom e.injective⟩,
    ⟨R₂.map e.toMonoidHom, hF₂.map e.toMonoidHom e.injective⟩⟩
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ e.surjective]
  · intro α' hα'
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h := hα'
      rw [map_comm_equiv] at h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h
    obtain ⟨h1, h2⟩ := hinv α hαU
    refine ⟨?_, ?_⟩
    · rw [map_comm_equiv, ← hα, h1]
    · rw [map_comm_equiv, ← hα, h2]

theorem HasParabolicPair.of_isSylow {X : Type*} [Group X] [Finite X] {U₀ U : Subgroup X}
    (h₀ : HasParabolicPair X U₀) (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasParabolicPair X U := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have := h₀.map (MulAut.conj k)
  rwa [hconj] at this

end Pair

section Generic

variable {G : Type} [Group G] [Finite G]

theorem pairConclusion_of_hasParabolicPair {L R : Subgroup G} {X : Type} [Group X]
    (e : ↥L ≃* X) {U₀ : Subgroup X} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (hP : HasParabolicPair X U₀) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf (R ⊓ L) L) : PairConclusion L R := by
  have : Finite X := Finite.of_equiv ↥L e.toEquiv
  have hSL : CFSG.QuasithinUnique.IsSylowTwoOf ((R ⊓ L).subgroupOf L) ⊤ :=
    isSylowTwoOf_subgroupOf_top hS
  set S : Subgroup X := ((R ⊓ L).subgroupOf L).map e.toMonoidHom with hSdef
  have hSX : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    refine isSylowTwoOf_iff_isSylowOf.2 ?_
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hSL)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨Q₁, Q₂, h1, h2, hsup, hinv, ⟨R₁, hF₁⟩, ⟨R₂, hF₂⟩⟩ := hP.of_isSylow hU₀ hSX
  let φ : X →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ]⟩
  have hφx : ∀ x : X, (φ x : G) = ((e.symm x : ↥L) : G) := fun x => rfl
  have hxS : ∀ x : X, x ∈ S ↔ ((e.symm x : ↥L) : G) ∈ R := by
    intro x
    rw [hSdef, Subgroup.mem_map_equiv]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, (e.symm x).2⟩
  have hinvR : ∀ r ∈ R, ∀ Q : Subgroup X,
      (∀ α : MulAut X, S.map α.toMonoidHom = S → Q.map α.toMonoidHom = Q) →
      r ∈ Subgroup.normalizer ((Q.map φ : Subgroup G) : Set G) := by
    intro r hr Q hQ
    let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨r, hRN hr⟩
    let α : MulAut X := e.symm.trans (ψ.trans e)
    have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = r * (y : G) * r⁻¹ := fun y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨r, hRN hr⟩ y
    have hφα : ∀ x, φ (α x) = r * φ x * r⁻¹ := by
      intro x
      show (((e.symm (e (ψ (e.symm x)))) : ↥L) : G) = r * ((e.symm x : ↥L) : G) * r⁻¹
      rw [MulEquiv.symm_apply_apply]
      exact hψ _
    have hαx : ∀ x : X, α x ∈ S ↔ x ∈ S := by
      intro x
      rw [hxS, hxS]
      have : ((e.symm (α x) : ↥L) : G) = r * ((e.symm x : ↥L) : G) * r⁻¹ := hφα x
      rw [this]
      constructor
      · intro h
        have h1 : r⁻¹ * (r * ((e.symm x : ↥L) : G) * r⁻¹) * r ∈ R :=
          R.mul_mem (R.mul_mem (R.inv_mem hr) h) hr
        simpa [mul_assoc] using h1
      · intro h
        exact R.mul_mem (R.mul_mem hr h) (R.inv_mem hr)
    have hαS : S.map α.toMonoidHom = S := by
      ext y
      rw [Subgroup.mem_map_equiv]
      obtain ⟨x, rfl⟩ := α.surjective y
      rw [MulEquiv.symm_apply_apply]
      exact (hαx x).symm
    have hQα := hQ α hαS
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
    have hcomp : ((MulAut.conj r : MulAut G) : G →* G).comp φ = φ.comp α.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact (hφα x).symm
    rw [hcomp, ← Subgroup.map_map, hQα]
  refine ⟨Q₁.map φ, Q₂.map φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range φ Q₁).trans hrange.le
  · exact (Subgroup.map_le_range φ Q₂).trans hrange.le
  · intro h
    apply h1
    rw [← hrange, MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective hφ h
  · intro h
    apply h2
    rw [← hrange, MonoidHom.range_eq_map] at h
    exact Subgroup.map_injective hφ h
  · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, hrange]
  · exact fun r hr => hinvR r hr Q₁ (fun α hα => (hinv α hα).1)
  · exact fun r hr => hinvR r hr Q₂ (fun α hα => (hinv α hα).2)
  · exact (hF₁.map φ hφ).charTwo
  · exact (hF₂.map φ hφ).charTwo
  · exact (hF₁.map φ hφ).not_hasChi0Block
  · exact (hF₂.map φ hφ).not_hasChi0Block

end Generic



end CFSG.QuasithinUnique.Vol2Native.L239.Lie
