module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamA
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusMain

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open CFSG.LieType.Steinberg.TwistedE6 (sigma)

section Field

variable {K : Type} [Field K]

theorem graphBeta6_graphTorusSLFieldAut (ρ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) (graphTorusSLFieldAut ρ g) =
      graphTorusSLFieldAut ρ ((slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) g) := by
  have h : (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K).toMonoidHom.comp
      (graphTorusSLFieldAut ρ).toMonoidHom = (graphTorusSLFieldAut ρ).toMonoidHom.comp
      (slConjugation 6 K (graphGram6 K) * slGraphAut 6 K).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense
      (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    simp only [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, graphTorusSLFieldAut_apply, map_transvection,
      graphBeta6_transvection, RingHom.coe_coe, map_neg]
  exact DFunLike.congr_fun h g

end Field

section Norm


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_normalized_cover6 (e : L ≃* adjointGroup .F4 K) {t : G}
    (Φ₁ : Matrix.SpecialLinearGroup (Fin 6) K →* G)
    (hker : Φ₁.ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) K))
    (hc : ∀ g, t * Φ₁ g * t⁻¹ = Φ₁ ((slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) g))
    (hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X) :
    ∃ Φ' : Matrix.SpecialLinearGroup (Fin 6) K →* G, Φ'.range = Φ₁.range ∧
      Φ'.ker ≤ center (Matrix.SpecialLinearGroup (Fin 6) K) ∧
      (∀ g, t * Φ' g * t⁻¹ = Φ' ((slConjugation 6 K (graphGram6 K) * slGraphAut 6 K) g)) ∧
      ∀ s : StatedSp 3 K, Φ' (sp6ToSL6 s) = levi6Hom e (RingEquiv.refl K) s := by
  set βC : MulAut (Matrix.SpecialLinearGroup (Fin 6) K) :=
    slConjugation 6 K (graphGram6 K) * slGraphAut 6 K with hβCdef
  set ι : StatedSp 3 K →* Matrix.SpecialLinearGroup (Fin 6) K := sp6ToSL6 with hιdef
  have hfix : fixedSubgroup βC = ι.range := fixedSubgroup_graphGram6
  have hιperf : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_statedSp_three]
  have hcore : perfectCore (fixedSubgroup βC) = ι.range := by
    rw [hfix]
    exact CFSG.Quasithin.perfectCore_eq_self_of_perfect hιperf
  have hβ : ∀ g, Φ₁ (βC g) = t * Φ₁ g * t⁻¹ := fun g => (hc g).symm
  have hmap := map_perfectCore_fixedSubgroup_eq Φ₁ hker hβ
  rw [hcore, hD] at hmap
  set κ : StatedSp 3 K →* G := Φ₁.comp ι with hκdef
  have hκr : κ.range = neighbourLeviG e .X := by
    rw [hκdef, MonoidHom.range_comp]
    exact hmap
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : ι g ∈ center (Matrix.SpecialLinearGroup (Fin 6) K) := hker hg
    have hgc' : g ∈ center (StatedSp 3 K) := by
      rw [mem_center_iff]
      intro h
      apply sp6ToSL6_injective
      rw [map_mul, map_mul]
      exact mem_center_iff.mp hgc (ι h)
    rw [CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot] at hgc'
    exact (mem_bot.mp hgc')
  have hlam := levi6Hom_injective e (RingEquiv.refl K)
  have hrange : (levi6Hom e (RingEquiv.refl K)).range = κ.range := by
    rw [range_levi6Hom, hκr]
  set δ : MulAut (StatedSp 3 K) := ((MonoidHom.ofInjective hlam).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hκ).symm with hδdef
  have hκδ : ∀ g, κ (δ g) = levi6Hom e (RingEquiv.refl K) g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκ).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hlam g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, ρ, hsρ⟩ := graphTorus_exists_eq_conj_statedSpMap δ
  set δh : MulAut (Matrix.SpecialLinearGroup (Fin 6) K) :=
    MulAut.conj (ι s) * graphTorusSLFieldAut ρ with hδh
  have hβs : βC (ι s) = ι s := by
    have : ι s ∈ fixedSubgroup βC := by
      rw [hfix]
      exact ⟨s, rfl⟩
    exact this
  have hβδ : ∀ g, βC (δh g) = δh (βC g) := by
    intro g
    have e1 : δh g = ι s * graphTorusSLFieldAut ρ g * (ι s)⁻¹ := rfl
    have e2 : δh (βC g) = ι s * graphTorusSLFieldAut ρ (βC g) * (ι s)⁻¹ := rfl
    have e3 : βC (graphTorusSLFieldAut ρ g) = graphTorusSLFieldAut ρ (βC g) :=
      graphBeta6_graphTorusSLFieldAut ρ g
    rw [e1, e2, map_mul, map_mul, map_inv, hβs, e3]
  set Φ' : Matrix.SpecialLinearGroup (Fin 6) K →* G := Φ₁.comp δh.toMonoidHom with hΦ'
  have hΦ'ι : ∀ g, Φ' (ι g) = levi6Hom e (RingEquiv.refl K) g := by
    intro g
    rw [← hκδ, hsρ, hκdef]
    change Φ₁ (δh (ι g)) = Φ₁ (ι (s * statedSpMap ((ρ : K ≃+* K) : K →+* K) 3 g * s⁻¹))
    rw [hδh, MulAut.mul_apply, MulAut.conj_apply, graphTorusSLFieldAut_apply, hιdef,
      ← sp6ToSL6_statedSpMap]
    simp only [map_mul, map_inv]
  refine ⟨Φ', ?_, ?_, fun g => ?_, hΦ'ι⟩
  · rw [hΦ', MonoidHom.range_comp, MonoidHom.range_eq_top.2 δh.surjective,
      ← MonoidHom.range_eq_map]
  · intro g hg
    have h1 : δh g ∈ center (Matrix.SpecialLinearGroup (Fin 6) K) := hker hg
    rw [← Subgroup.map_center_eq (δh.symm : Matrix.SpecialLinearGroup (Fin 6) K ≃* _)]
    exact ⟨δh g, h1, δh.symm_apply_apply g⟩
  · change t * Φ₁ (δh g) * t⁻¹ = Φ₁ (δh (βC g))
    rw [hc, hβδ]

end Norm

section Transport

variable {n : ℕ} {F K : Type} [Field F] [Field K]

@[expose] noncomputable def slRingEquiv (ε : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin n) F ≃* Matrix.SpecialLinearGroup (Fin n) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (ε : F →+* K))
    (Matrix.SpecialLinearGroup.map (ε.symm : K →+* F))
    (by
      ext g i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by
      ext g i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem exists_cover_transport {G : Type} [Group G] (ε : F ≃+* K)
    (Φ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ.ker ≤ center (Matrix.SpecialLinearGroup (Fin n) F)) :
    ∃ Φ' : Matrix.SpecialLinearGroup (Fin n) K →* G, Φ'.range = Φ.range ∧
      Φ'.ker ≤ center (Matrix.SpecialLinearGroup (Fin n) K) := by
  refine ⟨Φ.comp (slRingEquiv (n := n) ε).symm.toMonoidHom, ?_, fun g hg => ?_⟩
  · have hs : ((slRingEquiv (n := n) ε).symm.toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.2 (slRingEquiv (n := n) ε).symm.surjective
    rw [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]
  · have h1 : (slRingEquiv (n := n) ε).symm g ∈ center (Matrix.SpecialLinearGroup (Fin n) F) :=
      hker hg
    rw [← Subgroup.map_center_eq (slRingEquiv (n := n) ε)]
    exact ⟨_, h1, MulEquiv.apply_symm_apply _ g⟩

end Transport

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

@[expose] def IsLeviNormalizedA (e₁ : L ≃* adjointGroup .F4 K)
    (ΦA : e6ScLevi K e6A5Nodes →* G) : Prop :=
  ∀ s : StatedSp 3 K,
    ΦA (graphParamEquiv K (RingEquiv.refl K) (sp6ToSL6 s)) = levi6Hom e₁ (RingEquiv.refl K) s

theorem exists_graphParamA_normalized_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) (hX : HR8Kind e t f .X .linear6) :
    ∃ ΦA : e6ScLevi K e6A5Nodes →* G, ΦA.range = neighbourCore e .X ∧
      ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) ∧
      (∀ x y : e6ScLevi K e6A5Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) ∧
      IsLeviNormalizedA e ΦA := by
  obtain ⟨F, _, _, hF, Φ, hr, hk⟩ := exists_sl6_cover_neighbourCore hw hf e (by decide) hX
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv hF hw.card_eq
  obtain ⟨ΦK, hrK, hkK⟩ := exists_cover_transport ε Φ hk
  obtain ⟨Φ₁, hr₁, hk₁, hc₁⟩ := exists_graphCover6_X hw hf e hX hw.card_eq ΦK
    (hrK.trans hr) hkK
  have hD : perfectCore (Φ₁.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hr₁, perfectCore_neighbourCore_inf_centralizer_X hw hf e, neighbourLeviG_eq_modelToG]
  obtain ⟨Φ', hr', hk', hc', hn'⟩ := exists_normalized_cover6 e Φ₁ hk₁ hc₁ hD
  refine ⟨Φ'.comp (graphParamEquiv K (RingEquiv.refl K)).symm.toMonoidHom,
    (range_comp_graphParamEquiv_symm _ Φ').trans (hr'.trans hr₁),
    ker_comp_graphParamEquiv_symm_le_center _ hk', conj_comp_graphParamEquiv_symm _ hc',
    fun s => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hn']

omit [CharP K 2] in
theorem exists_graphParamA_normalized_Y [CharP K CFSG.LieType.Ree.ReeTag.F4.prime] {t : G}
    {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f) (e : L ≃* adjointGroup .F4 K)
    (hY : HR8Kind e t f .Y .linear6) :
    ∃ ΦA : e6ScLevi K e6A5Nodes →* G, ΦA.range = neighbourCore e .Y ∧
      ΦA.ker ≤ center (e6ScLevi K e6A5Nodes) ∧
      (∀ x y : e6ScLevi K e6A5Nodes,
        (y : e6Data_valid.minGroup K) = sigma K (RingHom.id K) x → t * ΦA x * t⁻¹ = ΦA y) ∧
      IsLeviNormalizedA (e.trans (graphAutF4 K).symm) ΦA := by
  rw [neighbourCore_Y_eq_X]
  exact exists_graphParamA_normalized_X hw hf _ ((hr8Kind_Y_iff_X e).1 hY)

end Setting

end CFSG.SeitzReduction.F4Pilot
