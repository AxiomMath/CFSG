module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootGenA1
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootGenWords
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Pure

theorem mem_normalizer_pCore_map {G : Type*} [Group G] (P : Subgroup G) (p : ℕ) {g : G}
    (hg : g ∈ P) :
    g ∈ Subgroup.normalizer (((CFSG.pCore p P).map P.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (CFSG.pCore_normal).conj_mem y hy ⟨g, hg⟩, by simp⟩
  · rintro ⟨y, hy, hyh⟩
    refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩, ?_, ?_⟩
    · simpa using (CFSG.pCore_normal).conj_mem y hy ⟨g, hg⟩⁻¹
    · have hyh' : (y : G) = g * h * g⁻¹ := hyh
      simp [hyh', mul_assoc]

end Pure

section Final


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem eq_top_of_normal_of_radical_le
    (hQ : (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
      (twistedE6RootGroup K σ).subtype = graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0)
    (H : Subgroup (twistedE6RootGroup K σ)) [hN : H.Normal]
    (hQH : twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) ≤ H) : H = ⊤ := by
  have hx : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a), xG σ a c ∈ H := by
    intro a c
    have hu : genU a ∈ relWeylTwist TwistTag.E6 := genU_mem a
    let nu : twistedE6RootGroup K σ :=
      ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) K (genU a),
        canonicalRep_mem_graphFixedRootGroup hu⟩
    have hz : ((nu * xG σ a c * nu⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈
        graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0 :=
      inf_le_inf_right _ (rootSpan_mono (image_genU_smul_subset a))
        (canonicalRep_conj_orbitX_mem TwistTag.E6 σ.toRingHom a hu c)
    rw [← hQ] at hz
    obtain ⟨q, hq, hqz⟩ := hz
    have hq' : q = nu * xG σ a c * nu⁻¹ := Subtype.ext hqz
    have hxq : xG σ a c = nu⁻¹ * q * nu⁻¹⁻¹ := by
      rw [hq']
      group
    rw [hxq]
    exact hN.conj_mem q (hQH hq) nu⁻¹
  have hy : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a), yG σ a c ∈ H := by
    intro a c
    have h := hN.conj_mem (xG σ a (-c)) (hx a (-c)) (nG σ a)
    rwa [nG_mul_xG_neg_mul_inv] at h
  have hle : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤
      H.map (twistedE6RootGroup K σ).subtype := by
    rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup σ.surjective]
    refine iSup_le fun a => (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨xG σ a c, hx a c, rfl⟩
    · exact ⟨yG σ a c, hy a c, rfl⟩
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨h, hh, hhg⟩ := hle g.2
  have : h = g := Subtype.ext hhg
  rwa [this] at hh

theorem twE6LongRootGenerates_of_structure
    (hP : (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).map
      (twistedE6RootGroup K σ).subtype = graphFixedParabolic TwistTag.E6 K σ.toRingHom J0)
    (hmax : ∀ H : Subgroup (twistedE6RootGroup K σ),
      twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ≤ H →
        H = twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ∨ H = ⊤)
    (hQ : (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
      (twistedE6RootGroup K σ).subtype = graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0)
    (hLevi : (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J0).subgroupOf
      (twistedE6RootGroup K σ) ≤
        Subgroup.normalizer ((twE6RootSubgroup K σ (-e6HighestRoot) :
          Subgroup (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) :
    ∃ n ∈ twE6LongRootSL2 (twE6RootSubgroup K σ e6HighestRoot)
        (twE6RootSubgroup K σ (-e6HighestRoot)),
      Subgroup.closure ((twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) :
          Set (twistedE6RootGroup K σ)) ∪
        ((twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
          (MulAut.conj n).toMonoidHom : Set (twistedE6RootGroup K σ))) = ⊤ := by
  refine ⟨nSL2 σ, nSL2_mem_SL2 σ, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hLeviP, hfac12, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K σ J0
  have hPQ : twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ≤
      Subgroup.normalizer (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) :
        Set (twistedE6RootGroup K σ)) :=
    fun g hg => mem_normalizer_pCore_map _ _ hg
  have hfac : ∀ g ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot),
      ∃ q ∈ twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot),
        ∃ m ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot),
          (nSL2 σ)⁻¹ * m * nSL2 σ ∈ twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) ∧
            g = q * m := by
    intro g hg
    have hg1 : (g : ModGL TwistTag.E6.tag K) ∈
        graphFixedParabolic TwistTag.E6 K σ.toRingHom J0 := by
      rw [← hP]
      exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨⟨q, m⟩, ⟨hq, hm, hqm⟩, -⟩ := hfac12 _ hg1
    have hq' : q ∈ (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
        (twistedE6RootGroup K σ).subtype := by
      rw [hQ]
      exact hq
    obtain ⟨q', hq'Q, rfl⟩ := hq'
    have hmG : m ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
      graphFixedParabolicLevi_le TwistTag.E6 K σ.toRingHom J0 hm
    have hm'P : (⟨m, hmG⟩ : twistedE6RootGroup K σ) ∈
        twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot) := by
      have hmP : m ∈ (twE6LongRootParabolic (twE6RootSubgroup K σ e6HighestRoot)).map
          (twistedE6RootGroup K σ).subtype := by
        rw [hP]
        exact hLeviP hm
      obtain ⟨p, hp, hpm⟩ := hmP
      have : p = ⟨m, hmG⟩ := Subtype.ext hpm
      rwa [this] at hp
    have hm'N := hLevi (Subgroup.mem_subgroupOf.2 hm : (⟨m, hmG⟩ : twistedE6RootGroup K σ) ∈
      (graphFixedParabolicLevi TwistTag.E6 K σ.toRingHom J0).subgroupOf (twistedE6RootGroup K σ))
    rw [← map_conj_X0 σ] at hm'N
    exact ⟨q', hq'Q, ⟨m, hmG⟩, hm'P,
      conj_mem_normalizer_of_mem_normalizer_map _ _ _ hm'N, Subtype.ext (by simpa using hqm)⟩
  have hnormal := normal_closure_union_conj hmax hPQ hfac (nSL2_not_mem_parabolic σ)
    (nSL2_mul_self_mem_parabolic σ)
  exact eq_top_of_normal_of_radical_le σ hQ _ fun x hx => Subgroup.subset_closure (Or.inl hx)

end Final

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot.Gen
