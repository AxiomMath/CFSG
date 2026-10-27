module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.HardMathSupport.Lang.AnisoE6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.Open

set_option linter.unusedSectionVars false


theorem closure_top_of_commute {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (e : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) (he1 : e ≠ 1)
    (hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      ∀ d : K, Commute (baseChangeGL (algebraMap k K) (e : ModGL TwistTag.E6.tag k))
          (xUnit Tag.E6 K i d) ∧
        Commute (baseChangeGL (algebraMap k K) (e : ModGL TwistTag.E6.tag k)) (yUnit Tag.E6 K i d)) :
    Subgroup.closure (((phiG σ hfix).range : Set (twistedE6RootGroup K σ)) ∪
      (Subgroup.centralizer ({phiG σ hfix e} : Set (twistedE6RootGroup K σ)) :
        Set (twistedE6RootGroup K σ))) = ⊤ := by
  classical
  set ι := phiG σ hfix with hιdef
  set eG : twistedE6RootGroup K σ := ι e with heGdef
  set H : Subgroup (twistedE6RootGroup K σ) := Subgroup.closure (((ι.range : Set (twistedE6RootGroup K σ))) ∪
      (Subgroup.centralizer ({eG} : Set (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) with hHdef
  have hιH : ∀ x, ι x ∈ H := fun x => Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
  have hcH : ∀ (y : twistedE6RootGroup K σ),
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) → y ∈ H := by
    intro y hy
    apply Subgroup.subset_closure
    right
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hy.eq
  have hXG : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
    fun a c => graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
  have hYG : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ twistedE6RootGroup K σ :=
    fun a c => graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (⟨orbitX TwistTag.E6 K σ.toRingHom a c, hXG a c⟩ : twistedE6RootGroup K σ) ∈ H ∧
      (⟨orbitY TwistTag.E6 K σ.toRingHom a c, hYG a c⟩ : twistedE6RootGroup K σ) ∈ H := by
    intro a c
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨0, ha⟩ (Or.inl rfl) c
      exact ⟨hcH _ h.1.symm, hcH _ h.2.symm⟩
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨1, ha⟩ (Or.inr rfl) c
      exact ⟨hcH _ h.1.symm, hcH _ h.2.symm⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      have hX : (⟨orbitX TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c, hXG _ c⟩ : twistedE6RootGroup K σ) =
          ι ⟨(xUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k), hxm.1⟩ := by
        apply Subtype.ext
        change (orbitX TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_xUnit, hc']
        exact coe_orbitX_two σ.toRingHom c
      have hY : (⟨orbitY TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c, hYG _ c⟩ : twistedE6RootGroup K σ) =
          ι ⟨(yUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k), hxm.2⟩ := by
        apply Subtype.ext
        change (orbitY TwistTag.E6 K σ.toRingHom ⟨2, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_yUnit, hc']
        exact coe_orbitY_two σ.toRingHom c
      exact ⟨by rw [hX]; exact hιH _, by rw [hY]; exact hιH _⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      have hX : (⟨orbitX TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c, hXG _ c⟩ : twistedE6RootGroup K σ) =
          ι ⟨(xUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k), hxm.1⟩ := by
        apply Subtype.ext
        change (orbitX TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_xUnit, hc']
        exact coe_orbitX_three σ.toRingHom c
      have hY : (⟨orbitY TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c, hYG _ c⟩ : twistedE6RootGroup K σ) =
          ι ⟨(yUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k), hxm.2⟩ := by
        apply Subtype.ext
        change (orbitY TwistTag.E6 K σ.toRingHom ⟨3, ha⟩ c : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c' : ModGL TwistTag.E6.tag k)
        rw [baseChangeGL_yUnit, hc']
        exact coe_orbitY_three σ.toRingHom c
      exact ⟨by rw [hX]; exact hιH _, by rw [hY]; exact hιH _⟩
  have hG : twistedE6RootGroup K σ ≤ H.map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, (hmemX a c).1, rfl⟩
    · exact ⟨_, (hmemX a c).2, rfl⟩
  have hmain : H = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  exact hmain

end CFSG.LieType.SeitzGeneration.ExcHighThree
