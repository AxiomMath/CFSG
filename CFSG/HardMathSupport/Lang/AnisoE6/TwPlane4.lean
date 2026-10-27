module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
public import CFSG.HardMathSupport.Lang.AnisoE6.Phi4Aux
public import CFSG.HardMathSupport.Lang.AnisoE6.FourA3Fixed
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcRankVacuous
public import CFSG.HardMathSupport.Lang.AnisoE6.ConjRoot

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.Open
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


section Orbits4

variable {K : Type} [Field K] (σ : K →+* K)

theorem orbit_zero_mem (i : Fin TwistTag.E6.tag.rank) (hi : i ∈ TwistTag.E6.orbit ⟨0, by decide⟩) :
    i = e6Index 0 ∨ i = e6Index 5 := by
  have e : TwistTag.E6.orbit ⟨0, by decide⟩ = ({0, 5} : Finset (Fin 6)) := rfl
  rw [e] at hi
  rcases Finset.mem_insert.1 hi with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.1 h)

theorem orbit_one_mem (i : Fin TwistTag.E6.tag.rank) (hi : i ∈ TwistTag.E6.orbit ⟨1, by decide⟩) :
    i = e6Index 2 ∨ i = e6Index 4 := by
  have e : TwistTag.E6.orbit ⟨1, by decide⟩ = ({2, 4} : Finset (Fin 6)) := rfl
  rw [e] at hi
  rcases Finset.mem_insert.1 hi with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.1 h)

theorem commute_orbitXY_zero {e : ModGL Tag.E6 K}
    (hecomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 5) →
      ∀ d : K, Commute e (xUnit Tag.E6 K i d) ∧ Commute e (yUnit Tag.E6 K i d))
    (c : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) :
    Commute e (orbitX TwistTag.E6 K σ ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) ∧
    Commute e (orbitY TwistTag.E6 K σ ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) := by
  have hmem : ∀ k : ℕ, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin ⟨0, by decide⟩) ∈
      TwistTag.E6.orbit ⟨0, by decide⟩ := fun k =>
    TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem _) k
  constructor
  · rw [coe_orbitX]
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact (hecomm _ (orbit_zero_mem _ (hmem k)) _).1
  · rw [coe_orbitY]
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact (hecomm _ (orbit_zero_mem _ (hmem k)) _).2

theorem orbitXY_one_mem_rootSpan (c : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨1, by decide⟩ c : ModGL TwistTag.E6.tag K) ∈
      rootSpan Tag.E6 K S₂ ∧
    (orbitY TwistTag.E6 K σ ⟨1, by decide⟩ c : ModGL TwistTag.E6.tag K) ∈
      rootSpan Tag.E6 K S₂ := by
  have hmem : ∀ k : ℕ, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin ⟨1, by decide⟩) ∈
      TwistTag.E6.orbit ⟨1, by decide⟩ := fun k =>
    TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem _) k
  constructor
  · rw [coe_orbitX]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [← pinnedX_single]
    rcases orbit_one_mem _ (hmem k) with h | h
    · rw [h]
      exact pinnedX_mem_rootSpan (Or.inl rfl) _
    · rw [h]
      exact pinnedX_mem_rootSpan (Or.inr (Or.inr (Or.inl rfl))) _
  · rw [coe_orbitY]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    rw [← pinnedX_neg_single]
    rcases orbit_one_mem _ (hmem k) with h | h
    · rw [h]
      exact pinnedX_mem_rootSpan (Or.inr (Or.inl rfl)) _
    · rw [h]
      exact pinnedX_mem_rootSpan (Or.inr (Or.inr (Or.inr rfl))) _

end Orbits4

section Main4

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] (σ : K ≃+* K)

theorem closure_centralizers_twistedE6_phi4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 4)
    (hF4 : F4Closing k p ℓ)
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : IsElemAbelian p E₀)
    (hE₀c : Nat.card E₀ = p ^ 2) (hR : ¬ NormRSub ℓ E₀) :
    cl E₀ = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := by
    intro c
    rw [hσ, ← hk, ← map_pow]
    congr 1
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hp' : p ∣ Nat.card k ^ 2 + 1 := by
    rw [hk]
    exact dvd_sq_add_one_of_orderOf_eq_four hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_four k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e4 (K := K) (algebraMap k K) hp'
  set γΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨γ, hγ⟩ with hγΓ
  have hordγ : orderOf γΓ = p := by
    rw [← Subgroup.orderOf_coe, show (γΓ : ModGL TwistTag.E6.tag k) = γ from rfl,
      ← orderOf_injective (baseChangeGL (algebraMap k K)) (baseChangeGL_injective _) γ]
    exact heord
  obtain ⟨EΓ, hEΓ, hEΓc, hγE⟩ := exists_plane_containing_of_sylowTorus hTΓ hordγ
  set ι := phiG σ hfix with hιdef
  set EH : Subgroup (twistedE6RootGroup K σ) := EΓ.map ι with hEHdef
  have hEH : IsElemAbelian p EH :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEΓ ι
  have hEHc : Nat.card EH = p ^ 2 := by
    rw [hEHdef, Subgroup.card_map_of_injective hinj, hEΓc]
  obtain ⟨g, hg⟩ := exists_conj_eq_of_sylowTorus hTG hE₀ hE₀c hEH hEHc
  have hNE : ¬ NormRSub ℓ EH := fun h => hR (normRSub_of_map_conj g (by rw [hg]; exact h))
  have hNΓ : ¬ NormRSub ℓ EΓ := fun h => hNE (normRSub_map ι hinj h)
  have hclΓ : cl EΓ = ⊤ := hF4 EΓ hEΓ hEΓc hNΓ
  have hH : ∀ x, ι x ∈ cl EH := fun x =>
    cl_map_le ι hinj EΓ ⟨x, by rw [hclΓ]; exact Subgroup.mem_top x, rfl⟩
  set eG : twistedE6RootGroup K σ := ι γΓ with heGdef
  have heG : eG ∈ EH := ⟨γΓ, hγE, rfl⟩
  have heG1 : eG ≠ 1 := by
    intro h
    have h1 : orderOf eG = p := by
      rw [heGdef, orderOf_injective ι hinj γΓ, hordγ]
    rw [h, orderOf_one] at h1
    exact hp.one_lt.ne h1
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) → y ∈ cl EH :=
    fun y hy => mem_cl_of_commute heG heG1 (Subtype.ext hy.eq)
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ cl EH →
      (x : ModGL TwistTag.E6.tag K) ∈ (cl EH).map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
  have hnΓ : nElt TwistTag.E6.tag k ωwWord ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k) :=
    nElt_flatten_mem k ωwFold
  set nΓ : twistedFixedGroup TwistTag.E6 k (RingHom.id k) := ⟨_, hnΓ⟩ with hnΓdef
  set nG : twistedE6RootGroup K σ := ι nΓ with hnGdef
  have hnG : (nG : ModGL TwistTag.E6.tag K) = nElt TwistTag.E6.tag K ωwWord :=
    baseChangeGL_nElt (algebraMap k K) Tag.E6 ωwWord
  have hmemX : ∀ (a : Fin TwistTag.E6.foldedTag.rank)
      (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        (cl EH).map (twistedE6RootGroup K σ).subtype ∧
      (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        (cl EH).map (twistedE6RootGroup K σ).subtype := by
    intro a c
    have hXG : (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
        (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hYG : (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈
        twistedE6RootGroup K σ :=
      graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
        (orbitY_mem_graphFixedNegUnipotent _ _ _ _)
    obtain ⟨a, ha⟩ := a
    have ha4 : a < 4 := ha
    interval_cases a
    · have h := commute_orbitXY_zero σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm), hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm)⟩
    ·
      obtain ⟨hX1, hY1⟩ := orbitXY_one_mem_rootSpan σ.toRingHom c
      have hcS0 : ∀ γ ∈ S₀, ∀ c : K, Commute (eG : ModGL TwistTag.E6.tag K)
          (pinnedX Tag.E6 K γ c) := by
        intro γ hγ c
        rcases hγ with rfl | rfl | rfl | rfl
        · rw [pinnedX_single]; exact (hcomm _ (Or.inl rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inl rfl) c).2
        · rw [pinnedX_single]; exact (hcomm _ (Or.inr rfl) c).1
        · rw [pinnedX_neg_single]; exact (hcomm _ (Or.inr rfl) c).2
      have hconj : ∀ z : twistedE6RootGroup K σ,
          (z : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₂ → z ∈ cl EH := by
        intro z hz
        set y : twistedE6RootGroup K σ := nG⁻¹ * z * nG with hy
        have hy' : (y : ModGL TwistTag.E6.tag K) ∈ rootSpan Tag.E6 K S₀ := by
          have e : (y : ModGL TwistTag.E6.tag K) =
              (nElt TwistTag.E6.tag K ωwWord)⁻¹ * (z : ModGL TwistTag.E6.tag K) *
                nElt TwistTag.E6.tag K ωwWord := by
            rw [hy]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnG]
          rw [e]
          exact nElt_inv_conj_mem_rootSpan K ωwWord ωw_inv_S₂ hz
        have hyc := commute_of_forall_pinnedX K hcS0 hy'
        have hycl : y ∈ cl EH := hgen y hyc.symm
        have : z = nG * y * nG⁻¹ := by rw [hy]; group
        rw [this]
        exact mul_mem (mul_mem (hH nΓ) hycl) (inv_mem (hH nΓ))
      exact ⟨hsub ⟨_, hXG⟩ (hconj ⟨_, hXG⟩ hX1), hsub ⟨_, hYG⟩ (hconj ⟨_, hYG⟩ hY1)⟩
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_two, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨1, by decide⟩ (e6Index 3) orbitWord_f4_one c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 3) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 3) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_two]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 3) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_two]
    · have hc : σ.toRingHom (c : K) = c := by
        have := mem_orbitField.1 c.2
        rwa [card_orbit_three, pow_one] at this
      have hcc : (c : K) ^ Nat.card k = c := by
        rw [hk, ← hσ]
        exact hc
      obtain ⟨c', hc'⟩ := CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := k) hcc
      have hxm := xyUnit_mem_fixed_of_orbitWord_eq k ⟨0, by decide⟩ (e6Index 1) orbitWord_f4_zero c'
      refine ⟨⟨ι ⟨xUnit Tag.E6 k (e6Index 1) c', hxm.1⟩, hH _, ?_⟩,
        ⟨ι ⟨yUnit Tag.E6 k (e6Index 1) c', hxm.2⟩, hH _, ?_⟩⟩
      · show baseChangeGL (algebraMap k K) (xUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_xUnit, hc', coe_orbitX_three]
      · show baseChangeGL (algebraMap k K) (yUnit Tag.E6 k (e6Index 1) c') = _
        rw [baseChangeGL_yUnit, hc', coe_orbitY_three]
  have hG : twistedE6RootGroup K σ ≤ (cl EH).map (twistedE6RootGroup K σ).subtype := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [(hmemX a c).1, (hmemX a c).2]
  have hmain : cl EH = ⊤ := by
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hG x.2
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  exact cl_eq_top_of_map (MulAut.conj g) E₀ (by rw [hg]; exact hmain)

end Main4

end CFSG.HardMathSupport.Lang.AnisoE6
