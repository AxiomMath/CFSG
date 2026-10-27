module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2Fixed
public import CFSG.HardMathSupport.Lang.AnisoE6.PlaneConjGen
public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.LieType.SeitzGeneration.ExcTorusF4
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.HardMathSupport.Lang.AnisoE6.ClGen

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.Open
  CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


section Embed

variable {k K : Type} [Field k] [Field K] [Algebra k K] (σ : K ≃+* K)
  (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)

@[expose] def phiG : twistedFixedGroup TwistTag.E6 k (RingHom.id k) →*
    twistedE6RootGroup K σ :=
  ((baseChangeGL (algebraMap k K)).comp (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).subtype).codRestrict
    _ fun g => map_baseChangeGL_le_graphFixedRootGroup (σ := σ.toRingHom) hfix ⟨g, g.2, rfl⟩

theorem coe_phiG (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) :
    ((phiG σ hfix g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K) g := rfl

theorem phiG_injective : Function.Injective (phiG σ hfix) := fun g g' h => by
  have h' := congrArg (fun x : twistedE6RootGroup K σ => (x : ModGL TwistTag.E6.tag K)) h
  exact Subtype.ext (baseChangeGL_injective (algebraMap k K) h')

end Embed

section Orbits

variable {K : Type} [Field K] (σ : K →+* K)

theorem orbit_short_mem (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩) (i : Fin TwistTag.E6.tag.rank)
    (hi : i ∈ TwistTag.E6.orbit a) :
    i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5 := by
  rcases ha with rfl | rfl
  · have e : TwistTag.E6.orbit ⟨0, by decide⟩ = ({0, 5} : Finset (Fin 6)) := rfl
    rw [e] at hi
    rcases Finset.mem_insert.1 hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.1 h)))
  · have e : TwistTag.E6.orbit ⟨1, by decide⟩ = ({2, 4} : Finset (Fin 6)) := rfl
    rw [e] at hi
    rcases Finset.mem_insert.1 hi with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_singleton.1 h)))

theorem commute_orbitXY_short {e : ModGL Tag.E6 K}
    (hecomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      ∀ d : K, Commute e (xUnit Tag.E6 K i d) ∧ Commute e (yUnit Tag.E6 K i d))
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩)
    (c : orbitField TwistTag.E6 K σ a) :
    Commute e (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) ∧
    Commute e (orbitY TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K) := by
  have hmem : ∀ k : ℕ, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a) ∈ TwistTag.E6.orbit a := by
    intro k
    exact TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k
  constructor
  · rw [coe_orbitX]
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact (hecomm _ (orbit_short_mem a ha _ (hmem k)) _).1
  · rw [coe_orbitY]
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact (hecomm _ (orbit_short_mem a ha _ (hmem k)) _).2

theorem card_orbit_two : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := rfl

theorem orbitMin_two : TwistTag.E6.orbitMin ⟨2, by decide⟩ = e6Index 3 := by
  have h : TwistTag.E6.orbitMin ⟨2, by decide⟩ = (⟨3, by decide⟩ : Fin TwistTag.E6.tag.rank) := by
    decide +kernel
  exact h

theorem card_orbit_three : (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 := rfl

theorem orbitMin_three : TwistTag.E6.orbitMin ⟨3, by decide⟩ = e6Index 1 := by
  have h : TwistTag.E6.orbitMin ⟨3, by decide⟩ = (⟨1, by decide⟩ : Fin TwistTag.E6.tag.rank) := by
    decide +kernel
  exact h

theorem coe_orbitX_two (c : orbitField TwistTag.E6 K σ ⟨2, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨2, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K (e6Index 3) c := by
  rw [coe_orbitX, card_orbit_two, orbitMin_two]
  simp <;> rfl

theorem coe_orbitY_two (c : orbitField TwistTag.E6 K σ ⟨2, by decide⟩) :
    (orbitY TwistTag.E6 K σ ⟨2, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      yUnit Tag.E6 K (e6Index 3) c := by
  rw [coe_orbitY, card_orbit_two, orbitMin_two]
  simp <;> rfl

theorem coe_orbitX_three (c : orbitField TwistTag.E6 K σ ⟨3, by decide⟩) :
    (orbitX TwistTag.E6 K σ ⟨3, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K (e6Index 1) c := by
  rw [coe_orbitX, card_orbit_three, orbitMin_three]
  simp <;> rfl

theorem coe_orbitY_three (c : orbitField TwistTag.E6 K σ ⟨3, by decide⟩) :
    (orbitY TwistTag.E6 K σ ⟨3, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      yUnit Tag.E6 K (e6Index 1) c := by
  rw [coe_orbitY, card_orbit_three, orbitMin_three]
  simp <;> rfl

end Orbits

theorem dvd_sq_add_add_one_of_orderOf_eq_three {p q : ℕ} (hp : p.Prime)
    (hord : orderOf (q : ZMod p) = 3) : p ∣ q ^ 2 + q + 1 := by
  haveI := Fact.mk hp
  have h3 : (q : ZMod p) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have h1 : (q : ZMod p) - 1 ≠ 0 := by
    intro h
    have : (q : ZMod p) = 1 := sub_eq_zero.1 h
    rw [this, orderOf_one] at hord
    omega
  have hm : ((q : ZMod p) - 1) * ((q : ZMod p) ^ 2 + q + 1) = 0 := by linear_combination h3
  have hz : (q : ZMod p) ^ 2 + q + 1 = 0 := (mul_eq_zero.1 hm).resolve_left h1
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) p).1 (by push_cast; exact hz)

@[expose] def F4Closing (k : Type) [Field k] (p ℓ : ℕ) : Prop :=
  ∀ E : Subgroup (twistedFixedGroup TwistTag.E6 k (RingHom.id k)), CFSG.Open.IsElemAbelian p E →
    Nat.card E = p ^ 2 → ¬ NormRSub ℓ E → cl E = ⊤

section Main

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] (σ : K ≃+* K)

theorem closure_centralizers_twistedE6_phi3 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card k = ℓ ^ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 3)
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
  have hp' : p ∣ Nat.card k ^ 2 + Nat.card k + 1 := by
    rw [hk]
    exact dvd_sq_add_add_one_of_orderOf_eq_three hp he
  have hTG : SylowTorus (twistedE6RootGroup K σ) p 2 :=
    sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_three k hp (by omega) hp').of_mulEquiv (e6FixedF4EquivAll k).symm
  have hinj := phiG_injective σ hfix
  obtain ⟨e, ⟨γ, hγ, rfl⟩, heord, hecomm⟩ := exists_e1 (K := K) (algebraMap k K) hp'
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
  have hcomm : ∀ i, (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) →
      ∀ d : K, Commute (eG : ModGL TwistTag.E6.tag K) (xUnit Tag.E6 K i d) ∧
        Commute (eG : ModGL TwistTag.E6.tag K) (yUnit Tag.E6 K i d) :=
    hecomm
  have hgen : ∀ y : twistedE6RootGroup K σ,
      Commute (y : ModGL TwistTag.E6.tag K) (eG : ModGL TwistTag.E6.tag K) → y ∈ cl EH :=
    fun y hy => mem_cl_of_commute heG heG1 (Subtype.ext hy.eq)
  have hsub : ∀ x : twistedE6RootGroup K σ, x ∈ cl EH →
      (x : ModGL TwistTag.E6.tag K) ∈ (cl EH).map (twistedE6RootGroup K σ).subtype :=
    fun x hx => ⟨x, hx, rfl⟩
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
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨0, ha⟩ (Or.inl rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm), hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm)⟩
    · have h := commute_orbitXY_short σ.toRingHom (e := (eG : ModGL TwistTag.E6.tag K)) hcomm
        ⟨1, ha⟩ (Or.inr rfl) c
      exact ⟨hsub ⟨_, hXG⟩ (hgen ⟨_, hXG⟩ h.1.symm), hsub ⟨_, hYG⟩ (hgen ⟨_, hYG⟩ h.2.symm)⟩
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

end Main

end CFSG.HardMathSupport.Lang.AnisoE6
