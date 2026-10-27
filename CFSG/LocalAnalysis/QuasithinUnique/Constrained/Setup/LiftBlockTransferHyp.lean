module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftXEmbed

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Family

section Hyp

variable {G : Type} [Group G]

theorem autOn_top_subgroupOf {X V : Subgroup G} (hVX : V ≤ X)
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (⊤ : Subgroup ↥X) (V.subgroupOf X) = (autOn X V).map (autEmbed hVX).toMonoidHom := by
  have := autOn_subgroupOf hVX hX (le_refl X)
  rwa [Subgroup.subgroupOf_self] at this

theorem thompsonJ_subgroupOf {X R : Subgroup G} (hRX : R ≤ X) :
    thompsonJ (R.subgroupOf X) = (thompsonJ R).subgroupOf X := by
  have h1 : (thompsonJ (R.subgroupOf X)).map X.subtype = thompsonJ R := by
    rw [← thompsonJ_map_of_injective' X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  rw [← h1]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm

theorem oddOrderSubgroup_top_eq_subgroupOf (X : Subgroup G) :
    oddOrderSubgroup (⊤ : Subgroup ↥X) = (oddOrderSubgroup X).subgroupOf X := by
  rw [← map_oddOrderSubgroup_top X]
  exact (Subgroup.comap_map_eq_self_of_injective X.subtype_injective _).symm

theorem autOn_le_top_iff {X R V : Subgroup G} (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hRX : R ≤ X) :
    autOn (thompsonJ (R.subgroupOf X)) (V.subgroupOf X) ≤
        autOn (oddOrderSubgroup (⊤ : Subgroup ↥X)) (V.subgroupOf X) ↔
      autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V := by
  rw [thompsonJ_subgroupOf hRX, oddOrderSubgroup_top_eq_subgroupOf,
    autOn_subgroupOf hVX hX ((B6.thompsonJ_le R).trans hRX),
    autOn_subgroupOf hVX hX (oddOrderSubgroup_le X),
    Subgroup.map_le_map_iff_of_injective (autEmbed hVX).injective]

theorem charTwo_top {X : Subgroup G} (h : CharTwo X) : CharTwo (⊤ : Subgroup ↥X) := by
  intro x hx
  have hmap : (pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype = pCoreOf 2 X := by
    rw [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_map_subtype 2 X ⊤, map_top_subtype]
  have hx1 : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
    rw [← hmap]
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx.2 y hy)
  have hx2 : (x : G) ∈ pCoreOf 2 X := h ⟨x.2, hx1⟩
  rw [← hmap] at hx2
  obtain ⟨y, hy, hyx⟩ := hx2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {H : Subgroup A}
    (h : H.Characteristic) : (H.map e.toMonoidHom).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.2 fun φ => ?_
  have h1 := Subgroup.characteristic_iff_map_eq.1 h ((e.trans φ).trans e.symm)
  calc (H.map e.toMonoidHom).map φ.toMonoidHom =
        (H.map ((e.trans φ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
        ext x
        simp
    _ = H.map e.toMonoidHom := by rw [h1]

theorem noChar_top {X R : Subgroup G} (hRX : R ≤ X)
    (h : ∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ X ≤ Subgroup.normalizer (Rc : Set G)) :
    ∀ Rc : Subgroup ↥X, Rc ≠ ⊥ → Rc ≤ baum (R.subgroupOf X) →
      (Rc.subgroupOf (baum (R.subgroupOf X))).Characteristic →
      ¬ (⊤ : Subgroup ↥X) ≤ Subgroup.normalizer (Rc : Set ↥X) := by
  intro Rc hne hle hchar htop
  have hS : (baum (R.subgroupOf X)).map X.subtype = baum R := by
    rw [← baum_map_of_injective X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  set S' := baum (R.subgroupOf X) with hS'
  let f : ↥S' ≃* ↥(baum R) :=
    (S'.equivMapOfInjective X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  have hf : ∀ z : ↥S', (f z : G) = ((z : ↥X) : G) := fun z => rfl
  have hRc : Rc.map X.subtype ≤ baum R := hS ▸ Subgroup.map_mono hle
  have hsub : (Rc.map X.subtype).subgroupOf (baum R) = (Rc.subgroupOf S').map f.toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.1 hy
      refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
      show f.symm y ∈ Rc.subgroupOf S'
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((f.symm y : ↥S') : ↥X) = x := by
        apply X.subtype_injective
        show (((f.symm y : ↥S') : ↥X) : G) = (x : G)
        rw [← hf, f.apply_symm_apply]
        exact hxy.symm
      show ((f.symm y : ↥S') : ↥X) ∈ Rc
      rw [h1]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨(z : ↥X), Subgroup.mem_subgroupOf.1 hz, (hf z).symm⟩
  refine h (Rc.map X.subtype) ?_ hRc ?_ ?_
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  · rw [hsub]
    exact characteristic_map_equiv f hchar
  · intro x hx
    have hx' : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer (Rc : Set ↥X) := htop (Subgroup.mem_top _)
    exact Subgroup.le_normalizer_map X.subtype ⟨_, hx', rfl⟩

theorem isCompList_map_equiv {A A' : Type} [Group A] [Group A'] (ψ : A ≃* A') {H : Subgroup A}
    {r : ℕ} {L : Fin r → Subgroup A} (h : IsCompList H r L) :
    IsCompList (H.map ψ.toMonoidHom) r (fun i => (L i).map ψ.toMonoidHom) :=
  let h' := isCompListIn_map ψ h
  ⟨h'.injective, fun i => (isComp_iff _ _).2 (h'.isComp i),
    fun D hD => h'.complete D ((isComp_iff _ _).1 hD)⟩

theorem isCompList_top {X V : Subgroup G} (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G))
    {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)} (h : IsCompList (autOn X V) r Lc) :
    IsCompList (autOn (⊤ : Subgroup ↥X) (V.subgroupOf X)) r
      (fun i => (Lc i).map (autEmbed hVX).toMonoidHom) := by
  rw [autOn_top_subgroupOf hVX hX]
  exact isCompList_map_equiv (autEmbed hVX) h

theorem evenSL2Setting_top {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting X R M V n F) :
    EvenSL2Setting (⊤ : Subgroup ↥X) (R.subgroupOf X) (M.subgroupOf X) (V.subgroupOf X) n F := by
  have hred := hS.reduced
  have hVX : V ≤ X := hred.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hRX : R ≤ X := hS.sylow.1
  have hMX : M ≤ X := hS.max.2.1.le
  have hT' : IsSylowTwoOf (R.subgroupOf X) (⊤ : Subgroup ↥X) :=
    ⟨le_top, hS.sylow.2.1.comap_subtype, by
      show ¬ 2 ∣ (R.subgroupOf X).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hS.sylow.2.2⟩
  refine ⟨hS.two_le, hS.card_eq, hT', ?_, ⟨?_, ?_, ?_⟩, isTwoReducedIn_top_subgroupOf hred, ?_, ?_, ?_⟩
  · intro hn
    apply hS.not_normal
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn
    exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 h1)
  · exact fun x hx => hS.max.1 hx
  · refine lt_top_iff_ne_top.2 fun h => ?_
    exact absurd hS.max.2.1 (not_lt_of_ge (Subgroup.subgroupOf_eq_top.1 h))
  · intro Y hRY hY
    have h1 : R ≤ Y.map X.subtype := by
      have := Subgroup.map_mono (f := X.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hRX] at this
    have h2 : Y.map X.subtype < X := by
      have := (Subgroup.map_lt_map_iff_of_injective X.subtype_injective).2 hY
      rwa [map_top_subtype] at this
    intro y hy
    exact hS.max.2.2 _ h1 h2 ⟨y, hy, rfl⟩
  ·
    intro h
    apply hS.thompson_ne
    have h1 : ⁅thompsonJ (R.subgroupOf X), V.subgroupOf X⁆.map X.subtype = ⁅thompsonJ R, V⁆ := by
      rw [Subgroup.map_commutator, thompsonJ_subgroupOf hRX, Subgroup.map_subgroupOf_eq_of_le
        ((B6.thompsonJ_le R).trans hRX), Subgroup.map_subgroupOf_eq_of_le hVX]
    rw [h, Subgroup.map_bot] at h1
    exact h1.symm
  ·
    rw [autOn_top_subgroupOf hVX hX]
    exact not_isSolvable_map (autEmbed hVX) hS.nonsolvable
  ·
    obtain ⟨D, hD, ⟨α⟩⟩ := hS.component
    refine ⟨D.map (autEmbed hVX).toMonoidHom, ?_, ⟨(quotientCenterMap (autEmbed hVX) D).trans α⟩⟩
    rw [autOn_top_subgroupOf hVX hX]
    exact (isComp_iff _ _).2 ((isComponentIn_map_iff (autEmbed hVX)).2 ((isComp_iff _ _).1 hD))

end Hyp

end CFSG.QuasithinUnique.Setup.Lift
