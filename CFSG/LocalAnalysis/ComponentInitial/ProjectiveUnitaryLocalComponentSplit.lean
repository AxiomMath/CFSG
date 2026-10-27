module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCentralizerTwo
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitarySummand

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

@[expose] def summandUnitarySet (B : V →ₛₗ[h.bar] V →ₗ[E] E) (A W : Submodule E V) :
    Set (sesqUnitaryGroup B) :=
  {g | (∀ w ∈ W, unitaryOp g w = w) ∧ ∃ hA : ∀ a ∈ A, unitaryOp g a ∈ A,
    LinearMap.det ((unitaryOp g).restrict hA) = 1}

section Orth

variable (hB : B.IsSymm) {A W : Submodule E V} (hc : IsCompl A W)
  (horth : ∀ a ∈ A, ∀ w ∈ W, B a w = 0)

include hB horth in
theorem sesqOrthSum_eq (x y : A × W) :
    sesqOrthSum (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W) x y =
      B (Submodule.prodEquivOfIsCompl A W hc x) (Submodule.prodEquivOfIsCompl A W hc y) := by
  have h1 : B (x.2 : V) (y.1 : V) = 0 := by
    rw [← hB.eq (y.1 : V) (x.2 : V), horth _ y.1.2 _ x.2.2, map_zero]
  rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', sesqOrthSum_apply,
    LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict₁₂_apply]
  simp only [map_add, LinearMap.add_apply, horth _ x.1.2 _ y.2.2, h1]
  ring

include hB horth in
theorem glConj_mem_sesqUnitaryGroup {g : LinearMap.GeneralLinearGroup E V}
    (hg : g ∈ sesqUnitaryGroup B) :
    glConj (Submodule.prodEquivOfIsCompl A W hc) g ∈
      sesqUnitaryGroup (sesqOrthSum (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W)) := by
  intro x y
  rw [sesqOrthSum_eq hB hc horth, sesqOrthSum_eq hB hc horth, glConj_apply, glConj_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hg]

include hB horth in
theorem glConj_symm_summandGL_mem {gA : LinearMap.GeneralLinearGroup E A}
    (hgA : gA ∈ sesqSpecialUnitaryGroup (B.domRestrict₁₂ A A)) :
    ∃ hb : glConj (Submodule.prodEquivOfIsCompl A W hc).symm (summandGL E A W gA) ∈
        sesqUnitaryGroup B,
      (⟨_, hb⟩ : sesqUnitaryGroup B) ∈ summandUnitarySet B A W := by
  set Ψ := Submodule.prodEquivOfIsCompl A W hc with hΨ
  have happ : ∀ v, ((glConj Ψ.symm (summandGL E A W gA) : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) v = Ψ ((summandGL E A W gA : A × W →ₗ[E] A × W) (Ψ.symm v)) := fun v => by
    rw [glConj_apply, LinearEquiv.symm_symm]
  have hU := summandSpecialUnitary_le (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W)
    ⟨gA, hgA, rfl⟩
  have hb : glConj Ψ.symm (summandGL E A W gA) ∈ sesqUnitaryGroup B := by
    intro x y
    rw [happ, happ, ← sesqOrthSum_eq hB hc horth, hU, sesqOrthSum_eq hB hc horth,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hW : ∀ w ∈ W, unitaryOp (⟨_, hb⟩ : sesqUnitaryGroup B) w = w := fun w hw => by
    change ((glConj Ψ.symm (summandGL E A W gA) : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) w = w
    rw [happ, show Ψ.symm w = (0, ⟨w, hw⟩) from
      Submodule.prodEquivOfIsCompl_symm_apply_right A W hc ⟨w, hw⟩, summandGL_apply, map_zero,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]
  have hAapp : ∀ a (ha : a ∈ A), unitaryOp (⟨_, hb⟩ : sesqUnitaryGroup B) a =
      (((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) ⟨a, ha⟩ : V) := fun a ha => by
    change ((glConj Ψ.symm (summandGL E A W gA) : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) a = _
    rw [happ, show Ψ.symm a = (⟨a, ha⟩, 0) from
      Submodule.prodEquivOfIsCompl_symm_apply_left A W hc ⟨a, ha⟩, summandGL_apply,
      Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]
  have hA : ∀ a ∈ A, unitaryOp (⟨_, hb⟩ : sesqUnitaryGroup B) a ∈ A := fun a ha => by
    rw [hAapp a ha]
    exact Submodule.coe_mem _
  refine ⟨hb, hW, hA, ?_⟩
  have heq : (unitaryOp (⟨_, hb⟩ : sesqUnitaryGroup B)).restrict hA =
      ((gA : LinearMap.GeneralLinearGroup E A) : Module.End E A) :=
    LinearMap.ext fun a => Subtype.ext (by rw [LinearMap.restrict_apply]; exact hAapp a a.2)
  rw [heq]
  exact (mem_sesqSpecialUnitaryGroup.mp hgA).2

include hB hc horth in
theorem fix_of_le_centralizer_summand (hp : p ≠ 2) [FiniteDimensional E V]
    (hsepA : (B.domRestrict₁₂ A A).SeparatingLeft)
    (hsepW : (B.domRestrict₁₂ W W).SeparatingLeft) (hm : 2 ≤ finrank E A)
    {S : Subgroup (sesqUnitaryGroup B)} (hS : summandUnitarySet B A W ⊆ S)
    {R : Subgroup (sesqUnitaryGroup B)} (hR : R ≤ Subgroup.centralizer (S : Set _))
    (hRp : ⁅R, R⁆ = R) :
    ∀ g ∈ R, ∀ a ∈ A, unitaryOp g a = a := by
  set Ψ := Submodule.prodEquivOfIsCompl A W hc with hΨ
  have hAs : (B.domRestrict₁₂ A A).IsSymm := ⟨fun x y => hB.eq x y⟩
  have hWs : (B.domRestrict₁₂ W W).IsSymm := ⟨fun x y => hB.eq x y⟩
  set R' := (R.map (sesqUnitaryGroup B).subtype).map (glConj Ψ) with hR'
  have hR'U : R' ≤ Subgroup.centralizer (summandSpecialUnitary (B.domRestrict₁₂ A A) W :
      Set (LinearMap.GeneralLinearGroup E (A × W))) ⊓
        sesqUnitaryGroup (sesqOrthSum (B.domRestrict₁₂ A A) (B.domRestrict₁₂ W W)) := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, glConj_mem_sesqUnitaryGroup hB hc horth r.2⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨gA, hgA, rfl⟩
    obtain ⟨hb, hbS⟩ := glConj_symm_summandGL_mem hB hc horth hgA
    have h1 := Subgroup.mem_centralizer_iff.mp (hR hr) _ (hS hbS)
    have h2 := congrArg (fun x : sesqUnitaryGroup B =>
      glConj Ψ ((x : LinearMap.GeneralLinearGroup E V))) h1
    simp only [Subgroup.coe_mul, map_mul] at h2
    have h3 : glConj Ψ (glConj Ψ.symm (summandGL E A W gA)) = summandGL E A W gA :=
      Units.ext (LinearMap.ext fun x => by
        rw [glConj_apply, glConj_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply,
          LinearEquiv.symm_apply_apply])
    rw [h3] at h2
    exact h2
  have hR'p : Group.IsPerfect R' :=
    Subgroup.isPerfect_iff.mpr (by rw [hR', ← Subgroup.map_commutator, ← Subgroup.map_commutator,
      hRp])
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hfix := (natural_odd_special_unitary_summand_centralizer h hodd (B.domRestrict₁₂ A A) hAs
    (CatalogueBUnitaryB.nondegenerate_of_isSymm hAs hsepA) (B.domRestrict₁₂ W W) hWs
    (CatalogueBUnitaryB.nondegenerate_of_isSymm hWs hsepW) hm).2.2.2 R' hR'U hR'p
  intro g hg a ha
  have h1 := hfix _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ ⟨a, ha⟩
  rw [glConj_apply] at h1
  have h2 := congrArg Ψ h1
  rw [LinearEquiv.apply_symm_apply, Submodule.coe_prodEquivOfIsCompl'] at h2
  simpa using h2

end Orth

theorem split_case (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {T : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0)
    (hAA : unitaryOp T * unitaryOp T = (l ^ 2) • 1) (hN : h.norm l = 1)
    (hP : eigenPlus l (unitaryOp T) ≠ ⊥)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    (hfix : ∀ x ∈ L, ∀ w ∈ eigenMinus l (unitaryOp T),
      unitaryOp (x : sesqUnitaryGroup B) w = w) :
    2 ≤ finrank E (eigenPlus l (unitaryOp T)) ∧
      ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
        Set (sesqUnitaryGroup B)) =
        summandUnitarySet B (eigenPlus l (unitaryOp T)) (eigenMinus l (unitaryOp T)) ∧
      ∀ R : Subgroup (sesqUnitaryGroup B),
        R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
          Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)) →
        ⁅R, R⁆ = R → ∀ g ∈ R, ∀ a ∈ eigenPlus l (unitaryOp T), unitaryOp g a = a := by
  have := h.finite
  obtain ⟨horth, hsepP, hsepM, e, he⟩ := exists_split_centralizer_equiv hp hB hBl hl0 hAA hN
  have h2 := two_ne_zero_of_odd h hp
  have hc : IsCompl (eigenPlus l (unitaryOp T)) (eigenMinus l (unitaryOp T)) :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have heA : ∀ (g : Subgroup.centralizer {T}) (a : eigenPlus l (unitaryOp T)),
      ((((e g).1 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
        Module.End E (eigenPlus l (unitaryOp T))) a : V) =
        unitaryOp (g : sesqUnitaryGroup B) a := fun g a =>
    LinearMap.congr_fun (he g).1 a
  have heW : ∀ (g : Subgroup.centralizer {T}) (w : eigenMinus l (unitaryOp T)),
      ((((e g).2 : LinearMap.GeneralLinearGroup E (eigenMinus l (unitaryOp T))) :
        Module.End E (eigenMinus l (unitaryOp T))) w : V) =
        unitaryOp (g : sesqUnitaryGroup B) w := fun g w =>
    LinearMap.congr_fun (he g).2 w
  have hsnd : ∀ x : Subgroup.centralizer {T}, (∀ w ∈ eigenMinus l (unitaryOp T),
      unitaryOp (x : sesqUnitaryGroup B) w = w) → (e x).2 = 1 := fun x hx =>
    Subtype.ext (Units.ext (LinearMap.ext fun w => Subtype.ext (by
      rw [heW]
      exact hx w w.2)))
  set ρ := (MonoidHom.fst _ _).comp e.toMonoidHom with hρ
  have hρs : Function.Surjective ρ := fun y => ⟨e.symm (y, 1), by simp [hρ]⟩
  have hρinj : ∀ x ∈ L, ∀ y ∈ L, ρ x = ρ y → x = y := fun x hx y hy hxy =>
    e.injective (Prod.ext hxy (by rw [hsnd x (hfix x hx), hsnd y (hfix y hy)]))
  have hL₁ : CFSG.IsComponent (L.map ρ) := by
    refine ⟨?_, hL.2.map hρs⟩
    have hbij : Function.Bijective (ρ.subgroupMap L) := by
      refine ⟨fun x y hxy => Subtype.ext (hρinj x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
      exact ρ.subgroupMap_surjective L
    exact (isQuasisimple_congr (MulEquiv.ofBijective (ρ.subgroupMap L) hbij)).1 hL.1
  have hA1 : 1 ≤ finrank E (eigenPlus l (unitaryOp T)) :=
    Nat.one_le_iff_ne_zero.mpr fun h0 => hP (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨hm, -, hL₁eq⟩ := eq_unitarySpecial_of_isComponent h hp hA1
    (C := B.domRestrict₁₂ (eigenPlus l (unitaryOp T)) (eigenPlus l (unitaryOp T)))
    ⟨fun x y => hB.eq x y⟩ hsepP hL₁
  have hdetρ : ∀ (x : Subgroup.centralizer {T})
      (hA : ∀ a ∈ eigenPlus l (unitaryOp T), unitaryOp (x : sesqUnitaryGroup B) a ∈
        eigenPlus l (unitaryOp T)),
      LinearMap.det ((unitaryOp (x : sesqUnitaryGroup B)).restrict hA) =
        LinearMap.det (((ρ x : sesqUnitaryGroup _) : LinearMap.GeneralLinearGroup E
          (eigenPlus l (unitaryOp T))) : Module.End E (eigenPlus l (unitaryOp T))) := by
    intro x hA
    congr 1
    exact LinearMap.ext fun a => Subtype.ext (by
      rw [LinearMap.restrict_apply]
      exact (heA x a).symm)
  have hset : ((L.map (Subgroup.centralizer {T}).subtype : Subgroup (sesqUnitaryGroup B)) :
      Set (sesqUnitaryGroup B)) =
        summandUnitarySet B (eigenPlus l (unitaryOp T)) (eigenMinus l (unitaryOp T)) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hA : ∀ a ∈ eigenPlus l (unitaryOp T), unitaryOp (x : sesqUnitaryGroup B) a ∈
          eigenPlus l (unitaryOp T) := fun a ha =>
        mapsTo_ker_sub_one_of_mem_centralizer l x.2 ha
      refine ⟨hfix x hx, hA, ?_⟩
      have hρx : ρ x ∈ unitarySpecial _ := hL₁eq ▸ Subgroup.mem_map_of_mem ρ hx
      exact (hdetρ x hA).trans (mem_unitarySpecial.mp hρx)
    · rintro ⟨hgW, hgA, hdet⟩
      have hgT : g ∈ Subgroup.centralizer {T} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine Subtype.ext (Units.ext ?_)
        change unitaryOp g * unitaryOp T = unitaryOp T * unitaryOp g
        refine commute_of_mapsTo_eigen h2 hl0 hAA (fun v hv => hgA v hv) (fun v hv => ?_)
        change unitaryOp g v ∈ eigenMinus l (unitaryOp T)
        rw [hgW v hv]
        exact hv
      set x : Subgroup.centralizer {T} := ⟨g, hgT⟩ with hx
      have hρx : ρ x ∈ L.map ρ := by
        rw [hL₁eq, mem_unitarySpecial, ← hdetρ x hgA]
        exact hdet
      obtain ⟨y, hy, hyx⟩ := hρx
      have hyx' : y = x := e.injective (Prod.ext hyx (by rw [hsnd y (hfix y hy), hsnd x hgW]))
      exact ⟨y, hy, by rw [hyx']; rfl⟩
  refine ⟨hm, hset, fun R hR hRp => ?_⟩
  exact fix_of_le_centralizer_summand hB hc horth hp hsepP hsepM hm (by rw [← hset]) hR hRp

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
