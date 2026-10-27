module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.Assembly.Subnormal
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

@[expose] noncomputable def centralQuotAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ center X) where
  toFun α := QuotientGroup.congr (center X) (center X) α (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem centralQuotAut_mk {X : Type*} [Group X] (α : MulAut X) (x : X) :
    centralQuotAut X α (x : X ⧸ center X) = ((α x : X) : X ⧸ center X) := rfl

variable {H : Type} [Group H]

@[expose] noncomputable def quotAction (X : Subgroup H) [X.Normal] {X₀ : Type*} [Group X₀]
    (e : ↥X ⧸ center ↥X ≃* X₀) : H →* MulAut X₀ :=
  (MulAut.congr e).toMonoidHom.comp ((centralQuotAut ↥X).comp MulAut.conjNormal)

theorem quotAction_apply (X : Subgroup H) [hX : X.Normal] {X₀ : Type*} [Group X₀]
    (e : ↥X ⧸ center ↥X ≃* X₀) (h x : H) (hx : x ∈ X) :
    quotAction X e h (e ((⟨x, hx⟩ : ↥X) : ↥X ⧸ center ↥X)) =
      e ((⟨h * x * h⁻¹, hX.conj_mem _ hx h⟩ : ↥X) : ↥X ⧸ center ↥X) := by
  simp [quotAction, MulAut.congr_apply, centralQuotAut_mk]
  rfl

theorem isQuasisimple_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

@[expose] noncomputable def quotCenterCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)

theorem coe_mem_centralizer_of_mem_center {X : Subgroup H} {z : ↥X} (hz : z ∈ center ↥X) :
    (z : H) ∈ centralizer (X : Set H) := by
  rw [mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨w, hw⟩)

theorem inducesInner_of_l34DiagFact {X₀ : Type} [Group X₀] (hX₀ : L34DiagFact X₀) [Finite H]
    {X L R : Subgroup H} [hXn : X.Normal] (hXp : commutator ↥X = ⊤) (e : ↥X ⧸ center ↥X ≃* X₀)
    (hLX : L ≤ X) (hL : CFSG.Open.IsQuasisimple ↥L)
    (hLt : StatedClassicalModel (rankTwoQuot L) .PSL 3 2 2)
    (hRL : R ≤ centralizer (L : Set H)) (hRe : CFSG.Open.IsElemAbelian 2 R)
    (hR4 : 4 ≤ Nat.card R) (hRX : R ⊓ centralizer (X : Set H) = ⊥) {y : H}
    (hyL : y ∈ normalizer (L : Set H)) (hyR : y ∈ centralizer (R : Set H))
    (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) : InducesInner y L := by
  classical
  set φ := quotAction X e with hφdef
  let κ : ↥X →* X₀ := e.toMonoidHom.comp (QuotientGroup.mk' (center ↥X))
  have hκ : ∀ (h : H) (x : ↥X), φ h (κ x) = κ ⟨h * x * h⁻¹, hXn.conj_mem _ x.2 h⟩ :=
    fun h x => quotAction_apply X e h x x.2
  have hκeq : ∀ x x' : ↥X, κ x = κ x' → x⁻¹ * x' ∈ center ↥X := by
    intro x x' h
    have h1 : κ (x⁻¹ * x') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : (QuotientGroup.mk' (center ↥X)) (x⁻¹ * x') = 1 := by
      apply e.injective
      rw [map_one]
      exact h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  set L₁ : Subgroup ↥X := L.subgroupOf X with hL₁
  set L'' : Subgroup X₀ := L₁.map κ with hL''
  have hmem : ∀ s, s ∈ L'' ↔ ∃ x : ↥X, (x : H) ∈ L ∧ κ x = s := by
    intro s
    simp only [hL'', mem_map, hL₁, mem_subgroupOf]
  have hpres : ∀ h ∈ normalizer (L : Set H), ∀ s ∈ L'', φ h s ∈ L'' := by
    intro h hh s hs
    obtain ⟨x, hx, rfl⟩ := (hmem s).1 hs
    rw [hκ]
    exact (hmem _).2 ⟨_, (mem_normalizer_iff.mp hh x).mp hx, rfl⟩
  let hL₁e : ↥L₁ ≃* ↥L := subgroupOfEquivOfLe hLX
  have hL₁ : CFSG.Open.IsQuasisimple ↥L₁ := isQuasisimple_of_equiv hL₁e.symm hL
  have hNA : center ↥X ≤ centralizer (L₁ : Set ↥X) := fun z hz =>
    mem_centralizer_iff.mpr fun l _ => mem_center_iff.mp hz l
  let L₂ : Subgroup (↥X ⧸ center ↥X) := L₁.map (QuotientGroup.mk' (center ↥X))
  let eQ : ↥L₁ ⧸ center ↥L₁ ≃* ↥L₂ ⧸ center ↥L₂ :=
    RankTwoSporadic.quotCenterEquivMap (N := center ↥X) hNA hL₁.1
  have hL₂ : CFSG.Open.IsQuasisimple ↥L₂ := by
    refine ⟨?_, ?_⟩
    · have : Group.IsPerfect ↥L₁ := (Group.isPerfect_def).2 hL₁.1
      exact (Group.isPerfect_def).1 (Group.IsPerfect.ofSurjective
        (f := (QuotientGroup.mk' (center ↥X)).subgroupMap L₁)
        ((QuotientGroup.mk' (center ↥X)).subgroupMap_surjective L₁))
    · have := hL₁.2
      exact eQ.symm.isSimpleGroup
  have hL''eq : L₂.map e.toMonoidHom = L'' := by
    rw [hL'', Subgroup.map_map]
  let eL₂ : ↥L₂ ≃* ↥L'' :=
    (L₂.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hL''eq)
  have hL'' : CFSG.Open.IsQuasisimple ↥L'' := isQuasisimple_of_equiv eL₂ hL₂
  have hL''t : StatedClassicalModel (rankTwoQuot L'') .PSL 3 2 2 :=
    SectionRank.statedClassicalModel_of_mulEquiv
      ((quotCenterCongr eL₂).symm.trans (eQ.symm.trans (quotCenterCongr hL₁e))) hLt
  set U : Subgroup (MulAut X₀) := R.map φ with hU
  have hUfix : ∀ u ∈ U, ∀ s ∈ L'', u s = s := by
    rintro _ ⟨r, hr, rfl⟩ s hs
    obtain ⟨x, hx, rfl⟩ := (hmem s).1 hs
    rw [hκ]
    congr 1
    apply Subtype.ext
    have h := mem_centralizer_iff.mp (hRL hr) x hx
    change r * (x : H) * r⁻¹ = x
    rw [← h, mul_inv_cancel_right]
  have hUe : CFSG.Open.IsElemAbelian 2 U := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, r, hr, rfl⟩ ⟨_, r', hr', rfl⟩
      apply Subtype.ext
      have h := congrArg Subtype.val (hRe.1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)
      simp only [Subgroup.coe_mul] at h
      change φ r * φ r' = φ r' * φ r
      rw [← map_mul, ← map_mul, h]
    · rintro _ ⟨r, hr, rfl⟩
      rw [← map_pow, hRe.2 r hr, map_one]
  have hinj : ∀ r ∈ R, φ r = 1 → r = 1 := by
    intro r hr h1
    have hrX : r ∈ centralizer (X : Set H) := by
      refine RankTwoSporadic.mem_centralizer_of_displacement hXp ?_ fun a ha => ?_
      · rw [normalizer_eq_top_iff.mpr hXn]
        exact mem_top r
      · have h2 : κ ⟨r * a * r⁻¹, hXn.conj_mem _ ha r⟩ = κ ⟨a, ha⟩ := by
          have h3 := hκ r ⟨a, ha⟩
          rw [h1, MulAut.one_apply] at h3
          exact h3.symm
        exact coe_mem_centralizer_of_mem_center (hκeq _ _ h2.symm)
    have hmem' : r ∈ R ⊓ centralizer (X : Set H) := ⟨hr, hrX⟩
    rw [hRX] at hmem'
    exact mem_bot.mp hmem'
  have hU4 : 4 ≤ Nat.card U := by
    have hf : Function.Injective (φ.comp R.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro r hr
      rw [MonoidHom.mem_ker] at hr
      exact (mem_bot).mpr (Subtype.ext (hinj r r.2 hr))
    have hrange : (φ.comp R.subtype).range = U := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact hR4
  have hσL : ∀ s, s ∈ L'' ↔ φ y s ∈ L'' := by
    intro s
    refine ⟨hpres y hyL s, fun h => ?_⟩
    have h2 := hpres y⁻¹ (inv_mem hyL) _ h
    rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
  have hσU : ∀ u ∈ U, φ y * u = u * φ y := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← map_mul, ← map_mul, ← mem_centralizer_iff.mp hyR r hr]
  have hσ3 : ∃ k : ℕ, φ y ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hy3
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨l, hl, hlx⟩ := hX₀ L'' U (φ y) hL'' hL''t hUfix hUe hU4 hσL hσU hσ3
  obtain ⟨l₀, hl₀L, rfl⟩ := (hmem l).1 hl
  refine ⟨l₀, hl₀L, fun x hx => ?_⟩
  have hzL : y * x * y⁻¹ * (l₀ * x * l₀⁻¹)⁻¹ ∈ L :=
    mul_mem ((mem_normalizer_iff.mp hyL x).mp hx)
      (inv_mem (mul_mem (mul_mem hl₀L hx) (inv_mem hl₀L)))
  let zX : ↥X := ⟨_, hLX hzL⟩
  have hkz : κ zX = φ y (κ ⟨x, hLX hx⟩) * (κ l₀ * κ ⟨x, hLX hx⟩ * (κ l₀)⁻¹)⁻¹ := by
    rw [hκ, ← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have hc := hlx (κ ⟨x, hLX hx⟩) ((hmem _).2 ⟨_, hx, rfl⟩)
  rw [← hkz] at hc
  obtain ⟨c, hcZ, hcz⟩ := hc
  have hcomm : ∀ a (ha : a ∈ L), κ zX * κ ⟨a, hLX ha⟩ = κ ⟨a, hLX ha⟩ * κ zX := by
    intro a ha
    have h := congrArg Subtype.val
      (mem_center_iff.mp hcZ ⟨κ ⟨a, hLX ha⟩, (hmem _).2 ⟨_, ha, rfl⟩⟩)
    simp only [Subgroup.coe_mul] at h
    have hcz' : (c : X₀) = κ zX := hcz
    rw [← hcz']
    exact h.symm
  have hzC : y * x * y⁻¹ * (l₀ * x * l₀⁻¹)⁻¹ ∈ centralizer (L : Set H) := by
    refine RankTwoSporadic.mem_centralizer_of_displacement hL.1 (le_normalizer hzL)
      fun a ha => ?_
    have h1 : κ (⟨a, hLX ha⟩ * zX) = κ (zX * ⟨a, hLX ha⟩) := by
      rw [map_mul, map_mul, hcomm a ha]
    have h2 := hκeq _ _ h1
    set ζ : ↥X := (⟨a, hLX ha⟩ * zX)⁻¹ * (zX * ⟨a, hLX ha⟩) with hζ
    have hζz : (zX : H) * ζ = ζ * zX := congrArg Subtype.val (mem_center_iff.mp h2 zX)
    have hval : a⁻¹ * ((zX : H) * a * (zX : H)⁻¹) = ζ := by
      have hζv : (ζ : H) = (zX : H)⁻¹ * a⁻¹ * (zX : H) * a := by
        simp only [hζ, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
        group
      calc a⁻¹ * ((zX : H) * a * (zX : H)⁻¹)
          = (zX : H) * ((zX : H)⁻¹ * a⁻¹ * (zX : H) * a) * (zX : H)⁻¹ := by group
        _ = (zX : H) * ζ * (zX : H)⁻¹ := by rw [hζv]
        _ = ζ := by rw [hζz, mul_inv_cancel_right]
    rw [show y * x * y⁻¹ * (l₀ * x * l₀⁻¹)⁻¹ = (zX : H) from rfl, hval]
    exact centralizer_le hLX (coe_mem_centralizer_of_mem_center h2)
  refine ⟨⟨_, hzL⟩, mem_center_iff.mpr fun w => Subtype.ext ?_, rfl⟩
  exact mem_centralizer_iff.mp hzC w w.2

theorem inducesInner_subgroupOf {L W : Subgroup H} (hLW : L ≤ W) {y : ↥W}
    (h : InducesInner y (L.subgroupOf W)) : InducesInner (y : H) L := by
  obtain ⟨l, hl, hlx⟩ := h
  refine ⟨l, hl, fun x hx => ?_⟩
  obtain ⟨c, hc, hcx⟩ := hlx ⟨x, hLW hx⟩ hx
  have hcL : ((c : ↥W) : H) ∈ L := c.2
  refine ⟨⟨(c : ↥W), hcL⟩, mem_center_iff.mpr fun w => Subtype.ext ?_, ?_⟩
  · have hw : (⟨w, hLW w.2⟩ : ↥W) ∈ L.subgroupOf W := w.2
    have h1 := congrArg (fun z : ↥W => (z : H))
      (congrArg Subtype.val (mem_center_iff.mp hc ⟨⟨w, hLW w.2⟩, hw⟩))
    simpa using h1
  · have h2 := congrArg (fun z : ↥W => (z : H)) hcx
    simpa using h2

end CFSG.ComponentClassification.RankTwoExceptional
