module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS1
public import CFSG.ClassicalInvolution.Asc77.AscFusionDiag
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups


theorem layer_acts_inner {W : Type} [Group W] [Finite W] {A : Subgroup W}
    (hA : TwoComponents.IsTwoComponent A) {x : W} (hx : x ∈ TwoLayer.subgroup W) :
    x ∈ Subgroup.normalizer (A : Set W) ∧
      ∃ b ∈ A, ∀ y ∈ A, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf A := by
  unfold TwoLayer.subgroup at hx
  rw [sSup_eq_iSup'] at hx
  refine Subgroup.iSup_induction
    (fun E : {E : Subgroup W | TwoComponents.IsTwoComponent E} => (E : Subgroup W)) hx
    (C := fun x => x ∈ Subgroup.normalizer (A : Set W) ∧
      ∃ b ∈ A, ∀ y ∈ A, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf A) ?_ ?_ ?_
  · rintro ⟨E, hE⟩ x hxE0
    have hxE : x ∈ E := hxE0
    by_cases hEA : E = A
    · rw [hEA] at hxE
      refine ⟨Subgroup.le_normalizer hxE, x, hxE, fun y hy => ?_⟩
      simp only [mul_inv_cancel]
      exact (oddCoreOf A).one_mem
    · obtain ⟨-, hEN, hcore⟩ :=
        TwoComponentInteraction.mutual_normalization_core_commutation E A hE hA hEA
      refine ⟨hEN hxE, 1, A.one_mem, fun y hy => ?_⟩
      have h1 := hcore (Subgroup.commutator_mem_commutator hxE hy)
      have h2 : ⁅x, y⁆ ∈ oddCoreOf A := (Subgroup.mem_inf.mp h1).2
      have e : x * y * x⁻¹ * ((1 : W) * y * (1 : W)⁻¹)⁻¹ = ⁅x, y⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact h2
  · refine ⟨(Subgroup.normalizer (A : Set W)).one_mem, 1, A.one_mem, fun y hy => ?_⟩
    simp only [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact (oddCoreOf A).one_mem
  · rintro x₁ x₂ ⟨hx₁N, b₁, hb₁, h₁⟩ ⟨hx₂N, b₂, hb₂, h₂⟩
    refine ⟨(Subgroup.normalizer (A : Set W)).mul_mem hx₁N hx₂N, b₁ * b₂, A.mul_mem hb₁ hb₂,
      fun y hy => ?_⟩
    have hy₂ : b₂ * y * b₂⁻¹ ∈ A := A.mul_mem (A.mul_mem hb₂ hy) (A.inv_mem hb₂)
    have o₂ := h₂ y hy
    have o₁ := h₁ _ hy₂
    have o₂' := mem_normalizer_oddCoreOf_of_mem_normalizer hx₁N o₂
    have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * (b₁ * b₂ * y * (b₁ * b₂)⁻¹)⁻¹ =
        (x₁ * (x₂ * y * x₂⁻¹ * (b₂ * y * b₂⁻¹)⁻¹) * x₁⁻¹) *
          (x₁ * (b₂ * y * b₂⁻¹) * x₁⁻¹ * (b₁ * (b₂ * y * b₂⁻¹) * b₁⁻¹)⁻¹) := by
      group
    show x₁ * x₂ * y * (x₁ * x₂)⁻¹ * (b₁ * b₂ * y * (b₁ * b₂)⁻¹)⁻¹ ∈ oddCoreOf A
    rw [e]
    exact (oddCoreOf A).mul_mem o₂' o₁



theorem mem_oddCoreOf_subgroupOf_iff {G : Type} [Group G] {Y K : Subgroup G} (hKY : K ≤ Y)
    {y : ↥Y} : y ∈ oddCoreOf (K.subgroupOf Y) ↔ (y : G) ∈ oddCoreOf K := by
  let e : ↥(K.subgroupOf Y) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKY
  have hinv : (classicalInvolutionOddCore ↥(K.subgroupOf Y)).map e.toMonoidHom =
      classicalInvolutionOddCore ↥K :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [mem_oddCoreOf_iff, mem_oddCoreOf_iff]
  constructor
  · rintro ⟨h, hmem⟩
    have hy : (y : G) ∈ K := h
    refine ⟨hy, ?_⟩
    rw [← hinv]
    exact ⟨⟨y, h⟩, hmem, rfl⟩
  · rintro ⟨h, hmem⟩
    have hy : y ∈ K.subgroupOf Y := h
    refine ⟨hy, ?_⟩
    rw [← hinv] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    have : w = ⟨y, hy⟩ := e.injective (hwe.trans rfl)
    rw [← this]
    exact hw



theorem layer_acts_inner_sub {G : Type} [Group G] [Finite G] {Y K : Subgroup G} (hKY : K ≤ Y)
    (hK : TwoComponents.IsTwoComponent (K.subgroupOf Y)) {x : G} (hxY : x ∈ Y)
    (hx : (⟨x, hxY⟩ : ↥Y) ∈ TwoLayer.subgroup ↥Y) :
    x ∈ Subgroup.normalizer (K : Set G) ∧
      ∃ b ∈ K, ∀ y ∈ K, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf K := by
  obtain ⟨hN, b', hb', h⟩ := layer_acts_inner hK hx
  refine ⟨?_, (b' : G), hb', fun y hy => ?_⟩
  · have h2 : (⟨x, hxY⟩ : ↥Y) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf Y := by
      rw [Subgroup.subgroupOf_normalizer_eq hKY]
      exact hN
    exact Subgroup.mem_subgroupOf.mp h2
  · have hy' : (⟨y, hKY hy⟩ : ↥Y) ∈ K.subgroupOf Y := hy
    have := h _ hy'
    rw [mem_oddCoreOf_subgroupOf_iff hKY] at this
    simpa using this


section Trivial

variable {G : Type} [Group G] [Finite G]

theorem trivialCore_le_twoLayer {B : Subgroup G} {b a : G} (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hBb : ∀ y ∈ B, b * y = y * b) (hab : b * a = a * b)
    (hBsn : (B.subgroupOf (Subgroup.centralizer ({b} : Set G))).IsSubnormal)
    {J₀ : Subgroup G} (hJ₀B : J₀ ≤ B) (hJ₀fix : ∀ x ∈ J₀, a * x * a⁻¹ = x)
    (hJ₀perf : ⁅J₀, J₀⁆ = J₀) (hJ₀qs : CFSG.IsQuasisimple (J₀ ⧸ pPrimeCore 2 J₀))
    (hJ₀sub : (J₀.subgroupOf (B ⊓ Subgroup.centralizer ({a} : Set G))).IsSubnormal) :
    J₀.subgroupOf (Subgroup.centralizer ({a} : Set G)) ≤
      TwoLayer.subgroup ↥(Subgroup.centralizer ({a} : Set G)) := by
  classical
  set Y : Subgroup G := Subgroup.centralizer ({a} : Set G) with hY
  have hJt' : B ≤ Subgroup.centralizer ({b} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hBb y hy).symm
  have htY : b ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr hab
  set R₂ : Subgroup G := Y ⊓ Subgroup.centralizer ({b} : Set G) with hR₂
  have hR₂Y : R₂ ≤ Y := inf_le_left
  have hR₂t : R₂ ≤ Subgroup.centralizer ({b} : Set G) := inf_le_right
  have hJ₀R₂ : J₀ ≤ R₂ := by
    intro x hx
    refine ⟨?_, hJt' (hJ₀B hx)⟩
    show x ∈ Subgroup.centralizer ({a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hJ₀fix x hx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hJ₀Y : J₀ ≤ Y := hJ₀R₂.trans hR₂Y
  set a₀ : ↥Y := ⟨b, htY⟩ with ha₀
  have hA2 : IsPGroup 2 (Subgroup.zpowers a₀) :=
    isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hb2) (fun h => hb1 (congrArg Subtype.val h))
  have hcentA : Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) =
      R₂.subgroupOf Y := by
    ext x
    constructor
    · intro hx
      have h1 : a₀ * x = x * a₀ := Subgroup.mem_centralizer_iff.mp hx a₀ (Subgroup.mem_zpowers a₀)
      refine ⟨x.2, ?_⟩
      show (x : G) ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val h1).symm
    · intro hx
      have hxt : (x : G) * b = b * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hcm : Commute a₀ x := Subtype.ext hxt.symm
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left hcm k).eq
  set LY : Subgroup ↥Y := J₀.subgroupOf Y with hLYdef
  have hLA : LY ≤ Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y) := by
    rw [hcentA]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hJ₀R₂ (Subgroup.mem_subgroupOf.mp hx))
  have hJsnR₂ : (B.subgroupOf R₂).IsSubnormal := by
    have h1 := hBsn.comap (Subgroup.inclusion hR₂t)
    have h2 : (B.subgroupOf (Subgroup.centralizer ({b} : Set G))).comap
        (Subgroup.inclusion hR₂t) = B.subgroupOf R₂ := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [h2] at h1
  set F : Subgroup G := B ⊓ Y with hF
  have hFR₂ : ∀ x : ↥F, ((x : ↥F) : G) ∈ R₂ := by
    intro x
    exact ⟨x.2.2, hJt' x.2.1⟩
  let ι : ↥F →* ↥R₂ := (F.subtype).codRestrict R₂ hFR₂
  have hrange : ι.range = B.subgroupOf R₂ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2.1
    · intro hx
      exact ⟨⟨x, ⟨hx, x.2.1⟩⟩, rfl⟩
  have hJ₀F : (J₀.subgroupOf F).IsSubnormal := hJ₀sub
  have hsnR₂ : (J₀.subgroupOf R₂).IsSubnormal := by
    have hsn := isSubnormal_map_of_isSubnormal_range ι hJ₀F (by rw [hrange]; exact hJsnR₂)
    have hid : (J₀.subgroupOf F).map ι = J₀.subgroupOf R₂ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxJ₀ : (x : G) ∈ J₀ := hx
        exact ⟨⟨x, ⟨hJ₀B hxJ₀, x.2.1⟩⟩, hxJ₀, rfl⟩
    rwa [hid] at hsn
  have hLsubY : IsSubnormal LY
      (Subgroup.centralizer ((Subgroup.zpowers a₀ : Subgroup ↥Y) : Set ↥Y)) := by
    rw [hcentA]
    have h1 : IsSubnormal (J₀.subgroupOf R₂) ⊤ := Components.chain_of_mathlib_subnormal hsnR₂
    have h2 := Components.chain_map (Subgroup.inclusion hR₂Y) h1
    have e1 : (J₀.subgroupOf R₂).map (Subgroup.inclusion hR₂Y) = LY := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        have hxJ₀ : (x : G) ∈ J₀ := hx
        exact ⟨⟨x, hJ₀R₂ hxJ₀⟩, hxJ₀, rfl⟩
    have e2 : (⊤ : Subgroup ↥R₂).map (Subgroup.inclusion hR₂Y) = R₂.subgroupOf Y := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    rwa [e1, e2] at h2
  have e : ↥LY ≃* ↥J₀ := Subgroup.subgroupOfEquivOfLe hJ₀Y
  have hJ₀perf' : Group.IsPerfect ↥J₀ := Subgroup.isPerfect_iff.mpr hJ₀perf
  have hLYperf : commutator ↥LY = ⊤ := by
    have : Group.IsPerfect ↥LY :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  have hLq0 : CFSG.Open.IsQuasisimple (↥J₀ ⧸ componentClassificationOddCore ↥J₀) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.quotientMulEquivOfEq
        (CatalogueBAlternating.primeCore_two_eq_oddCore ↥J₀).symm)
      (CatalogueBAlternating.quasisimple_iff_native.mp hJ₀qs)
  have hLYq : CFSG.Open.IsQuasisimple (↥LY ⧸ componentClassificationOddCore LY) :=
    Components.quasisimple_of_equiv
      (QuotientGroup.congr (componentClassificationOddCore LY) (componentClassificationOddCore J₀)
        e (OddCore.equiv_invariant e)) hLq0
  exact Balance.le_twoLayer_of_l2PrimeBalance l2PrimeBalance hA2 hLA hLsubY hLYperf hLYq

end Trivial

section Chart

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
  (e : (↥K ⧸ classicalInvolutionOddCore ↥K) ≃* SL(2, F))

@[expose] def chartMap : ↥K →* SL(2, F) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))

theorem chartMap_surjective : Function.Surjective (chartMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem chartMap_eq_one_iff (y : ↥K) :
    chartMap e y = 1 ↔ y ∈ classicalInvolutionOddCore ↥K := by
  rw [chartMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_one e, e.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem mem_oddCoreOf_iff_chart {w : G} :
    w ∈ oddCoreOf K ↔ ∃ h : w ∈ K, chartMap e ⟨w, h⟩ = 1 := by
  rw [mem_oddCoreOf_iff]
  constructor
  · rintro ⟨h, hw⟩
    exact ⟨h, (chartMap_eq_one_iff e _).mpr hw⟩
  · rintro ⟨h, hw⟩
    exact ⟨h, (chartMap_eq_one_iff e _).mp hw⟩

@[expose] noncomputable def chartAut (α : MulAut ↥K) : MulAut SL(2, F) :=
  e.symm.trans ((QuotientGroup.congr (classicalInvolutionOddCore ↥K)
    (classicalInvolutionOddCore ↥K) α (OddCore.char_invariant α)).trans e)

theorem chartAut_apply (α : MulAut ↥K) (y : ↥K) :
    chartAut e α (chartMap e y) = chartMap e (α y) := by
  simp only [chartAut, chartMap, MulEquiv.trans_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply]
  exact congrArg e (QuotientGroup.congr_mk _ _ α _ y)

@[expose] noncomputable def chartHom : MulAut ↥K →* MulAut SL(2, F) where
  toFun := chartAut e
  map_one' := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨y, rfl⟩ := chartMap_surjective e s
    rw [chartAut_apply]
    rfl
  map_mul' α β := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨y, rfl⟩ := chartMap_surjective e s
    show chartAut e (α * β) (chartMap e y) =
      chartAut e α (chartAut e β (chartMap e y))
    rw [chartAut_apply, chartAut_apply, chartAut_apply]
    rfl

@[expose] noncomputable def actSL (R : Subgroup G) (hR : R ≤ Subgroup.normalizer (K : Set G)) :
    R →* MulAut SL(2, F) :=
  (chartHom e).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hR))

theorem actSL_apply (R : Subgroup G) (hR : R ≤ Subgroup.normalizer (K : Set G)) (x : R)
    (y : ↥K) :
    actSL e R hR x (chartMap e y) =
      chartMap e (K.normalizerMonoidHom ⟨(x : G), hR x.2⟩ y) :=
  chartAut_apply e _ y


theorem chart_conj_eq {x b : G} (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hb : b ∈ K)
    {y : G} (hy : y ∈ K) (h : x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf K) :
    chartMap e (K.normalizerMonoidHom ⟨x, hxN⟩ ⟨y, hy⟩) =
      chartMap e ⟨b, hb⟩ * chartMap e ⟨y, hy⟩ * (chartMap e ⟨b, hb⟩)⁻¹ := by
  obtain ⟨hmem, hone⟩ := (mem_oddCoreOf_iff_chart e).mp h
  have hxy : x * y * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  have hby : b * y * b⁻¹ ∈ K := K.mul_mem (K.mul_mem hb hy) (K.inv_mem hb)
  have e1 : (⟨x * y * x⁻¹ * (b * y * b⁻¹)⁻¹, hmem⟩ : ↥K) =
      ⟨x * y * x⁻¹, hxy⟩ * (⟨b * y * b⁻¹, hby⟩ : ↥K)⁻¹ := rfl
  rw [e1, map_mul, map_inv, mul_inv_eq_one] at hone
  have e2 : (K.normalizerMonoidHom ⟨x, hxN⟩ ⟨y, hy⟩ : ↥K) = ⟨x * y * x⁻¹, hxy⟩ := rfl
  rw [e2, hone]
  have e3 : (⟨b * y * b⁻¹, hby⟩ : ↥K) = ⟨b, hb⟩ * ⟨y, hy⟩ * (⟨b, hb⟩ : ↥K)⁻¹ := rfl
  rw [e3, map_mul, map_mul, map_inv]

end Chart




section Sign

variable {F : Type} [Field F]

@[expose] def signNormalizer (g : SL(2, F)) : Subgroup SL(2, F) where
  carrier := {h | h * g = g * h ∨ h * g = (-1) * g * h}
  mul_mem' := by
    have hc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := sl2_neg_one_central
    have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
      apply Subtype.ext
      simp
    rintro h₁ h₂ (h1 | h1) (h2 | h2)
    · left
      calc h₁ * h₂ * g = h₁ * (h₂ * g) := mul_assoc _ _ _
        _ = h₁ * (g * h₂) := by rw [h2]
        _ = (h₁ * g) * h₂ := (mul_assoc _ _ _).symm
        _ = (g * h₁) * h₂ := by rw [h1]
        _ = g * (h₁ * h₂) := mul_assoc _ _ _
    · right
      calc h₁ * h₂ * g = h₁ * (h₂ * g) := mul_assoc _ _ _
        _ = h₁ * ((-1) * g * h₂) := by rw [h2]
        _ = (-1) * (h₁ * g) * h₂ := by
            have := hc h₁
            calc h₁ * ((-1) * g * h₂) = (h₁ * (-1)) * g * h₂ := by group
              _ = ((-1) * h₁) * g * h₂ := by rw [← this]
              _ = (-1) * (h₁ * g) * h₂ := by group
        _ = (-1) * (g * h₁) * h₂ := by rw [h1]
        _ = (-1) * g * (h₁ * h₂) := by group
    · right
      calc h₁ * h₂ * g = h₁ * (h₂ * g) := mul_assoc _ _ _
        _ = h₁ * (g * h₂) := by rw [h2]
        _ = (h₁ * g) * h₂ := (mul_assoc _ _ _).symm
        _ = ((-1) * g * h₁) * h₂ := by rw [h1]
        _ = (-1) * g * (h₁ * h₂) := by group
    · left
      calc h₁ * h₂ * g = h₁ * (h₂ * g) := mul_assoc _ _ _
        _ = h₁ * ((-1) * g * h₂) := by rw [h2]
        _ = (-1) * (h₁ * g) * h₂ := by
            have := hc h₁
            calc h₁ * ((-1) * g * h₂) = (h₁ * (-1)) * g * h₂ := by group
              _ = ((-1) * h₁) * g * h₂ := by rw [← this]
              _ = (-1) * (h₁ * g) * h₂ := by group
        _ = (-1) * ((-1) * g * h₁) * h₂ := by rw [h1]
        _ = ((-1) * (-1)) * g * (h₁ * h₂) := by group
        _ = g * (h₁ * h₂) := by rw [hcc, one_mul]
  one_mem' := Or.inl (by simp)
  inv_mem' := by
    have hc : ∀ x : SL(2, F), (-1 : SL(2, F)) * x = x * (-1) := sl2_neg_one_central
    have hcc : (-1 : SL(2, F)) * (-1) = 1 := by
      apply Subtype.ext
      simp
    rintro h (h1 | h1)
    · left
      show h⁻¹ * g = g * h⁻¹
      calc h⁻¹ * g = h⁻¹ * (g * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * g) * h⁻¹ := by rw [h1]
        _ = g * h⁻¹ := by group
    · right
      show h⁻¹ * g = (-1) * g * h⁻¹
      have e1 : g * h⁻¹ = (-1) * (h⁻¹ * g) := by
        calc g * h⁻¹ = h⁻¹ * (h * g) * h⁻¹ := by group
          _ = h⁻¹ * ((-1) * g * h) * h⁻¹ := by rw [h1]
          _ = ((-1) * (h⁻¹ * g)) := by
              have := hc h⁻¹
              calc h⁻¹ * ((-1) * g * h) * h⁻¹ = (h⁻¹ * (-1)) * g := by group
                _ = ((-1) * h⁻¹) * g := by rw [← this]
                _ = (-1) * (h⁻¹ * g) := by group
      calc h⁻¹ * g = ((-1) * (-1)) * (h⁻¹ * g) := by rw [hcc, one_mul]
        _ = (-1) * ((-1) * (h⁻¹ * g)) := by group
        _ = (-1) * (g * h⁻¹) := by rw [← e1]
        _ = (-1) * g * h⁻¹ := by group

theorem mem_signNormalizer_iff (g h : SL(2, F)) :
    h ∈ signNormalizer g ↔ h * g = g * h ∨ h * g = (-1) * g * h := Iff.rfl



end Sign

section Chart2

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
  (e : (↥K ⧸ classicalInvolutionOddCore ↥K) ≃* SL(2, F))

theorem actSL_eq_conj (R : Subgroup G) (hR : R ≤ Subgroup.normalizer (K : Set G)) {x : G}
    (hx : x ∈ R) {b : G} (hb : b ∈ K)
    (h : ∀ y ∈ K, x * y * x⁻¹ * (b * y * b⁻¹)⁻¹ ∈ oddCoreOf K) :
    actSL e R hR ⟨x, hx⟩ = MulAut.conj (chartMap e ⟨b, hb⟩) := by
  refine MulEquiv.ext fun s => ?_
  obtain ⟨y, rfl⟩ := chartMap_surjective e s
  rw [actSL_apply, MulAut.conj_apply]
  exact chart_conj_eq e (hR hx) hb y.2 (h y y.2)

theorem comm_mem_oddCoreOf_iff_central {w : G} (hw : w ∈ K) :
    (∀ y ∈ K, ⁅w, y⁆ ∈ oddCoreOf K) ↔ chartMap e ⟨w, hw⟩ ∈ Subgroup.center SL(2, F) := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨y, rfl⟩ := chartMap_surjective e s
    obtain ⟨hmem, hone⟩ := (mem_oddCoreOf_iff_chart e).mp (h y y.2)
    have e1 : (⟨⁅w, (y : G)⁆, hmem⟩ : ↥K) = ⁅(⟨w, hw⟩ : ↥K), y⁆ := rfl
    rw [e1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hone
    exact hone.symm
  · intro h y hy
    rw [Subgroup.mem_center_iff] at h
    rw [mem_oddCoreOf_iff_chart e]
    have hmem : ⁅w, y⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hw hy) (K.inv_mem hw)) (K.inv_mem hy)
    refine ⟨hmem, ?_⟩
    have e1 : (⟨⁅w, y⁆, hmem⟩ : ↥K) = ⁅(⟨w, hw⟩ : ↥K), ⟨y, hy⟩⁆ := rfl
    rw [e1, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (h (chartMap e ⟨y, hy⟩)).symm

end Chart2


end CFSG.ClassicalInvolution.Asc77.AscFusion
