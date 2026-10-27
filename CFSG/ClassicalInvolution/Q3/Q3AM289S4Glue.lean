module

public import CFSG.ClassicalInvolution.Q3.Q3T8B16B
public import CFSG.ClassicalInvolution.Q3.Q3NMClass

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G]


theorem exists_conj_lift_involutions' {X Λ : Subgroup G}
    (hΛ : Λ ≤ Subgroup.normalizer (X : Set G)) {z t t' : G} (hzΛ : z ∈ Λ) (hz2 : z * z = 1)
    (hzX : ∀ x ∈ X, ⁅x, z⁆ ∈ oddCoreOf X) (htX : t ∈ X) (ht'X : t' ∈ X) (ht2 : t * t = 1)
    (ht'2 : t' * t' = 1) (hzt : z * t = t * z)
    (hzt' : z * t' = t' * z)
    (hq : ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X,
      g * QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t, htX⟩ * g⁻¹ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨t', ht'X⟩) :
    ∃ y ∈ X, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t' := by
  classical
  set O : Subgroup G := oddCoreOf X with hOdef
  have hOodd : Odd (Nat.card O) := oddCoreOf_odd_natCard X
  have hOX : O ≤ X := oddCoreOf_le_self X
  have hconjO : ∀ g ∈ Λ, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer (hΛ hg)) o).mp ho
  have hCz : ∀ g ∈ Subgroup.centralizer ({z} : Set G), g * z * g⁻¹ = z := fun g hg => by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  set M : Subgroup ↥X := classicalInvolutionOddCore ↥X with hM
  set π : ↥X →* (↥X ⧸ M) := QuotientGroup.mk' M with hπ
  have hker : ∀ a : ↥X, π a = 1 → (a : G) ∈ O := fun a h =>
    mem_oddCoreOf_iff.mpr ⟨a.2, (QuotientGroup.eq_one_iff _).mp h⟩
  have hker' : ∀ a : ↥X, (a : G) ∈ O → π a = 1 := fun a h =>
    (QuotientGroup.eq_one_iff _).mpr (mem_oddCoreOf_iff.mp h).2
  have hnot : ∀ c : G, c ∈ X → c * c = 1 → c ≠ 1 → ∀ hcX : c ∈ X, π ⟨c, hcX⟩ ≠ 1 := by
    intro c _ hc2 hc1 hcX h
    exact hc1 (eq_one_of_isPGroup_of_mem_odd hOodd (hker _ h)
      (ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2))
  set X₁ : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G) with hX₁
  have hlift : ∀ q : ↥X ⧸ M, ∃ x : G, ∃ hx : x ∈ X₁, π ⟨x, hx.1⟩ = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, hoz⟩ := exists_mul_mem_centralizer hOodd hconjO hzΛ hz2 (hzX a a.2)
    have hoX : o⁻¹ ∈ X := X.inv_mem (hOX ho)
    refine ⟨o⁻¹ * a, ⟨X.mul_mem hoX a.2, hoz⟩, ?_⟩
    have e : (⟨o⁻¹ * a, X.mul_mem hoX a.2⟩ : ↥X) = ⟨o⁻¹, hoX⟩ * a := rfl
    rw [e, map_mul, hker' ⟨o⁻¹, hoX⟩ (O.inv_mem ho), one_mul]
    rfl
  have hOodd₁ : Odd (Nat.card (O ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) :=
    hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hu2 : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htX⟩ * ⟨t, htX⟩ : ↥X) = 1 := Subtype.ext ht2
    rw [this, map_one]
  obtain ⟨gq, hgq⟩ := hq
  obtain ⟨x₁, hx₁, hπx₁⟩ := hlift gq
  have htX₁ : t ∈ X₁ := ⟨htX, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hux : x₁ * t * x₁⁻¹ ∈ X₁ := X₁.mul_mem (X₁.mul_mem hx₁ htX₁) (X₁.inv_mem hx₁)
  have hπu : π ⟨x₁ * t * x₁⁻¹, hux.1⟩ = π ⟨t', ht'X⟩ := by
    have e : (⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X) = ⟨x₁, hx₁.1⟩ * ⟨t, htX⟩ * ⟨x₁, hx₁.1⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hπx₁, ← hgq]
  have ht'X₁ : t' ∈ X₁ := ⟨ht'X, Subgroup.mem_centralizer_singleton_iff.mpr hzt'.symm⟩
  have hinv : (x₁ * t * x₁⁻¹)⁻¹ * t' ∈ O ⊓ Subgroup.centralizer ({z} : Set G) := by
    refine ⟨?_, (X₁.mul_mem (X₁.inv_mem hux) ht'X₁).2⟩
    have h1 : π ((⟨x₁ * t * x₁⁻¹, hux.1⟩ : ↥X)⁻¹ * ⟨t', ht'X⟩) = 1 := by
      rw [map_mul, map_inv, hπu, inv_mul_cancel]
    exact hker _ h1
  have hu2' : (x₁ * t * x₁⁻¹) * (x₁ * t * x₁⁻¹) = 1 := by
    calc x₁ * t * x₁⁻¹ * (x₁ * t * x₁⁻¹) = x₁ * (t * t) * x₁⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨ν, hν, hνe⟩ := CFSG.ClassicalInvolution.Q3.Q3T8.AF.exists_conj_of_inv_mul_mem hu2' ht'2
    hOodd₁ hinv
  refine ⟨ν * x₁, X.mul_mem (hOX hν.1) hx₁.1, ?_, ?_⟩
  · calc ν * x₁ * z * (ν * x₁)⁻¹ = ν * (x₁ * z * x₁⁻¹) * ν⁻¹ := by group
      _ = ν * z * ν⁻¹ := by rw [hCz x₁ hx₁.2]
      _ = z := hCz ν hν.2
  · calc ν * x₁ * t * (ν * x₁)⁻¹ = ν * (x₁ * t * x₁⁻¹) * ν⁻¹ := by group
      _ = t' := hνe.symm

open CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification
  CFSG.ClassicalInvolution.Q3.Q3NM

@[expose] noncomputable def layerQuotHom {Y : Subgroup G} {c : G}
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G)) : ↥Y →* OddQuot c :=
  (oddQuotMk c).comp (Subgroup.inclusion hYC)

theorem layerQuotHom_ker {Y : Subgroup G} {c : G} (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hCY : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y) :
    (layerQuotHom hYC).ker = classicalInvolutionOddCore ↥Y := by
  ext y
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h1 : (⟨(y : G), hYC y.2⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) :=
      (QuotientGroup.eq_one_iff _).mp h
    have h2 : (y : G) ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
      mem_oddCoreOf_iff.mpr ⟨hYC y.2, h1⟩
    have hN : oddCoreOf (Subgroup.centralizer ({c} : Set G)) ⊓ Y ≤ oddCoreOf Y := by
      refine T8V.le_oddCoreOf_of_normal_odd' inf_le_right ?_
        (Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.card_dvd_of_le inf_le_left))
      intro g hg
      rw [mem_normalizer_iff_conjSub_eq]
      have h1 : conjSub g (oddCoreOf (Subgroup.centralizer ({c} : Set G))) =
          oddCoreOf (Subgroup.centralizer ({c} : Set G)) := by
        rw [← CFSG.ClassicalInvolution.Asc77.Thompson.oddCoreOf_conjSub_eq,
          conjSub_eq_self_of_mem (hYC hg)]
      have hgY : conjSub g Y = Y := conjSub_eq_self_of_mem hg
      have h3 : conjSub g (oddCoreOf (Subgroup.centralizer ({c} : Set G)) ⊓ Y) =
          conjSub g (oddCoreOf (Subgroup.centralizer ({c} : Set G))) ⊓ conjSub g Y :=
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective
      rw [h3, h1, hgY]
    obtain ⟨hx, h4⟩ := mem_oddCoreOf_iff.mp (hN ⟨h2, y.2⟩)
    exact h4
  · intro h
    have h1 : (y : G) ∈ oddCoreOf Y := mem_oddCoreOf_iff.mpr ⟨y.2, h⟩
    have h2 : (y : G) ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
      oddCoreOf_inf_le hCY ⟨h1, hYC y.2⟩
    obtain ⟨hx2, h3⟩ := mem_oddCoreOf_iff.mp h2
    exact (QuotientGroup.eq_one_iff _).mpr h3

theorem layerQuotHom_range {Y : Subgroup G} {c : G}
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G)) :
    (layerQuotHom hYC).range = modOdd c Y := by
  unfold layerQuotHom modOdd
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

@[expose] noncomputable def layerQuotEquiv {Y : Subgroup G} {c : G}
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hCY : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y) :
    (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* ↥(modOdd c Y) :=
  (QuotientGroup.quotientMulEquivOfEq (layerQuotHom_ker hYC hCY).symm).trans
    ((QuotientGroup.quotientKerEquivRange (layerQuotHom hYC)).trans
      (MulEquiv.subgroupCongr (layerQuotHom_range hYC)))

theorem layerQuotEquiv_mk {Y : Subgroup G} {c : G}
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hCY : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y) (y : ↥Y) :
    ((layerQuotEquiv hYC hCY (QuotientGroup.mk' _ y) : ↥(modOdd c Y)) : OddQuot c) =
      oddQuotMk c ⟨(y : G), hYC y.2⟩ := rfl

theorem isComponent_modOdd_layer {Y : Subgroup G} {c : G}
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hCY : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ classicalInvolutionOddCore ↥Y)) :
    CFSG.IsComponent (modOdd c Y) := by
  classical
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hq' : CFSG.IsQuasisimple ↥(modOdd c Y) :=
    CFSG.ClassicalInvolution.Asc77.AscFusion.isQuasisimple_of_mulEquiv
      (layerQuotEquiv hYC hCY).symm hq
  have hnorm : (modOdd c Y).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (componentClassificationOddCore ↥C) g
    have hhY : conjSub (h : G) Y = Y := hCY h h.2
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hcn : (h : G) * y * (h : G)⁻¹ ∈ Y := by
      have : (h : G) * y * (h : G)⁻¹ ∈ conjSub (h : G) Y := ⟨y, hyY, rfl⟩
      rwa [hhY] at this
    refine ⟨h * y * h⁻¹, Subgroup.mem_subgroupOf.mpr hcn, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  exact ⟨hq', hnorm.isSubnormal⟩


theorem hyp51At_of_layer {Y : Subgroup G} {c w : G} {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) (hwB : w ∈ B) (hw1 : w ≠ 1)
    (hwc : w ≠ c) (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hCY : ∀ g ∈ Subgroup.centralizer ({c} : Set G), conjSub g Y = Y)
    (hq : CFSG.IsQuasisimple (↥Y ⧸ classicalInvolutionOddCore ↥Y)) (hwY : w ∈ Y)
    (hwnc : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩ ∉
      Subgroup.center (↥Y ⧸ classicalInvolutionOddCore ↥Y))
    (P : MulAut ↥(modOdd c Y) → Prop) (hrow : AutOddFreeOn ↥(modOdd c Y) P)
    (hP : ∀ x ∈ inducedImage (modOdd c Y) (modOdd c B), P (x : MulAut ↥(modOdd c Y))) :
    Hyp51At B c := by
  classical
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) := hYC hwY
  have hQ := isComponent_modOdd_layer hYC hCY hq
  have hzQ : oddQuotMk c ⟨w, hwC⟩ ∈ modOdd c Y := oddQuotMk_mem_modOdd hwY hwC
  have hQeq : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      L = modOdd c Y := by
    intro L hL hm
    by_contra hne
    obtain ⟨y, hyL, hy⟩ := hm _ (oddQuotMk_mem_modOdd hwB hwC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hwB hw1 hwc hwC)
    exact hy (Q3.commute_of_ne_isComponent hQ hL (Ne.symm hne) hzQ hyL)
  refine ⟨fun L L' hL hL' hm hm' => (hQeq L hL hm).trans (hQeq L' hL' hm').symm,
    fun L hL hm => ?_⟩
  have hLQ := hQeq L hL hm
  subst hLQ
  set e := layerQuotEquiv hYC hCY with he
  have h2 : ∀ x ∈ inducedImage (modOdd c Y) (modOdd c B), x * x = 1 := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := hx
    have hn' : (n : OddQuot c) ∈ modOdd c B := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨b, hb, hbn⟩ := hn'
    have hbb : b * b = 1 := Subtype.ext (Lemma52Proof.mul_self_eq_one_of_mem hB hb)
    have hnn : n * n = 1 := by
      apply Subtype.ext
      show (n : OddQuot c) * (n : OddQuot c) = 1
      rw [← hbn, ← map_mul, hbb, map_one]
    rw [← map_mul, hnn, map_one]
  have hne : ∃ x ∈ inducedImage (modOdd c Y) (modOdd c B), x ≠ 1 := by
    set wbar : OddQuot c := oddQuotMk c ⟨w, hwC⟩ with hwbar
    have hwn : wbar ∈ Subgroup.normalizer ((modOdd c Y : Subgroup (OddQuot c)) :
        Set (OddQuot c)) := Subgroup.le_normalizer hzQ
    refine ⟨toInducedAutOn (modOdd c Y) ⟨wbar, hwn⟩,
      ⟨⟨wbar, hwn⟩, Subgroup.mem_subgroupOf.mpr (oddQuotMk_mem_modOdd hwB hwC), rfl⟩, ?_⟩
    intro h1
    apply hwnc
    have hfix : ∀ y : ↥(modOdd c Y), wbar * (y : OddQuot c) = (y : OddQuot c) * wbar := by
      intro y
      have h6 : conjOnNormalizer (modOdd c Y) ⟨wbar, hwn⟩ = 1 := congrArg Subtype.val h1
      have h4 : wbar * (y : OddQuot c) * wbar⁻¹ = (y : OddQuot c) := by
        have h5 := congrArg (fun f : MulAut ↥(modOdd c Y) => ((f y : ↥(modOdd c Y)) : OddQuot c)) h6
        exact h5
      calc wbar * (y : OddQuot c) = wbar * (y : OddQuot c) * wbar⁻¹ * wbar := by group
        _ = (y : OddQuot c) * wbar := by rw [h4]
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    have hmk : e (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hwY⟩) =
        ⟨wbar, hzQ⟩ := Subtype.ext rfl
    rw [map_mul, map_mul, hmk]
    exact Subtype.ext (hfix (e g)).symm
  exact alphaOf_inducedImage_eq_bot_of_on (modOdd c Y) (modOdd c B) P hrow h2 hne hP

theorem autOddFreeOn_of_mulEquiv {X X' : Type} [Group X] [Finite X] [Group X'] [Finite X']
    (e : X ≃* X') (P : MulAut X → Prop) (h : AutOddFreeOn X P) :
    AutOddFreeOn X' (fun f' => P ((MulAut.congr e).symm f')) := by
  intro 𝒳' hinn' f' hP' hf'
  set φ : MulAut X ≃* MulAut X' := MulAut.congr e with hφ
  set 𝒳 : Subgroup (MulAut X) := 𝒳'.map φ.symm.toMonoidHom with h𝒳
  have hinn : innSubgroup X ≤ 𝒳 := by
    rintro _ ⟨x, rfl⟩
    refine ⟨φ (MulAut.conj x), hinn' ⟨e x, ?_⟩, by simp⟩
    ext y
    simp [hφ, MulAut.congr_apply, MulAut.conj_apply]
  let ε : ↥𝒳' ≃* ↥𝒳 := φ.symm.subgroupMap 𝒳'
  have hf : orderOf (ε f') = 2 := by rw [MulEquiv.orderOf_eq]; exact hf'
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv ε f' (h 𝒳 hinn (ε f') hP' hf)

end Glue

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
