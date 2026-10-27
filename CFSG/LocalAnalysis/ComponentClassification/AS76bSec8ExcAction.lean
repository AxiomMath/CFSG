module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoChar2C0Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalLift

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Conj

variable {C : Type*} [Group C]

theorem cent_conj (c x : C) :
    cent (c * x * c⁻¹) = (cent x).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [h]
      _ = x * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * y := by group

noncomputable def centConjEquiv (c x : C) : ↥(cent x) ≃* ↥(cent (c * x * c⁻¹)) :=
  ((cent x).equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
    (MulEquiv.subgroupCongr (cent_conj c x).symm)

theorem charTwo_conj {x : C} (h : CharTwo x) (c : C) : CharTwo (c * x * c⁻¹) :=
  CFSG.LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv (centConjEquiv c x) h

theorem zx_conj (c x : C) : zx (c * x * c⁻¹) = (zx x).map (MulAut.conj c).toMonoidHom := by
  ext w
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  have key : ∀ v : C, v ∈ cent (c * x * c⁻¹) ↔ c⁻¹ * v * c ∈ cent x := by
    intro v
    rw [cent_conj, mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · rintro ⟨hw, hwc, hw2⟩
    refine ⟨(key w).1 hw, fun d hd => ?_, ?_⟩
    · have hd' : c * d * c⁻¹ ∈ cent (c * x * c⁻¹) := by
        rw [key]
        simpa [mul_assoc] using hd
      have h := hwc _ hd'
      calc c⁻¹ * w * c * d = c⁻¹ * (w * (c * d * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * d * c⁻¹) * w) * c := by rw [h]
        _ = d * (c⁻¹ * w * c) := by group
    · calc c⁻¹ * w * c * (c⁻¹ * w * c) = c⁻¹ * (w * w) * c := by group
        _ = 1 := by rw [hw2]; group
  · rintro ⟨hw, hwc, hw2⟩
    refine ⟨(key w).2 hw, fun d hd => ?_, ?_⟩
    · have h := hwc _ ((key d).1 hd)
      calc w * d = c * ((c⁻¹ * w * c) * (c⁻¹ * d * c)) * c⁻¹ := by group
        _ = c * ((c⁻¹ * d * c) * (c⁻¹ * w * c)) * c⁻¹ := by rw [h]
        _ = d * w := by group
    · have h : c * (c⁻¹ * w * c * (c⁻¹ * w * c)) * c⁻¹ = 1 := by rw [hw2]; group
      calc w * w = c * (c⁻¹ * w * c * (c⁻¹ * w * c)) * c⁻¹ := by group
        _ = 1 := h

theorem card_zx_conj (c x : C) : Nat.card (zx (c * x * c⁻¹)) = Nat.card (zx x) := by
  rw [zx_conj, card_map_of_injective (MulAut.conj c).injective]

theorem zx_eq_of_centreData {x : C} {Z : Subgroup C} (h : CentreData x Z) : zx x = Z := by
  ext w
  constructor
  · rintro ⟨hw, hwc, hw2⟩
    exact h.centre_inv w hw hwc hw2
  · intro hw
    refine ⟨h.le_cent hw, fun c hc => h.commute w hw c hc, ?_⟩
    rw [← sq]
    exact h.elem.2 w hw

theorem mem_zx {x : C} (hx : x * x = 1) : x ∈ zx x :=
  ⟨mem_centralizer_singleton_iff.2 rfl, fun _ hc => (mem_centralizer_singleton_iff.1 hc).symm, hx⟩

end Conj

theorem map_oUpperTwo {P Q : Type*} [Group P] [Group Q] [Finite P] (f : P →* Q)
    (hker : Odd (Nat.card f.ker)) (M : Subgroup P) :
    (oUpperTwo M).map f = oUpperTwo (M.map f) := by
  rw [oUpperTwo, oUpperTwo, MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨m, ⟨hm, hmo⟩, rfl⟩
    exact ⟨⟨m, hm, rfl⟩, hmo.of_dvd_nat (orderOf_map_dvd f m)⟩
  · rintro ⟨⟨m, hm, rfl⟩, hco⟩
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    have h1 : m ^ orderOf (f m) ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
    have h2 : Odd (orderOf (m ^ orderOf (f m))) := RankTwoL3Even.odd_orderOf_of_mem hker h1
    have h3 : orderOf m ∣ orderOf (f m) * orderOf (m ^ orderOf (f m)) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hco.mul h2).of_dvd_nat h3

section Img

variable {G : Type} [Group G] {A : Subgroup G} {C : Type*} [Group C]

@[expose] def img (ψ : normalizer (A : Set G) →* MulAut C) (H : Subgroup G) : Subgroup C :=
  ((H.subgroupOf (normalizer (A : Set G))).map ψ).comap (MulAut.conj : C →* MulAut C)

@[expose] def ActsIn (ψ : normalizer (A : Set G) →* MulAut C) (T : Subgroup G) (U : Subgroup C) :
    Prop :=
  img ψ T ≤ U

variable {ψ : normalizer (A : Set G) →* MulAut C}

theorem mem_img {H : Subgroup G} {c : C} :
    c ∈ img ψ H ↔ ∃ h ∈ H, ∃ hN : h ∈ normalizer (A : Set G), ψ ⟨h, hN⟩ = MulAut.conj c := by
  constructor
  · rintro ⟨⟨h, hN⟩, hh, hc⟩
    exact ⟨h, hh, hN, hc⟩
  · rintro ⟨h, hh, hN, hc⟩
    exact ⟨⟨h, hN⟩, hh, hc⟩

theorem img_mono {H H' : Subgroup G} (h : H ≤ H') : img ψ H ≤ img ψ H' := by
  intro c hc
  obtain ⟨x, hx, hxN, hxc⟩ := mem_img.1 hc
  exact mem_img.2 ⟨x, h hx, hxN, hxc⟩

theorem actsIn_iff {T : Subgroup G} {U : Subgroup C} :
    ActsIn ψ T U ↔ ∀ u ∈ T, ∀ (huN : u ∈ normalizer (A : Set G)) (y : C),
      ψ ⟨u, huN⟩ = MulAut.conj y → y ∈ U := by
  constructor
  · intro h u hu huN y hy
    exact h (mem_img.2 ⟨u, hu, huN, hy⟩)
  · intro h c hc
    obtain ⟨u, hu, huN, hy⟩ := mem_img.1 hc
    exact h u hu huN c hy

variable (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)

@[expose] noncomputable def toC : ↥A →* C :=
  (MonoidHom.ofInjective (RankTwoHypIIY.conj_injective_of_center_eq_bot hZC)).symm.toMonoidHom.comp
    ((ψ.comp (inclusion (le_normalizer : A ≤ normalizer (A : Set G)))).codRestrict _
      fun a => hψ.map_mem a a.2)

theorem conj_toC (a : ↥A) :
    MulAut.conj (toC hZC hψ a) = ψ ⟨a, le_normalizer a.2⟩ := by
  have h := MonoidHom.apply_ofInjective_symm (RankTwoHypIIY.conj_injective_of_center_eq_bot hZC)
    (((ψ.comp (inclusion (le_normalizer : A ≤ normalizer (A : Set G)))).codRestrict _
      fun a => hψ.map_mem a a.2) a)
  exact h

theorem toC_eq_iff {a : ↥A} {c : C} :
    toC hZC hψ a = c ↔ ψ ⟨a, le_normalizer a.2⟩ = MulAut.conj c := by
  rw [← conj_toC hZC hψ a]
  exact (RankTwoHypIIY.conj_injective_of_center_eq_bot hZC).eq_iff.symm

theorem toC_surjective : Function.Surjective (toC hZC hψ) := by
  intro c
  obtain ⟨a, ha, hac⟩ := hψ.exists_eq (MulAut.conj c) ⟨c, rfl⟩
  exact ⟨⟨a, ha⟩, (toC_eq_iff hZC hψ).2 hac⟩

theorem mem_ker_toC {a : ↥A} : a ∈ (toC hZC hψ).ker ↔ (a : G) ∈ centralizer (A : Set G) := by
  rw [MonoidHom.mem_ker, toC_eq_iff, map_one]
  exact hψ.eq_one_iff _

theorem card_ker_toC : Nat.card (toC hZC hψ).ker = Nat.card (center A) := by
  rw [← RankTwoL3Even.card_inf_centralizer_eq]
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1, mem_inf.2 ⟨a.1.2, (mem_ker_toC hZC hψ).1 a.2⟩⟩
      invFun := fun b => ⟨⟨b.1, (mem_inf.1 b.2).1⟩, (mem_ker_toC hZC hψ).2 (mem_inf.1 b.2).2⟩
      left_inv := fun a => rfl
      right_inv := fun b => rfl }

theorem mem_img_iff_of_le {H : Subgroup G} (hHA : H ≤ A) {c : C} :
    c ∈ img ψ H ↔ c ∈ (H.subgroupOf A).map (toC hZC hψ) := by
  rw [mem_img]
  constructor
  · rintro ⟨h, hh, hN, hc⟩
    exact ⟨⟨h, hHA hh⟩, hh, (toC_eq_iff hZC hψ).2 hc⟩
  · rintro ⟨a, ha, hac⟩
    exact ⟨a, ha, le_normalizer a.2, (toC_eq_iff hZC hψ).1 hac⟩

theorem img_eq_map {H : Subgroup G} (hHA : H ≤ A) :
    img ψ H = (H.subgroupOf A).map (toC hZC hψ) := by
  ext c
  exact mem_img_iff_of_le hZC hψ hHA

theorem mem_of_toC_eq (hZA : Odd (Nat.card (center A))) {a b : ↥A} (ha : a * a = 1)
    (h : toC hZC hψ a = toC hZC hψ b) {Y : Subgroup G} (hb : (b : G) ∈ Y) : (a : G) ∈ Y := by
  set z := a⁻¹ * b with hzdef
  have hz : z ∈ (toC hZC hψ).ker := by
    rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hzodd : Odd (orderOf z) :=
    RankTwoL3Even.odd_orderOf_of_mem (by rw [card_ker_toC]; exact hZA) hz
  have hcomm : Commute a z := by
    have hzC := (mem_ker_toC hZC hψ).1 hz
    exact Subtype.ext (mem_centralizer_iff.1 hzC a a.2)
  obtain ⟨n, hn⟩ := hzodd
  have hb' : b = a * z := by rw [hzdef]; group
  have hpow : b ^ orderOf z = a := by
    rw [hb', hcomm.mul_pow, pow_orderOf_eq_one, mul_one, hn, pow_succ, pow_mul,
      show a ^ 2 = 1 by rw [sq]; exact ha, one_pow, one_mul]
  have : ((b ^ orderOf z : ↥A) : G) ∈ Y := by
    rw [Subgroup.coe_pow]
    exact pow_mem hb _
  rwa [hpow] at this

end Img

section Sec3

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}

theorem not_mem_centralizer (hc : Sec3 A R T g) (h32 : Lemma32) {t : G} (ht : t ∈ T)
    (ht1 : t ≠ 1) : t ∉ centralizer (A : Set G) := by
  intro htK
  have hg : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [normalizer_centralizer_eq hc.hyp.standard]
    exact hc.not_mem
  have hodd := (tightlyEmbedded_centralizer hc.hyp.standard).2 g hg
  refine ht1 (RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hodd (mem_inf.2 ⟨htK, hc.sylowT.le ht⟩)) (k := 1) ?_)
  rw [pow_one]
  exact (hc.elemT h32).2 t ht

theorem sec3_rightConjugate (hc : Sec3 A R T g) {a : G} (ha : a ∈ A) :
    Sec3 A R (rightConjugate T a) (g * a) := by
  refine ⟨hc.hyp, hc.sylowR, fun h => hc.not_mem ?_, ?_, ?_⟩
  · have := mul_mem h (inv_mem (le_normalizer ha))
    rwa [mul_inv_cancel_right] at this
  · have := AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT a
    rwa [rightConjugate_mul] at this
  · intro x hx
    rw [mem_rightConjugate_iff] at hx
    rw [mem_centralizer_iff]
    intro r hr
    have h1 : r * (a * x * a⁻¹) = a * x * a⁻¹ * r :=
      mem_centralizer_iff.1 (hc.le_centralizer hx) r hr
    have h2 : a * r = r * a := mem_centralizer_iff.1 (hc.sylowR.le hr) a ha
    have h3 : a⁻¹ * r * a = r := by rw [mul_assoc, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
    calc r * x = a⁻¹ * r * a * x := by rw [h3]
      _ = a⁻¹ * (r * (a * x * a⁻¹)) * a := by group
      _ = a⁻¹ * (a * x * a⁻¹ * r) * a := by rw [h1]
      _ = x * (a⁻¹ * r * a) := by group
      _ = x * r := by rw [h3]

variable (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit hZC in
theorem exists_conj_of_mem (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) {t : G} (ht : t ∈ T) (htN : t ∈ normalizer (A : Set G)) :
    ∃ x : C, ψ ⟨t, htN⟩ = MulAut.conj x := by
  obtain ⟨p, hp, htp⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨x, hx⟩ := hψ.map_mem p hp
  refine ⟨x, ?_⟩
  have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hp)⟩ = 1 :=
    (hψ.eq_one_iff _).2 (hc.sylowR.le htp)
  rw [psi_mul (inv_mem htN) (le_normalizer hp), psi_inv htN, inv_mul_eq_one] at h1
  rw [h1, hx]

theorem involution_of_conj (hc : Sec3 A R T g) (h32 : Lemma32) {t : G} (ht : t ∈ T)
    (htN : t ∈ normalizer (A : Set G)) {x : C} (hx : ψ ⟨t, htN⟩ = MulAut.conj x) :
    x * x = 1 ∧ (t ≠ 1 → x ≠ 1) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  refine ⟨hinj ?_, fun ht1 hx1 => ?_⟩
  · have h1 : (⟨t * t, mul_mem htN htN⟩ : normalizer (A : Set G)) = 1 :=
      Subtype.ext (show t * t = 1 by rw [← sq]; exact (hc.elemT h32).2 t ht)
    have h2 : ψ ⟨t * t, mul_mem htN htN⟩ = ψ ⟨t, htN⟩ * ψ ⟨t, htN⟩ := psi_mul htN htN
    rw [h1, map_one, hx, ← map_mul] at h2
    rw [map_one]
    exact h2.symm
  · rw [hx1, map_one] at hx
    exact not_mem_centralizer hc h32 ht ht1 ((hψ.eq_one_iff _).1 hx)

omit hZC in
theorem exists_pin (hc : Sec3 A R T g) {t : G} (ht : t ∈ T) (htN : t ∈ normalizer (A : Set G))
    {x y : C} (hx : ψ ⟨t, htN⟩ = MulAut.conj x) (hxy : IsConj y x) :
    ∃ a ∈ A, Sec3 A R (rightConjugate T a⁻¹) (g * a⁻¹) ∧ a * t * a⁻¹ ∈ rightConjugate T a⁻¹ ∧
      ∃ h : a * t * a⁻¹ ∈ normalizer (A : Set G), ψ ⟨a * t * a⁻¹, h⟩ = MulAut.conj y := by
  obtain ⟨c, hc'⟩ := isConj_iff.1 hxy
  obtain ⟨a, ha, haψ⟩ := hψ.exists_eq (MulAut.conj c⁻¹) ⟨c⁻¹, rfl⟩
  have haN := le_normalizer ha
  have hN : a * t * a⁻¹ ∈ normalizer (A : Set G) := mul_mem (mul_mem haN htN) (inv_mem haN)
  refine ⟨a, ha, sec3_rightConjugate hc (inv_mem ha), ?_, hN, ?_⟩
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht
  · have e : (⟨a * t * a⁻¹, hN⟩ : normalizer (A : Set G)) =
        ⟨a, haN⟩ * ⟨t, htN⟩ * ⟨a, haN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, haψ, hx, ← hc', ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

end Sec3

section Residual

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit [Finite G] in
theorem img_centralizer_eq (hZA : Odd (Nat.card (center A))) {t : G}
    (htN : t ∈ normalizer (A : Set G)) (ht2 : t ^ 2 = 1) {x : C}
    (hx : ψ ⟨t, htN⟩ = MulAut.conj x) :
    img ψ (A ⊓ centralizer ({t} : Set G)) = cent x := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  ext c
  rw [mem_img, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h, hh, hN, hc⟩
    obtain ⟨-, hht⟩ := mem_inf.1 hh
    have h1 : ψ ⟨h, hN⟩ * ψ ⟨t, htN⟩ = ψ ⟨t, htN⟩ * ψ ⟨h, hN⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.1 hht))
    rw [hc, hx, ← map_mul, ← map_mul] at h1
    exact hinj h1
  · intro hcx
    obtain ⟨a, ha, hat, haψ⟩ := exists_mem_commute_of_psi_commute hψ hZA htN ht2
      (x := MulAut.conj c) ⟨c, rfl⟩ (by rw [hx, ← map_mul, ← map_mul, hcx])
    exact ⟨a, mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 hat⟩, le_normalizer ha, haψ⟩

theorem eq_one_of_residualMem (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {t : G} (ht : t ∈ T) (htA : t ∈ A) {x : C}
    (hx : ψ ⟨t, le_normalizer htA⟩ = MulAut.conj x) (hres : ResidualMem x) : t = 1 := by
  classical
  by_contra ht1
  have ht2 : t ^ 2 = 1 := (hc.elemT h32).2 t ht
  have hker : Odd (Nat.card (toC hZC hψ).ker) := by rw [card_ker_toC]; exact hZA
  set f := toC hZC hψ with hfdef
  set M := A ⊓ centralizer ({t} : Set G) with hMdef
  have hMA : M ≤ A := inf_le_left
  set M' := M.subgroupOf A with hM'def
  have hM'map : M'.map f = cent x := by
    rw [← img_eq_map hZC hψ hMA, img_centralizer_eq hZC hψ hZA (le_normalizer htA) ht2 hx]
  set XA := oUpperTwo M ⊔ ⁅M, M⁆ with hXAdef
  set X' := oUpperTwo M' ⊔ ⁅M', M'⁆ with hX'def
  have hsub : Odd (Nat.card A.subtype.ker) := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact odd_one
  have hXA : XA = X'.map A.subtype := by
    rw [hXAdef, hX'def, Subgroup.map_sup, Subgroup.map_commutator,
      map_oUpperTwo A.subtype hsub M', hM'def, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hMA]
  have hXAA : XA ≤ A := by
    rw [hXA]
    exact map_subtype_le _
  set XC := oUpperTwo (cent x) ⊔ ⁅cent x, cent x⁆ with hXCdef
  have hXC : X'.map f = XC := by
    rw [hX'def, Subgroup.map_sup, Subgroup.map_commutator, map_oUpperTwo f hker, hM'map]
  have hX'eq : XA.subgroupOf A = X' := by
    rw [hXA]
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective X'
  have hmem : t ∈ admResidual XA := by
    rw [admResidual, Subgroup.mem_sInf]
    rintro Y ⟨hYX, hN, hsolv, hab⟩
    set YC := (Y.subgroupOf A).map f with hYCdef
    have hYC : YC ≤ XC := by
      rw [← hXC, ← hX'eq]
      refine map_mono fun a ha => ?_
      rw [mem_subgroupOf] at ha ⊢
      exact hYX ha
    have hNC : (YC.subgroupOf XC).Normal := by
      refine ⟨fun n hn k => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      have hk : (k : C) ∈ X'.map f := by rw [hXC]; exact k.2
      obtain ⟨a, haX, hak⟩ := hk
      obtain ⟨y, hyY, hyn⟩ := hn
      have haXA : (a : G) ∈ XA := by
        rw [← hX'eq] at haX
        exact haX
      have hyXA : (y : G) ∈ XA := hYX hyY
      have h1 := hN.conj_mem ⟨y, hyXA⟩ hyY ⟨a, haXA⟩
      rw [mem_subgroupOf] at h1
      refine ⟨a * y * a⁻¹, h1, ?_⟩
      simp only [map_mul, map_inv, hak, hyn, Subgroup.coe_mul, Subgroup.coe_inv]
    have hφ : ∀ a : ↥XA, f (inclusion hXAA a) ∈ XC := by
      intro a
      have ha : inclusion hXAA a ∈ X' := by
        rw [← hX'eq, mem_subgroupOf]
        exact a.2
      rw [← hXC]
      exact ⟨inclusion hXAA a, ha, rfl⟩
    let φ : ↥XA →* ↥XC := (f.comp (inclusion hXAA)).codRestrict XC hφ
    have hφs : Function.Surjective φ := by
      rintro ⟨k, hk⟩
      rw [← hXC] at hk
      obtain ⟨a, haX, rfl⟩ := hk
      have haX' : a ∈ X' := haX
      rw [← hX'eq, mem_subgroupOf] at haX'
      exact ⟨⟨a, haX'⟩, Subtype.ext rfl⟩
    have hle : Y.subgroupOf XA ≤ (YC.subgroupOf XC).comap φ := by
      intro u hu
      have hu' : inclusion hXAA u ∈ Y.subgroupOf A := by
        rw [mem_subgroupOf]
        exact hu
      show ((φ u : ↥XC) : C) ∈ YC
      exact ⟨inclusion hXAA u, hu', rfl⟩
    let Φ := QuotientGroup.map (Y.subgroupOf XA) (YC.subgroupOf XC) φ hle
    have hΦs : Function.Surjective Φ :=
      QuotientGroup.map_surjective_of_surjective (Y.subgroupOf XA) (YC.subgroupOf XC) φ
        ((QuotientGroup.mk_surjective).comp hφs) hle
    have hsolvC : Lemma39.SolvAbSylow (XC ⧸ YC.subgroupOf XC) :=
      Lemma39.SolvAbSylow.of_surjective Φ hΦs ⟨hsolv, hab⟩
    have hxY : x ∈ YC := Lemma39.admResidual_le hYC hsolvC hres
    obtain ⟨b, hb, hbx⟩ := hxY
    have hb' : (b : G) ∈ Y := hb
    refine mem_of_toC_eq hZC hψ hZA (a := ⟨t, htA⟩) (Subtype.ext ?_) ?_ hb'
    · rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
      exact ht2
    · rw [hbx, toC_eq_iff]
      exact hx
  have htAg := (Lemma39.lemma39_one h4 h32 h34 hc.hyp hc.sylowT ht ht1 hOut).1 hmem
  have htK : t ∈ rightConjugate (centralizer (A : Set G)) g := hc.sylowT.le ht
  rw [mem_rightConjugate_iff] at htAg htK
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hodd : Odd (orderOf (g * t * g⁻¹)) :=
    RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨htAg, htK⟩)
  have h1 : g * t * g⁻¹ = 1 := RankTwoL3Even.eq_one_of_odd_of_pow_two hodd (k := 1)
    (by rw [pow_one, conj_pow, ht2, mul_one, mul_inv_cancel])
  exact ht1 (by
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)

theorem inf_eq_bot_of_reps (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y) : T ⊓ A = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  rw [mem_bot]
  obtain ⟨htT, htA⟩ := mem_inf.1 ht
  by_contra ht1
  have htN := le_normalizer htA
  obtain ⟨x, hx⟩ := exists_conj_of_mem hψ hc h32 h4 h34 htT htN
  obtain ⟨hx2, hx1⟩ := involution_of_conj hZC hψ hc h32 htT htN hx
  obtain ⟨y, hy, hyx⟩ := hcover x hx2 (hx1 ht1)
  obtain ⟨a, ha, hc', hmem, hN, hψa⟩ := exists_pin hψ hc htT htN hx hyx
  have haA : a * t * a⁻¹ ∈ A := mul_mem (mul_mem ha htA) (inv_mem ha)
  have h1 := eq_one_of_residualMem hZC hψ h4 h32 h34 hc' hOut hZA hmem haA hψa (hres y hy)
  apply ht1
  calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
    _ = 1 := by rw [h1]; group

end Residual

section CharTwo

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

theorem exists_pow_mem_center (hZA : Odd (Nat.card (center A))) {t : G}
    (htN : t ∈ normalizer (A : Set G)) (ht2 : t ^ 2 = 1) {x : C}
    (hx : ψ ⟨t, htN⟩ = MulAut.conj x) (hchar : CharTwo x) {a : G}
    (ha : a ∈ CFSG.inSubgroup CFSG.generalizedFitting (A ⊓ centralizer ({t} : Set G))) :
    ∃ k : ℕ, a ^ 2 ^ k ∈ (center A).map A.subtype := by
  have himg := img_centralizer_eq hZC hψ hZA htN ht2 hx
  have hle : A ⊓ centralizer ({t} : Set G) ≤ A := inf_le_left
  have hmem : ∀ b : ↥(A ⊓ centralizer ({t} : Set G)), toC hZC hψ (inclusion hle b) ∈ cent x := by
    intro b
    rw [← himg, img_eq_map hZC hψ hle]
    exact ⟨inclusion hle b, b.2, rfl⟩
  let φ : ↥(A ⊓ centralizer ({t} : Set G)) →* ↥(cent x) :=
    ((toC hZC hψ).comp (inclusion hle)).codRestrict _ hmem
  have hφs : Function.Surjective φ := by
    rintro ⟨c, hc'⟩
    rw [← himg, img_eq_map hZC hψ hle] at hc'
    obtain ⟨b, hb, rfl⟩ := hc'
    exact ⟨⟨b, hb⟩, Subtype.ext rfl⟩
  have hker : φ.ker ≤ center ↥(A ⊓ centralizer ({t} : Set G)) := by
    intro b hb
    have h1 : inclusion hle b ∈ (toC hZC hψ).ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hb)
    have h2 := (mem_ker_toC hZC hψ).1 h1
    rw [mem_center_iff]
    intro b'
    exact Subtype.ext (mem_centralizer_iff.1 h2 b' (hle b'.2))
  obtain ⟨b, hb, rfl⟩ := ha
  obtain ⟨k, hk⟩ := RankTwoChar2C0.exists_two_pow_mem_ker φ hφs hker hchar hb
  refine ⟨k, ?_⟩
  rw [RankTwoL3Even.map_center_eq_inf_centralizer]
  have h1 : inclusion hle (b ^ 2 ^ k) ∈ (toC hZC hψ).ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
  refine mem_inf.2 ⟨?_, (mem_ker_toC hZC hψ).1 h1⟩
  rw [Subgroup.coe_subtype, ← Subgroup.coe_pow]
  exact (b ^ 2 ^ k).2.1

theorem actsIn_zx (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) (hTA : T ⊓ A = ⊥)
    (hchar : ∀ t ∈ T, t ≠ 1 → ∀ (htN : t ∈ normalizer (A : Set G)) (x : C),
      ψ ⟨t, htN⟩ = MulAut.conj x → CharTwo x)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G)) {x₀ : C}
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) : ActsIn ψ T (zx x₀) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hTel := hc.elemT h32
  have hF : ∀ t ∈ T, t ≠ 1 → ∀ a ∈ CFSG.inSubgroup CFSG.generalizedFitting
      (A ⊓ centralizer ({t} : Set G)), ∃ k : ℕ, a ^ 2 ^ k ∈ (center A).map A.subtype := by
    intro t ht ht1 a ha
    have htN := hc.le_normalizer ht
    obtain ⟨y, hy⟩ := exists_conj_of_mem hψ hc h32 h4 h34 ht htN
    exact exists_pow_mem_center hZC hψ hZA htN (hTel.2 t ht) hy (hchar t ht ht1 htN y hy) ha
  have hZT : (center A).map A.subtype ≤ centralizer (T : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨p, hpA, hp⟩ := hc.exists_aPart h32 h4 h34 ht
    have h1 : Commute (z : G) p := (congrArg Subtype.val (mem_center_iff.1 hz ⟨p, hpA⟩)).symm
    have h2 : Commute (z : G) (t⁻¹ * p) := mem_centralizer_iff.1 (hc.sylowR.le hp) z z.2
    have ht' : t = p * (t⁻¹ * p)⁻¹ := by group
    rw [ht']
    exact (h1.mul_right h2.inv_right).symm.eq
  have hX := sylowInTightTwoNilpotent_of_hyp31 h32 h4 h34 hc.hyp hc.sylowT A
  have h27 := lemma27 hTel (by rw [hc.card_eq]; exact hc.four_le) hc.le_normalizer hX hZT hF
    (by rw [inf_comm]; exact hTA)
  have hcomm := commutator_eq_bot_iff_le_centralizer.1 (h27 t₀ ht₀ ht₀1)
  have ht₀2 : t₀ ^ 2 = 1 := hTel.2 t₀ ht₀
  have himg := img_centralizer_eq hZC hψ hZA ht₀N ht₀2 hx₀
  rw [actsIn_iff]
  intro s hs hsN c hc'
  refine ⟨?_, fun d hd => ?_, (involution_of_conj hZC hψ hc h32 hs hsN hc').1⟩
  · rw [mem_centralizer_singleton_iff]
    have h1 : s * t₀ = t₀ * s := congrArg Subtype.val (hTel.1.is_comm.comm ⟨s, hs⟩ ⟨t₀, ht₀⟩)
    have h2 : ψ ⟨s, hsN⟩ * ψ ⟨t₀, ht₀N⟩ = ψ ⟨t₀, ht₀N⟩ * ψ ⟨s, hsN⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h1)
    rw [hc', hx₀, ← map_mul, ← map_mul] at h2
    exact hinj h2
  · rw [← himg, mem_img] at hd
    obtain ⟨a, ha, haN, had⟩ := hd
    have h1 : a * s = s * a := mem_centralizer_iff.1 (hcomm ha) s hs |>.symm
    have h2 : ψ ⟨s, hsN⟩ * ψ ⟨a, haN⟩ = ψ ⟨a, haN⟩ * ψ ⟨s, hsN⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h1.symm)
    rw [hc', had, ← map_mul, ← map_mul] at h2
    exact hinj h2

theorem card_le_of_actsIn [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {U : Subgroup C} (hT : ActsIn ψ T U) : Nat.card T ≤ Nat.card U := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have key : ∀ s : T, ∃ c : U, ψ ⟨s, hc.le_normalizer s.2⟩ = MulAut.conj (c : C) := by
    intro s
    obtain ⟨c, hc'⟩ := exists_conj_of_mem hψ hc h32 h4 h34 s.2 (hc.le_normalizer s.2)
    exact ⟨⟨c, (actsIn_iff.1 hT) s s.2 _ c hc'⟩, hc'⟩
  choose F hF using key
  refine Nat.card_le_card_of_injective F fun s s' h => ?_
  have hsN := hc.le_normalizer s.2
  have hs'N := hc.le_normalizer s'.2
  have h1 : ψ ⟨(s : G)⁻¹ * s', mul_mem (inv_mem hsN) hs'N⟩ = 1 := by
    rw [psi_mul (inv_mem hsN) hs'N, psi_inv hsN, hF s, hF s', h, inv_mul_cancel]
  have h2 := (hψ.eq_one_iff _).1 h1
  by_contra hne
  refine not_mem_centralizer hc h32 (mul_mem (inv_mem s.2) s'.2) ?_ h2
  intro h3
  exact hne (Subtype.ext (inv_mul_eq_one.1 h3))

end CharTwo

end CFSG.ComponentClassification.RankTwoExceptional.Exc
