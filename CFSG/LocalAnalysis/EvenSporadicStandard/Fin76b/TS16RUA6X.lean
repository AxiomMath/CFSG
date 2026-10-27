module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Wr
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Def

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

open Subgroup

@[expose] noncomputable def cx₁ (x : Yaut) : MulAut A6 :=
  open Classical in if h : x ∈ Yone then coord₁ ⟨x, h⟩ else 1

@[expose] noncomputable def cx₂ (x : Yaut) : MulAut A6 :=
  open Classical in if h : x ∈ Yone then coord₂ ⟨x, h⟩ else 1

theorem cx₁_eq {x : Yaut} (hx : x ∈ Yone) : cx₁ x = coord₁ ⟨x, hx⟩ := by
  unfold cx₁
  exact dif_pos hx

theorem cx₂_eq {x : Yaut} (hx : x ∈ Yone) : cx₂ x = coord₂ ⟨x, hx⟩ := by
  unfold cx₂
  exact dif_pos hx

theorem cx_apply {x : Yaut} (hx : x ∈ Yone) (a b : A6) : x (a, b) = (cx₁ x a, cx₂ x b) := by
  rw [cx₁_eq hx, cx₂_eq hx]
  exact coord_apply ⟨x, hx⟩ a b

theorem cx₁_mul {x y : Yaut} (hx : x ∈ Yone) (hy : y ∈ Yone) :
    cx₁ (x * y) = cx₁ x * cx₁ y := by
  rw [cx₁_eq (mul_mem hx hy), cx₁_eq hx, cx₁_eq hy]
  exact map_mul coord₁ ⟨x, hx⟩ ⟨y, hy⟩

theorem cx₂_mul {x y : Yaut} (hx : x ∈ Yone) (hy : y ∈ Yone) :
    cx₂ (x * y) = cx₂ x * cx₂ y := by
  rw [cx₂_eq (mul_mem hx hy), cx₂_eq hx, cx₂_eq hy]
  exact map_mul coord₂ ⟨x, hx⟩ ⟨y, hy⟩

theorem eq_one_of_cx {x : Yaut} (hx : x ∈ Yone) (h₁ : cx₁ x = 1) (h₂ : cx₂ x = 1) : x = 1 := by
  refine MulEquiv.ext fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [cx_apply hx, h₁, h₂]
  rfl

theorem card_A6 : Nat.card A6 = 360 := CFSG.EvenSporadicStandard.M24Std.DRes.card_alt6

theorem conj_prod_injective : Function.Injective (MulAut.conj : A6 × A6 →* Yaut) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a, b⟩ h
  rw [MonoidHom.mem_ker] at h
  have ha : ∀ x : A6, a * x = x * a := fun x => by
    have := congrArg (fun τ : Yaut => (τ (x, 1)).1) h
    simp only [MulAut.conj_apply, Prod.mk_mul_mk, Prod.inv_mk, MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 (by simpa using this)
  have hb : ∀ y : A6, b * y = y * b := fun y => by
    have := congrArg (fun τ : Yaut => (τ (1, y)).2) h
    simp only [MulAut.conj_apply, Prod.mk_mul_mk, Prod.inv_mk, MulAut.one_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 (by simpa using this)
  have ha1 := CFSG.EvenSporadicStandard.M24Std.DRes.alt6_central ha
  have hb1 := CFSG.EvenSporadicStandard.M24Std.DRes.alt6_central hb
  rw [ha1, hb1]
  exact Subgroup.one_mem _

theorem exists_ne_one_of_card {Ab : Subgroup Yaut} (eAb : ↥Ab ≃* A6) : ∃ x ∈ Ab, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Subsingleton ↥Ab :=
    ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
  have h1 : Nat.card ↥Ab = 1 := Nat.card_of_subsingleton 1
  rw [Nat.card_congr eAb.toEquiv, card_A6] at h1
  omega

theorem sq_of_cent_image (hA : A6AutFacts) {Ab : Subgroup Yaut} (eAb : ↥Ab ≃* A6)
    (p : ↥Ab →* MulAut A6) (hp : Function.Injective p) {F : Subgroup Yaut} (hFAb : F ≤ Ab)
    (hF8 : Nat.card ↥F = 8) {w : MulAut A6}
    (hw : ∀ (f : Yaut) (hf : f ∈ F), w * p ⟨f, hFAb hf⟩ = p ⟨f, hFAb hf⟩ * w) : w * w = 1 := by
  refine hA.sq_A6 p.range ⟨(MonoidHom.ofInjective hp).symm.trans eAb⟩ ((F.subgroupOf Ab).map p)
    (Subgroup.map_le_range p _) ?_ w ?_
  · rw [Subgroup.card_map_of_injective hp, ← hF8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFAb).toEquiv
  · rintro _ ⟨⟨f, hfAb⟩, hf, rfl⟩
    exact hw f hf

theorem caseI (hA : A6AutFacts) {Ab : Subgroup Yaut} (hAb1 : Ab ≤ Yone) (eAb : ↥Ab ≃* A6)
    (hk₁ : ∀ x ∈ Ab, cx₁ x = 1 → x = 1) (hk₂ : ∀ x ∈ Ab, cx₂ x = 1 → x = 1)
    {F : Subgroup Yaut} (hFAb : F ≤ Ab) (hF8 : Nat.card ↥F = 8)
    {s : Yaut} (hs8 : orderOf s = 8) (hsF : ∀ f ∈ F, s * f = f * s) : False := by
  let p₁ : ↥Ab →* MulAut A6 := coord₁.comp (Subgroup.inclusion hAb1)
  let p₂ : ↥Ab →* MulAut A6 := coord₂.comp (Subgroup.inclusion hAb1)
  have hp₁ : Function.Injective p₁ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have : cx₁ (x : Yaut) = 1 := by rw [cx₁_eq (hAb1 x.2)]; exact hx
    exact hk₁ x x.2 this
  have hp₂ : Function.Injective p₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have : cx₂ (x : Yaut) = 1 := by rw [cx₂_eq (hAb1 x.2)]; exact hx
    exact hk₂ x x.2 this
  have hs2 : s * s ∈ Yone := sq_mem_Yone s
  have hFY : ∀ f ∈ F, f ∈ Yone := fun f hf => hAb1 (hFAb hf)
  have hcomm : ∀ f ∈ F, (s * s) * f = f * (s * s) := fun f hf => by
    calc s * s * f = s * (s * f) := by rw [mul_assoc]
      _ = s * (f * s) := by rw [hsF f hf]
      _ = (s * f) * s := by rw [mul_assoc]
      _ = (f * s) * s := by rw [hsF f hf]
      _ = f * (s * s) := by rw [mul_assoc]
  have hw₁ : cx₁ (s * s) * cx₁ (s * s) = 1 := by
    refine sq_of_cent_image hA eAb p₁ hp₁ hFAb hF8 fun f hf => ?_
    have := congrArg cx₁ (hcomm f hf)
    rw [cx₁_mul hs2 (hFY f hf), cx₁_mul (hFY f hf) hs2] at this
    have e : p₁ ⟨f, hFAb hf⟩ = cx₁ f := (cx₁_eq (hFY f hf)).symm
    rw [e]
    exact this
  have hw₂ : cx₂ (s * s) * cx₂ (s * s) = 1 := by
    refine sq_of_cent_image hA eAb p₂ hp₂ hFAb hF8 fun f hf => ?_
    have := congrArg cx₂ (hcomm f hf)
    rw [cx₂_mul hs2 (hFY f hf), cx₂_mul (hFY f hf) hs2] at this
    have e : p₂ ⟨f, hFAb hf⟩ = cx₂ f := (cx₂_eq (hFY f hf)).symm
    rw [e]
    exact this
  have hs4 : s * s * (s * s) = 1 := by
    refine eq_one_of_cx (mul_mem hs2 hs2) ?_ ?_
    · rw [cx₁_mul hs2 hs2]; exact hw₁
    · rw [cx₂_mul hs2 hs2]; exact hw₂
  have hpow : s ^ 4 = 1 := by
    calc s ^ 4 = s * s * (s * s) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := hs4
  have := orderOf_dvd_of_pow_eq_one hpow
  rw [hs8] at this
  omega

theorem caseII (hA : A6AutFacts) (X : Subgroup Yaut)
    (hinn : ∀ a b : A6, (MulAut.conj (a, b) : Yaut) ∈ X) {z : Yaut} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {Ab : Subgroup Yaut} (hAb1 : Ab ≤ Yone) (eAb : ↥Ab ≃* A6)
    (hAbz : ∀ x ∈ Ab, x * z = z * x)
    (hcz : Nat.card ↥(X ⊓ centralizer ({z} : Set Yaut)) = 1440)
    (hk₁ : ∀ x ∈ Ab, cx₁ x = 1 → x = 1) (hk₂ : ∀ x ∈ Ab, cx₂ x = 1) : False := by
  let p₁ : ↥Ab →* MulAut A6 := coord₁.comp (Subgroup.inclusion hAb1)
  have hp₁ : Function.Injective p₁ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have : cx₁ (x : Yaut) = 1 := by rw [cx₁_eq (hAb1 x.2)]; exact hx
    exact hk₁ x x.2 this
  by_cases hzY : z ∈ Yone
  · obtain ⟨ζ₁, ζ₂, hζ⟩ := mem_Yone.1 hzY
    have hcomm1 : ∀ x ∈ Ab, cx₁ x * ζ₁ = ζ₁ * cx₁ x := by
      intro x hx'
      have hx := hAb1 hx'
      refine MulEquiv.ext fun a => ?_
      have h := congrArg (fun τ : Yaut => (τ (a, 1)).1) (hAbz x hx')
      simp only [MulAut.mul_apply, hζ, cx_apply hx, map_one] at h
      exact h
    have hζ1 : ζ₁ = 1 := by
      refine hA.cent_A6 p₁.range ⟨(MonoidHom.ofInjective hp₁).symm.trans eAb⟩ ζ₁ ?_
      rintro _ ⟨x, rfl⟩
      have e : p₁ x = cx₁ (x : Yaut) := (cx₁_eq (hAb1 x.2)).symm
      rw [e]
      exact (hcomm1 x x.2).symm
    have hζ2sq : ζ₂ * ζ₂ = 1 := by
      refine MulEquiv.ext fun b => ?_
      have h := congrArg (fun τ : Yaut => (τ (1, b)).2) hz2
      simp only [MulAut.mul_apply, hζ, map_one, MulAut.one_apply] at h
      exact h
    have hζ2ne : ζ₂ ≠ 1 := by
      intro h
      apply hz1
      refine MulEquiv.ext fun p => ?_
      obtain ⟨a, b⟩ := p
      rw [hζ, hζ1, h]
      rfl
    have h5 := hA.fix_invol ζ₂ hζ2sq hζ2ne
    let φ : A6 × ↥(fixSub ζ₂) →* Yaut :=
      (MulAut.conj : A6 × A6 →* Yaut).comp
        (MonoidHom.prodMap (MonoidHom.id A6) (fixSub ζ₂).subtype)
    have hφinj : Function.Injective φ := by
      refine conj_prod_injective.comp ?_
      intro p q h
      exact Prod.ext (Prod.ext_iff.1 h).1 (Subtype.ext (Prod.ext_iff.1 h).2)
    have hcardR : Nat.card ↥φ.range = 360 * Nat.card ↥(fixSub ζ₂) := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, card_A6]
    have hle : φ.range ≤ X ⊓ centralizer ({z} : Set Yaut) := by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      refine ⟨hinn a b.1, mem_centralizer_singleton_iff.2 ?_⟩
      refine MulEquiv.ext fun p => ?_
      obtain ⟨x, y⟩ := p
      have hb : ζ₂ b.1 = b.1 := b.2
      show (MulAut.conj (a, b.1) * z) (x, y) = (z * MulAut.conj (a, b.1)) (x, y)
      simp only [MulAut.mul_apply, MulAut.conj_apply, Prod.mk_mul_mk, Prod.inv_mk, hζ, hζ1,
        MulAut.one_apply, map_mul, map_inv, hb]
    have h5' : 5 ≤ Nat.card ↥(fixSub ζ₂) := h5
    have hcard' : 360 * Nat.card ↥(fixSub ζ₂) ≤ 1440 := by
      have := Subgroup.card_le_of_le hle
      rw [hcz, hcardR] at this
      exact this
    omega
  · obtain ⟨g₁, g₂, hg⟩ := exists_swap_of_not_mem_Yone hzY
    obtain ⟨x, hx', hx1⟩ := exists_ne_one_of_card eAb
    apply hx1
    have hx := hAb1 hx'
    have hc1 : cx₁ x = 1 := by
      refine MulEquiv.ext fun c => ?_
      have h := congrArg (fun τ : Yaut => (τ (1, g₁.symm c)).1) (hAbz x hx')
      simp only [MulAut.mul_apply, hg, cx_apply hx, hk₂ x hx', map_one, MulAut.one_apply,
        MulEquiv.apply_symm_apply] at h
      exact h
    exact eq_one_of_cx hx hc1 (hk₂ x hx')

theorem caseII' (hA : A6AutFacts) (X : Subgroup Yaut)
    (hinn : ∀ a b : A6, (MulAut.conj (a, b) : Yaut) ∈ X) {z : Yaut} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {Ab : Subgroup Yaut} (hAb1 : Ab ≤ Yone) (eAb : ↥Ab ≃* A6)
    (hAbz : ∀ x ∈ Ab, x * z = z * x)
    (hcz : Nat.card ↥(X ⊓ centralizer ({z} : Set Yaut)) = 1440)
    (hk₁ : ∀ x ∈ Ab, cx₁ x = 1) (hk₂ : ∀ x ∈ Ab, cx₂ x = 1 → x = 1) : False := by
  let p₂ : ↥Ab →* MulAut A6 := coord₂.comp (Subgroup.inclusion hAb1)
  have hp₂ : Function.Injective p₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have : cx₂ (x : Yaut) = 1 := by rw [cx₂_eq (hAb1 x.2)]; exact hx
    exact hk₂ x x.2 this
  by_cases hzY : z ∈ Yone
  · obtain ⟨ζ₁, ζ₂, hζ⟩ := mem_Yone.1 hzY
    have hcomm2 : ∀ x ∈ Ab, cx₂ x * ζ₂ = ζ₂ * cx₂ x := by
      intro x hx'
      have hx := hAb1 hx'
      refine MulEquiv.ext fun b => ?_
      have h := congrArg (fun τ : Yaut => (τ (1, b)).2) (hAbz x hx')
      simp only [MulAut.mul_apply, hζ, cx_apply hx, map_one] at h
      exact h
    have hζ2 : ζ₂ = 1 := by
      refine hA.cent_A6 p₂.range ⟨(MonoidHom.ofInjective hp₂).symm.trans eAb⟩ ζ₂ ?_
      rintro _ ⟨x, rfl⟩
      have e : p₂ x = cx₂ (x : Yaut) := (cx₂_eq (hAb1 x.2)).symm
      rw [e]
      exact (hcomm2 x x.2).symm
    have hζ1sq : ζ₁ * ζ₁ = 1 := by
      refine MulEquiv.ext fun a => ?_
      have h := congrArg (fun τ : Yaut => (τ (a, 1)).1) hz2
      simp only [MulAut.mul_apply, hζ, map_one, MulAut.one_apply] at h
      exact h
    have hζ1ne : ζ₁ ≠ 1 := by
      intro h
      apply hz1
      refine MulEquiv.ext fun p => ?_
      obtain ⟨a, b⟩ := p
      rw [hζ, hζ2, h]
      rfl
    have h5 := hA.fix_invol ζ₁ hζ1sq hζ1ne
    let φ : ↥(fixSub ζ₁) × A6 →* Yaut :=
      (MulAut.conj : A6 × A6 →* Yaut).comp
        (MonoidHom.prodMap (fixSub ζ₁).subtype (MonoidHom.id A6))
    have hφinj : Function.Injective φ := by
      refine conj_prod_injective.comp ?_
      intro p q h
      exact Prod.ext (Subtype.ext (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
    have hcardR : Nat.card ↥φ.range = Nat.card ↥(fixSub ζ₁) * 360 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, card_A6]
    have hle : φ.range ≤ X ⊓ centralizer ({z} : Set Yaut) := by
      rintro _ ⟨⟨b, a⟩, rfl⟩
      refine ⟨hinn b.1 a, mem_centralizer_singleton_iff.2 ?_⟩
      refine MulEquiv.ext fun p => ?_
      obtain ⟨x, y⟩ := p
      have hb : ζ₁ b.1 = b.1 := b.2
      show (MulAut.conj (b.1, a) * z) (x, y) = (z * MulAut.conj (b.1, a)) (x, y)
      simp only [MulAut.mul_apply, MulAut.conj_apply, Prod.mk_mul_mk, Prod.inv_mk, hζ, hζ2,
        MulAut.one_apply, map_mul, map_inv, hb]
    have h5' : 5 ≤ Nat.card ↥(fixSub ζ₁) := h5
    have hcard' : Nat.card ↥(fixSub ζ₁) * 360 ≤ 1440 := by
      have := Subgroup.card_le_of_le hle
      rw [hcz, hcardR] at this
      exact this
    omega
  · obtain ⟨g₁, g₂, hg⟩ := exists_swap_of_not_mem_Yone hzY
    obtain ⟨x, hx', hx1⟩ := exists_ne_one_of_card eAb
    apply hx1
    have hx := hAb1 hx'
    have hc2 : cx₂ x = 1 := by
      refine MulEquiv.ext fun c => ?_
      have h := congrArg (fun τ : Yaut => (τ (g₂.symm c, 1)).2) (hAbz x hx')
      simp only [MulAut.mul_apply, hg, cx_apply hx, hk₁ x hx', map_one, MulAut.one_apply,
        MulEquiv.apply_symm_apply] at h
      exact h
    exact hk₂ x hx' hc2

theorem a6x_aut (hA : A6AutFacts) (X : Subgroup Yaut)
    (hinn : ∀ a b : A6, (MulAut.conj (a, b) : Yaut) ∈ X) {z : Yaut} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) {Ab : Subgroup Yaut} (eAb : ↥Ab ≃* A6) (hAbz : ∀ x ∈ Ab, x * z = z * x)
    (hcz : Nat.card ↥(X ⊓ centralizer ({z} : Set Yaut)) = 1440)
    {F : Subgroup Yaut} (hFAb : F ≤ Ab) (hF8 : Nat.card ↥F = 8)
    {s : Yaut} (hs8 : orderOf s = 8) (hsF : ∀ f ∈ F, s * f = f * s) : False := by
  have hAb1 : Ab ≤ Yone := le_Yone_of_simple eAb
  let p₁ : ↥Ab →* MulAut A6 := coord₁.comp (Subgroup.inclusion hAb1)
  let p₂ : ↥Ab →* MulAut A6 := coord₂.comp (Subgroup.inclusion hAb1)
  haveI : IsSimpleGroup A6 := CFSG.EvenSporadicStandard.M24Std.DRes.alt6_simple
  haveI : IsSimpleGroup ↥Ab := eAb.isSimpleGroup
  have hker₁ : ∀ x (hx : x ∈ Ab), cx₁ x = 1 ↔ (⟨x, hx⟩ : ↥Ab) ∈ p₁.ker := fun x hx => by
    rw [MonoidHom.mem_ker, cx₁_eq (hAb1 hx)]
    rfl
  have hker₂ : ∀ x (hx : x ∈ Ab), cx₂ x = 1 ↔ (⟨x, hx⟩ : ↥Ab) ∈ p₂.ker := fun x hx => by
    rw [MonoidHom.mem_ker, cx₂_eq (hAb1 hx)]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p₁.ker with h1 | h1 <;>
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal p₂.ker with h2 | h2
  · refine caseI hA hAb1 eAb ?_ ?_ hFAb hF8 hs8 hsF
    · intro x hx h
      have hm : (⟨x, hx⟩ : ↥Ab) ∈ p₁.ker := (hker₁ x hx).1 h
      rw [h1, Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
    · intro x hx h
      have hm : (⟨x, hx⟩ : ↥Ab) ∈ p₂.ker := (hker₂ x hx).1 h
      rw [h2, Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
  · refine caseII hA X hinn hz2 hz1 hAb1 eAb hAbz hcz ?_ ?_
    · intro x hx h
      have hm : (⟨x, hx⟩ : ↥Ab) ∈ p₁.ker := (hker₁ x hx).1 h
      rw [h1, Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
    · intro x hx
      exact (hker₂ x hx).2 (by rw [h2]; exact Subgroup.mem_top _)
  · refine caseII' hA X hinn hz2 hz1 hAb1 eAb hAbz hcz ?_ ?_
    · intro x hx
      exact (hker₁ x hx).2 (by rw [h1]; exact Subgroup.mem_top _)
    · intro x hx h
      have hm : (⟨x, hx⟩ : ↥Ab) ∈ p₂.ker := (hker₂ x hx).1 h
      rw [h2, Subgroup.mem_bot] at hm
      exact congrArg Subtype.val hm
  · obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card eAb
    apply hx1
    refine eq_one_of_cx (hAb1 hx) ?_ ?_
    · exact (hker₁ x hx).2 (by rw [h1]; exact Subgroup.mem_top _)
    · exact (hker₂ x hx).2 (by rw [h2]; exact Subgroup.mem_top _)

section Transfer

variable {X : Type} [Group X]

theorem kappa_injective (N : Subgroup X) [N.Normal] (e : ↥N ≃* A6 × A6)
    (hC : centralizer (N : Set X) = ⊥) : Function.Injective (TS8Wr.kappa N e) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (MulAut.conjNormal g : MulAut N) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    exact hg
  have hmem : g ∈ centralizer (N : Set X) := by
    rw [mem_centralizer_iff]
    intro n hn
    have h2 := congrArg (fun γ : MulAut N => (γ ⟨n, hn⟩ : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [hC] at hmem
  exact mem_bot.1 hmem

theorem kappa_inner (N : Subgroup X) [N.Normal] (e : ↥N ≃* A6 × A6) (n : ↥N) :
    TS8Wr.kappa N e (n : X) = MulAut.conj (e n) := by
  refine MulEquiv.ext fun p => ?_
  show e ((MulAut.conjNormal (n : X) : MulAut N) (e.symm p)) = (MulAut.conj (e n)) p
  have h : (MulAut.conjNormal (n : X) : MulAut N) (e.symm p) = n * e.symm p * n⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulAut.conj_apply]

theorem a6x (hA : A6AutFacts) {N : Subgroup X} [N.Normal] (e : ↥N ≃* A6 × A6)
    (hC : centralizer (N : Set X) = ⊥) {z : X} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {Ab : Subgroup X} (eAb : ↥Ab ≃* A6) (hAbz : ∀ x ∈ Ab, x * z = z * x)
    (hcz : Nat.card ↥(centralizer ({z} : Set X)) = 1440)
    {F : Subgroup X} (hFAb : F ≤ Ab) (hF8 : Nat.card ↥F = 8)
    {s : X} (hs8 : orderOf s = 8) (hsF : ∀ f ∈ F, s * f = f * s) : False := by
  set ρ := TS8Wr.kappa N e with hρdef
  have hρ : Function.Injective ρ := kappa_injective N e hC
  have hinn : ∀ a b : A6, (MulAut.conj (a, b) : Yaut) ∈ ρ.range := fun a b =>
    ⟨(e.symm (a, b) : X), by rw [kappa_inner, MulEquiv.apply_symm_apply]⟩
  have hcent : ρ.range ⊓ centralizer ({ρ z} : Set Yaut) = (centralizer ({z} : Set X)).map ρ := by
    ext y
    constructor
    · rintro ⟨⟨x, rfl⟩, hy⟩
      refine ⟨x, mem_centralizer_singleton_iff.2 ?_, rfl⟩
      apply hρ
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hy
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
  refine a6x_aut hA ρ.range hinn (z := ρ z) ?_ ?_
    (Ab := Ab.map ρ) ((Ab.equivMapOfInjective ρ hρ).symm.trans eAb) ?_ ?_
    (F := F.map ρ) (Subgroup.map_mono hFAb) ?_ (s := ρ s) ?_ ?_
  · rw [← map_mul, hz2, map_one]
  · intro h
    exact hz1 (hρ (h.trans (map_one ρ).symm))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hAbz x hx]
  · rw [hcent, Subgroup.card_map_of_injective hρ]
    exact hcz
  · rw [Subgroup.card_map_of_injective hρ]
    exact hF8
  · rw [orderOf_injective ρ hρ s]
    exact hs8
  · intro f hf
    obtain ⟨x, hx, rfl⟩ := hf
    rw [← map_mul, ← map_mul, hsF x hx]

end Transfer

end CFSG.EvenSporadicStandard.Fin76b.A6X
