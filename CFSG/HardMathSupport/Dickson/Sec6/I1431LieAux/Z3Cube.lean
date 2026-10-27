module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Z3CubeLift
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Aux.Cube

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem three_dvd_of_isInnerAut_zpow {Q : Type*} [Group Q] {τ : MulAut Q} (h3 : τ ^ 3 = 1)
    (hn : ¬ IsInnerAut τ) {k : ℤ} (hk : IsInnerAut (τ ^ k)) : (3 : ℤ) ∣ k := by
  by_contra hk3
  have hred : τ ^ k = τ ^ (k % 3) := by
    have hk' : k = k % 3 + 3 * (k / 3) := by omega
    conv_lhs => rw [hk']
    have : τ ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
    rw [zpow_add, zpow_mul, this, one_zpow, mul_one]
  have hcases : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [hred] at hk
  rcases hcases with h1 | h2
  · rw [h1, zpow_one] at hk
    exact hn hk
  · rw [h2] at hk
    apply hn
    have hsq : IsInnerAut (τ ^ (2 : ℤ) * τ ^ (2 : ℤ)) := (innerAut Q).mul_mem hk hk
    have : τ ^ (2 : ℤ) * τ ^ (2 : ℤ) = τ := by
      rw [← zpow_add, show (2 : ℤ) + 2 = 1 + 3 by norm_num, zpow_add, zpow_one]
      have : τ ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
      rw [this, mul_one]
    rwa [this] at hsq


theorem conj_mem_stabAut_of_mem {Y : Type*} [Group Y] {J : Subgroup Y} {t : Y} (ht : t ∈ J) :
    MulAut.conj t ∈ stabAut J := by
  rw [mem_stabAut]
  intro y
  simp only [MulAut.conj_apply]
  constructor
  · intro hy
    have := J.mul_mem (J.mul_mem (J.inv_mem ht) hy) ht
    simpa [mul_assoc] using this
  · intro hy
    exact J.mul_mem (J.mul_mem ht hy) (J.inv_mem ht)

theorem conj_mem_stabAut_of_center {Y : Type*} [Group Y] {J : Subgroup Y} {w : Y}
    (hw : w ∈ Subgroup.center Y) : MulAut.conj w ∈ stabAut J := by
  rw [mem_stabAut]
  intro y
  have : w * y * w⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.1 hw y]
    group
  simp only [MulAut.conj_apply, this]

theorem conj_mem_stabAut_of_fix {Y : Type*} [Group Y] {J : Subgroup Y} {x : Y}
    (hJ : ∀ j ∈ J, x * j * x⁻¹ = j) : MulAut.conj x ∈ stabAut J := by
  rw [mem_stabAut]
  intro y
  simp only [MulAut.conj_apply]
  constructor
  · intro hy
    have h1 := hJ _ hy
    have h2 : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
      calc x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * x := by rw [h1]
        _ = x * y * x⁻¹ := by group
    have h3 : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = x * y * x⁻¹ := h2
    rw [h3]
    exact hy
  · intro hy
    rw [hJ y hy]
    exact hy

theorem inducedBarHom_conj_mk {Y : Type*} [Group Y] {J : Subgroup Y} (g : Y)
    (hg : MulAut.conj g ∈ stabAut J) (j j' : ↥J) (hj' : (j' : Y) = g * (j : Y) * g⁻¹) :
    inducedBarHom J ⟨MulAut.conj g, hg⟩ (QuotientGroup.mk j) = QuotientGroup.mk j' := by
  rw [inducedBarHom_mk]
  congr 1
  apply Subtype.ext
  rw [restrictAut_coe, hj']
  rfl



theorem Y1431Cfg.exists_elemAbelian_27 (h0 : L2CentreThree) {V : InndiagVocab} {Y : Type}
    [Group Y] [Finite Y] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (hin : ∀ a ∈ Â, a ∈ innerAut Y) :
    ∃ E : Subgroup (Y ⧸ Subgroup.center Y), IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := CFSG.HardMathSupport.Solomon.Proving.l2OrderUnique_holds
  have hF := CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds
  obtain ⟨x, z, hxξ, hzÂ, hzξ, hx3, hz3, hxz⟩ := c.exists_inner_pair hin
  obtain ⟨⟨h, hfld⟩, hntriv⟩ := c.field _ hzÂ hzξ
  set γ : ↥(stabAut J) := ⟨MulAut.conj z, h⟩ with hγ
  set τ : MulAut (barOf 3 J) := inducedBarHom J γ with hτ
  have hτ1 : τ ≠ 1 := fun h1 => hntriv ⟨h, h1⟩
  have hγ3 : γ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c.elemAbelian.2 _ hzÂ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hγ3, map_one]
  have hQ := isQuasisimple_barOf_of_glaPComponent Nat.prime_three c.comp
  have hO : GLAPPrimeCore 3 (barOf 3 J) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  have hZp : IsPGroup 3 (Subgroup.center (barOf 3 J)) := isPGroup_center_of_core_eq_bot hO
  obtain ⟨F, hFf, hFfin, θ, F₀, hF₀f, hF₀fin, h4, hqcube, ⟨ee⟩, hβ1⟩ :=
    fieldAut_cube_facts hU hF hQ hτ3 hτ1 hfld c.typeL2 c.not_dvd c.ne_eight
  have hZ : Subgroup.center (barOf 3 J) = ⊥ := by
    by_contra hZ
    obtain ⟨F', hF'f, hF'fin, hF'card, ⟨e'⟩⟩ := c.typeL2
    have h9 := h0 (barOf 3 J) hQ hZp hZ F' ⟨e'⟩
    exact l2fld_not_cube_nine (Nat.card F₀) (hqcube.symm.trans (hF'card.symm.trans h9))
  have h3dvd : 3 ∣ Nat.card (StatedProj (StatedSL 2 F₀)) := l2fld_three_dvd_card_psl2
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set β := MulAut.congr θ (centerDescend (barOf 3 J) τ) with hβ
  let w : ↥(Lemma510Ns.fixSub β) := ee.symm u
  have hwfix : β (w : StatedProj (StatedSL 2 F)) = w := Lemma510Ns.mem_fixSub.1 w.2
  have hword : orderOf (w : StatedProj (StatedSL 2 F)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact (orderOf_injective ee.symm.toMonoidHom ee.symm.injective u).trans hu
  let tt : barOf 3 J ⧸ Subgroup.center (barOf 3 J) := θ.symm (w : StatedProj (StatedSL 2 F))
  have htfix : centerDescend (barOf 3 J) τ tt = tt := by
    apply θ.injective
    have hθtt : θ tt = (w : StatedProj (StatedSL 2 F)) := θ.apply_symm_apply _
    have : β (θ tt) = θ (centerDescend (barOf 3 J) τ tt) := by
      show θ (centerDescend (barOf 3 J) τ (θ.symm (θ tt))) = _
      rw [MulEquiv.symm_apply_apply]
    rw [← this, hθtt, hwfix]
  have htord : orderOf tt = 3 :=
    (orderOf_injective θ.symm.toMonoidHom θ.symm.injective _).trans hword
  let e0 := barEquivBot hZ
  let tb : barOf 3 J := e0 tt
  have htbfix : inducedBarHom J γ tb = tb := by
    have h1 := congr_barEquivBot hZ τ
    have h2 : τ tb = e0 (centerDescend (barOf 3 J) τ (e0.symm tb)) := by
      conv_lhs => rw [← h1]
      rfl
    rw [show inducedBarHom J γ tb = τ tb from rfl, h2, show e0.symm tb = tt from
      e0.symm_apply_apply tt, htfix]
  have htbord : orderOf tb = 3 := (orderOf_injective e0.toMonoidHom e0.injective tt).trans htord
  obtain ⟨t, htz, ht3, htnt⟩ := exists_fixed_order_three_lift z h hz3 htbfix htbord
  have hJfix : ∀ j ∈ J, x * j * x⁻¹ = j := fun j hj => by
    have := Lemma510Ns.mem_fixSub.1 (c.comp.1 hj)
    rw [hxξ] at this
    simpa [MulAut.conj_apply] using this
  have hxM : MulAut.conj x ∈ stabAut J := conj_mem_stabAut_of_fix hJfix
  have htM : MulAut.conj (t : Y) ∈ stabAut J := conj_mem_stabAut_of_mem t.2
  let M : Subgroup Y := (stabAut J).comap (MulAut.conj : Y →* MulAut Y)
  let Ψ : ↥M →* MulAut (barOf 3 J) :=
    (inducedBarHom J).comp ((MulAut.conj : Y →* MulAut Y).subgroupComap (stabAut J))
  have hΨ : ∀ (g : Y) (hg : g ∈ M), Ψ ⟨g, hg⟩ = inducedBarHom J ⟨MulAut.conj g, hg⟩ :=
    fun g hg => rfl
  have hxM' : x ∈ M := hxM
  have htM' : (t : Y) ∈ M := htM
  have hzM' : z ∈ M := h
  have hΨtriv : ∀ (g : Y) (hg : g ∈ M), (∀ j : ↥J, g * (j : Y) * g⁻¹ = j) → Ψ ⟨g, hg⟩ = 1 := by
    intro g hg hgj
    rw [hΨ]
    ext y
    induction y using QuotientGroup.induction_on with
    | H j =>
      rw [inducedBarHom_conj_mk g hg j j (hgj j).symm]
      rfl
  have hΨX : Ψ ⟨x, hxM'⟩ = 1 := hΨtriv x hxM' fun j => hJfix j j.2
  have hΨcenter : ∀ (w : Y) (hw : w ∈ Subgroup.center Y),
      Ψ ⟨w, conj_mem_stabAut_of_center hw⟩ = 1 := by
    intro w hw
    refine hΨtriv w _ fun j => ?_
    rw [← Subgroup.mem_center_iff.1 hw (j : Y)]
    group
  set m : barOf 3 J := QuotientGroup.mk t with hm
  have hΨT : Ψ ⟨(t : Y), htM'⟩ = MulAut.conj m := by
    rw [hΨ]
    ext y
    induction y using QuotientGroup.induction_on with
    | H j =>
      rw [inducedBarHom_conj_mk (t : Y) htM j (t * j * t⁻¹) rfl]
      simp [hm, MulAut.conj_apply]
  have hΨZ : Ψ ⟨z, hzM'⟩ = τ := rfl
  have hnotinner : ¬ IsInnerAut τ := by
    have := not_isInnerAut_descend_of_fieldAut hU hF hQ hτ3 hτ1 hfld c.typeL2 c.not_dvd
      c.ne_eight
    rintro ⟨u, hu⟩
    exact this ⟨QuotientGroup.mk u, by rw [← hu, CFSG.HardMathSupport.Solomon.Coordinator.centerDescend_conj]⟩
  have hm3 : m ^ 3 = 1 := by
    rw [hm, ← QuotientGroup.mk_pow, ht3]
    rfl
  have hmord : orderOf m = 3 := orderOf_eq_prime hm3 htnt
  have hxne : x ∉ Subgroup.center Y := fun hx => by
    apply c.ne_one
    rw [hxξ]
    ext y
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.1 hx y]
    group
  have hind : ∀ i j k : ℤ,
      (QuotientGroup.mk x : Y ⧸ Subgroup.center Y) ^ i *
          (QuotientGroup.mk (t : Y) : Y ⧸ Subgroup.center Y) ^ j *
          (QuotientGroup.mk z : Y ⧸ Subgroup.center Y) ^ k = 1 →
        (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j ∧ (3 : ℤ) ∣ k := by
    intro i j k hijk
    have hw : x ^ i * (t : Y) ^ j * z ^ k ∈ Subgroup.center Y := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_zpow, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
      exact hijk
    have hΨw := hΨcenter _ hw
    have hprod : (⟨x ^ i * (t : Y) ^ j * z ^ k, conj_mem_stabAut_of_center hw⟩ : ↥M) =
        (⟨x, hxM'⟩ : ↥M) ^ i * (⟨(t : Y), htM'⟩ : ↥M) ^ j * (⟨z, hzM'⟩ : ↥M) ^ k := by
      apply Subtype.ext
      simp
    rw [hprod, map_mul, map_mul, map_zpow, map_zpow, map_zpow, hΨX, hΨT, hΨZ, one_zpow,
      one_mul] at hΨw
    have hk_inner : IsInnerAut (τ ^ k) := by
      refine ⟨(m ^ j)⁻¹, ?_⟩
      rw [map_inv, map_zpow, ← eq_inv_of_mul_eq_one_right hΨw]
    have hk3 : (3 : ℤ) ∣ k := three_dvd_of_isInnerAut_zpow hτ3 hnotinner hk_inner
    have hτk : τ ^ k = 1 := zpow_eq_one_of_dvd_three hτ3 hk3
    rw [hτk, mul_one] at hΨw
    have hmj : m ^ j = 1 := by
      have h1 : MulAut.conj (m ^ j) = 1 := by rw [map_zpow]; exact hΨw
      have hmem : m ^ j ∈ Subgroup.center (barOf 3 J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (barOf 3 J) => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * m ^ j = (m ^ j * g * (m ^ j)⁻¹) * m ^ j := by rw [this]
          _ = m ^ j * g := by group
      rw [hZ, Subgroup.mem_bot] at hmem
      exact hmem
    have hj3 : (3 : ℤ) ∣ j := by
      have := (orderOf_dvd_iff_zpow_eq_one (G := barOf 3 J)).2 hmj
      rw [hmord] at this
      exact_mod_cast this
    have htj : (t : Y) ^ j = 1 := by
      have : (t : Y) ^ 3 = 1 := by
        have := congrArg Subtype.val ht3
        simpa using this
      exact zpow_eq_one_of_dvd_three this hj3
    have hzk : z ^ k ∈ Subgroup.center Y := by
      obtain ⟨k', rfl⟩ := hk3
      rw [zpow_mul]
      exact Subgroup.zpow_mem _ (by simpa using hz3) _
    have hxi : x ^ i ∈ Subgroup.center Y := by
      rw [htj, mul_one] at hw
      exact (Subgroup.mul_mem_cancel_right _ hzk).1 hw
    have hxord : orderOf (QuotientGroup.mk x : Y ⧸ Subgroup.center Y) = 3 := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow]
        exact (QuotientGroup.eq_one_iff _).2 hx3
      · intro h1
        exact hxne ((QuotientGroup.eq_one_iff _).1 h1)
    refine ⟨?_, hj3, hk3⟩
    have h2 : (QuotientGroup.mk x : Y ⧸ Subgroup.center Y) ^ i = 1 := by
      rw [← QuotientGroup.mk_zpow]
      exact (QuotientGroup.eq_one_iff _).2 hxi
    have := (orderOf_dvd_iff_zpow_eq_one (G := Y ⧸ Subgroup.center Y)).2 h2
    rw [hxord] at this
    exact_mod_cast this
  have hab : (QuotientGroup.mk x : Y ⧸ Subgroup.center Y) * QuotientGroup.mk (t : Y) =
      QuotientGroup.mk (t : Y) * QuotientGroup.mk x := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have := hJfix t t.2
    exact (mul_inv_eq_iff_eq_mul.1 this)
  have hac : (QuotientGroup.mk x : Y ⧸ Subgroup.center Y) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk x := by
    have h1 : (QuotientGroup.mk ⁅x, z⁆ : Y ⧸ Subgroup.center Y) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hxz
    rw [show (QuotientGroup.mk ⁅x, z⁆ : Y ⧸ Subgroup.center Y) =
      ⁅(QuotientGroup.mk x : Y ⧸ Subgroup.center Y), QuotientGroup.mk z⁆ from
      map_commutatorElement (QuotientGroup.mk' (Subgroup.center Y)) x z] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hbc : (QuotientGroup.mk (t : Y) : Y ⧸ Subgroup.center Y) * QuotientGroup.mk z =
      QuotientGroup.mk z * QuotientGroup.mk (t : Y) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (mul_inv_eq_iff_eq_mul.1 htz).symm
  refine exists_elemAbelian_27_of_indep hab hac hbc ?_ ?_ ?_ hind
  · rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hx3
  · rw [← QuotientGroup.mk_pow]
    have : (t : Y) ^ 3 = 1 := by
      have := congrArg Subtype.val ht3
      simpa using this
    rw [this]
    rfl
  · rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 hz3


end CFSG.HardMathSupport.Dickson.Sec6.I1431
