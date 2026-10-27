module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinFact
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Standard
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.Generic.TypeA

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

section Spin

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem spinAction_eq_of_central
    {R : Subgroup (spinGroup Q)} {L : Subgroup (V ≃ₗ[F] V)} {i : V ≃ₗ[F] V}
    (hRL : R.map (spinAction Q) = L) (hL : IsFundamental Q L i)
    (hnc : ∀ r ∈ R, (∀ y, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup Q)) → r = 1)
    {r : spinGroup Q} (hr : r ∈ R) (hr1 : r ≠ 1) (hrc : ∀ a ∈ R, r * a = a * r) :
    spinAction Q r = i := by
  obtain ⟨F₁, hL1, hi1⟩ := hL
  have hrL : spinAction Q r ∈ L := hRL ▸ Subgroup.mem_map_of_mem _ hr
  rw [hL1] at hrL
  obtain ⟨A, hA⟩ := hrL
  have hθ1 : spinAction Q r ≠ 1 := by
    intro h
    apply hr1
    apply hnc r hr
    intro y
    have hc : r ∈ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q h
    have h1 : r * y * r⁻¹ * y⁻¹ = 1 := by
      have : r * y = y * r := (Subgroup.mem_center_iff.mp hc y).symm
      rw [this]
      group
    rw [h1]
    exact Subgroup.one_mem _
  have hAc : A ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have hB : F₁.La B ∈ L := hL1 ▸ ⟨B, rfl⟩
    obtain ⟨a, haR, ha⟩ := hRL ▸ hB
    apply F₁.La_injective
    rw [map_mul, map_mul, hA, ← ha, ← map_mul, ← map_mul, hrc a haR]
  rcases (mem_center_sl2_iff A).mp hAc with h1 | h1
  · exfalso
    apply hθ1
    rw [← hA, h1, map_one]
  · rw [← hA, h1, hi1]

end Spin

section Group

variable {K : Type*} [Group K]

theorem comm_mem_center_of_mem_center {z : K} (hz : z ∈ Subgroup.center K) (y : K) :
    z * y * z⁻¹ * y⁻¹ ∈ Subgroup.center K := by
  have h : z * y = y * z := (Subgroup.mem_center_iff.mp hz y).symm
  rw [h]
  have : y * z * z⁻¹ * y⁻¹ = 1 := by group
  rw [this]
  exact Subgroup.one_mem _

theorem central_of_twin {R R' : Subgroup K} (hcomm : ∀ a ∈ R, ∀ a' ∈ R', a * a' = a' * a)
    (hncR : ∀ x ∈ R, (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K) → x = 1)
    (hncR' : ∀ x ∈ R', (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center K) → x = 1) {r r' : K}
    (hr : r ∈ R) (hr' : r' ∈ R')
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center K) :
    (∀ a ∈ R, r * a = a * r) ∧ ∀ a ∈ R', r' * a = a * r' := by
  have hrr' : r * r' = r' * r := hcomm r hr r' hr'
  constructor
  · intro a ha
    have h1 : a * r' = r' * a := hcomm a ha r' hr'
    have h2 : a⁻¹ * r' = r' * a⁻¹ := hcomm a⁻¹ (R.inv_mem ha) r' hr'
    have hz : a * r * a⁻¹ * r⁻¹ = (r * r' * a * (r * r')⁻¹ * a⁻¹)⁻¹ := by
      calc a * r * a⁻¹ * r⁻¹ = a * r * (a⁻¹ * r') * r'⁻¹ * r⁻¹ := by group
        _ = a * r * (r' * a⁻¹) * r'⁻¹ * r⁻¹ := by rw [h2]
        _ = (r * r' * a * (r * r')⁻¹ * a⁻¹)⁻¹ := by group
    have hzc : a * r * a⁻¹ * r⁻¹ ∈ Subgroup.center K := by
      rw [hz]
      exact (Subgroup.center K).inv_mem (hcen a)
    have hz1 : a * r * a⁻¹ * r⁻¹ = 1 := by
      refine hncR _ (R.mul_mem (R.mul_mem (R.mul_mem ha hr) (R.inv_mem ha)) (R.inv_mem hr)) ?_
      intro y
      exact comm_mem_center_of_mem_center hzc y
    have : a * r = r * a := by
      have h3 : a * r = (a * r * a⁻¹ * r⁻¹) * (r * a) := by group
      rw [h3, hz1, one_mul]
    exact this.symm
  · intro a ha
    have h1 : a * r = r * a := (hcomm r hr a ha).symm
    have h2 : a⁻¹ * r = r * a⁻¹ := (hcomm r hr a⁻¹ (R'.inv_mem ha)).symm
    have hz : a * r' * a⁻¹ * r'⁻¹ = (r * r' * a * (r * r')⁻¹ * a⁻¹)⁻¹ := by
      calc a * r' * a⁻¹ * r'⁻¹
          = (r' * r * a * (r' * r)⁻¹ * a⁻¹)⁻¹ := by
            calc a * r' * a⁻¹ * r'⁻¹ = (r' * a * r'⁻¹ * a⁻¹)⁻¹ := by group
              _ = (r' * (r * a) * r⁻¹ * r'⁻¹ * a⁻¹)⁻¹ := by
                  rw [← h1]
                  group
              _ = (r' * r * a * (r' * r)⁻¹ * a⁻¹)⁻¹ := by group
        _ = (r * r' * a * (r * r')⁻¹ * a⁻¹)⁻¹ := by rw [hrr']
    have hzc : a * r' * a⁻¹ * r'⁻¹ ∈ Subgroup.center K := by
      rw [hz]
      exact (Subgroup.center K).inv_mem (hcen a)
    have hz1 : a * r' * a⁻¹ * r'⁻¹ = 1 := by
      refine hncR' _ (R'.mul_mem (R'.mul_mem (R'.mul_mem ha hr') (R'.inv_mem ha))
        (R'.inv_mem hr')) ?_
      intro y
      exact comm_mem_center_of_mem_center hzc y
    have : a * r' = r' * a := by
      have h3 : a * r' = (a * r' * a⁻¹ * r'⁻¹) * (r' * a) := by group
      rw [h3, hz1, one_mul]
    exact this.symm

end Group

section Omega

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [FiniteDimensional F V]

theorem eq_of_mul_eq_one_or_neg (h2 : (2 : F) ≠ 0) (hdim : 8 < Module.finrank F V)
    {L L' : Subgroup (V ≃ₗ[F] V)} {i i' : V ≃ₗ[F] V} (hL : IsFundamental Q L i)
    (hL' : IsFundamental Q L' i') (hu : i * i' = 1 ∨ i * i' = LinearEquiv.neg F) : i = i' := by
  obtain ⟨fr, -, rfl⟩ := hL
  obtain ⟨fr', -, rfl⟩ := hL'
  rcases hu with h | h
  · calc fr.La (-1) = fr.La (-1) * (fr'.La (-1) * fr'.La (-1)) := by
          rw [Frame.La_neg_one_mul_self, mul_one]
      _ = (fr.La (-1) * fr'.La (-1)) * fr'.La (-1) := by rw [mul_assoc]
      _ = fr'.La (-1) := by rw [h, one_mul]
  · exfalso
    have h1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    have h1' := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr'
    have hs := Submodule.finrank_sup_add_finrank_inf_eq fr.perp fr'.perp
    have hle : Module.finrank F ↥(fr.perp ⊔ fr'.perp) ≤ Module.finrank F V :=
      Submodule.finrank_le _
    have hpos : 0 < Module.finrank F ↥(fr.perp ⊓ fr'.perp) := by omega
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hv1 : fr.La (-1) v = v :=
      Frame.La_apply_of_coords_eq_zero fr (-1) ((Frame.mem_perp_iff fr).mp hv.1)
    have hv2 : fr'.La (-1) v = v :=
      Frame.La_apply_of_coords_eq_zero fr' (-1) ((Frame.mem_perp_iff fr').mp hv.2)
    have h3 : (fr.La (-1) * fr'.La (-1)) v = v := by
      rw [LinearEquiv.mul_apply, hv2, hv1]
    rw [h] at h3
    have h4 : (2 : F) • v = 0 := by
      have : -v = v := h3
      rw [two_smul]
      nth_rewrite 1 [← this]
      exact neg_add_cancel v
    rcases smul_eq_zero.mp h4 with h5 | h5
    · exact h2 h5
    · exact hv0 (Subtype.ext h5)

end Omega

section Minus

variable {F : Type} [Field F] [Finite F] {b c : F} {n : ℕ}

omit [Finite F] in
theorem finrank_vm (hn : 1 ≤ n) : Module.finrank F (Vm n F) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem same_involution_of_twin (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 5 ≤ n)
    (hodd : Odd (Nat.card F)) (hperfK : Group.IsPerfect (spinGroup (quadMinus n F b c)))
    {R R' : Subgroup (spinGroup (quadMinus n F b c))} {i i' : Vm n F ≃ₗ[F] Vm n F}
    (hR : IsFundamental (quadMinus n F b c) (R.map (spinAction (quadMinus n F b c))) i)
    (hR' : IsFundamental (quadMinus n F b c) (R'.map (spinAction (quadMinus n F b c))) i')
    (hcomm : ∀ a ∈ R, ∀ a' ∈ R', a * a' = a' * a)
    (hncR : ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    (hncR' : ∀ x ∈ R',
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    {r r' : spinGroup (quadMinus n F b c)} (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R')
    (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈
      Subgroup.center (spinGroup (quadMinus n F b c))) :
    i = i' := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hdim : 8 < Module.finrank F (Vm n F) := by
    rw [finrank_vm (by omega)]
    omega
  obtain ⟨hcR, hcR'⟩ := central_of_twin hcomm hncR hncR' hr hr' hcen
  have hθr : spinAction (quadMinus n F b c) r = i :=
    spinAction_eq_of_central rfl hR hncR hr hr1 hcR
  have hθr' : spinAction (quadMinus n F b c) r' = i' :=
    spinAction_eq_of_central rfl hR' hncR' hr' hr'1 hcR'
  have hc : r * r' ∈ Subgroup.center (spinGroup (quadMinus n F b c)) :=
    CFSG.ClassicalInvolution.RouteD.mem_center_of_comm_mem_center (fun s => hcen s)
  have hrange := CFSG.LieType.Universal.Spin.range_spinAction_quadMinus (by omega : 4 ≤ n) hirr
  have hmem : spinAction (quadMinus n F b c) (r * r') ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n F b c) :=
    hrange ▸ ⟨_, rfl⟩
  let z : ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n F b c)) := ⟨_, hmem⟩
  have hzc : z ∈ Subgroup.center
      ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n F b c)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hu : (u : Vm n F ≃ₗ[F] Vm n F) ∈ (spinAction (quadMinus n F b c)).range := by
      rw [hrange]
      exact u.2
    obtain ⟨y, hy⟩ := hu
    apply Subtype.ext
    show (u : Vm n F ≃ₗ[F] Vm n F) * spinAction (quadMinus n F b c) (r * r') =
      spinAction (quadMinus n F b c) (r * r') * (u : Vm n F ≃ₗ[F] Vm n F)
    rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc y)]
  have hcommi : i * i' = i' * i := by
    rw [← hθr, ← hθr', ← map_mul, ← map_mul, hcomm r hr r' hr']
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    show (spinAction (quadMinus n F b c) (r * r')) * spinAction (quadMinus n F b c) (r * r') = 1
    rw [map_mul, hθr, hθr']
    calc i * i' * (i * i') = i * (i' * i) * i' := by group
      _ = i * (i * i') * i' := by rw [hcommi]
      _ = (i * i) * (i' * i') := by group
      _ = 1 := by rw [hR.mul_self, hR'.mul_self, mul_one]
  have : Nontrivial (Vm n F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadMinus (by omega : 4 ≤ n) hirr
  rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
    h | h
  · exact eq_of_mul_eq_one_or_neg h2 hdim hR hR'
      (Or.inl (by rw [← hθr, ← hθr', ← map_mul]; exact congrArg Subtype.val h))
  · exact eq_of_mul_eq_one_or_neg h2 hdim hR hR'
      (Or.inr (by rw [← hθr, ← hθr', ← map_mul]; exact h))

end Minus

section Twin

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
  {n : ℕ}

noncomputable abbrev twinFrame (hn : 3 ≤ n) : Frame (quadMinus n F b c) :=
  (minusFrame n b c).toHypFrame.toFrame (twIdx0_ne_twIdx1 hn) true false

omit [Finite F] in
theorem toFrame_true_true_eq_swap (hn : 3 ≤ n) :
    (minusFrame n b c).toHypFrame.toFrame (twIdx0_ne_twIdx1 hn) true true =
      (twinFrame (b := b) (c := c) hn).swap := rfl

omit [Finite F] in
theorem rankOne_zero_eq_range (hn : 3 ≤ n) :
    CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn) =
      ((minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn) true false).range :=
  rankOne_minusRootGroup_of_lt n hirr (k := twIdx0 hn) (by simp only [twIdx0]; omega)

omit [Finite F] in
theorem map_rankOne_zero (hn : 3 ≤ n) :
    (CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn)).map
      (spinAction (quadMinus n F b c)) = (twinFrame (b := b) (c := c) hn).La.range := by
  rw [rankOne_zero_eq_range hirr hn, ← MonoidHom.range_comp,
    CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2 (minusFrame n b c).toHypFrame]

omit [Finite F] in
theorem spinAction_longSL2_tt_mem (hn : 3 ≤ n) (A : SL(2, F)) :
    spinAction (quadMinus n F b c)
      ((minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn) true true A) ∈
        (twinFrame (b := b) (c := c) hn).swap.La.range := by
  have h := DFunLike.congr_fun (CFSG.ClassicalInvolution.ModelFacts.spinAction_comp_longSL2
    (minusFrame n b c).toHypFrame (twIdx0_ne_twIdx1 hn) true true) A
  rw [MonoidHom.comp_apply] at h
  rw [h, toFrame_true_true_eq_swap]
  exact ⟨A, rfl⟩

omit [Finite F] in
theorem map_conj_shortWeyl_le (hn : 3 ≤ n) :
    ((conjSub (shortWeyl n hirr (twIdx1 hn))
        (CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn))).map
      (spinAction (quadMinus n F b c))) ≤ (twinFrame (b := b) (c := c) hn).swap.La.range := by
  rw [rankOne_zero_eq_range hirr hn]
  rintro _ ⟨x, ⟨y, ⟨A, rfl⟩, rfl⟩, rfl⟩
  have e1 : shortWeylBool (twIdx1 hn) (twIdx0 hn) true = true := by
    simp [shortWeylBool, twIdx0_ne_twIdx1 hn]
  have e2 : shortWeylBool (twIdx1 hn) (twIdx1 hn) false = true := by simp [shortWeylBool]
  have e3 : shortWeylBool (twIdx1 hn) (twIdx1 hn) true = false := by simp [shortWeylBool]
  have e4 : shortWeylBool (twIdx1 hn) (twIdx0 hn) false = false := by
    simp [shortWeylBool, twIdx0_ne_twIdx1 hn]
  have s1 : (longWeylSign (twIdx1 hn) (twIdx0 hn) : F) = 1 := by
    simp [longWeylSign, twIdx0_ne_twIdx1 hn]
  have s2 : (longWeylSign (twIdx1 hn) (twIdx1 hn) : F) = -1 := by simp [longWeylSign]
  have hφ := Frame.sl2_apply_mem
    ((spinAction (quadMinus n F b c)).comp
      ((MulAut.conj (shortWeyl n hirr (twIdx1 hn))).toMonoidHom.comp
        ((minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn) true false)))
    (twinFrame (b := b) (c := c) hn).swap.La.range ?_ ?_ A
  · exact hφ
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection]
    show spinAction (quadMinus n F b c) (shortWeyl n hirr (twIdx1 hn) *
      (minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn) true false (upperSL2 c') *
        (shortWeyl n hirr (twIdx1 hn))⁻¹) ∈ _
    rw [HypFrame.longSL2_upperSL2, shortWeyl_conj_longRoot n hirr (twIdx1 hn)
      (twIdx0_ne_twIdx1 hn) true false c', e1, e2, s1, s2, one_mul,
      ← HypFrame.longSL2_upperSL2 (minusFrame n b c).toHypFrame (twIdx0_ne_twIdx1 hn) true true]
    exact spinAction_longSL2_tt_mem hn _
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection]
    show spinAction (quadMinus n F b c) (shortWeyl n hirr (twIdx1 hn) *
      (minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn) true false (lowerSL2 c') *
        (shortWeyl n hirr (twIdx1 hn))⁻¹) ∈ _
    rw [HypFrame.longSL2_lowerSL2, shortWeyl_conj_longRoot n hirr (twIdx1 hn)
      (twIdx0_ne_twIdx1 hn).symm (!false) (!true) c']
    simp only [Bool.not_false, Bool.not_true, e3, e4, s1, s2]
    have := spinAction_longSL2_tt_mem (b := b) (c := c) hn (lowerSL2 (-1 * 1 * c'))
    rw [HypFrame.longSL2_lowerSL2] at this
    simpa only [Bool.not_true] using this

noncomputable abbrev twinR0 (hn : 3 ≤ n) : Subgroup (spinGroup (quadMinus n F b c)) :=
  CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx0 hn)

noncomputable abbrev twinR0' (hn : 3 ≤ n) : Subgroup (spinGroup (quadMinus n F b c)) :=
  conjSub (shortWeyl n hirr (twIdx1 hn)) (twinR0 hirr hn)

noncomputable abbrev twinInv (hn : 3 ≤ n) : Vm n F ≃ₗ[F] Vm n F :=
  (twinFrame (b := b) (c := c) hn).La (-1)

omit [Finite F] in
theorem isFundamental_twinR0 (hn : 3 ≤ n) :
    IsFundamental (quadMinus n F b c) ((twinR0 hirr hn).map (spinAction (quadMinus n F b c)))
      (twinInv (b := b) (c := c) hn) := by
  rw [map_rankOne_zero hirr hn]
  exact IsFundamental.of_frame _

omit [Finite F] in
theorem isFundamental_map_conj (hn : 3 ≤ n) (g : spinGroup (quadMinus n F b c)) :
    IsFundamental (quadMinus n F b c)
      ((conjSub g (twinR0 hirr hn)).map (spinAction (quadMinus n F b c)))
      (spinAction (quadMinus n F b c) g * twinInv (b := b) (c := c) hn *
        (spinAction (quadMinus n F b c) g)⁻¹) := by
  rw [← conjSub_map]
  have hg : ((spinToOrthogonalGroup (quadMinus n F b c) g :
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n F b c)) : Vm n F ≃ₗ[F] Vm n F) =
        spinAction (quadMinus n F b c) g :=
    LinearEquiv.ext (coe_spinToOrthogonalGroup_apply _ g)
  have := IsFundamental.conj (spinToOrthogonalGroup (quadMinus n F b c) g).2
    (isFundamental_twinR0 hirr hn)
  rw [hg] at this
  exact this

theorem isFundamental_twinR0' (hodd : Odd (Nat.card F)) (hn : 3 ≤ n) :
    IsFundamental (quadMinus n F b c) ((twinR0' hirr hn).map (spinAction (quadMinus n F b c)))
      (twinInv (b := b) (c := c) hn) := by
  have h := isFundamental_map_conj hirr hn (shortWeyl n hirr (twIdx1 hn))
  have hle := map_conj_shortWeyl_le hirr hn
  have hL' : IsFundamental (quadMinus n F b c)
      (twinFrame (b := b) (c := c) hn).swap.La.range (twinInv (b := b) (c := c) hn) :=
    IsFundamental.of_frame_swap _
  have h1 := hL'.eq_of_orderOf_eq_two hodd (hle h.mem) (h.orderOf_eq_two hodd)
  rw [h1] at h
  exact h

theorem twinR0'_ne (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F) (hn : 3 ≤ n) :
    twinR0' hirr hn ≠ twinR0 hirr hn := by
  intro h
  have hle : (twinR0' hirr hn).map (spinAction (quadMinus n F b c)) ≤
      (twinFrame (b := b) (c := c) hn).swap.La.range := map_conj_shortWeyl_le hirr hn
  rw [h, map_rankOne_zero hirr hn] at hle
  have hL₀ := isFundamental_twinR0 hirr hn
  rw [map_rankOne_zero hirr hn] at hL₀
  have hab : ∀ x ∈ (twinFrame (b := b) (c := c) hn).La.range,
      ∀ y ∈ (twinFrame (b := b) (c := c) hn).La.range, x * y = y * x := by
    rintro _ ⟨A, rfl⟩ y hy
    obtain ⟨B, hB⟩ := hle hy
    rw [← hB]
    exact Frame.La_comm_La_swap _ A B
  have hcomm := hL₀.commutator_eq h4
  have hbot : ⁅(twinFrame (b := b) (c := c) hn).La.range,
      (twinFrame (b := b) (c := c) hn).La.range⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx y hy
    exact (hab y hy x hx)
  rw [hbot] at hcomm
  have hi : twinInv (b := b) (c := c) hn ∈ (twinFrame (b := b) (c := c) hn).La.range := hL₀.mem
  rw [← hcomm] at hi
  exact hL₀.ne_one hodd ((Subgroup.mem_bot).mp hi)

theorem eq_twinR0'_of_twin (hn : 5 ≤ n) (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hperfK : Group.IsPerfect (spinGroup (quadMinus n F b c)))
    (hsc : FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    {R' : Subgroup (spinGroup (quadMinus n F b c))}
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (hne : R' ≠ twinR0 hirr (by omega : 3 ≤ n))
    (hcomm : Commutes (twinR0 hirr (by omega : 3 ≤ n)) R')
    {r r' : spinGroup (quadMinus n F b c)} (hr : r ∈ twinR0 hirr (by omega : 3 ≤ n))
    (hr1 : r ≠ 1) (hr' : r' ∈ R') (hr'1 : r' ≠ 1)
    (hcen : ∀ y, r * r' * y * (r * r')⁻¹ * y⁻¹ ∈
      Subgroup.center (spinGroup (quadMinus n F b c))) :
    R' = twinR0' hirr (by omega : 3 ≤ n) := by
  have hn3 : 3 ≤ n := by omega
  have hR₀mem : twinR0 hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx0 hn3) (by simp only [twIdx0]; omega)
  have hR₀'mem : twinR0' hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    conjSub_mem_fundamentalSubgroups hR₀mem _
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R' hR'
  have hF' := isFundamental_map_conj hirr hn3 g
  rw [← hg] at hF'
  have hinv := same_involution_of_twin hirr hn hodd hperfK (isFundamental_twinR0 hirr hn3) hF'
    hcomm (hnc _ hR₀mem) (hnc _ hR') hr hr1 hr' hr'1 hcen
  rw [← hinv] at hF'
  obtain ⟨L'', hL'', hneL, -, huniq⟩ :=
    IsFundamental.exists_twin hodd (isFundamental_twinR0 hirr hn3)
  have h1 := huniq _ hF'
  have h2 := huniq _ (isFundamental_twinR0' hirr hodd hn3)
  have hθ : ∀ X ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      X.map (spinAction (quadMinus n F b c)) =
        (twinR0 hirr hn3).map (spinAction (quadMinus n F b c)) → X = twinR0 hirr hn3 :=
    fun X hX h => Gaps.eq_of_map_eq_of_central _ (ker_spinAction_le_center _) (hperf X hX)
      (hperf _ hR₀mem) h
  rcases h1 with h1 | h1
  · exact absurd (hθ R' hR' h1) hne
  rcases h2 with h2 | h2
  · exact absurd (hθ _ hR₀'mem h2) (twinR0'_ne hirr hodd h4 hn3)
  exact Gaps.eq_of_map_eq_of_central _ (ker_spinAction_le_center _) (hperf R' hR')
    (hperf _ hR₀'mem) (h1.trans h2.symm)

omit [Finite F] in
theorem sl2_hom_ext_of_upper_lower {G : Type*} [Group G] (φ ψ : SL(2, F) →* G)
    (h01 : ∀ c, φ (upperSL2 c) = ψ (upperSL2 c)) (h10 : ∀ c, φ (lowerSL2 c) = ψ (lowerSL2 c)) :
    φ = ψ := by
  refine MonoidHom.ext fun A => ?_
  have h := Frame.sl2_apply_mem (φ.prod ψ) ((MonoidHom.fst G G).eqLocus (MonoidHom.snd G G))
    (fun c => ?_) (fun c => ?_) A
  · exact h
  · rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection]
    exact h01 c
  · rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection]
    exact h10 c

@[expose] def twIdx2 (hn : 4 ≤ n) : Fin (n - 1) := ⟨2, by omega⟩

omit [Finite F] in
theorem conj_shortWeyl_two_longSL2 (hn : 4 ≤ n) :
    (MulAut.conj (shortWeyl n hirr (twIdx2 hn))).toMonoidHom.comp
      ((minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 (by omega : 3 ≤ n)) true false) =
        (minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 (by omega : 3 ≤ n)) true false := by
  have hn3 : 3 ≤ n := by omega
  have h20 : twIdx0 hn3 ≠ twIdx2 hn := fun h => by
    have := congrArg Fin.val h; simp [twIdx0, twIdx2] at this
  have h21 : twIdx1 hn3 ≠ twIdx2 hn := fun h => by
    have := congrArg Fin.val h; simp [twIdx1, twIdx2] at this
  have e1 : shortWeylBool (twIdx2 hn) (twIdx0 hn3) true = true := by simp [shortWeylBool, h20]
  have e2 : shortWeylBool (twIdx2 hn) (twIdx1 hn3) false = false := by simp [shortWeylBool, h21]
  have e3 : shortWeylBool (twIdx2 hn) (twIdx1 hn3) true = true := by simp [shortWeylBool, h21]
  have e4 : shortWeylBool (twIdx2 hn) (twIdx0 hn3) false = false := by simp [shortWeylBool, h20]
  have s1 : (longWeylSign (twIdx2 hn) (twIdx0 hn3) : F) = 1 := by simp [longWeylSign, h20]
  have s2 : (longWeylSign (twIdx2 hn) (twIdx1 hn3) : F) = 1 := by simp [longWeylSign, h21]
  refine sl2_hom_ext_of_upper_lower _ _ (fun c' => ?_) (fun c' => ?_)
  · show shortWeyl n hirr (twIdx2 hn) *
      (minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn3) true false (upperSL2 c') *
        (shortWeyl n hirr (twIdx2 hn))⁻¹ = _
    rw [HypFrame.longSL2_upperSL2, shortWeyl_conj_longRoot n hirr (twIdx2 hn)
      (twIdx0_ne_twIdx1 hn3) true false c', e1, e2, s1, s2, one_mul, one_mul]
  · show shortWeyl n hirr (twIdx2 hn) *
      (minusFrame n b c).longSL2 (twIdx0_ne_twIdx1 hn3) true false (lowerSL2 c') *
        (shortWeyl n hirr (twIdx2 hn))⁻¹ = _
    rw [HypFrame.longSL2_lowerSL2, shortWeyl_conj_longRoot n hirr (twIdx2 hn)
      (twIdx0_ne_twIdx1 hn3).symm (!false) (!true) c']
    simp only [Bool.not_false, Bool.not_true, e3, e4, s1, s2, one_mul, one_mul]

noncomputable abbrev twinR1 (hn : 4 ≤ n) : Subgroup (spinGroup (quadMinus n F b c)) :=
  CurtisTits.rankOne (minusDatum n hirr).rootGroup (twIdx1 (by omega : 3 ≤ n))

theorem twIdx1_ne_twIdx2 (hn : 4 ≤ n) : twIdx1 (by omega : 3 ≤ n) ≠ twIdx2 hn := fun h => by
  have := congrArg Fin.val h
  simp [twIdx1, twIdx2] at this

omit [Finite F] in
theorem twinR1_eq_range (hn : 4 ≤ n) :
    twinR1 hirr hn = ((minusFrame n b c).longSL2 (twIdx1_ne_twIdx2 hn) true false).range :=
  rankOne_minusRootGroup_of_lt n hirr (k := twIdx1 (by omega : 3 ≤ n)) (by
    simp only [twIdx1]; omega)

omit [Finite F] in
theorem conj_shortWeyl_mul_le (hn : 4 ≤ n) :
    conjSub (shortWeyl n hirr (twIdx1 (by omega : 3 ≤ n)) * shortWeyl n hirr (twIdx2 hn))
      (twinR1 hirr hn) ≤ twinR1 hirr hn := by
  have hn3 : 3 ≤ n := by omega
  have h12 := twIdx1_ne_twIdx2 hn
  have h21 : twIdx2 hn ≠ twIdx1 hn3 := h12.symm
  have a1 : shortWeylBool (twIdx2 hn) (twIdx1 hn3) true = true := by simp [shortWeylBool, h12]
  have a2 : shortWeylBool (twIdx2 hn) (twIdx2 hn) false = true := by simp [shortWeylBool]
  have a3 : shortWeylBool (twIdx2 hn) (twIdx2 hn) true = false := by simp [shortWeylBool]
  have a4 : shortWeylBool (twIdx2 hn) (twIdx1 hn3) false = false := by simp [shortWeylBool, h12]
  have b1 : shortWeylBool (twIdx1 hn3) (twIdx1 hn3) true = false := by simp [shortWeylBool]
  have b2 : shortWeylBool (twIdx1 hn3) (twIdx2 hn) true = true := by simp [shortWeylBool, h21]
  have b3 : shortWeylBool (twIdx1 hn3) (twIdx2 hn) false = false := by simp [shortWeylBool, h21]
  have b4 : shortWeylBool (twIdx1 hn3) (twIdx1 hn3) false = true := by simp [shortWeylBool]
  have s1 : (longWeylSign (twIdx2 hn) (twIdx1 hn3) : F) = 1 := by simp [longWeylSign, h12]
  have s2 : (longWeylSign (twIdx2 hn) (twIdx2 hn) : F) = -1 := by simp [longWeylSign]
  have s3 : (longWeylSign (twIdx1 hn3) (twIdx1 hn3) : F) = -1 := by simp [longWeylSign]
  have s4 : (longWeylSign (twIdx1 hn3) (twIdx2 hn) : F) = 1 := by simp [longWeylSign, h21]
  rw [twinR1_eq_range hirr hn]
  rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
  have hφ := Frame.sl2_apply_mem
    ((MulAut.conj (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn))).toMonoidHom.comp
      ((minusFrame n b c).longSL2 h12 true false))
    ((minusFrame n b c).longSL2 h12 true false).range ?_ ?_ A
  · exact hφ
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_upperSL2_eq_transvection]
    show (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn)) *
      (minusFrame n b c).longSL2 h12 true false (upperSL2 c') *
        (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn))⁻¹ ∈ _
    have : (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn)) *
        (minusFrame n b c).longSL2 h12 true false (upperSL2 c') *
          (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn))⁻¹ =
        shortWeyl n hirr (twIdx1 hn3) * (shortWeyl n hirr (twIdx2 hn) *
          (minusFrame n b c).longSL2 h12 true false (upperSL2 c') *
            (shortWeyl n hirr (twIdx2 hn))⁻¹) * (shortWeyl n hirr (twIdx1 hn3))⁻¹ := by group
    rw [this, HypFrame.longSL2_upperSL2,
      shortWeyl_conj_longRoot n hirr (twIdx2 hn) h12 true false c',
      a1, a2, s1, s2, shortWeyl_conj_longRoot n hirr (twIdx1 hn3) h12 true true,
      b1, b2, s3, s4, (minusFrame n b c).longRoot_swap h12 false true]
    refine ⟨lowerSL2 (-(-1 * 1 * (1 * -1 * c'))), ?_⟩
    rw [HypFrame.longSL2_lowerSL2]
    simp only [Bool.not_false, Bool.not_true]
  · intro c'
    rw [← CFSG.ClassicalInvolution.ModelFacts.coe_lowerSL2_eq_transvection]
    show (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn)) *
      (minusFrame n b c).longSL2 h12 true false (lowerSL2 c') *
        (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn))⁻¹ ∈ _
    have : (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn)) *
        (minusFrame n b c).longSL2 h12 true false (lowerSL2 c') *
          (shortWeyl n hirr (twIdx1 hn3) * shortWeyl n hirr (twIdx2 hn))⁻¹ =
        shortWeyl n hirr (twIdx1 hn3) * (shortWeyl n hirr (twIdx2 hn) *
          (minusFrame n b c).longSL2 h12 true false (lowerSL2 c') *
            (shortWeyl n hirr (twIdx2 hn))⁻¹) * (shortWeyl n hirr (twIdx1 hn3))⁻¹ := by group
    rw [this, HypFrame.longSL2_lowerSL2]
    simp only [Bool.not_false, Bool.not_true]
    rw [shortWeyl_conj_longRoot n hirr (twIdx2 hn) h12.symm true false c', a3, a4, s2, s1,
      shortWeyl_conj_longRoot n hirr (twIdx1 hn3) h12.symm false false, b3, b4, s4, s3,
      (minusFrame n b c).longRoot_swap h12.symm false true]
    refine ⟨upperSL2 (-(1 * -1 * (-1 * 1 * c'))), ?_⟩
    rw [HypFrame.longSL2_upperSL2]

theorem conj_shortWeyl_mul_eq (hn : 4 ≤ n) :
    conjSub (shortWeyl n hirr (twIdx1 (by omega : 3 ≤ n)) * shortWeyl n hirr (twIdx2 hn))
      (twinR1 hirr hn) = twinR1 hirr hn := by
  have hfin : Finite (spinGroup (quadMinus n F b c)) := finite_spinGroup_quadMinus n b c
  refine Subgroup.eq_of_le_of_card_ge (conj_shortWeyl_mul_le hirr hn) ?_
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]

omit [Finite F] in
theorem conjSub_shortWeyl_two_twinR0 (hn : 4 ≤ n) :
    conjSub (shortWeyl n hirr (twIdx2 hn)) (twinR0 hirr (by omega : 3 ≤ n)) =
      twinR0 hirr (by omega : 3 ≤ n) := by
  rw [twinR0, rankOne_zero_eq_range hirr (by omega : 3 ≤ n), conjSub, ← MonoidHom.range_comp,
    conj_shortWeyl_two_longSL2 hirr hn]

theorem exists_standardPair_R0_R1 (hn : 4 ≤ n) (h2 : (2 : F) ≠ 0) :
    ∃ W, LinearBlockStandardPair F W (twinR0 hirr (by omega : 3 ≤ n)) (twinR1 hirr hn) := by
  obtain ⟨-, W, hW⟩ := CFSG.ClassicalInvolution.ModelFacts.standardPair_minusDatum hn h2 hirr
  exact ⟨W, hW⟩

theorem exists_standardPair_R1_twin (hn : 4 ≤ n) (h2 : (2 : F) ≠ 0) :
    ∃ W, LinearBlockStandardPair F W (twinR1 hirr hn) (twinR0' hirr (by omega : 3 ≤ n)) := by
  obtain ⟨W, hW⟩ := exists_standardPair_R0_R1 hirr hn h2
  have h := CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW
    (shortWeyl n hirr (twIdx1 (by omega : 3 ≤ n)) * shortWeyl n hirr (twIdx2 hn))
  have e0 : conjSub (shortWeyl n hirr (twIdx1 (by omega : 3 ≤ n)) * shortWeyl n hirr (twIdx2 hn))
      (twinR0 hirr (by omega : 3 ≤ n)) = twinR0' hirr (by omega : 3 ≤ n) := by
    rw [conjSub_mul, conjSub_shortWeyl_two_twinR0 hirr hn]
  have e1 := conj_shortWeyl_mul_eq hirr hn
  rw [conjSub] at e0 e1
  rw [e0, e1] at h
  exact ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm h⟩

theorem twin_partner_spin (hn : 5 ≤ n) (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    (hperfK : Group.IsPerfect (spinGroup (quadMinus n F b c)))
    (hsc : FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), R ≤ ⁅R, R⁆)
    (hnc : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), ∀ x ∈ R,
      (∀ y, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) → x = 1)
    {R R' : Subgroup (spinGroup (quadMinus n F b c))}
    (hR : R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (hR' : R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr)) (hne : R ≠ R')
    (hcomm : Commutes R R')
    (hant : ∃ r ∈ R, r ≠ 1 ∧ ∃ r' ∈ R', r' ≠ 1 ∧ ∀ y,
      r * r' * y * (r * r')⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c))) :
    ∃ R'' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      (∃ W, LinearBlockStandardPair F W R R'') ∧ ∃ W, LinearBlockStandardPair F W R'' R' := by
  have hn3 : 3 ≤ n := by omega
  have hn4 : 4 ≤ n := by omega
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hR₀mem : twinR0 hirr hn3 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx0 hn3) (by simp only [twIdx0]; omega)
  have hR₁mem : twinR1 hirr hn4 ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    rankOne_mem_fund_minus hirr (k := twIdx1 hn3) (by simp only [twIdx1]; omega)
  obtain ⟨g, hg⟩ := hsc _ hR₀mem R hR
  obtain ⟨r, hr, hr1, r', hr', hr'1, hcen⟩ := hant
  have hR₁' : conjSub g⁻¹ R' ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    conjSub_mem_fundamentalSubgroups hR' g⁻¹
  have hRg : conjSub g⁻¹ R = twinR0 hirr hn3 := by
    rw [hg, conjSub_inv_conjSub]
  have hne₁ : conjSub g⁻¹ R' ≠ twinR0 hirr hn3 := by
    intro h
    apply hne
    rw [← hRg] at h
    have := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  have hcomm₁ : Commutes (twinR0 hirr hn3) (conjSub g⁻¹ R') := by
    rw [← hRg]
    exact (commutes_conjSub_iff g⁻¹).mpr hcomm
  have hr₁ : g⁻¹ * r * g ∈ twinR0 hirr hn3 := by
    rw [← hRg]
    exact mem_conjSub_iff.mpr (by simpa [mul_assoc] using hr)
  have hr₁' : g⁻¹ * r' * g ∈ conjSub g⁻¹ R' := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hr'
  have hcen₁ : ∀ y, (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ *
      y⁻¹ ∈ Subgroup.center (spinGroup (quadMinus n F b c)) := by
    intro y
    have h := hcen (g * y * g⁻¹)
    set w := r * r' * (g * y * g⁻¹) * (r * r')⁻¹ * (g * y * g⁻¹)⁻¹ with hw
    have hc : g⁻¹ * w = w * g⁻¹ := Subgroup.mem_center_iff.mp h g⁻¹
    have e : (g⁻¹ * r * g) * (g⁻¹ * r' * g) * y * ((g⁻¹ * r * g) * (g⁻¹ * r' * g))⁻¹ * y⁻¹ =
        g⁻¹ * w * g := by
      rw [hw]
      group
    rw [e, hc, mul_assoc, inv_mul_cancel, mul_one]
    exact h
  have hone : ∀ x : spinGroup (quadMinus n F b c), x ≠ 1 → g⁻¹ * x * g ≠ 1 := by
    intro x hx h
    apply hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this, h]
    group
  have key := eq_twinR0'_of_twin hirr hn hodd h4 hperfK hsc hperf hnc hR₁' hne₁ hcomm₁ hr₁
    (hone r hr1) hr₁' (hone r' hr'1) hcen₁
  have hR'eq : R' = conjSub g (twinR0' hirr hn3) := by
    rw [← key, conjSub_conjSub_inv]
  refine ⟨conjSub g (twinR1 hirr hn4), conjSub_mem_fundamentalSubgroups hR₁mem g, ?_, ?_⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_R0_R1 hirr hn4 h2
    rw [hg]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩
  · obtain ⟨W, hW⟩ := exists_standardPair_R1_twin hirr hn4 h2
    rw [hR'eq]
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW g⟩

end Twin

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinPartnerFactTwin_pOmegaMinus_five (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    TwinPartnerFactTwin p f .POmegaMinus 5 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaMinus 5 p f :=
    ⟨Fact.out, hf, by norm_num⟩
  obtain ⟨hodd, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  intro R hR R' hR' hne hcomm hant
  have hsc := CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaMinus 5 p f
    Fact.out trivial hadm (by decide) (by decide)
  have hperf := CFSG.ClassicalInvolution.RouteD.Gaps.fundPerfect_modelUniv hp2
    (t := .POmegaMinus) (n := 5) (e := f) trivial hadm (by omega)
  have hnc := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p .POmegaMinus 5 f trivial hadm
    (by decide)
  have hK := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .POmegaMinus 5 p f Fact.out
    trivial hadm).1
  exact twin_partner_spin (minusCoeffs_irr p f) (by norm_num) hodd h4
    (Group.isPerfect_def.mpr hK.1) hsc hperf hnc hR hR' hne hcomm hant

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
