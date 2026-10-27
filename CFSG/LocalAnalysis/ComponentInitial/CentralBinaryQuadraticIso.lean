module

public import CFSG.LocalAnalysis.ComponentInitial.CentralBinarySquareMap
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {P P' : Type*} [Group P] [Group P']

theorem sq_eq_one_of_elem_sub {W : Subgroup P} (h : CFSG.IsElementaryAbelian 2 W) :
    ∀ w ∈ W, w ^ 2 = 1 := fun w hw =>
  CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W) w hw

theorem sq_eq_one_of_elem {G : Type*} [Group G] (h : CFSG.IsElementaryAbelian 2 G) :
    ∀ u : G, u ^ 2 = 1 := fun u => by
  have hd := h.exponent_dvd_p
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hd u

@[expose] def fibreProd {W : Subgroup P} {W' : Subgroup P'} [W.Normal] [W'.Normal]
    (f : P ⧸ W ≃* P' ⧸ W') : Subgroup (P × P') where
  carrier := {p | f (p.1 : P ⧸ W) = (p.2 : P' ⧸ W')}
  mul_mem' {p p'} hp hp' := by
    change f ((p.1 * p'.1 : P) : P ⧸ W) = ((p.2 * p'.2 : P') : P' ⧸ W')
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul]
    exact congrArg₂ (· * ·) hp hp'
  one_mem' := by
    change f ((1 : P) : P ⧸ W) = ((1 : P') : P' ⧸ W')
    rw [QuotientGroup.mk_one, QuotientGroup.mk_one, map_one]
  inv_mem' {p} hp := by
    change f ((p.1⁻¹ : P) : P ⧸ W) = ((p.2⁻¹ : P') : P' ⧸ W')
    rw [QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_inv]
    exact congrArg (·⁻¹) hp

theorem central_binary_extension_quadratic_isomorphism [Finite P] [Finite P']
    {W : Subgroup P} {W' : Subgroup P'} [W.Normal] [W'.Normal]
    (hWc : W ≤ center P) (hW'c : W' ≤ center P')
    (hWel : CFSG.IsElementaryAbelian 2 W) (hW'el : CFSG.IsElementaryAbelian 2 W')
    (hUel : CFSG.IsElementaryAbelian 2 (P ⧸ W)) (hU'el : CFSG.IsElementaryAbelian 2 (P' ⧸ W'))
    (f : P ⧸ W ≃* P' ⧸ W') (g : W ≃* W') :
    (∃ h : P ≃* P', (∀ w : W, h w = g w) ∧ ∀ x : P, (h x : P' ⧸ W') = f x) ↔
      ∀ u : P ⧸ W, g (squareMap hWc (sq_eq_one_of_elem_sub hWel) (sq_eq_one_of_elem hUel) u) =
        squareMap hW'c (sq_eq_one_of_elem_sub hW'el) (sq_eq_one_of_elem hU'el) (f u) := by
  have hW2 := sq_eq_one_of_elem_sub hWel
  have hW'2 := sq_eq_one_of_elem_sub hW'el
  have hU := sq_eq_one_of_elem hUel
  have hU' := sq_eq_one_of_elem hU'el
  constructor
  · rintro ⟨h, hW, hf⟩ u
    induction u using QuotientGroup.induction_on with | H x => ?_
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (f (x : P ⧸ W))
    apply Subtype.ext
    rw [← hy]
    change (g ⟨x ^ 2, sq_mem_of_quotient hU x⟩ : P') = y ^ 2
    rw [← hW]
    change h (x ^ 2) = y ^ 2
    have hyx : (h x)⁻¹ * y ∈ W' := QuotientGroup.eq.1 ((hf x).trans hy.symm)
    have hy' : y = h x * ((h x)⁻¹ * y) := by group
    rw [hy', (show Commute (h x) ((h x)⁻¹ * y) from
      (mem_center_iff.1 (hW'c hyx) (h x))).mul_pow, hW'2 _ hyx, mul_one, map_pow]
  · intro hq
    have hsq : ∀ x : P, ∀ y : P', f (x : P ⧸ W) = (y : P' ⧸ W') →
        (g ⟨x ^ 2, sq_mem_of_quotient hU x⟩ : P') = y ^ 2 := by
      intro x y hxy
      have := congrArg Subtype.val (hq (x : P ⧸ W))
      rw [hxy] at this
      exact this
    set E := fibreProd f with hE
    have hmemE : ∀ x y, (x, y) ∈ E ↔ f (x : P ⧸ W) = (y : P' ⧸ W') := fun _ _ => Iff.rfl
    have hδmem : ∀ w : W, ((w : P), (g w : P')) ∈ E := fun w => by
      rw [hmemE, (QuotientGroup.eq_one_iff (w : P)).2 w.2,
        (QuotientGroup.eq_one_iff (g w : P')).2 (g w).2, map_one]
    have hμmem : ∀ w' : W', ((1 : P), (w' : P')) ∈ E := fun w' => by
      rw [hmemE, QuotientGroup.mk_one, map_one, (QuotientGroup.eq_one_iff (w' : P')).2 w'.2]
    let δ : W →* E :=
      { toFun := fun w => ⟨((w : P), (g w : P')), hδmem w⟩
        map_one' := Subtype.ext (Prod.ext rfl (by simp))
        map_mul' := fun w w' => Subtype.ext (Prod.ext rfl (by simp)) }
    let μ : W' →* E :=
      { toFun := fun w' => ⟨((1 : P), (w' : P')), hμmem w'⟩
        map_one' := rfl
        map_mul' := fun w w' => Subtype.ext (Prod.ext (one_mul 1).symm rfl) }
    have hδinj : ∀ w, δ w = 1 → w = 1 := fun w h => Subtype.ext (congrArg (fun e => e.1.1) h)
    have hDc : δ.range ≤ center E := by
      rintro _ ⟨w, rfl⟩
      refine mem_center_iff.2 fun e => Subtype.ext (Prod.ext ?_ ?_)
      · exact mem_center_iff.1 (hWc w.2) e.1.1
      · exact mem_center_iff.1 (hW'c (g w).2) e.1.2
    have : δ.range.Normal := ⟨fun n hn e => by
      rw [mem_center_iff.1 (hDc hn) e, mul_inv_cancel_right]
      exact hn⟩
    have hsqD : ∀ e : E, e ^ 2 ∈ δ.range := by
      rintro ⟨⟨x, y⟩, hxy⟩
      refine ⟨⟨x ^ 2, sq_mem_of_quotient hU x⟩, Subtype.ext (Prod.ext rfl ?_)⟩
      change (g ⟨x ^ 2, sq_mem_of_quotient hU x⟩ : P') = y ^ 2
      exact hsq x y hxy
    have hE'2 : ∀ z : E ⧸ δ.range, z ^ 2 = 1 := fun z => by
      induction z using QuotientGroup.induction_on with | H e => ?_
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hsqD e
    have hE'comm : ∀ a b : E ⧸ δ.range, a * b = b * a := fun a b => by
      have h1 := hE'2 (a * b)
      have h2 := hE'2 a
      have h3 := hE'2 b
      rw [sq] at h1 h2 h3
      calc a * b = a * (a * b * (a * b)) * b := by rw [h1, mul_one]
        _ = (a * a) * b * a * (b * b) := by group
        _ = b * a := by rw [h2, h3, one_mul, mul_one]
    have hE'el : CFSG.IsElementaryAbelian 2 (E ⧸ δ.range) :=
      { toIsMulCommutative := ⟨⟨hE'comm⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hE'2 }
    obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 (E ⧸ δ.range)
      (μ.range.map (QuotientGroup.mk' δ.range))
    set H := C.comap (QuotientGroup.mk' δ.range) with hH
    have hDH : δ.range ≤ H := fun e he => by
      rw [hH, mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff e).2 he]
      exact one_mem _
    have hμH : ∀ w', μ w' ∈ H → w' = 1 := by
      intro w' hw'
      have hbot : QuotientGroup.mk' δ.range (μ w') ∈
          C ⊓ μ.range.map (QuotientGroup.mk' δ.range) :=
        ⟨hw', mem_map_of_mem _ ⟨w', rfl⟩⟩
      rw [hC.symm.inf_eq_bot, mem_bot, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hbot
      obtain ⟨w, hw⟩ := hbot
      have h1 : (w : P) = 1 := congrArg (fun e => e.1.1) hw
      have hw1 : w = 1 := Subtype.ext h1
      have h2 : (g w : P') = w' := congrArg (fun e => e.1.2) hw
      rw [hw1, map_one] at h2
      exact Subtype.ext h2.symm
    have hsplit : ∀ e : E, ∃ w' : W', e * (μ w')⁻¹ ∈ H := by
      intro e
      have he : QuotientGroup.mk' δ.range e ∈ C ⊔ μ.range.map (QuotientGroup.mk' δ.range) := by
        rw [hC.symm.sup_eq_top]
        exact mem_top _
      have hMn : (μ.range.map (QuotientGroup.mk' δ.range)).Normal := ⟨fun n hn g => by
        rw [hE'comm g n, mul_inv_cancel_right]; exact hn⟩
      rw [← SetLike.mem_coe, Subgroup.mul_normal C (μ.range.map (QuotientGroup.mk' δ.range))] at he
      obtain ⟨c, hc, _, ⟨_, ⟨w', rfl⟩, rfl⟩, hce⟩ := he
      refine ⟨w', ?_⟩
      rw [hH, mem_comap, map_mul, map_inv, ← hce, mul_inv_cancel_right]
      exact hc
    have hex : ∀ x : P, ∃ y : P', ∃ hxy : (x, y) ∈ E, (⟨(x, y), hxy⟩ : E) ∈ H := by
      intro x
      obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (f (x : P ⧸ W))
      obtain ⟨w', hw'⟩ := hsplit ⟨(x, y₀), hy₀.symm⟩
      set e := ((⟨(x, y₀), hy₀.symm⟩ : E) * (μ w')⁻¹ : E) with he
      have he1 : (e : P × P').1 = x := by
        change x * (1 : P)⁻¹ = x
        rw [inv_one, mul_one]
      have hmem : (x, (e : P × P').2) ∈ E := by
        have h := e.2
        rw [show (e : P × P') = (x, (e : P × P').2) from Prod.ext he1 rfl] at h
        exact h
      refine ⟨(e : P × P').2, hmem, ?_⟩
      convert hw' using 1
      exact Subtype.ext (Prod.ext he1.symm rfl)
    have huniq : ∀ (x : P) (y y' : P') (hy : (x, y) ∈ E) (hy' : (x, y') ∈ E),
        (⟨(x, y), hy⟩ : E) ∈ H → (⟨(x, y'), hy'⟩ : E) ∈ H → y = y' := by
      intro x y y' hy hy' hH1 hH2
      have hW' : y⁻¹ * y' ∈ W' :=
        QuotientGroup.eq.1 (((hmemE _ _).1 hy).symm.trans ((hmemE _ _).1 hy'))
      have hprod : μ ⟨y⁻¹ * y', hW'⟩ = (⟨(x, y), hy⟩ : E)⁻¹ * ⟨(x, y'), hy'⟩ :=
        Subtype.ext (Prod.ext (by change (1 : P) = x⁻¹ * x; rw [inv_mul_cancel]) rfl)
      have h1 := hμH ⟨y⁻¹ * y', hW'⟩ (by rw [hprod]; exact mul_mem (inv_mem hH1) hH2)
      have h2 : y⁻¹ * y' = 1 := congrArg Subtype.val h1
      rw [inv_mul_eq_one] at h2
      exact h2
    choose hfun hhE hhH using hex
    have hmul : ∀ x x', hfun (x * x') = hfun x * hfun x' := by
      intro x x'
      have hm : (x * x', hfun x * hfun x') ∈ E := mul_mem (hhE x) (hhE x')
      exact huniq _ _ _ (hhE _) hm (hhH _) (mul_mem (hhH x) (hhH x'))
    let hhom : P →* P' :=
      { toFun := hfun
        map_one' := huniq 1 _ 1 (hhE 1) (one_mem E) (hhH 1) (one_mem H)
        map_mul' := hmul }
    have hg : ∀ w : W, hfun w = g w := fun w =>
      huniq _ _ _ (hhE _) (hδmem w) (hhH _) (hDH ⟨w, rfl⟩)
    have hfw : ∀ x : P, (hfun x : P' ⧸ W') = f x := fun x => ((hmemE _ _).1 (hhE x)).symm
    have hinj : Function.Injective hhom := by
      rw [injective_iff_map_eq_one]
      intro x hx
      change hfun x = 1 at hx
      have h1 : f (x : P ⧸ W) = 1 := by rw [← hfw, hx, QuotientGroup.mk_one]
      rw [map_eq_one_iff f f.injective, QuotientGroup.eq_one_iff] at h1
      have h2 := hg ⟨x, h1⟩
      rw [show ((⟨x, h1⟩ : W) : P) = x from rfl, hx] at h2
      have h3 : g ⟨x, h1⟩ = 1 := Subtype.ext h2.symm
      rw [map_eq_one_iff g g.injective] at h3
      exact congrArg Subtype.val h3
    have hcard : Nat.card P = Nat.card P' := by
      rw [card_eq_card_quotient_mul_card_subgroup W, card_eq_card_quotient_mul_card_subgroup W',
        Nat.card_congr f.toEquiv, Nat.card_congr g.toEquiv]
    have hbij : Function.Bijective hhom := hinj.bijective_of_nat_card_le hcard.ge
    exact ⟨MulEquiv.ofBijective hhom hbij, hg, hfw⟩

end CFSG.LocalAnalysis.ComponentInitial
