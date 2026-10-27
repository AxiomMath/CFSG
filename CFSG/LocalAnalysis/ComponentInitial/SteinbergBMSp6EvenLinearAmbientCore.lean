module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup LinearFlag LinearThreeFourOuter

variable {k : Type} [Field k] {σ : k ≃+* k}
variable {Y : Type} [Group Y] {D : Subgroup Y} [D.Normal]

@[expose] def layerAct (χ : D ≃* projectiveSL 3 k) : Y →* MulAut (projectiveSL 3 k) :=
  (MulAut.congr χ).toMonoidHom.comp MulAut.conjNormal

theorem layerAct_apply (χ : D ≃* projectiveSL 3 k) (y : Y) (p : projectiveSL 3 k) :
    layerAct χ y p = χ (MulAut.conjNormal y (χ.symm p)) :=
  rfl

theorem layerAct_coe (χ : D ≃* projectiveSL 3 k) (d : D) :
    layerAct χ (d : Y) = MulAut.conj (χ d) := by
  ext p
  rw [layerAct_apply, MulAut.conj_apply]
  have h : MulAut.conjNormal (d : Y) (χ.symm p) = d * χ.symm p * d⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem layerAct_of_intertwine (χ : D ≃* projectiveSL 3 k) {a : Y}
    (hχ : ∀ d : D, χ (MulAut.conjNormal a d) = fieldAut 3 k σ (χ d)) :
    layerAct χ a = fieldAut 3 k σ := by
  ext p
  rw [layerAct_apply, hχ, MulEquiv.apply_symm_apply]

theorem layerAct_injective (χ : D ≃* projectiveSL 3 k) (hCD : centralizer (D : Set Y) = ⊥) :
    Function.Injective (layerAct χ) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hy' : y ∈ centralizer (D : Set Y) := by
    rw [mem_centralizer_iff]
    intro d hd
    have h1 := congrArg (fun φ : MulAut (projectiveSL 3 k) => φ (χ ⟨d, hd⟩)) hy
    simp only [layerAct_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
    have h2 := congrArg (fun x : D => (x : Y)) (χ.injective h1)
    simp only [MulAut.conjNormal_apply] at h2
    calc d * y = y * d * y⁻¹ * y := by rw [h2]
      _ = y * d := by rw [inv_mul_cancel_right]
  rw [hCD] at hy'
  exact (mem_bot.1 hy')

theorem conj_eq_layerAct (χ : D ≃* projectiveSL 3 k) (p : projectiveSL 3 k) :
    MulAut.conj p = layerAct χ (χ.symm p : Y) := by
  rw [layerAct_coe, MulEquiv.apply_symm_apply]

abbrev OutP (k : Type) [Field k] : Type :=
  kˣ ⋊[inversionAction kˣ] (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))

abbrev outEl (x : kˣ) (u v : ZMod 2) : OutP k :=
  ⟨x, (Multiplicative.ofAdd u, Multiplicative.ofAdd v)⟩

theorem outEl_mul (x y : kˣ) (u v u' v' : ZMod 2) :
    outEl x u v * outEl y u' v' =
      outEl (x * if u + v = 0 then y else y⁻¹) (u + u') (v + v') := by
  refine SemidirectProduct.ext ?_ ?_
  · rw [SemidirectProduct.mul_left, inversionAction_apply]
  · rfl

theorem outEl_s_mul_zero_one (x : kˣ) :
    (outEl 1 1 0 : OutP k) * outEl x 0 1 = outEl x⁻¹ 1 1 := by
  rw [outEl_mul, ite_eq_right (by decide), one_mul]
  rfl

theorem outEl_s_mul_one_one (x : kˣ) :
    (outEl 1 1 0 : OutP k) * outEl x 1 1 = outEl x⁻¹ 0 1 := by
  rw [outEl_mul, ite_eq_right (by decide), one_mul]
  rfl

theorem outEl_pow_three_one_one (hk : Nat.card k = 4) (y : kˣ) :
    outEl y 1 1 ^ 3 = (outEl 1 1 1 : OutP k) := by
  rw [pow_succ, pow_two, outEl_mul, outEl_mul, ite_eq_left (by decide), ite_eq_left (by decide),
    ← pow_two, ← pow_succ, units_pow_three hk]
  rfl

theorem outEl_graph_reach (hk : Nat.card k = 4) (x : kˣ) :
    (outEl 1 1 0 : OutP k) * ((outEl 1 1 0) * outEl x 0 1) ^ 3 = outEl 1 0 1 := by
  rw [outEl_s_mul_zero_one, outEl_pow_three_one_one hk, outEl_s_mul_one_one, inv_one]

theorem outEl_eta (π : OutP k) :
    π = outEl π.left (Multiplicative.toAdd π.right.1) (Multiplicative.toAdd π.right.2) :=
  SemidirectProduct.ext rfl rfl

theorem outEl_inv_zero_zero (x : kˣ) : (outEl x 0 0 : OutP k)⁻¹ = outEl x⁻¹ 0 0 := by
  rw [inv_eq_iff_mul_eq_one, outEl_mul, ite_eq_left (by decide), mul_inv_cancel]
  rfl

theorem outEl_conj_field (h : kˣ) :
    (outEl h 0 0 : OutP k) * outEl 1 1 0 * (outEl h 0 0)⁻¹ = outEl (h * h) 1 0 := by
  rw [outEl_inv_zero_zero, outEl_mul, ite_eq_left (by decide), mul_one, outEl_mul,
    ite_eq_right (by decide), inv_inv]
  rfl

abbrev noGraph (k : Type) [Field k] : Subgroup (OutP k) :=
  ((MonoidHom.snd _ _).comp SemidirectProduct.rightHom).ker

theorem card_noGraph (hk : Nat.card k = 4) : Nat.card (noGraph k) = 6 := by
  have e : noGraph k ≃ kˣ × Multiplicative (ZMod 2) :=
    { toFun := fun π => (π.1.left, π.1.right.1)
      invFun := fun xu => ⟨⟨xu.1, (xu.2, 1)⟩, rfl⟩
      left_inv := fun π => by
        apply Subtype.ext
        refine SemidirectProduct.ext rfl (Prod.ext rfl ?_)
        exact (MonoidHom.mem_ker.1 π.2).symm
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_units_eq_three hk, Nat.card_eq_fintype_card]
  rfl

theorem even_linear_layer_extension_core [Finite Y] (hk : Nat.card k = 4)
    (hσ : ∀ c, σ c = c ^ 2) (χ : D ≃* projectiveSL 3 k) {a : Y}
    (hχ : ∀ d : D, χ (MulAut.conjNormal a d) = fieldAut 3 k σ (χ d))
    (hCD : centralizer (D : Set Y) = ⊥) (hCa : centralizer {a} ≤ zpowers a ⊔ D) :
    ∃ η : Y →* Multiplicative (ZMod 2), η a = Multiplicative.ofAdd 1 ∧ (∀ d ∈ D, η d = 1) ∧
      (∀ t : Y, t ^ 2 = 1 → η t = 1 → t ∈ D) ∧
      (∀ t : Y, t ^ 2 = 1 → η t = Multiplicative.ofAdd 1 → ∃ y : Y, y * t * y⁻¹ = a) ∧
      (Nat.card Y = 2 * 20160 ∨ Nat.card Y = 6 * 20160) := by
  have hfin : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  have hker := ker_eq_range_conj hσ hk hΨ
  set ρ := layerAct (Y := Y) χ with hρdef
  have hρinj : Function.Injective ρ := layerAct_injective χ hCD
  set φ := Ψ.comp ρ with hφdef
  have hΨconj : ∀ p, Ψ (MulAut.conj p) = 1 := fun p => by
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨p, rfl⟩
  have hφD : ∀ d ∈ D, φ d = 1 := fun d hd => by
    change Ψ (ρ ((⟨d, hd⟩ : D) : Y)) = 1
    rw [hρdef, layerAct_coe, hΨconj]
  have hρa : ρ a = fieldAut 3 k σ := layerAct_of_intertwine χ hχ
  have hΨnf : ∀ (A : GL (Fin 3) k) (u v : ZMod 2),
      Ψ (nf σ A u v) = outEl (Matrix.GeneralLinearGroup.det A) u v := hΨ
  have hφa : φ a = outEl 1 1 0 := by
    change Ψ (ρ a) = _
    rw [hρa, ← nf_one_zero σ, hΨnf, map_one]
  have hΨδ : Ψ (dualAut 3 k) = outEl 1 0 1 := by
    rw [← nf_zero_one σ, hΨnf, map_one]
  have hΨc : ∀ H : GL (Fin 3) k, Ψ (conjAut 3 k H) = outEl (Matrix.GeneralLinearGroup.det H) 0 0 :=
    fun H => by rw [← nf_zero_zero σ H, hΨnf]
  have hlift : ∀ α : MulAut (projectiveSL 3 k), Ψ α ∈ φ.range → ∃ w : Y, ρ w = α := by
    rintro α ⟨y, hy⟩
    have h1 : ρ y * α⁻¹ ∈ Ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change φ y * (Ψ α)⁻¹ = 1
      rw [hy, mul_inv_cancel]
    rw [hker] at h1
    obtain ⟨p, hp⟩ := h1
    refine ⟨(χ.symm p : Y)⁻¹ * y, ?_⟩
    rw [map_mul, map_inv, hρdef, ← conj_eq_layerAct, ← hρdef, hp, _root_.mul_inv_rev, inv_inv,
      mul_assoc, inv_mul_cancel, mul_one]
  have hkerφ : ∀ y, φ y = 1 → y ∈ D := fun y hy => by
    have h1 : ρ y ∈ Ψ.ker := hy
    rw [hker] at h1
    obtain ⟨p, hp⟩ := h1
    rw [conj_eq_layerAct χ p] at hp
    rw [← hρinj hp]
    exact (χ.symm p).2
  set gr : Y →* Multiplicative (ZMod 2) :=
    ((MonoidHom.snd _ _).comp SemidirectProduct.rightHom).comp φ with hgrdef
  have hgr_le : zpowers a ⊔ D ≤ gr.ker := by
    refine sup_le ?_ fun d hd => ?_
    · rw [zpowers_le, MonoidHom.mem_ker]
      change (φ a).right.2 = 1
      rw [hφa]
      rfl
    · rw [MonoidHom.mem_ker]
      change (φ d).right.2 = 1
      rw [hφD d hd]
      rfl
  have hgr : ∀ y, gr y = 1 := by
    intro y
    by_contra hy
    have hy2 : (φ y).right.2 = Multiplicative.ofAdd 1 := by
      rcases zmod_two_cases (Multiplicative.toAdd (φ y).right.2) with h | h
      · refine absurd ?_ hy
        change (φ y).right.2 = 1
        rw [← ofAdd_toAdd ((φ y).right.2), h]
        rfl
      · rw [← ofAdd_toAdd ((φ y).right.2), h]
    obtain ⟨y₁, x₁, hy₁⟩ : ∃ y₁ : Y, ∃ x₁ : kˣ, φ y₁ = outEl x₁ 0 1 := by
      have e := outEl_eta (φ y)
      rw [hy2, toAdd_ofAdd] at e
      rcases zmod_two_cases (Multiplicative.toAdd (φ y).right.1) with h | h
      · exact ⟨y, (φ y).left, by rw [e, h]⟩
      · refine ⟨a * y, ((φ y).left)⁻¹, ?_⟩
        rw [map_mul, hφa, e, h, outEl_s_mul_one_one]
    have hreach : φ (a * (a * y₁) ^ 3) = outEl 1 0 1 := by
      rw [map_mul, map_pow, map_mul, hφa, hy₁, outEl_graph_reach hk]
    obtain ⟨w, hw⟩ := hlift (dualAut 3 k) ⟨_, hreach.trans hΨδ.symm⟩
    have hwa : w ∈ centralizer {a} := by
      rw [mem_centralizer_singleton_iff]
      apply hρinj
      rw [map_mul, map_mul, hw, hρa, dualAut_mul_fieldAut]
    have h1 := MonoidHom.mem_ker.1 (hgr_le (hCa hwa))
    change (φ w).right.2 = 1 at h1
    rw [show φ w = Ψ (ρ w) from rfl, hw, hΨδ] at h1
    exact (show (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 by decide) h1
  set η : Y →* Multiplicative (ZMod 2) :=
    ((MonoidHom.fst _ _).comp SemidirectProduct.rightHom).comp φ with hηdef
  have hφη : ∀ y, φ y = outEl (φ y).left (Multiplicative.toAdd (η y)) 0 := fun y => by
    have e := outEl_eta (φ y)
    have hg : (φ y).right.2 = 1 := hgr y
    rw [hg] at e
    exact e
  refine ⟨η, ?_, fun d hd => ?_, fun t ht hηt => ?_, fun t ht hηt => ?_, ?_⟩
  · change (φ a).right.1 = _
    rw [hφa]
  · change (φ d).right.1 = 1
    rw [hφD d hd]
    rfl
  ·
    apply hkerφ
    have e := hφη t
    rw [hηt, toAdd_one] at e
    have hsq : φ t * φ t = 1 := by rw [← map_mul, ← pow_two, ht, map_one]
    rw [e, outEl_mul, ite_eq_left (by decide)] at hsq
    have hx2 : (φ t).left * (φ t).left = 1 := congrArg SemidirectProduct.left hsq
    have hx3 := units_pow_three hk (φ t).left
    have hx1 : (φ t).left = 1 := by
      calc (φ t).left = (φ t).left ^ 3 * ((φ t).left * (φ t).left)⁻¹ := by group
        _ = 1 := by rw [hx3, hx2, inv_one, one_mul]
    rw [e, hx1]
    rfl
  ·
    obtain ⟨⟨A, u, v⟩, hA⟩ := exists_nf hσ hk (ρ t)
    have e := hφη t
    rw [hηt, toAdd_ofAdd] at e
    have hΨt : Ψ (ρ t) = outEl (Matrix.GeneralLinearGroup.det A) u v := by rw [hA, hΨnf]
    have huv : u = 1 ∧ v = 0 := by
      have h1 : φ t = outEl (Matrix.GeneralLinearGroup.det A) u v := hΨt
      rw [e] at h1
      have hr := congrArg SemidirectProduct.right h1
      change ((Multiplicative.ofAdd (1 : ZMod 2), Multiplicative.ofAdd (0 : ZMod 2)) :
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
          (Multiplicative.ofAdd u, Multiplicative.ofAdd v) at hr
      rw [Prod.mk.injEq] at hr
      exact ⟨(Multiplicative.ofAdd.injective hr.1).symm,
        (Multiplicative.ofAdd.injective hr.2).symm⟩
    obtain ⟨rfl, rfl⟩ := huv
    have hρt : ρ t = conjAut 3 k A * fieldAut 3 k σ := by
      rw [hA, nf, val_one_two, ZMod.val_zero, pow_one, pow_zero, mul_one]
    have hsq : (conjAut 3 k A * fieldAut 3 k σ) ^ 2 = 1 := by
      rw [← hρt, ← map_pow, ht, map_one]
    obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent (K := k) (f := 2)
      (by norm_num) (by rw [hk]; norm_num) le_rfl A σ (sigma_ne_one hσ hk) hsq
    have hφt : φ t = outEl (Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det H)
        1 0 := by
      change Ψ (ρ t) = _
      rw [hρt, hH, map_mul, map_mul, map_inv, hΨc, ← nf_one_zero σ, hΨnf, map_one,
        outEl_conj_field]
    have hφta : φ ((t * a) ^ 2) = outEl (Matrix.GeneralLinearGroup.det H) 0 0 := by
      rw [map_pow, map_mul, hφt, hφa, outEl_mul, ite_eq_right (by decide), inv_one, mul_one,
        pow_two, outEl_mul, ite_eq_left (by decide)]
      have h3 := units_pow_three hk (Matrix.GeneralLinearGroup.det H)
      have e4 : Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det H *
          (Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det H) =
            Matrix.GeneralLinearGroup.det H := by
        calc _ = Matrix.GeneralLinearGroup.det H ^ 3 * Matrix.GeneralLinearGroup.det H := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = _ := by rw [h3, one_mul]
      rw [e4]
      rfl
    obtain ⟨w, hw⟩ := hlift (conjAut 3 k H) ⟨_, hφta.trans (hΨc H).symm⟩
    refine ⟨w⁻¹, ?_⟩
    apply hρinj
    rw [map_mul, map_mul, map_inv, inv_inv, hρt, hH, hw, ← hρa]
    group
  ·
    have hcardD : Nat.card D = 20160 := by
      rw [Nat.card_congr χ.toEquiv]
      exact GL3TwoFixedModel.card_projectiveSL_three_four hk
    have hkerD : φ.ker = D := le_antisymm (fun y hy => hkerφ y hy) fun d hd => hφD d hd
    have hcardY : Nat.card Y = Nat.card D * Nat.card φ.range := by
      rw [← hkerD, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
        mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hle : φ.range ≤ noGraph k := by
      rintro _ ⟨y, rfl⟩
      exact hgr y
    have hdvd6 : Nat.card φ.range ∣ 6 := by
      rw [← card_noGraph hk]
      exact Subgroup.card_dvd_of_le hle
    have hdvd2 : 2 ∣ Nat.card φ.range := by
      have hmem : φ a ∈ φ.range := MonoidHom.mem_range.2 ⟨a, rfl⟩
      have h1 : orderOf (⟨φ a, hmem⟩ : φ.range) = 2 := by
        rw [Subgroup.orderOf_mk, hφa]
        refine orderOf_eq_prime ?_ ?_
        · rw [pow_two, outEl_mul, ite_eq_right (by decide), inv_one, mul_one]
          rfl
        · intro h
          have h' := congrArg (fun π : OutP k => Multiplicative.toAdd π.right.1) h
          change (1 : ZMod 2) = 0 at h'
          exact absurd h' (by decide)
      have h2 := orderOf_dvd_natCard (⟨φ a, hmem⟩ : φ.range)
      rwa [h1] at h2
    have hc : Nat.card φ.range = 2 ∨ Nat.card φ.range = 6 := by
      obtain ⟨m, hm⟩ := hdvd2
      rw [hm] at hdvd6 ⊢
      have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
        (by simpa using hdvd6)
      rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
      · left; rfl
      · right; rfl
    rw [hcardY, hcardD]
    rcases hc with h | h <;> rw [h]
    · left; norm_num
    · right; norm_num

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
