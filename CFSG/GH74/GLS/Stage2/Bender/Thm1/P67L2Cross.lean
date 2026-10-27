module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L2Char
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Cent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.PSL2Table
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement MatrixGroups


section CrossL2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem no_elemAbelian_sq_psl2 (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} (hr : r.Prime)
    (hr2 : Odd r) (hrp : ringChar F ≠ r) (E : Subgroup K) (hE : ∀ c ∈ E, c ^ r = 1)
    (hEc : Nat.card ↥E = r ^ 2) : False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨n, -, hq⟩ := FiniteField.card F (ringChar F)
  have hqcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hq
  have : Fact r.Prime := ⟨hr⟩
  set E' : Subgroup (PSL2 F) := E.map (toPSL e).toMonoidHom with hE'
  have hE'c : Nat.card ↥E' = r ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (toPSL e).injective]; exact hEc
  have hE'p : ∀ c ∈ E', c ^ r = 1 := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE c hc, map_one]
  by_cases h7 : 7 ≤ Nat.card F
  · have hpg : IsPGroup r ↥E' := by
      refine IsPGroup.of_card (n := 2) hE'c
    obtain ⟨R, hR⟩ := hpg.exists_le_sylow
    have hcop : Nat.Coprime r (Nat.card F) := by
      rw [hqcard]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr hp).mpr (Ne.symm hrp))
    have hcyc := psl2_sylow_isCyclic_of_coprime_field_card F hqcard h7 r (by
      rintro rfl; exact absurd hr2 (by decide)) hcop R
    have hEcyc : IsCyclic ↥E' := by
      have : IsCyclic ↥(E'.subgroupOf (R : Subgroup (PSL2 F))) := Subgroup.isCyclic _
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hR).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hR).surjective
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E')
    have h1 : orderOf g ∣ r := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      exact hE'p g g.2
    rw [hg, hE'c] at h1
    have := Nat.le_of_dvd hr.pos h1
    have h2 : r < r ^ 2 := by nlinarith [hr.one_lt]
    omega
  ·
    have hq5 : Nat.card F = 5 := by
      have h3 := hF.2
      have h4 := hF.1
      obtain ⟨k, hk⟩ := h4
      omega
    have hp5 : ringChar F = 5 := by
      have := hqcard
      rw [hq5] at this
      have h5 : (ringChar F) ^ (n : ℕ) = 5 := this.symm
      have := (Nat.prime_five.eq_one_or_self_of_dvd (ringChar F) ?_)
      · rcases this with h | h
        · exact absurd h hp.ne_one
        · exact h
      · exact (dvd_pow_self _ n.ne_zero).trans (by rw [h5])
    have hcardP : Nat.card (PSL2 F) = 60 := by
      have := CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd (F := F) (p := ringChar F) (f := (n : ℕ))
        hqcard (by rw [hp5]; norm_num)
      rw [this, hqcard.symm, hq5]
      norm_num
    have hdvd : r ^ 2 ∣ 60 := by
      rw [← hcardP, ← hE'c]
      exact Subgroup.card_subgroup_dvd_card E'
    have hr_le : r ≤ 8 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      nlinarith [hr.one_lt]
    interval_cases r <;> first
      | exact absurd hr (by decide)
      | exact absurd hr2 (by decide)
      | exact absurd hdvd (by decide)

theorem not_le_innDiag (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} (hr : r.Prime) (hr2 : Odd r)
    (hrp : ringChar F ≠ r) {V : Subgroup (MulAut K)} (hVe : IsElementaryAbelian r ↥V)
    (hVc : Nat.card ↥V = r ^ 2) : ¬ V ≤ innDiagSub e := by
  intro hVD
  have : Fact r.Prime := ⟨hr⟩
  have hVI : ∀ v ∈ V, v ∈ innAut K := fun v hv =>
    mem_innAut_of_odd_pow hF e (hVD hv) hr2
      (elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) v hv)
  set E : Subgroup K := V.comap (MulAut.conj : K →* MulAut K) with hE
  have hinj := conj_injective_of_L2 e
  have hEmap : E.map (MulAut.conj : K →* MulAut K) = V := by
    rw [hE, Subgroup.map_comap_eq_self]
    intro v hv
    exact hVI v hv
  have hEc : Nat.card ↥E = r ^ 2 := by
    rw [← hVc, ← hEmap, Subgroup.card_map_of_injective hinj]
  refine no_elemAbelian_sq_psl2 hF e hr hr2 hrp E (fun c hc => ?_) hEc
  apply hinj
  rw [map_pow, map_one]
  exact elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) _ hc

theorem exists_conj_fieldAut (e : K ≃* L2 F) {r : ℕ} (hr : r.Prime) {b : MulAut K}
    (hb : b ^ r = 1) (hbD : b ∉ innDiagSub e) :
    ∃ (σ : F ≃+* F) (d : MulAut K), orderOf σ = r ∧ d ∈ innDiagSub e ∧
      b = d * fieldAutHom e σ * d⁻¹ := by
  set x : PGammaL2 F := (pgammaAut e).symm b with hx
  have hxb : pgammaAut e x = b := by simp [hx]
  have hxr : x ^ r = 1 := by
    apply (pgammaAut e).injective
    rw [map_pow, hxb, hb, map_one]
  set σ := x.right with hσ
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hbD
    have : x = SemidirectProduct.inl x.left :=
      SemidirectProduct.ext (by simp) (by simpa using h1)
    rw [← hxb, this, pgammaAut_inl]
    exact ⟨x.left, rfl⟩
  have hσr : σ ^ r = 1 := by
    have h1 := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) hxr
    rw [map_pow, map_one] at h1
    exact h1
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf σ = r := orderOf_eq_prime hσr hσ1
  obtain ⟨C, hC⟩ := H90.pgammaL2_conj_inr_of_pow_eq_one x (by rw [← hσ, hord]; exact hxr)
  refine ⟨σ, pgammaAut e (SemidirectProduct.inl C), hord, ?_, ?_⟩
  · rw [pgammaAut_inl]; exact ⟨C, rfl⟩
  · have hx2 : x = SemidirectProduct.inl C * SemidirectProduct.inr σ *
        (SemidirectProduct.inl C)⁻¹ := by
      rw [← hC]; group
    rw [← hxb, hx2, map_mul, map_mul, map_inv, pgammaAut_inr]


end CrossL2

section CrossL2b

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem isOddPrimePower_card_of_ne_two (F₀ : Type) [Field F₀] [Finite F₀] (h2 : (2 : F₀) ≠ 0) :
    IsOddPrimePower (Nat.card F₀) := by
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hp : (ringChar F₀).Prime := CharP.char_is_prime F₀ (ringChar F₀)
  have : Fact (ringChar F₀).Prime := ⟨hp⟩
  obtain ⟨n, -, hq⟩ := FiniteField.card F₀ (ringChar F₀)
  refine ⟨ringChar F₀, (n : ℕ), hp, ?_, n.pos, by rw [Nat.card_eq_fintype_card]; exact hq⟩
  rcases hp.eq_two_or_odd' with h | h
  · exfalso
    apply h2
    have : ((2 : ℕ) : F₀) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
    simpa using this
  · exact h

theorem eq_bot_of_normal_abelian_odd (F₀ : Type) [Field F₀] [Finite F₀] (h2 : (2 : F₀) ≠ 0)
    (N : Subgroup (L2 F₀)) [hN : N.Normal] (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  classical
  by_contra hne
  have hodd' := isOddPrimePower_card_of_ne_two F₀ h2
  have hN1 : Nat.card ↥N ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  set s := (Nat.card ↥N).minFac with hs
  have hsp : s.Prime := Nat.minFac_prime hN1
  have hsd : s ∣ Nat.card ↥N := Nat.minFac_dvd _
  have hsodd : Odd s := Odd.of_dvd_nat hodd hsd
  have : Fact s.Prime := ⟨hsp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' s hsd
  let P : Subgroup (L2 F₀) :=
    { carrier := {y | y ∈ N ∧ ∃ k : ℕ, y ^ (s ^ k) = 1}
      one_mem' := ⟨N.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨N.mul_mem ha hb, k + l, ?_⟩
        have hc : Commute a b := hab a ha b hb
        rw [hc.mul_pow]
        have h1 : a ^ (s ^ (k + l)) = 1 := by
          rw [pow_add, pow_mul, hk, one_pow]
        have h2 : b ^ (s ^ (k + l)) = 1 := by
          rw [pow_add, mul_comm, pow_mul, hl, one_pow]
        rw [h1, h2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        refine ⟨N.inv_mem ha, k, ?_⟩
        rw [inv_pow, hk, inv_one] }
  have hPn : P.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨haN, k, hk⟩ := ha
    refine ⟨hN.conj_mem a haN g, k, ?_⟩
    rw [conj_pow, hk]; simp
  have hPp : IsPGroup s ↥P := by
    intro y
    obtain ⟨-, k, hk⟩ := y.2
    exact ⟨k, Subtype.ext hk⟩
  have hPbot := normal_pSubgroup_eq_bot_of_psl2_odd F₀ hodd' s hsp hsodd
    (P.map (L2.equivPSL F₀).toMonoidHom)
    (hPn.map (L2.equivPSL F₀).toMonoidHom (L2.equivPSL F₀).surjective)
    (by
      have := hPp.map (L2.equivPSL F₀).toMonoidHom
      exact this)
  have hxP : (x : L2 F₀) ∈ P := by
    refine ⟨x.2, 1, ?_⟩
    have h1 : (x : ↥N) ^ s = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hx1 : (L2.equivPSL F₀) (x : L2 F₀) ∈ P.map (L2.equivPSL F₀).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hxP
  rw [hPbot, Subgroup.mem_bot] at hx1
  have hx2 : (x : L2 F₀) = 1 := (L2.equivPSL F₀).injective (by rw [hx1, map_one])
  have hx3 : x = 1 := Subtype.ext hx2
  rw [hx3, orderOf_one] at hx
  exact hsp.one_lt.ne hx


theorem two_ne_zero_of_L2Field (hF : L2Field F) : (2 : F) ≠ 0 := by
  intro h
  have : Fintype F := Fintype.ofFinite F
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have h2 : ringChar F ∣ 2 := by
    have : ((2 : ℕ) : F) = 0 := by simpa using h
    exact (ringChar.spec F 2).mp this
  have h3 : ringChar F = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨n, -, hq⟩ := FiniteField.card F (ringChar F)
  have hqe : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, hq, h3]
    exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr hF.1) hqe

theorem mulAut_conj_conj' (φ : MulAut K) (a : K) :
    φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  ext y; simp [MulAut.conj_apply]

theorem inn_inter_eq_bot_pure (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} {V Z : Subgroup (MulAut K)}
    (h2 : N2Cfg K r V Z) (h3 : N3Full K V Z) {σ : F ≃+* F} (hσ : orderOf σ = r)
    (hfV : fieldAutHom e σ ∈ V) (hf1 : fieldAutHom e σ ≠ 1) :
    ∀ c : K, MulAut.conj c ∈ Z → c = 1 := by
  classical
  obtain ⟨-, hr2, -, -, hZab, hZodd, -, -, hcomm⟩ := h2
  have hinj := conj_injective_of_L2 e
  have hodd : Odd (orderOf σ) := hσ ▸ hr2
  set f : MulAut K := fieldAutHom e σ with hf
  set W : Subgroup K := Z.comap (MulAut.conj : K →* MulAut K) with hW
  set Γ : Subgroup K := fixSub f with hΓ
  have hWΓ : W ≤ Γ := by
    intro c hc
    have hz : MulAut.conj c ∈ Z := hc
    have hcm := hcomm f hfV _ hz
    have h1 := mulAut_conj_conj' f c
    have h4 : f * MulAut.conj c * f⁻¹ = MulAut.conj c := by
      rw [hcm]; group
    rw [h4] at h1
    exact (hinj h1).symm
  have hΓnorm : ∀ g ∈ Γ, ∀ c ∈ W, g * c * g⁻¹ ∈ W := by
    intro g hg c hc
    have hgn := h3 f hfV hf1 g hg
    have hz : MulAut.conj c ∈ Z := hc
    have := (Subgroup.mem_normalizer_iff.mp hgn _).mp hz
    show MulAut.conj (g * c * g⁻¹) ∈ Z
    simpa [map_mul, map_inv] using this
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hZab _ ha _ hb
  have hWodd : Odd (Nat.card ↥W) := by
    have hle : W.map (MulAut.conj : K →* MulAut K) ≤ Z := fun x ⟨c, hc, hx⟩ => hx ▸ hc
    have hd : Nat.card ↥(W.map (MulAut.conj : K →* MulAut K)) ∣ Nat.card ↥Z :=
      Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hinj] at hd
    exact Odd.of_dvd_nat hZodd hd
  have hΓeq : Γ = GH74.GLS.fixedSubgroup K f := rfl
  let ι : ↥Γ ≃* L2 ↥(fixedField σ) := fixedSubgroupEquivL2 e σ hodd
  let N : Subgroup (L2 ↥(fixedField σ)) := (W.subgroupOf Γ).map ι.toMonoidHom
  have hWn : (W.subgroupOf Γ).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hWΓ]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc; simpa using hΓnorm g hg c hc
    · intro hc
      have := hΓnorm g⁻¹ (Γ.inv_mem hg) _ hc
      simpa [mul_assoc] using this
  have hNn : N.Normal := hWn.map ι.toMonoidHom ι.surjective
  have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hWab _ (Subgroup.mem_subgroupOf.mp ha) _ (Subgroup.mem_subgroupOf.mp hb)
  have hNodd : Odd (Nat.card ↥N) := by
    have h1 : Nat.card ↥N = Nat.card ↥(W.subgroupOf Γ) :=
      Subgroup.card_map_of_injective ι.injective
    have h2' : Nat.card ↥(W.subgroupOf Γ) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWΓ).toEquiv
    rw [h1, h2']; exact hWodd
  have h2F₀ : (2 : ↥(fixedField σ)) ≠ 0 := by
    intro h
    apply two_ne_zero_of_L2Field hF
    have h' := map_ofNat (fixedField σ).subtype 2
    rw [h] at h'
    simpa using h'.symm
  have hNbot := eq_bot_of_normal_abelian_odd _ h2F₀ N hNab hNodd
  intro c hc
  have hcΓ : c ∈ Γ := hWΓ hc
  have h5 : (⟨c, hcΓ⟩ : ↥Γ) ∈ W.subgroupOf Γ := Subgroup.mem_subgroupOf.mpr hc
  have h6 : ι ⟨c, hcΓ⟩ ∈ N := Subgroup.mem_map_of_mem _ h5
  rw [hNbot, Subgroup.mem_bot] at h6
  have h7 : (⟨c, hcΓ⟩ : ↥Γ) = 1 := ι.injective (by rw [h6, map_one])
  exact congrArg Subtype.val h7

end CrossL2b



section Rigid

variable {F : Type} [Field F]

theorem psl2FieldAut_mk_unip' (σ : F ≃+* F) (t : F) :
    psl2FieldAut F σ (mk (unip t)) = mk (unip (σ t)) := by
  have h : Matrix.SpecialLinearGroup.map σ.toRingHom (unip t) = unip (σ t) := by
    apply SL_ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) =
    QuotientGroup.mk' (Subgroup.center _) (unip (σ t))
  rw [psl2RingEquiv_mk, h]

@[expose] def weylSL (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem psl2FieldAut_mk_weyl (σ : F ≃+* F) :
    psl2FieldAut F σ (mk (weylSL F)) = mk (weylSL F) := by
  have h : Matrix.SpecialLinearGroup.map σ.toRingHom (weylSL F) = weylSL F := by
    apply SL_ext
    all_goals
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      simp [weylSL]
  rw [psl2FieldAut_apply]
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (weylSL F)) =
    QuotientGroup.mk' (Subgroup.center _) (weylSL F)
  rw [psl2RingEquiv_mk, h]

theorem unip_eq_zero_of_comm_weyl (c : F)
    (h : mk (unip c) * mk (weylSL F) = mk (weylSL F) * mk (unip c)) : c = 0 := by
  rw [← map_mul, ← map_mul] at h
  have h' := (QuotientGroup.eq (s := Subgroup.center SL(2, F))).mp h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h'
  set A : SL(2, F) := unip c * weylSL F with hA
  set B : SL(2, F) := weylSL F * unip c with hB
  have hBA : (B : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) r := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hBA
  simp only [hA, hB, Matrix.SpecialLinearGroup.coe_mul] at h11
  simp [unip, weylSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h11
  exact h11



theorem pslIncl_mk_unip (σ : F ≃+* F) (t : ↥(fixedField σ)) :
    pslIncl σ (mk (unip t)) = mk (unip (t : F)) := by
  have h : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (unip t) = unip (t : F) := by
    apply SL_ext
    all_goals
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      simp [unip]
  change pslIncl σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) = _
  rw [QuotientGroup.mk'_apply, pslIncl_mk, h]
  rfl

theorem pslIncl_mk_weyl (σ : F ≃+* F) :
    pslIncl σ (mk (weylSL ↥(fixedField σ))) = mk (weylSL F) := by
  have h : Matrix.SpecialLinearGroup.map (fixedField σ).subtype (weylSL ↥(fixedField σ)) =
      weylSL F := by
    apply SL_ext
    all_goals
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      simp [weylSL]
  change pslIncl σ (QuotientGroup.mk' (Subgroup.center _) (weylSL _)) = _
  rw [QuotientGroup.mk'_apply, pslIncl_mk, h]
  rfl

theorem psl2_rigid [Finite F] (h2 : (2 : F) ≠ 0) (σ : F ≃+* F) (α : MulAut PSL(2, F))
    (hα : ∀ y : PSL2 ↥(fixedField σ), α (pslIncl σ y) = pslIncl σ y) :
    ∃ τ : F ≃+* F, (∀ t : F, σ t = t → τ t = t) ∧ α = psl2FieldAut F τ := by
  obtain ⟨x, rfl⟩ := (semilinearEquivAut F).surjective α
  have hx : semilinearEquivAut F x = pglAction F x.left * psl2FieldAut F x.right := by
    change semilinearAction F x = _
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  rw [hx] at hα ⊢
  have hunip : ∀ t : F, σ t = t →
      (pglAction F x.left * psl2FieldAut F x.right) (mk (unip t)) = mk (unip t) := by
    intro t ht
    have := hα (mk (unip (⟨t, (mem_fixedField_iff σ t).mpr ht⟩ : ↥(fixedField σ))))
    rwa [pslIncl_mk_unip] at this
  have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (hunip 1 (map_one σ))
  rw [MulAut.mul_apply, psl2FieldAut_mk_unip', map_one, toPGL_pglAction] at h1
  obtain ⟨c, hc⟩ := GH74.GLS.IVK.L2Borel.exists_eq_toPGL_of_commute one_ne_zero
    (mul_inv_eq_iff_eq_mul.mp h1)
  have hg : pglAction F x.left = MulAut.conj (mk (unip c)) := by rw [hc, pglAction_toPGL]
  have hτ : ∀ t : F, σ t = t → x.right t = t := by
    intro t ht
    have h3 := hunip t ht
    rw [MulAut.mul_apply, psl2FieldAut_mk_unip', hg, MulAut.conj_apply,
      unipotent_mul_comm (mk_unip_mem_unipotent c) (mk_unip_mem_unipotent _),
      mul_inv_cancel_right, mk_unip_eq_mk_unip_iff h2] at h3
    exact h3
  have hc0 : c = 0 := by
    have h3 := hα (mk (weylSL ↥(fixedField σ)))
    rw [pslIncl_mk_weyl, MulAut.mul_apply, psl2FieldAut_mk_weyl, hg, MulAut.conj_apply] at h3
    apply unip_eq_zero_of_comm_weyl
    have h4 := congrArg (fun y => y * mk (unip c)) h3
    simpa [mul_assoc] using h4
  refine ⟨x.right, hτ, ?_⟩
  have hu0 : (unip (0 : F) : SL(2, F)) = 1 := by apply SL_ext <;> simp [unip]
  rw [hg, hc0, hu0, map_one, map_one, one_mul]


theorem mem_zpowers_of_fixes_fixedField [Finite F] (σ : F ≃+* F)
    (τ : F ≃+* F) (hτ : ∀ t : F, σ t = t → τ t = t) : τ ∈ Subgroup.zpowers σ := by
  classical
  have hG : IsGaloisGroup (Subgroup.zpowers σ) (fixedField σ) F :=
    IsGaloisGroup.fixedPoints (Subgroup.zpowers σ) F
  let τ' : F ≃ₐ[fixedField σ] F := AlgEquiv.ofRingEquiv (f := τ) (fun x => by
    exact hτ x ((mem_fixedField_iff σ x).mp x.2))
  obtain ⟨h, hh⟩ :=
    (IsGaloisGroup.mulEquivAlgEquiv (Subgroup.zpowers σ) (fixedField σ) F).surjective τ'
  have hτh : (h : F ≃+* F) = τ := by
    ext x
    have := congrArg (fun a : F ≃ₐ[fixedField σ] F => a x) hh
    exact this
  rw [← hτh]
  exact h.2

end Rigid

section RigidK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem eq_one_of_fixes_fixSub (hF : L2Field F) (e : K ≃* L2 F) {σ : F ≃+* F}
    (hodd : Odd (orderOf σ)) {z : MulAut K}
    (hz : ∀ g ∈ GH74.GLS.fixedSubgroup K (fieldAutHom e σ), z g = g)
    (hzo : Nat.Coprime (orderOf z) (orderOf σ)) : z = 1 := by
  classical
  set α : MulAut (PSL2 F) := MulAut.congr (toPSL e) z with hα
  have hαfix : ∀ y : PSL2 ↥(fixedField σ), α (pslIncl σ y) = pslIncl σ y := by
    intro y
    have hmem : pslToK e σ y ∈ GH74.GLS.fixedSubgroup K (fieldAutHom e σ) := by
      rw [← range_pslToK e σ hodd]; exact ⟨y, rfl⟩
    have h1 := hz _ hmem
    rw [← toPSL_pslToK e σ y]
    show (toPSL e) (z ((toPSL e).symm ((toPSL e) (pslToK e σ y)))) = _
    rw [MulEquiv.symm_apply_apply, h1]
  obtain ⟨τ, hτ, hατ⟩ := psl2_rigid (two_ne_zero_of_L2Field hF) σ α hαfix
  have hτσ : τ ∈ Subgroup.zpowers σ := mem_zpowers_of_fixes_fixedField σ τ hτ
  have hτpow : τ ^ orderOf σ = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτσ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hαpow : α ^ orderOf σ = 1 := by
    rw [hατ, ← map_pow, hτpow, map_one]
  have hzpow : z ^ orderOf σ = 1 := by
    apply (MulAut.congr (toPSL e)).injective
    rw [map_pow, map_one]
    exact hαpow
  have hdvd : orderOf z ∣ orderOf σ := orderOf_dvd_of_pow_eq_one hzpow
  have : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd hzo hdvd
  exact orderOf_eq_one_iff.mp this

end RigidK


section CrossAssembly

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem congr_eq_conj' (d v : MulAut K) : MulAut.congr (d : K ≃* K) v = d * v * d⁻¹ := by
  ext x; simp [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_apply]

theorem cf67_L2_cross (hF : L2Field F) (e : K ≃* L2 F) {r : ℕ} {V Z : Subgroup (MulAut K)}
    (h2 : N2Cfg K r V Z) (h3 : N3Full K V Z) (hr : ringChar F ≠ r) : False := by
  classical
  have h2' := h2
  obtain ⟨hrp, hr2, hVe, hVc, -, -, -, -, -⟩ := h2'
  have : Fact r.Prime := ⟨hrp⟩
  have hnle : ¬ V ≤ innDiagSub e := not_le_innDiag hF e hrp hr2 hr hVe hVc
  obtain ⟨b, hbV, hbD⟩ := Set.not_subset.mp hnle
  have hbr : b ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) b hbV
  obtain ⟨σ, d, hσ, -, hbd⟩ := exists_conj_fieldAut e hrp hbr hbD
  obtain ⟨V', hV'⟩ : ∃ V' : Subgroup (MulAut K),
      V' = V.map (MulAut.congr (d⁻¹ : MulAut K)).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨Z', hZ'⟩ : ∃ Z' : Subgroup (MulAut K),
      Z' = Z.map (MulAut.congr (d⁻¹ : MulAut K)).toMonoidHom := ⟨_, rfl⟩
  have h2c : N2Cfg K r V' Z' := by
    rw [hV', hZ']; exact h2.map_mulEquiv (MulAut.congr (d⁻¹ : MulAut K))
  have h3c : N3Full K V' Z' := by
    rw [hV', hZ']; exact h3.map_mulEquiv (d⁻¹ : MulAut K)
  have hfV : fieldAutHom e σ ∈ V' := by
    rw [hV']
    refine ⟨b, hbV, ?_⟩
    show MulAut.congr (d⁻¹ : MulAut K) b = _
    rw [congr_eq_conj', hbd]; group
  have hf1 : fieldAutHom e σ ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hbd
    exact hbD (hbd ▸ (innDiagSub e).one_mem)
  have h2c' := h2c
  obtain ⟨-, -, -, -, hZab', hZodd', hZcop', hZbot', hcomm'⟩ := h2c'
  have hW := inn_inter_eq_bot_pure hF e h2c h3c hσ hfV hf1
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot'
  have hodd : Odd (orderOf σ) := hσ ▸ hr2
  have hfix : ∀ g ∈ GH74.GLS.fixedSubgroup K (fieldAutHom e σ), (z : MulAut K) g = g := by
    intro g hg
    have hgn := h3c _ hfV hf1 g hg
    have h5 := (Subgroup.mem_normalizer_iff.mp hgn z).mp z.2
    have h6 : MulAut.conj g * (z : MulAut K) * (MulAut.conj g)⁻¹ * (z : MulAut K)⁻¹ ∈ Z' :=
      Subgroup.mul_mem _ h5 (Subgroup.inv_mem _ z.2)
    have h7 : MulAut.conj g * (z : MulAut K) * (MulAut.conj g)⁻¹ * (z : MulAut K)⁻¹ =
        MulAut.conj (g * (z : MulAut K) g⁻¹) := by
      have : (z : MulAut K) * (MulAut.conj g)⁻¹ * (z : MulAut K)⁻¹ =
          MulAut.conj ((z : MulAut K) g⁻¹) := by
        have := mulAut_conj_conj' (z : MulAut K) g⁻¹
        simpa [map_inv] using this
      calc MulAut.conj g * (z : MulAut K) * (MulAut.conj g)⁻¹ * (z : MulAut K)⁻¹
          = MulAut.conj g * ((z : MulAut K) * (MulAut.conj g)⁻¹ * (z : MulAut K)⁻¹) := by group
        _ = MulAut.conj (g * (z : MulAut K) g⁻¹) := by rw [this, map_mul]
    rw [h7] at h6
    have h8 := hW _ h6
    have h9 : (z : MulAut K) g⁻¹ = g⁻¹ := by
      have := congrArg (fun t => g⁻¹ * t) h8
      simpa using this
    have := congrArg (fun t => t⁻¹) h9
    simpa using this
  have hdvd : orderOf (z : MulAut K) ∣ Nat.card ↥Z' := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hcop : Nat.Coprime (orderOf (z : MulAut K)) (orderOf σ) := by
    rw [hσ]; exact Nat.Coprime.coprime_dvd_left hdvd hZcop'
  have hz : (z : MulAut K) = 1 :=
    eq_one_of_fixes_fixSub hF e hodd hfix hcop
  exact hz1 (Subtype.ext hz)

end CrossAssembly


end CFSG.GH74.GLS.Stage2.Bender.Thm1
