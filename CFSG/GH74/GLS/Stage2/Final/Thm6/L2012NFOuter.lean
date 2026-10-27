module

public import CFSG.GH74.GLS.SP.Local.SPLFitA
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundGrp
public import CFSG.GH74.GLS.IVK.Lifted.Outer14

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK.Lifted CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
open scoped commutatorElement MatrixGroups

section Fit


@[expose] noncomputable def quotCenterEquiv' {F : Type} [Field F] {K : Type} [Group K] (e : K ≃* SL2 F) :
    K ⧸ Subgroup.center K ≃* L2 F :=
  QuotientGroup.congr (Subgroup.center K)
    ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) e (by
      rw [Subgroup.map_center_eq e]
      exact (CFSG.Semidihedral.ProjectiveSL2Cover.statedScalarKernel_eq_center F 2).symm)

open CFSG.GH74.GLS.SP.Local CFSG.GH74.GLS.IVK.Proofs2 in
theorem odd_abelian_le_xuInn_gen {F : Type} [Field F] [Finite F] (hF : L2Field F)
    {K : Type} [Group K] [Finite K] (e : K ≃* L2 F) {u : MulAut K} (hu : u ∈ innDiagSub e)
    (hu2 : orderOf u = 2)
    {M : Type} [Group M] [Finite M] (α : M →* MulAut K)
    (hα : ∀ m : M, α m * u = u * α m)
    (W : Subgroup M) (hWodd : Odd (Nat.card ↥W)) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hX : ∀ k ∈ xu u, ∃ m : M, α m = MulAut.conj k ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, α w ∈ xuInn u := by
  obtain ⟨Yu, hYuC, hYuN, hYuodd, ⟨k₂, hk₂⟩, hFit, ⟨hnormX, hcyc⟩, -⟩ := ivk_1_3d F hF K e u hu hu2
  set W' : Subgroup (MulAut K) := W.map α with hW'
  have hW'C : W' ≤ centralizer ({u} : Set (MulAut K)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hα w
  have hW'odd : Odd (Nat.card ↥W') := Odd.of_dvd_nat hWodd (Subgroup.card_map_dvd W α)
  have hW'ab : ∀ a ∈ W', ∀ b ∈ W', a * b = b * a := by
    rintro _ ⟨w₁, hw₁, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
    rw [← map_mul, ← map_mul, hWab w₁ hw₁ w₂ hw₂]
  have hW'Yu : W' ≤ Yu := fun g hg =>
    mem_of_odd_orderOf_of_two_power_index _ Yu hYuC hYuN k₂ hk₂ (hW'C hg)
      (Odd.of_dvd_nat hW'odd (Subgroup.orderOf_dvd_natCard W' hg))
  have hXW' : ∀ x ∈ xuInn u, ∀ g ∈ W', x * g * x⁻¹ ∈ W' := by
    intro x hx g hg
    obtain ⟨k, hk, rfl⟩ := hx
    obtain ⟨m, hm, hmW⟩ := hX k hk
    obtain ⟨w, hw, rfl⟩ := hg
    rw [← hm, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨m * w * m⁻¹, hmW w hw, by simp⟩
  have hN : (xuInn u).subgroupOf Yu = CFSG.fittingSubgroup ↥Yu := by
    rw [← hFit]
    exact Subgroup.comap_map_eq_self_of_injective Yu.subtype_injective _
  have hcomm : ∀ a b : ↥Yu, ⁅a, b⁆ ∈ CFSG.fittingSubgroup ↥Yu := by
    intro a b
    rw [← hN]
    have h1 : QuotientGroup.mk' ((xuInn u).subgroupOf Yu) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (IsCyclic.commGroup (α := ↥Yu ⧸ (xuInn u).subgroupOf Yu)).mul_comm _ _
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hmain := le_fitting_of_normalized_abelian (W'.subgroupOf Yu)
    (fun a ha b hb => Subtype.ext (hW'ab _ ha _ hb)) hcomm (by
      intro x hx w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      have hxX : (x : MulAut K) ∈ xuInn u := by
        rw [← hFit]; exact ⟨x, hx, rfl⟩
      simpa using hXW' _ hxX _ hw)
  intro w hw
  have hmem : (⟨α w, hW'Yu ⟨w, hw, rfl⟩⟩ : ↥Yu) ∈ W'.subgroupOf Yu := ⟨w, hw, rfl⟩
  have := hmain hmem
  rw [← hFit]
  exact ⟨_, this, rfl⟩



open CFSG.GH74.GLS.SP.Local CFSG.GH74.GLS.IVK.Proofs2 in
theorem lift_xu_gen {K : Type} [Group K] [Finite K] (hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1) (φ : MulAut K)
    {kb : K ⧸ Subgroup.center K}
    (hkb : kb ∈ xu (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K φ)) :
    ∃ k : K, Odd (orderOf k) ∧ φ k = k ∧ (k : K ⧸ Subgroup.center K) = kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φb := CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K φ with hφb
  have hodd : Odd (orderOf kb) := by
    obtain ⟨c, hc, rfl⟩ := hkb
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(fixedSubgroup (K ⧸ Subgroup.center K) φb))) :=
      pPrimeCore_coprime_card
    have hd : orderOf c ∣ Nat.card (pPrimeCore 2 ↥(fixedSubgroup (K ⧸ Subgroup.center K) φb)) :=
      Subgroup.orderOf_dvd_natCard _ hc
    have hodd' : Odd (orderOf c) := Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hd hcop)
    rwa [show orderOf ((fixedSubgroup (K ⧸ Subgroup.center K) φb).subtype c) = orderOf c from
      Subgroup.orderOf_coe _]
  have hfix : φb kb = kb := by
    have := xu_le_fixedSubgroup φb hkb
    rwa [mem_fixedSubgroup_iff'] at this
  obtain ⟨k, hk, hkk⟩ := exists_odd_lift hZ hodd
  refine ⟨k, hk, ?_, hkk⟩
  have hc : φ k * k⁻¹ ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : ((φ k : K) : K ⧸ Subgroup.center K) = (k : K ⧸ Subgroup.center K) := by
      rw [← CFSG.GH74.GLS.IVK.Lifted.autQuotCenter_mk, hkk]
      exact hfix
    simp [h1]
  set c : K := φ k * k⁻¹ with hcdef
  have hck : c * k = k * c := ((Subgroup.mem_center_iff.mp hc k)).symm
  have hφk : φ k = c * k := by rw [hcdef]; group
  obtain ⟨m, hm⟩ := hk
  have hr : (φ k) ^ orderOf k = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h2 : (c * k) ^ orderOf k = c ^ orderOf k * k ^ orderOf k := by
    rw [(Commute.mul_pow (show Commute c k from hck))]
  rw [hφk, h2, pow_orderOf_eq_one, mul_one] at hr
  have h3 : c ^ orderOf k = c := by
    rw [hm, pow_succ, pow_mul, hZ c hc, one_pow, one_mul]
  have hc1 : c = 1 := by rw [← h3]; exact hr
  rw [hφk, hc1, one_mul]


open CFSG.GH74.GLS.SP.Local in
theorem spl_fit_outer : ∀ (F : Type) [Field F] [Finite F], L2Field F →
    ∀ (K : Type) [Group K] [Finite K] (e : K ≃* SL2 F) (φ : MulAut K), φ * φ = 1 →
    CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K φ ∈ innDiagSub (quotCenterEquiv' e) →
    CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K φ ≠ 1 →
    ∀ (M : Type) [Group M] [Finite M] (α : M →* MulAut K),
      (∀ m : M, α m * φ = φ * α m) →
    ∀ W : Subgroup M, Odd (Nat.card ↥W) → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) →
      (∀ k : K, Odd (orderOf k) → φ k = k →
        ∃ m : M, α m = MulAut.conj k ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) →
      ∀ w ∈ W, ∃ k : K, Odd (orderOf k) ∧ φ k = k ∧ α w = MulAut.conj k := by
  intro F _ _ hF K _ _ e φ hφ2 hφin hφ1 M _ _ α hα W hWodd hWab hX
  have hZ : ∀ c ∈ Subgroup.center K, c ^ 2 = 1 := fun c hc => center_sq_eq_one hF e hc
  have hperf := perfect_of_SL2 hF e
  set ub : MulAut (K ⧸ Subgroup.center K) := CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K φ with hub
  have hub2 : orderOf ub = 2 := by
    have h1 : ub ^ 2 = 1 := by
      rw [hub, pow_two, ← map_mul, hφ2, map_one]
    exact orderOf_eq_prime h1 hφ1
  let αb : M →* MulAut (K ⧸ Subgroup.center K) :=
    (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K).comp α
  have hαb_mk : ∀ (m : M) (x : K), αb m (x : K ⧸ Subgroup.center K) = ((α m x : K) : K ⧸ Subgroup.center K) :=
    fun m x => CFSG.GH74.GLS.IVK.Lifted.autQuotCenter_mk (α m) x
  have hαb : ∀ m : M, αb m * ub = ub * αb m := by
    intro m
    show (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K) (α m) * (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K) φ =
      (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K) φ * (CFSG.GH74.GLS.IVK.Lifted.autQuotCenter K) (α m)
    rw [← map_mul, ← map_mul, hα m]
  have hXb : ∀ kb ∈ CFSG.GH74.GLS.IVK.xu ub,
      ∃ m : M, αb m = MulAut.conj kb ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W := by
    intro kb hkb
    obtain ⟨k, hk, hkc, hkk⟩ := lift_xu_gen hZ φ hkb
    obtain ⟨m, hm, hmW⟩ := hX k hk hkc
    refine ⟨m, ?_, hmW⟩
    ext x
    induction x using QuotientGroup.induction_on with | H x => ?_
    rw [hαb_mk, hm, MulAut.conj_apply, MulAut.conj_apply, ← hkk]
    simp
  have hmain := odd_abelian_le_xuInn_gen hF (quotCenterEquiv' e) hφin hub2 αb hαb W hWodd hWab hXb
  intro w hw
  obtain ⟨kb, hkb, hkbw⟩ := hmain w hw
  obtain ⟨k, hk, hkc, hkk⟩ := lift_xu_gen hZ φ hkb
  refine ⟨k, hk, hkc, ?_⟩
  have hφw : α w * (MulAut.conj k)⁻¹ = 1 := by
    apply CFSG.GH74.GLS.IVK.Lifted.mulAut_eq_one_of_central_diff hperf
    intro x
    have h1 : (((α w * (MulAut.conj k)⁻¹) x : K) : K ⧸ Subgroup.center K) =
        (x : K ⧸ Subgroup.center K) := by
      rw [MulAut.mul_apply]
      have h2 : ((MulAut.conj k)⁻¹ x) = k⁻¹ * x * k := by
        simp
      rw [h2, ← hαb_mk, ← hkbw, MulAut.conj_apply, ← hkk]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    have h3 := QuotientGroup.eq_iff_div_mem.mp h1
    simpa [div_eq_mul_inv] using h3
  have := congrArg (· * MulAut.conj k) hφw
  simpa using this




theorem toPSL_quot_mk {F : Type} [Field F] {K : Type} [Group K] (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (k : K) :
    toPSL (quotCenterEquiv' (e.trans (specialLinearGroupEquivStatedSL 2 F)))
      (QuotientGroup.mk k : K ⧸ center K) = (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 2) F)) (e k)) := by
  apply (projectiveSpecialLinearGroupEquivStatedProj 2 F).injective
  rw [toPSL_apply]
  unfold L2.equivPSL
  rw [MulEquiv.apply_symm_apply]
  rfl


theorem autQuot_mem_innDiagSub {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (φ : MulAut K)
    (h : (gammaOf hodd h3 (MulAut.congr e φ)).right = 1) :
    autQuotCenter K φ ∈ innDiagSub (quotCenterEquiv'
      (e.trans (specialLinearGroupEquivStatedSL 2 F))) := by
  set e' := quotCenterEquiv' (e.trans (specialLinearGroupEquivStatedSL 2 F)) with he'
  rw [mem_innDiagSub_iff]
  have hcongr : MulAut.congr (toPSL e') (autQuotCenter K φ) = psl2AutHom (MulAut.congr e φ) := by
    ext x
    obtain ⟨y, rfl⟩ := (toPSL e').surjective x
    induction y using QuotientGroup.induction_on with | H k => ?_
    show toPSL e' ((autQuotCenter K φ) ((toPSL e').symm (toPSL e' (QuotientGroup.mk k)))) = _
    rw [MulEquiv.symm_apply_apply, autQuotCenter_mk, he', toPSL_quot_mk, toPSL_quot_mk]
    show _ = psl2MulAutOf (MulAut.congr e φ) (QuotientGroup.mk' _ (e k))
    rw [psl2MulAutOf_mk]
    show _ = QuotientGroup.mk' _ (e (φ (e.symm (e k))))
    rw [MulEquiv.symm_apply_apply]
  rw [fieldProj_apply]
  show ((semilinearEquivAut F).symm (MulAut.congr (toPSL e') (autQuotCenter K φ))).right = 1
  rw [hcongr]
  have := fieldProj_psl2AutHom hodd h3 (MulAut.congr e φ)
  rw [fieldProj_apply] at this
  have h0 : toPSL (L2.equivPSL F).symm = MulEquiv.refl (PSL2 F) := by
    ext x
    simp [toPSL]
  have h1 : ((semilinearEquivAut F).symm (MulAut.congr (toPSL (L2.equivPSL F).symm) (psl2AutHom (MulAut.congr e φ)))).right = (gammaOf hodd h3 (MulAut.congr e φ)).right := this
  rw [h0] at h1
  rw [← h] 
  exact h1


end Fit

section FitG

variable {G : Type} [Group G]

theorem fit_G_outer [Finite G] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    {K : Subgroup G} (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    {t : G} (ht : t ∈ normalizer (K : Set G)) (ht2 : t * t = 1)
    (hout : ¬ ∃ a ∈ K, ∀ k ∈ K, t * k * t⁻¹ = a * k * a⁻¹)
    (hfld : (gammaOf hodd h3 (MulAut.congr e (conjAut K t ht))).right = 1)
    (M : Subgroup G) (hMN : M ≤ normalizer (K : Set G)) (hMt : ∀ m ∈ M, m * t = t * m)
    (W : Subgroup G) (hWM : W ≤ M) (hWodd : Odd (Nat.card ↥W))
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hX : ∀ k ∈ K, Odd (orderOf k) → k * t = t * k →
      ∃ m ∈ M, (∀ x ∈ K, m * x * m⁻¹ = k * x * k⁻¹) ∧ ∀ w ∈ W, m * w * m⁻¹ ∈ W) :
    ∀ w ∈ W, ∃ k ∈ K, Odd (orderOf k) ∧ k * t = t * k ∧ ∀ x ∈ K, w * x * w⁻¹ = k * x * k⁻¹ := by
  have hL2 : L2Field F := ⟨hodd, h3⟩
  set e₂ : ↥K ≃* SL2 F := e.trans (specialLinearGroupEquivStatedSL 2 F) with he₂
  set φ : MulAut ↥K := conjAut K t ht with hφdef
  have hφ2 : φ * φ = 1 := conjAut_mul_self ht ht2
  have hin : CFSG.GH74.GLS.IVK.Lifted.autQuotCenter ↥K φ ∈
      innDiagSub (quotCenterEquiv' e₂) :=
    autQuot_mem_innDiagSub hodd h3 e φ hfld
  have hperf := CFSG.GH74.GLS.SP.Local.perfect_of_SL2 hL2 e₂
  have hne : CFSG.GH74.GLS.IVK.Lifted.autQuotCenter ↥K φ ≠ 1 := by
    intro h1
    apply hout
    have hφ1 : φ = 1 := by
      apply CFSG.GH74.GLS.IVK.Lifted.mulAut_eq_one_of_central_diff hperf
      intro k
      have := congrArg (fun ψ => ψ (k : ↥K ⧸ Subgroup.center ↥K)) h1
      simp only [CFSG.GH74.GLS.IVK.Lifted.autQuotCenter_mk, MulAut.one_apply] at this
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, this]
      simp
    refine ⟨1, K.one_mem, fun k hk => ?_⟩
    have := congrArg (fun ψ => ((ψ ⟨k, hk⟩ : ↥K) : G)) hφ1
    simpa [hφdef, conjAut_apply] using this
  let α : ↥M →* MulAut ↥K :=
    MonoidHom.mk' (fun m => conjAut K (m : G) (hMN m.2)) (fun m m' => by
      ext k
      simp [conjAut_apply, mul_assoc])
  have hα : ∀ m : ↥M, α m * φ = φ * α m := by
    intro m
    ext k
    show (m : G) * (t * (k : G) * t⁻¹) * (m : G)⁻¹ = t * ((m : G) * (k : G) * (m : G)⁻¹) * t⁻¹
    have hm := hMt m m.2
    calc (m : G) * (t * (k : G) * t⁻¹) * (m : G)⁻¹ = ((m : G) * t) * (k : G) * ((m : G) * t)⁻¹ := by group
      _ = (t * (m : G)) * (k : G) * (t * (m : G))⁻¹ := by rw [hm]
      _ = t * ((m : G) * (k : G) * (m : G)⁻¹) * t⁻¹ := by group
  have hWodd' : Odd (Nat.card ↥(W.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv]
  have hWab' : ∀ x ∈ W.subgroupOf M, ∀ y ∈ W.subgroupOf M, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact hWab x.1 hx y.1 hy
  have hX' : ∀ k : ↥K, Odd (orderOf k) → φ k = k →
      ∃ m : ↥M, α m = MulAut.conj k ∧ ∀ w ∈ W.subgroupOf M, m * w * m⁻¹ ∈ W.subgroupOf M := by
    intro k hk hkφ
    have hko : Odd (orderOf (k : G)) := by rwa [Subgroup.orderOf_coe]
    have hkt : (k : G) * t = t * k := by
      have := congrArg Subtype.val hkφ
      simp only [hφdef, conjAut_apply] at this
      calc (k : G) * t = (t * (k : G) * t⁻¹) * t := by rw [this]
        _ = t * k := by group
    obtain ⟨m, hmM, hmx, hmW⟩ := hX k.1 k.2 hko hkt
    refine ⟨⟨m, hmM⟩, ?_, ?_⟩
    · ext x
      have := hmx x.1 x.2
      simpa [α, conjAut_apply] using this
    · intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      exact hmW w.1 hw
  have hmain := spl_fit_outer F hL2 ↥K e₂ φ hφ2 hin hne ↥M α hα
    (W.subgroupOf M) hWodd' hWab' hX'
  intro w hw
  obtain ⟨k, hkodd, hkφ, hαk⟩ := hmain ⟨w, hWM hw⟩ (by rw [Subgroup.mem_subgroupOf]; exact hw)
  refine ⟨k.1, k.2, ?_, ?_, ?_⟩
  · rwa [Subgroup.orderOf_coe]
  · have := congrArg Subtype.val hkφ
    simp only [hφdef, conjAut_apply] at this
    calc (k : G) * t = (t * (k : G) * t⁻¹) * t := by rw [this]
      _ = t * k := by group
  · intro x hx
    have := congrArg (fun ψ => ((ψ ⟨x, hx⟩ : ↥K) : G)) hαk
    simpa [α, conjAut_apply] using this

end FitG

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
