module

public import CFSG.GroupTheory.ABGDGroups.LinearStructure
public import CFSG.GH74.GLS.IVK.L2.Fixed14a
public import CFSG.GH74.GLS.IVK.L2.FourNormalizer
public import CFSG.GH74.GLS.IVK.L2.GroupAux
public import CFSG.GH74.GLS.IVK.L2.Lemma12k
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ABGDGroups CFSG.ABGLocalTools

section KI2Aux

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

omit [Finite K] in
theorem thetaAut_conj (k : K) :
    thetaAut e (MulAut.conj k) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k)) := by
  rw [← innDiagHom_toPGL e k, thetaAut_innDiagHom]

omit [Finite K] in
theorem mem_innAut_iff (a : MulAut K) : a ∈ innAut K ↔ thetaAut e a ∈ pGammaL2PSLRange F := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [thetaAut_conj, mem_pGammaL2PSLRange_iff F]
    exact ⟨toPSL e k, rfl⟩
  · intro h
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).1 h
    refine ⟨(toPSL e).symm y, ?_⟩
    apply (thetaAut e).injective
    rw [thetaAut_conj, MulEquiv.apply_symm_apply, hy]

omit [Finite K] in
include e in
theorem comm_mem_innAut (hF : L2Field F) (a b : MulAut K) : a * b * a⁻¹ * b⁻¹ ∈ innAut K := by
  rw [mem_innAut_iff e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutator_mem_pGammaL2PSLRange (F := F) (isOddPrimePower_of_L2Field hF) _ _

omit [Finite K] in
theorem fieldProj_conj (d x : MulAut K) : fieldProj e (d * x * d⁻¹) = fieldProj e x := by
  rw [map_mul, map_mul, map_inv, ringEquiv_mul_comm (fieldProj e d) (fieldProj e x), mul_inv_cancel_right]

omit [Finite K] in
theorem exists_conj_fieldAut (u : MulAut K) (hu : orderOf u = 2) (hud : u ∉ innDiagSub e) :
    ∃ a ∈ innDiagSub e, a⁻¹ * u * a = fieldAutHom e (fieldProj e u) := by
  have hproj : fieldProj e u ≠ 1 := fun h => hud ((mem_innDiagSub_iff e u).mpr h)
  have hord : orderOf (thetaAut e u) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hu
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr (thetaAut e u) hord
    (by rw [← fieldProj_apply]; exact hproj)
  refine ⟨innDiagHom e C, ⟨C, rfl⟩, ?_⟩
  apply (thetaAut e).injective
  rw [map_mul, map_mul, map_inv, thetaAut_innDiagHom, thetaAut_fieldAutHom, fieldProj_apply]
  exact hC


theorem isElementaryAbelian_two {G : Type*} [Group G] (B : Subgroup G)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1) :
    IsElementaryAbelian 2 ↥B := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

theorem isElementaryAbelian_two_data {G : Type*} [Group G] (A : Subgroup G)
    (hA : IsElementaryAbelian 2 ↥A) :
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ (∀ x ∈ A, x * x = 1) := by
  have := hA
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · exact congrArg Subtype.val (hA.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) x hx
    rwa [pow_two] at this

include e in
theorem card_inf_innDiag_eq_four (hF : L2Field F) (A : Subgroup (MulAut K))
    (hA : IsElementaryAbelian 2 ↥A) (hc : Nat.card ↥A = 8) :
    Nat.card ↥(A ⊓ innDiagSub e) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hsq⟩ := isElementaryAbelian_two_data A hA
  have hpow : ∀ a : ↥A, a ^ 2 = 1 := fun a => by
    apply Subtype.ext
    simpa [pow_two] using hsq a a.2
  obtain ⟨T', hT'⟩ := (IsElementaryAbelian.isPGroup 2 ↥A).exists_le_sylow
  set φ : ↥A →* (F ≃+* F) := (fieldProj e).comp A.subtype with hφ
  have hX : A ⊓ innDiagSub e = φ.ker.map A.subtype := by
    ext x
    constructor
    · rintro ⟨hxA, hxD⟩
      exact ⟨⟨x, hxA⟩, (mem_innDiagSub_iff e x).1 hxD, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, (mem_innDiagSub_iff e _).2 (MonoidHom.mem_ker.1 ha)⟩
  have hcardX : Nat.card ↥(A ⊓ innDiagSub e) = Nat.card φ.ker := by
    rw [hX]; exact Subgroup.card_map_of_injective A.subtype_injective
  have hker : Nat.card φ.ker ≤ 4 := by
    have := card_le_four_of_le_inf e hF T' (A ⊓ innDiagSub e) (inf_le_left.trans hT') inf_le_right
      (fun x hx y hy => hcomm x hx.1 y hy.1) (fun x hx => hsq x hx.1)
    omega
  have hrange : Nat.card φ.range ≤ 2 := by
    have := ringAut_isCyclic F
    have : IsCyclic φ.range := Subgroup.isCyclic _
    have h1 : Monoid.exponent φ.range ∣ 2 := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      show φ a ^ 2 = 1
      rw [← map_pow, hpow a, map_one]
    rw [IsCyclic.exponent_eq_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hprod := Subgroup.card_ker_mul_card_range φ
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  rw [hcardX]
  rw [hc] at hprod
  interval_cases h : Nat.card φ.range
  · omega
  · omega

include e in
theorem exists_involution_outside (hF : L2Field F) (A : Subgroup (MulAut K))
    (hA : IsElementaryAbelian 2 ↥A) (hc : Nat.card ↥A = 8) :
    ∃ u ∈ A, u ∉ innDiagSub e ∧ orderOf u = 2 := by
  obtain ⟨hcomm, hsq⟩ := isElementaryAbelian_two_data A hA
  have h4 := card_inf_innDiag_eq_four e hF A hA hc
  have hnot : ¬ A ≤ innDiagSub e := by
    intro hle
    rw [inf_eq_left.2 hle, hc] at h4
    omega
  obtain ⟨y, hyA, hyD⟩ := Set.not_subset.mp hnot
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyD (innDiagSub e).one_mem
  exact ⟨y, hyA, hyD, orderOf_eq_prime (by rw [pow_two]; exact hsq y hyA) hy1⟩


theorem mem_map_conj {G : Type*} [Group G] (A : Subgroup G) (c x : G) :
    x ∈ A.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h1 : c⁻¹ * (c * a * c⁻¹) * c = a := by group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h1]; exact ha
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem card_map_conj {G : Type*} [Group G] (A : Subgroup G) (c : G) :
    Nat.card ↥(A.map (MulAut.conj c).toMonoidHom) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem isElementaryAbelian_map_conj {G : Type*} [Group G] (A : Subgroup G)
    (hA : IsElementaryAbelian 2 ↥A) (c : G) :
    IsElementaryAbelian 2 ↥(A.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨hcomm, hsq⟩ := isElementaryAbelian_two_data A hA
  apply isElementaryAbelian_two
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hcomm a ha b hb
    calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [this]
      _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hsq a ha
    calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem exists_conj_fourSubgroups_diag (hF : L2Field F) (N : L2Notation e)
    {U₁ U₂ : Subgroup (MulAut K)} (h₁ : U₁ ≤ innAut K) (h₂ : U₂ ≤ innAut K)
    (f₁ : IsFourSubgroup U₁) (f₂ : IsFourSubgroup U₂) :
    ∃ d ∈ innDiagSub e, U₁.map (MulAut.conj d).toMonoidHom = U₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp₁ : IsPGroup 2 ↥U₁ := IsPGroup.of_card (n := 2) (by rw [f₁.2]; norm_num)
  have hp₂ : IsPGroup 2 ↥U₂ := IsPGroup.of_card (n := 2) (by rw [f₂.2]; norm_num)
  obtain ⟨g₁, hg₁m, hg₁⟩ := exists_conj_le_sylow_inf N.T (innAut K) h₁ hp₁
  obtain ⟨g₂, hg₂m, hg₂⟩ := exists_conj_le_sylow_inf N.T (innAut K) h₂ hp₂
  have hW₁P : U₁.map (MulAut.conj g₁⁻¹).toMonoidHom ≤ N.P := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g₁⁻¹).toMonoidHom u = g₁⁻¹ * u * g₁ := by simp
    rw [e1]
    exact hg₁ u hu
  have hW₂P : U₂.map (MulAut.conj g₂⁻¹).toMonoidHom ≤ N.P := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g₂⁻¹).toMonoidHom u = g₂⁻¹ * u * g₂ := by simp
    rw [e1]
    exact hg₂ u hu
  obtain ⟨p, hpPt, hp⟩ := ivk_1_3f_a F hF K e N _ _ hW₁P hW₂P (isFourSubgroup_map _ f₁)
    (isFourSubgroup_map _ f₂)
  refine ⟨g₂ * p * g₁⁻¹, ?_, ?_⟩
  · exact (innDiagSub e).mul_mem ((innDiagSub e).mul_mem (innAut_le_innDiagSub e hg₂m) hpPt.2)
      ((innDiagSub e).inv_mem (innAut_le_innDiagSub e hg₁m))
  · ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hmem : (MulAut.conj p) ((MulAut.conj g₁⁻¹) u) ∈ U₂.map (MulAut.conj g₂⁻¹).toMonoidHom := by
        rw [← hp]
        exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨u₂, hu₂, h⟩ := hmem
      have hy : (MulAut.conj (g₂ * p * g₁⁻¹)).toMonoidHom u = u₂ := by
        have h' := congrArg (fun z => g₂ * z * g₂⁻¹) h
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv] at h' ⊢
        calc g₂ * p * g₁⁻¹ * u * (g₁ * (p⁻¹ * g₂⁻¹)) = g₂ * (p * (g₁⁻¹ * u * g₁) * p⁻¹) * g₂⁻¹ := by
              group
          _ = g₂ * (g₂⁻¹ * u₂ * g₂) * g₂⁻¹ := by rw [h']
          _ = u₂ := by group
      rw [hy]
      exact hu₂
    · intro hy
      have hmem : (MulAut.conj g₂⁻¹) y ∈ (U₁.map (MulAut.conj g₁⁻¹).toMonoidHom).map
          (MulAut.conj p).toMonoidHom := by
        rw [hp]
        exact ⟨y, hy, rfl⟩
      obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := hmem
      refine ⟨u, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, inv_inv] at h ⊢
      calc g₂ * p * g₁⁻¹ * u * (g₁ * (p⁻¹ * g₂⁻¹)) = g₂ * (p * (g₁⁻¹ * u * g₁) * p⁻¹) * g₂⁻¹ := by
            group
        _ = g₂ * (g₂⁻¹ * y * g₂) * g₂⁻¹ := by rw [h]
        _ = y := by group


theorem E8_conj_to_E0 (hF : L2Field F) (N : L2Notation e)
    {U : Subgroup (MulAut K)} (hUinn : U ≤ innAut K) (hU4 : IsFourSubgroup U)
    (hUC : centralizer (U : Set (MulAut K)) = U ⊔ fieldAutSub e)
    (A : Subgroup (MulAut K)) (hA : IsElementaryAbelian 2 ↥A) (hc : Nat.card ↥A = 8) :
    ∃ σ : F ≃+* F, σ ≠ 1 ∧ σ ^ 2 = 1 ∧ ∃ c ∈ innDiagSub e,
      A.map (MulAut.conj c).toMonoidHom = U ⊔ Subgroup.zpowers (fieldAutHom e σ) := by
  obtain ⟨u, huA, hud, hu2⟩ := exists_involution_outside e hF A hA hc
  obtain ⟨a, haD, hconj⟩ := exists_conj_fieldAut e u hu2 hud
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = fieldProj e u := ⟨_, rfl⟩
  rw [← hσ] at hconj
  have hσ1 : σ ≠ 1 := fun h => hud ((mem_innDiagSub_iff e u).2 (hσ ▸ h))
  have hσ2 : σ ^ 2 = 1 := by
    have hu2' : u ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu2] at this
    rw [hσ, ← map_pow, hu2', map_one]
  refine ⟨σ, hσ1, hσ2, ?_⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (MulAut K), A' = A.map (MulAut.conj a⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hA'ea : IsElementaryAbelian 2 ↥A' := hA' ▸ isElementaryAbelian_map_conj A hA a⁻¹
  have hA'c : Nat.card ↥A' = 8 := by rw [hA', card_map_conj]; exact hc
  obtain ⟨hcomm', hsq'⟩ := isElementaryAbelian_two_data A' hA'ea
  have hf : fieldAutHom e σ ∈ A' := by
    rw [hA', mem_map_conj]
    have : a⁻¹⁻¹ * fieldAutHom e σ * a⁻¹ = u := by rw [← hconj]; group
    rw [this]; exact huA
  have hfσ : fieldProj e (fieldAutHom e σ) = σ := fieldProj_fieldAutHom e σ
  have hV4 : Nat.card ↥(A' ⊓ innDiagSub e) = 4 := card_inf_innDiag_eq_four e hF A' hA'ea hA'c
  have hVinn : A' ⊓ innDiagSub e ≤ innAut K := by
    rintro v ⟨hvA', hvD⟩
    by_contra hvn
    have hvf : fieldProj e v = 1 := (mem_innDiagSub_iff e v).1 hvD
    have hmul : fieldAutHom e σ * v ∈ A' := A'.mul_mem hf hvA'
    have hsqfv : (fieldAutHom e σ * v) * (fieldAutHom e σ * v) = 1 := hsq' _ hmul
    have hfp : fieldProj e (fieldAutHom e σ * v) = σ := by rw [map_mul, hfσ, hvf, mul_one]
    have hne1 : fieldAutHom e σ * v ≠ 1 := by
      intro h
      rw [h, map_one] at hfp
      exact hσ1 hfp.symm
    have hord2 : orderOf (fieldAutHom e σ * v) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hsqfv) hne1
    have hnD : fieldAutHom e σ * v ∉ innDiagSub e := by
      rw [mem_innDiagSub_iff, hfp]; exact hσ1
    obtain ⟨c, hcD, hc'⟩ := exists_conj_fieldAut e _ hord2 hnD
    rw [hfp] at hc'
    have hfv : fieldAutHom e σ * v = c * fieldAutHom e σ * c⁻¹ :=
      calc fieldAutHom e σ * v = c * (c⁻¹ * (fieldAutHom e σ * v) * c) * c⁻¹ := by group
        _ = c * fieldAutHom e σ * c⁻¹ := by rw [hc']
    have hv : v = (fieldAutHom e σ)⁻¹ * c * fieldAutHom e σ * c⁻¹ :=
      calc v = (fieldAutHom e σ)⁻¹ * (fieldAutHom e σ * v) := by group
        _ = (fieldAutHom e σ)⁻¹ * (c * fieldAutHom e σ * c⁻¹) := by rw [hfv]
        _ = (fieldAutHom e σ)⁻¹ * c * fieldAutHom e σ * c⁻¹ := by group
    apply hvn
    rw [hv]
    have := comm_mem_innAut e hF (fieldAutHom e σ)⁻¹ c
    simpa using this
  have hVfour : IsFourSubgroup (A' ⊓ innDiagSub e) :=
    ⟨isElementaryAbelian_two _ (fun x hx y hy => hcomm' x hx.1 y hy.1) (fun x hx => hsq' x hx.1), hV4⟩
  obtain ⟨g, hgD, hgV⟩ := exists_conj_fourSubgroups_diag e hF N hVinn hUinn hVfour hU4
  have hUA'' : U ≤ A'.map (MulAut.conj g).toMonoidHom := by
    rw [← hgV]
    exact Subgroup.map_mono inf_le_left
  have hf''A'' : g * fieldAutHom e σ * g⁻¹ ∈ A'.map (MulAut.conj g).toMonoidHom :=
    ⟨_, hf, by simp [MulAut.conj_apply]⟩
  have hf''C : g * fieldAutHom e σ * g⁻¹ ∈ centralizer (U : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [← hgV] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvA' : v ∈ A' := hv.1
    have hcm := hcomm' (fieldAutHom e σ) hf v hvA'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * v * g⁻¹ * (g * fieldAutHom e σ * g⁻¹) = g * (v * fieldAutHom e σ) * g⁻¹ := by group
      _ = g * (fieldAutHom e σ * v) * g⁻¹ := by rw [hcm]
      _ = g * fieldAutHom e σ * g⁻¹ * (g * v * g⁻¹) := by group
  rw [hUC] at hf''C
  have hFU : ∀ w ∈ U, ∀ φ ∈ fieldAutSub e, w * φ = φ * w := by
    intro w hw φ hφ
    have : φ ∈ centralizer (U : Set (MulAut K)) := by
      rw [hUC]; exact Subgroup.mem_sup_right hφ
    exact (Subgroup.mem_centralizer_iff.1 this) w hw
  obtain ⟨w, hwU, φ, hφ, hfw⟩ := (mem_sup_of_commute hFU).1 hf''C
  obtain ⟨τ, rfl⟩ := hφ
  have hστ : τ = σ := by
    have h1 := congrArg (fieldProj e) hfw
    rw [fieldProj_conj, hfσ, map_mul, fieldProj_fieldAutHom] at h1
    rw [(mem_innDiagSub_iff e w).1 (innAut_le_innDiagSub e (hUinn hwU)), one_mul] at h1
    exact h1.symm
  rw [hστ] at hfw
  have hfA'' : fieldAutHom e σ ∈ A'.map (MulAut.conj g).toMonoidHom := by
    have h1 : fieldAutHom e σ = w⁻¹ * (g * fieldAutHom e σ * g⁻¹) := by rw [hfw]; group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hUA'' hwU)) hf''A''
  have hE₀le : U ⊔ Subgroup.zpowers (fieldAutHom e σ) ≤ A'.map (MulAut.conj g).toMonoidHom :=
    sup_le hUA'' ((Subgroup.zpowers_le).2 hfA'')
  have hA''c : Nat.card ↥(A'.map (MulAut.conj g).toMonoidHom) = 8 := by
    rw [card_map_conj]; exact hA'c
  have hne : U ≠ U ⊔ Subgroup.zpowers (fieldAutHom e σ) := by
    intro h
    have h1 : fieldAutHom e σ ∈ U := by
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have h2 := (mem_innDiagSub_iff e _).1 (innAut_le_innDiagSub e (hUinn h1))
    rw [hfσ] at h2
    exact hσ1 h2
  have hcardE₀ : 8 ≤ Nat.card ↥(U ⊔ Subgroup.zpowers (fieldAutHom e σ)) := by
    have hdvd : Nat.card ↥U ∣ Nat.card ↥(U ⊔ Subgroup.zpowers (fieldAutHom e σ)) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hU4' : Nat.card ↥U = 4 := hU4.2
    have hpos : 0 < Nat.card ↥(U ⊔ Subgroup.zpowers (fieldAutHom e σ)) := Nat.card_pos
    by_contra hlt
    rw [hU4'] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have h4 : Nat.card ↥(U ⊔ Subgroup.zpowers (fieldAutHom e σ)) = 4 := by omega
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (by omega))
  have hE₀ : U ⊔ Subgroup.zpowers (fieldAutHom e σ) = A'.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hE₀le (by omega)
  refine ⟨g * a⁻¹, (innDiagSub e).mul_mem hgD ((innDiagSub e).inv_mem haD), ?_⟩
  rw [hE₀]
  ext x
  rw [mem_map_conj, mem_map_conj A' g x, hA', mem_map_conj]
  have h5 : (g * a⁻¹)⁻¹ * x * (g * a⁻¹) = a⁻¹⁻¹ * (g⁻¹ * x * g) * a⁻¹ := by group
  rw [h5]


theorem isElementaryAbelian_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsElementaryAbelian 2 ↥A) (hB : IsElementaryAbelian 2 ↥B)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElementaryAbelian 2 ↥(A ⊔ B) := by
  obtain ⟨hAc, hAs⟩ := isElementaryAbelian_two_data A hA
  obtain ⟨hBc, hBs⟩ := isElementaryAbelian_two_data B hB
  apply isElementaryAbelian_two
  · intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute h).1 hx
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_of_commute h).1 hy
    have c1 : Commute a a' := hAc a ha a' ha'
    have c2 : Commute a b' := h a ha b' hb'
    have c3 : Commute b a' := (h a' ha' b hb).symm
    have c4 : Commute b b' := hBc b hb b' hb'
    exact (Commute.mul_left (c1.mul_right c2) (c3.mul_right c4)).eq
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute h).1 hx
    have hab : Commute b a := (h a ha b hb).symm
    rw [hab.mul_mul_mul_comm a b, hAs a ha, hBs b hb, one_mul]

theorem isElementaryAbelian_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 ↥A) : IsElementaryAbelian 2 ↥(A.map φ) :=
  CFSG.IsElementaryAbelian.subgroup_map hA _

theorem mulAut_conj_conj {K : Type*} [Group K] (α : MulAut K) (k : K) :
    α * MulAut.conj k * α⁻¹ = MulAut.conj (α k) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem card_le_four_of_dihedralSylow {G : Type*} [Group G] [Finite G] (hG : HasDihedralSylowTwo G)
    (E : Subgroup G) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card ↥E ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEp : IsPGroup 2 ↥E := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hsq g g.2⟩
  obtain ⟨S, hS⟩ := hEp.exists_le_sylow
  obtain ⟨m, hm, ⟨φ⟩⟩ := hG S
  have hne : NeZero (2 ^ m) := ⟨by positivity⟩
  have hES : E ≤ (S : Subgroup G) := hS
  let E' : Subgroup ↥(S : Subgroup G) := E.subgroupOf (S : Subgroup G)
  have hcard1 : Nat.card ↥E' = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  let E'' : Subgroup (DihedralGroup (2 ^ m)) := E'.map φ.toMonoidHom
  have hcard2 : Nat.card ↥E'' = Nat.card ↥E' := Subgroup.card_map_of_injective φ.injective
  have hb : Nat.card ↥E'' ≤ 4 := by
    apply DihedralAux.card_le_four_of_elemAbelian
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (hsq a ha)
      rw [this, map_one]
  omega

theorem card_le_four_of_le_pgl2 {G : Type} [Group G] [Finite G] {F' : Type} [Field F'] [Finite F']
    (hF' : IsOddPrimePower (Nat.card F')) (Y : Subgroup G) (eY : ↥Y ≃* PGL2 F')
    (E : Subgroup G) (hEY : E ≤ Y) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card ↥E ≤ 4 := by
  have hD : HasDihedralSylowTwo ↥Y :=
    hasDihedralSylowTwo_of_equiv eY.symm (pgl2_odd_hasDihedralSylowTwo_model F' hF')
  have h1 := card_le_four_of_dihedralSylow hD (E.subgroupOf Y)
    (fun x hx y hy => Subtype.ext (hcomm x hx y hy))
    (fun x hx => Subtype.ext (hsq x hx))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv] at h1

theorem exists_E8_of_involution_outside (hF : L2Field F) (u : MulAut K) (hu : orderOf u = 2)
    (hud : u ∉ innDiagSub e) :
    ∃ E : Subgroup (MulAut K), E ≤ innAut K ⊔ Subgroup.zpowers u ∧ IsElementaryAbelian 2 ↥E ∧
      Nat.card ↥E = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haD, hconj⟩ := exists_conj_fieldAut e u hu hud
  obtain ⟨σ, hσ⟩ : ∃ σ : F ≃+* F, σ = fieldProj e u := ⟨_, rfl⟩
  rw [← hσ] at hconj
  have hu2' : u ^ 2 = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu] at this
  have hσ1 : σ ≠ 1 := fun h => hud ((mem_innDiagSub_iff e u).2 (hσ ▸ h))
  have hσ2 : σ ^ 2 = 1 := by rw [hσ, ← map_pow, hu2', map_one]
  have hord2 : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have h14 := ivk_1_4a F hF K e σ
  obtain ⟨F₀, hF₀f, hF₀fin, hq, ⟨eF⟩⟩ := h14.2.2 (by rw [hord2]; exact even_two)
  have hq2 : Nat.card F₀ ^ 2 = Nat.card F := by rw [← hord2]; exact hq
  have hF₀odd : Odd (Nat.card F₀) := by
    have h1 : Odd (Nat.card F₀ ^ 2) := by rw [hq2]; exact hF.1
    rw [pow_two] at h1
    exact (Nat.odd_mul.1 h1).1
  have hF₀pp : IsOddPrimePower (Nat.card F₀) := isOddPrimePower_card_of_odd hF₀odd
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow 2 (PGL2 F₀)))
  obtain ⟨m, hm, ⟨d⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F₀ hF₀pp S₀
  obtain ⟨V₀, -, hV₀⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S₀ : Subgroup (PGL2 F₀)) hm d
  have hV₀ea : IsElementaryAbelian 2 ↥V₀ :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by rw [hV₀.exponent_two] }
  let ι : PGL2 F₀ →* MulAut K :=
    ((MulAut.conj : K →* MulAut K).comp (fixedSubgroup K (fieldAutHom e σ)).subtype).comp
      eF.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (conj_injective_of_L2 e).comp (Subtype.val_injective.comp eF.symm.injective)
  have hιinn : ∀ y, ι y ∈ innAut K := fun y => ⟨_, rfl⟩
  have hιfix : ∀ y, fieldAutHom e σ * ι y * (fieldAutHom e σ)⁻¹ = ι y := by
    intro y
    have hk : fieldAutHom e σ ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K) =
        ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K) := (eF.symm y).2
    show fieldAutHom e σ * MulAut.conj ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K) *
      (fieldAutHom e σ)⁻¹ = MulAut.conj ((eF.symm y : fixedSubgroup K (fieldAutHom e σ)) : K)
    rw [mulAut_conj_conj, hk]
  set W : Subgroup (MulAut K) := V₀.map ι with hW
  have hWea : IsElementaryAbelian 2 ↥W := isElementaryAbelian_map ι V₀ hV₀ea
  have hWcard : Nat.card ↥W = 4 := by
    rw [hW, Subgroup.card_map_of_injective hι]; exact hV₀.card_four
  have hWinn : W ≤ innAut K := by
    rintro _ ⟨y, -, rfl⟩
    exact hιinn y
  have hWfix : ∀ w ∈ W, fieldAutHom e σ * w = w * fieldAutHom e σ := by
    rintro _ ⟨y, -, rfl⟩
    have := hιfix y
    calc fieldAutHom e σ * ι y = (fieldAutHom e σ * ι y * (fieldAutHom e σ)⁻¹) * fieldAutHom e σ := by
          group
      _ = ι y * fieldAutHom e σ := by rw [this]
  set V' : Subgroup (MulAut K) := W.map (MulAut.conj a).toMonoidHom with hV'
  have hV'ea : IsElementaryAbelian 2 ↥V' := isElementaryAbelian_map _ W hWea
  have hV'card : Nat.card ↥V' = 4 := by rw [hV', card_map_conj]; exact hWcard
  have hV'inn : V' ≤ innAut K := by
    rintro _ ⟨w, hw, rfl⟩
    exact (innAut_normal).conj_mem w (hWinn hw) a
  have hV'D : V' ≤ innDiagSub e := hV'inn.trans (innAut_le_innDiagSub e)
  have hV'u : ∀ v ∈ V', v * u = u * v := by
    rintro _ ⟨w, hw, rfl⟩
    have hu' : u = a * fieldAutHom e σ * a⁻¹ := by rw [← hconj]; group
    have hf := hWfix w hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hu']
    calc a * w * a⁻¹ * (a * fieldAutHom e σ * a⁻¹) = a * (w * fieldAutHom e σ) * a⁻¹ := by group
      _ = a * (fieldAutHom e σ * w) * a⁻¹ := by rw [hf]
      _ = a * fieldAutHom e σ * a⁻¹ * (a * w * a⁻¹) := by group
  have hzea : IsElementaryAbelian 2 ↥(Subgroup.zpowers u) := by
    apply isElementaryAbelian_two
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact (Commute.zpow_zpow_self u i j).eq
    · rintro _ ⟨i, rfl⟩
      rw [← zpow_add, ← two_mul, zpow_mul]
      have : u ^ (2 : ℤ) = 1 := by exact_mod_cast hu2'
      rw [this, one_zpow]
  have hEea : IsElementaryAbelian 2 ↥(V' ⊔ Subgroup.zpowers u) := by
    apply isElementaryAbelian_sup_of_commute hV'ea hzea
    rintro v hv _ ⟨i, rfl⟩
    exact (Commute.zpow_right (hV'u v hv) i).eq
  have hle8 : Nat.card ↥(V' ⊔ Subgroup.zpowers u) ≤ 8 := card_le_eight_of_elemAbelian e hF _ hEea
  have hne : V' ≠ V' ⊔ Subgroup.zpowers u := by
    intro h
    have h1 : u ∈ V' := by
      rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    exact hud ((innAut_le_innDiagSub e) (hV'inn h1))
  have hge8 : 8 ≤ Nat.card ↥(V' ⊔ Subgroup.zpowers u) := by
    have hdvd : Nat.card ↥V' ∣ Nat.card ↥(V' ⊔ Subgroup.zpowers u) :=
      Subgroup.card_dvd_of_le le_sup_left
    have hpos : 0 < Nat.card ↥(V' ⊔ Subgroup.zpowers u) := Nat.card_pos
    by_contra hlt
    rw [hV'card] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have h4 : Nat.card ↥(V' ⊔ Subgroup.zpowers u) = 4 := by omega
    exact hne (Subgroup.eq_of_le_of_card_ge le_sup_left (by omega))
  exact ⟨V' ⊔ Subgroup.zpowers u, sup_le_sup_right hV'inn _, hEea, by omega⟩

end KI2Aux

end CFSG.GH74.GLS.IVK
