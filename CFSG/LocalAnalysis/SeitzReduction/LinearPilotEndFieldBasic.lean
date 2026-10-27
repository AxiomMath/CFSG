module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR4LangPSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalSubfield
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (linearFieldPart linearFieldPart_eq)

section Generic

variable {G : Type*} [Group G]

theorem exists_conj_eq_mul_of_odd {t k : G} (ht : t * t = 1) (hk : t * k * t⁻¹ = k⁻¹)
    (hodd : Odd (orderOf k)) : ∃ d : G, d⁻¹ * t * d = t * k := by
  obtain ⟨s, hs⟩ := hodd
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hpow : ∀ a : ℕ, t * k ^ a * t⁻¹ = (k ^ a)⁻¹ := by
    intro a
    rw [← conj_pow, hk, inv_pow]
  refine ⟨k ^ (s + 1), ?_⟩
  have h1 : t⁻¹ * (k ^ (s + 1))⁻¹ * t = k ^ (s + 1) := by
    have h := hpow (s + 1)
    rw [htinv] at h ⊢
    rw [← h]
    calc t * (t * k ^ (s + 1) * t) * t = (t * t) * k ^ (s + 1) * (t * t) := by group
      _ = k ^ (s + 1) := by rw [ht, one_mul, mul_one]
  have hk1 : k ^ (2 * s + 1) = 1 := by rw [← hs, pow_orderOf_eq_one]
  calc (k ^ (s + 1))⁻¹ * t * k ^ (s + 1)
      = t * (t⁻¹ * (k ^ (s + 1))⁻¹ * t) * k ^ (s + 1) := by group
    _ = t * k ^ (s + 1) * k ^ (s + 1) := by rw [h1]
    _ = t * (k ^ (2 * s + 1) * k) := by rw [mul_assoc, ← pow_add, ← pow_succ]; ring_nf
    _ = t * k := by rw [hk1, one_mul]

theorem exists_orderOf_eq_of_odd_ker [Finite G] {B : Type*} [Group B] (φ : G →* B)
    (hker : Odd (Nat.card φ.ker)) {ξ : B} (hξ : ξ ∈ φ.range) {c : ℕ}
    (hξo : orderOf ξ = 2 ^ c) : ∃ x : G, φ x = ξ ∧ orderOf x = 2 ^ c := by
  obtain ⟨x₀, rfl⟩ := hξ
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨1, ?_, by rw [orderOf_one, pow_zero]⟩
    rw [pow_zero, orderOf_eq_one_iff] at hξo
    rw [map_one, hξo]
  set y := x₀ ^ (2 ^ c) with hy
  have hyker : y ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hy, map_pow, ← hξo, pow_orderOf_eq_one]
  have hr : Odd (orderOf y) := by
    have h1 : orderOf (⟨y, hyker⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hker h1
  have hcop : Nat.Coprime (orderOf y) (2 ^ c) :=
    Nat.Coprime.pow_right c (Nat.coprime_two_right.2 hr)
  have h2c : 1 < 2 ^ c := Nat.one_lt_two_pow (by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h2c
  refine ⟨x₀ ^ (orderOf y * u), ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, hξo, hu, pow_one]
  · have hx1 : (x₀ ^ (orderOf y * u)) ^ 2 ^ c = 1 := by
      rw [← pow_mul, mul_comm (orderOf y * u), pow_mul, ← hy, pow_mul, pow_orderOf_eq_one,
        one_pow]
    have hdvd1 : orderOf (x₀ ^ (orderOf y * u)) ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one hx1
    have hdvd2 : 2 ^ c ∣ orderOf (x₀ ^ (orderOf y * u)) := by
      have h := orderOf_map_dvd φ (x₀ ^ (orderOf y * u))
      rwa [map_pow, ← pow_mod_orderOf, hξo, hu, pow_one, hξo] at h
    exact Nat.dvd_antisymm hdvd1 hdvd2

theorem odd_card_of_inf_centralizer_eq_bot [Finite G] {H : Subgroup G} {t : G} (ht : t * t = 1)
    (htH : t ∈ normalizer (H : Set G)) (hfix : H ⊓ centralizer ({t} : Set G) = ⊥) :
    Odd (Nat.card H) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ := H.normalizerMonoidHom ⟨t, htH⟩ with hτ
  set σ : Equiv.Perm H := τ.toEquiv with hσ
  have hτ2 : τ * τ = 1 := by
    have h1 : (⟨t, htH⟩ : normalizer (H : Set G)) * ⟨t, htH⟩ = 1 := Subtype.ext ht
    rw [hτ, ← map_mul, h1, map_one]
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    refine Equiv.ext fun x => ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    change τ (τ x) = x
    rw [← MulAut.mul_apply, hτ2, MulAut.one_apply]
  have hfixpt : ∀ x : H, σ x = x → x = 1 := by
    intro x hx
    have hx' : τ x = x := hx
    have hxt : (x : G) ∈ H ⊓ centralizer ({t} : Set G) := by
      refine ⟨x.2, mem_centralizer_singleton_iff.2 ?_⟩
      have h := congrArg Subtype.val hx'
      rw [hτ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      calc (x : G) * t = t * x * t⁻¹ * t := by rw [h]
        _ = t * x := by group
    rw [hfix, mem_bot] at hxt
    exact Subtype.ext hxt
  have hsupp : σ.supportᶜ = {1} := by
    ext x
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · exact hfixpt x
    · rintro rfl
      exact map_one τ
  have hmod := Equiv.Perm.card_compl_support_modEq hσ2
  rw [hsupp, Finset.card_singleton] at hmod
  rw [Nat.card_eq_fintype_card, Nat.odd_iff]
  exact hmod.symm

end Generic

section Aut

variable {n : ℕ} {F : Type*} [Field F]

theorem mulAut_mul_conj_eq (β : MulAut (projectiveSL n F)) (y : projectiveSL n F) :
    β * MulAut.conj y = MulAut.conj (β y) * β := by
  rw [← mulAut_mul_conj_mul_inv_eq_conj β y, inv_mul_cancel_right]

theorem dualAut_pow_eq_pow_mod (ε : ℕ) : dualAut n F ^ ε = dualAut n F ^ (ε % 2) := by
  have hδδ : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  conv_lhs => rw [← Nat.mod_add_div ε 2, pow_add, pow_mul, sq, hδδ, one_pow, mul_one]

variable [Finite F]

@[expose] noncomputable def innerStd (n : ℕ) (F : Type*) [Field F] [Finite F] :
    Subgroup (MulAut (projectiveSL n F)) where
  carrier := {α | ∃ (x : projectiveSL n F) (ρ : F ≃+* F) (ε : ℕ),
    α = MulAut.conj x * fieldAut n F ρ * dualAut n F ^ ε}
  one_mem' := ⟨1, 1, 0, by rw [map_one, map_one, pow_zero, mul_one, mul_one]⟩
  mul_mem' := by
    rintro _ _ ⟨x, ρ, ε, rfl⟩ ⟨y, τ, ν, rfl⟩
    have hcomm : ∀ k : ℕ, dualAut n F ^ k * fieldAut n F τ = fieldAut n F τ * dualAut n F ^ k :=
      fun k => ((show Commute (dualAut n F) (fieldAut n F τ) from
        dualAut_mul_fieldAut τ).pow_left k).eq
    refine ⟨x * (fieldAut n F ρ * dualAut n F ^ ε) y, ρ * τ, ε + ν, ?_⟩
    calc MulAut.conj x * fieldAut n F ρ * dualAut n F ^ ε *
          (MulAut.conj y * fieldAut n F τ * dualAut n F ^ ν)
        = MulAut.conj x * ((fieldAut n F ρ * dualAut n F ^ ε) * MulAut.conj y) *
            fieldAut n F τ * dualAut n F ^ ν := by group
      _ = MulAut.conj x * (MulAut.conj ((fieldAut n F ρ * dualAut n F ^ ε) y) *
            (fieldAut n F ρ * dualAut n F ^ ε)) * fieldAut n F τ * dualAut n F ^ ν := by
          rw [mulAut_mul_conj_eq]
      _ = MulAut.conj (x * (fieldAut n F ρ * dualAut n F ^ ε) y) * fieldAut n F ρ *
            (dualAut n F ^ ε * fieldAut n F τ) * dualAut n F ^ ν := by
          rw [map_mul]; group
      _ = MulAut.conj (x * (fieldAut n F ρ * dualAut n F ^ ε) y) * fieldAut n F (ρ * τ) *
            dualAut n F ^ (ε + ν) := by
          rw [hcomm, map_mul (fieldAut n F), pow_add]; group
  inv_mem' := by
    rintro _ ⟨x, ρ, ε, rfl⟩
    have hδδ : dualAut n F * dualAut n F = 1 :=
      (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
    have hδinv : (dualAut n F ^ ε)⁻¹ = dualAut n F ^ ε := by
      rw [← inv_pow, inv_eq_of_mul_eq_one_right hδδ]
    have hcomm : dualAut n F ^ ε * fieldAut n F ρ⁻¹ = fieldAut n F ρ⁻¹ * dualAut n F ^ ε :=
      ((show Commute (dualAut n F) (fieldAut n F ρ⁻¹) from
        dualAut_mul_fieldAut ρ⁻¹).pow_left ε).eq
    refine ⟨(dualAut n F ^ ε * fieldAut n F ρ⁻¹) x⁻¹, ρ⁻¹, ε, ?_⟩
    calc (MulAut.conj x * fieldAut n F ρ * dualAut n F ^ ε)⁻¹
        = (dualAut n F ^ ε * fieldAut n F ρ⁻¹) * MulAut.conj x⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, hδinv, ← map_inv (fieldAut n F), ← map_inv MulAut.conj]
          group
      _ = MulAut.conj ((dualAut n F ^ ε * fieldAut n F ρ⁻¹) x⁻¹) *
            (dualAut n F ^ ε * fieldAut n F ρ⁻¹) := mulAut_mul_conj_eq _ _
      _ = _ := by rw [hcomm, mul_assoc]

theorem mem_innerStd_iff {α : MulAut (projectiveSL n F)} :
    α ∈ innerStd n F ↔ ∃ (x : projectiveSL n F) (ρ : F ≃+* F) (ε : ℕ), ε ≤ 1 ∧
      α = MulAut.conj x * fieldAut n F ρ * dualAut n F ^ ε := by
  constructor
  · rintro ⟨x, ρ, ε, rfl⟩
    exact ⟨x, ρ, ε % 2, by omega, by rw [dualAut_pow_eq_pow_mod]⟩
  · rintro ⟨x, ρ, ε, -, rfl⟩
    exact ⟨x, ρ, ε, rfl⟩

theorem range_conj_le_innerStd :
    (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range ≤ innerStd n F := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, 1, 0, by rw [map_one, pow_zero, mul_one, mul_one]⟩

theorem fieldAut_mul_dualAut_pow_mem_innerStd (ρ : F ≃+* F) (ε : ℕ) :
    fieldAut n F ρ * dualAut n F ^ ε ∈ innerStd n F :=
  ⟨1, ρ, ε, by rw [map_one, one_mul]⟩

theorem conjAut_range_normal (hn : 3 ≤ n) : (conjAut n F).range.Normal := by
  obtain ⟨hcc, -, hfc, hδδ, hδc, -⟩ := standard_automorphism_transport (K := F) (n := n)
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := F) hn).2 g
  have hδinv : (dualAut n F)⁻¹ = dualAut n F := inv_eq_of_mul_eq_one_right hδδ
  have h1 : ∃ A₁ : GL (Fin n) F, dualAut n F ^ ε * conjAut n F A * (dualAut n F ^ ε)⁻¹ =
      conjAut n F A₁ := by
    rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
    · exact ⟨A, by rw [pow_zero, one_mul, inv_one, mul_one]⟩
    · exact ⟨_, by rw [pow_one, hδinv, hδc]⟩
  obtain ⟨A₁, hA₁⟩ := h1
  refine ⟨B * Matrix.GeneralLinearGroup.map (ρ : F →+* F) A₁ * B⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hfc, ← hA₁]
  group

theorem two_not_dvd_index_innerStd [CharP F 2] (hn : 3 ≤ n) : ¬ 2 ∣ (innerStd n F).index := by
  set D := (conjAut n F).range with hD
  have hDn : D.Normal := conjAut_range_normal hn
  set I := (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range with hI
  have hsup : innerStd n F ⊔ D = ⊤ := by
    refine eq_top_iff.2 fun α _ => ?_
    obtain ⟨A, ρ, ε, -, rfl⟩ := (automorphism_generation (K := F) hn).2 α
    rw [mul_assoc, sup_comm]
    exact mul_mem_sup ⟨A, rfl⟩ (fieldAut_mul_dualAut_pow_mem_innerStd ρ ε)
  have h1 := Subgroup.relIndex_sup_right (innerStd n F) D
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.index_inf (H := innerStd n F) (K := D)
  have h3 := Subgroup.index_inf (H := D) (K := innerStd n F)
  rw [inf_comm, h3, ← h1] at h2
  have hD0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : (innerStd n F).index = (innerStd n F).relIndex D := by
    rw [mul_comm D.index] at h2
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hD0) h2
  have hIle : I ≤ innerStd n F := range_conj_le_innerStd
  have h4 : (innerStd n F).relIndex D ∣ I.relIndex D :=
    Subgroup.relIndex_dvd_of_le_left D hIle
  set f := (conjAut n F).rangeRestrict with hf
  have hfs : Function.Surjective f := (conjAut n F).rangeRestrict_surjective
  set K₁ := (Matrix.GeneralLinearGroup.det : GL (Fin n) F →* Fˣ).ker with hK₁
  have hK₁le : K₁.map f ≤ I.subgroupOf D := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_subgroupOf]
    have hdet : (g : Matrix (Fin n) (Fin n) F).det = 1 := by
      have h := MonoidHom.mem_ker.mp hg
      have h' := congrArg Units.val h
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'
    set S : Matrix.SpecialLinearGroup (Fin n) F := ⟨g, hdet⟩
    have hgS : Matrix.SpecialLinearGroup.toGL S = g := Units.ext rfl
    change conjAut n F g ∈ I
    rw [← hgS, conjAut_toGL]
    exact ⟨_, rfl⟩
  have h5 : I.relIndex D ∣ K₁.index :=
    (Subgroup.index_dvd_of_le hK₁le).trans (Subgroup.index_map_dvd K₁ hfs)
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have h6 : K₁.index = Nat.card F - 1 := by
    rw [hK₁, Subgroup.index_ker, MonoidHom.range_eq_top.mpr
      Matrix.GeneralLinearGroup.det_surjective, Subgroup.card_top, Nat.card_units]
  obtain ⟨e, he, hF⟩ := exists_natCard_eq_two_pow_of_charP F
  have hodd : Odd (Nat.card F - 1) := by
    rw [hF]
    have h2e : Even (2 ^ e) := (Nat.even_pow' (by omega)).2 even_two
    obtain ⟨r, hr⟩ := h2e
    refine ⟨r - 1, ?_⟩
    have : 1 ≤ r := by
      have := Nat.one_le_two_pow (n := e)
      omega
    omega
  intro h2dvd
  rw [hidx] at h2dvd
  rw [h6] at h5
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((h2dvd.trans h4).trans h5))

theorem exists_conj_mem_innerStd [CharP F 2] (hn : 3 ≤ n)
    {W : Subgroup (MulAut (projectiveSL n F))} (hW : IsPGroup 2 W) :
    ∃ g : MulAut (projectiveSL n F), ∀ w ∈ W, g⁻¹ * w * g ∈ innerStd n F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (innerStd n F)) := inferInstance
  set P := (S₀ : Subgroup (innerStd n F)).map (innerStd n F).subtype with hP
  have hPp : IsPGroup 2 P := S₀.isPGroup'.map _
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hP, Subgroup.index_map_subtype]
    exact (Fact.out : (2 : ℕ).Prime).not_dvd_mul S₀.not_dvd_index (two_not_dvd_index_innerStd hn)
  set S := hPp.toSylow hPidx with hS
  obtain ⟨S', hS'⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (projectiveSL n F)) S S'
  refine ⟨g, fun w hw => ?_⟩
  have hw' : w ∈ ((g • S : Sylow 2 _) : Subgroup (MulAut (projectiveSL n F))) := hg ▸ hS' hw
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hw'
  obtain ⟨p, hpS, rfl⟩ := hw'
  have hpP : p ∈ P := hpS
  obtain ⟨q, -, rfl⟩ := hpP
  have hconj : MulAut.conj g • ((innerStd n F).subtype q) =
      g * ((innerStd n F).subtype q) * g⁻¹ := rfl
  rw [hconj, show g⁻¹ * (g * ((innerStd n F).subtype q) * g⁻¹) * g = (innerStd n F).subtype q
    by group]
  exact q.2

theorem mul_mem_semilinearAutGroup_mul_inv (hn : 3 ≤ n) (g : MulAut (projectiveSL n F))
    {e : MulAut (projectiveSL n F)} (he : e ∈ semilinearAutGroup n F) :
    g * e * g⁻¹ ∈ semilinearAutGroup n F := by
  have hδδ : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  have hδinv : (dualAut n F)⁻¹ = dualAut n F := inv_eq_of_mul_eq_one_right hδδ
  obtain ⟨B, ρ, ε, hε, rfl⟩ := (automorphism_generation (K := F) hn).2 g
  have hs : conjAut n F B * fieldAut n F ρ ∈ semilinearAutGroup n F :=
    mem_semilinearAutGroup_iff.2 ⟨B, ρ, rfl⟩
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one]
    exact mul_mem (mul_mem hs he) (inv_mem hs)
  · rw [pow_one]
    have h1 := dualAut_mul_mul_dualAut_mem he
    have h2 : conjAut n F B * fieldAut n F ρ * dualAut n F * e *
        (conjAut n F B * fieldAut n F ρ * dualAut n F)⁻¹ =
        (conjAut n F B * fieldAut n F ρ) * (dualAut n F * e * dualAut n F) *
          (conjAut n F B * fieldAut n F ρ)⁻¹ := by
      rw [mul_inv_rev (conjAut n F B * fieldAut n F ρ) (dualAut n F), hδinv]
      group
    rw [h2]
    exact mul_mem (mul_mem hs h1) (inv_mem hs)

omit [Finite F] in
theorem conj_mem_semilinearAutGroup (x : projectiveSL n F) :
    MulAut.conj x ∈ semilinearAutGroup n F := by
  obtain ⟨S, rfl⟩ := proj_surjective n F x
  rw [← conjAut_toGL]
  exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _)

theorem linearFieldPart_conj_mul (hn : 3 ≤ n) (x : projectiveSL n F) (ρ : F ≃+* F) (ε : ℕ) :
    linearFieldPart F hn (MulAut.conj x * fieldAut n F ρ * dualAut n F ^ ε) = ρ := by
  rw [map_mul, map_mul, map_pow, linearFieldPart_mulAut_conj, linearFieldPart_fieldAut,
    linearFieldPart_dualAut, one_pow, one_mul, mul_one]

theorem orderOf_fieldAut_mul_dualAut_pow (hn : 3 ≤ n) {ρ : F ≃+* F} {c : ℕ} (hc : 1 ≤ c)
    (hρ : orderOf ρ = 2 ^ c) (ε : ℕ) :
    orderOf (fieldAut n F ρ * dualAut n F ^ ε) = 2 ^ c := by
  have hδδ : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  have hcomm : Commute (fieldAut n F ρ) (dualAut n F ^ ε) :=
    ((show Commute (dualAut n F) (fieldAut n F ρ) from dualAut_mul_fieldAut ρ).symm).pow_right ε
  have h2c : 2 ^ c = 2 * 2 ^ (c - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : (fieldAut n F ρ * dualAut n F ^ ε) ^ 2 ^ c = 1 := by
    rw [hcomm.mul_pow, ← map_pow, ← hρ, pow_orderOf_eq_one, map_one, one_mul, ← pow_mul,
      hρ, mul_comm, h2c, mul_assoc, pow_mul, sq, hδδ, one_pow]
  have h2 : 2 ^ c ∣ orderOf (fieldAut n F ρ * dualAut n F ^ ε) := by
    have h := orderOf_map_dvd (linearFieldPart F hn) (fieldAut n F ρ * dualAut n F ^ ε)
    rwa [map_mul, map_pow, linearFieldPart_fieldAut, linearFieldPart_dualAut, one_pow,
      mul_one, hρ] at h
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h1) h2

end Aut

section Lang

variable {X : Type*} [Group X]

theorem exists_conj_eq_of_isLangSurjective
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {α : MulAut X} (hα : α * α = 1)
    (hL : IsLangSurjective α) {z : X} (hz : (MulAut.conj z * α) * (MulAut.conj z * α) = 1) :
    ∃ y : X, MulAut.conj y * α * (MulAut.conj y)⁻¹ = MulAut.conj z * α := by
  have hαα : ∀ v : X, α (α v) = v := fun v => by
    rw [← MulAut.mul_apply, hα, MulAut.one_apply]
  have hαc : ∀ v : X, α * MulAut.conj v = MulAut.conj (α v) * α := fun v => by
    rw [← mulAut_mul_conj_mul_inv_eq_conj α v, inv_mul_cancel_right]
  have hz' : α z = z⁻¹ := by
    have h1 : MulAut.conj (z * α z) = 1 := by
      calc MulAut.conj (z * α z) = MulAut.conj z * MulAut.conj (α z) * (α * α) := by
            rw [hα, mul_one, map_mul]
        _ = MulAut.conj z * α * (MulAut.conj z * α) := by
            rw [show MulAut.conj z * α * (MulAut.conj z * α) =
              MulAut.conj z * (α * MulAut.conj z) * α by group, hαc z]
            group
        _ = 1 := hz
    have h2 : z * α z = 1 := hinj (h1.trans (map_one _).symm)
    exact eq_inv_of_mul_eq_one_right h2
  obtain ⟨x, hx⟩ := hL z hz'
  refine ⟨(α x)⁻¹, ?_⟩
  calc MulAut.conj (α x)⁻¹ * α * (MulAut.conj (α x)⁻¹)⁻¹
      = MulAut.conj (α x)⁻¹ * (α * MulAut.conj (α x)) := by
        rw [map_inv, inv_inv, mul_assoc]
    _ = MulAut.conj (α x)⁻¹ * (MulAut.conj (α (α x)) * α) := by rw [hαc]
    _ = MulAut.conj ((α x)⁻¹ * x) * α := by rw [hαα, map_mul, mul_assoc]
    _ = MulAut.conj z * α := by rw [hx]

end Lang

section Lift

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_exact_lift (hn : 3 ≤ n) {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1)
    {𝒜 : Subgroup (MulAut (projectiveSL n F))}
    (hI : (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range ≤ 𝒜)
    {W : Subgroup (MulAut (projectiveSL n F))} (hW𝒜 : W ≤ 𝒜) (hW : IsPGroup 2 W)
    (hσW : fieldAut n F σ ∈ W) {w : MulAut (projectiveSL n F)} (hwW : w ∈ W) {c : ℕ}
    (hc : 2 ≤ c) (hwo : orderOf (linearFieldPart F hn w) = 2 ^ c) :
    ∃ ξ ∈ 𝒜, orderOf ξ = 2 ^ c ∧ linearFieldPart F hn ξ = linearFieldPart F hn w ∧
      ∃ u : projectiveSL n F,
        ξ ^ 2 ^ (c - 1) = MulAut.conj u * fieldAut n F σ * (MulAut.conj u)⁻¹ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_innerStd hn hW
  obtain ⟨s, ρ, ε, -, hgw⟩ := mem_innerStd_iff.1 (hg w hwW)
  have hρ : ρ = linearFieldPart F hn w := by
    have h := linearFieldPart_conj_mul hn s ρ ε
    rw [← hgw] at h
    rw [← h, show g⁻¹ * w * g = g⁻¹ * w * g⁻¹⁻¹ by rw [inv_inv], linearFieldPart_conj_eq]
  set γ := fieldAut n F ρ * dualAut n F ^ ε with hγ
  set ξ := g * γ * g⁻¹ with hξ
  have hξw : ξ = MulAut.conj (g s⁻¹) * w := by
    have hw : w = g * (MulAut.conj s * γ) * g⁻¹ := by
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = g * (MulAut.conj s * γ) * g⁻¹ := by rw [hgw, hγ, mul_assoc (MulAut.conj s)]
    rw [hw, hξ, ← mulAut_mul_conj_mul_inv_eq_conj g s⁻¹, map_inv]
    group
  have hξA : ξ ∈ 𝒜 := by
    rw [hξw]
    exact mul_mem (hI ⟨_, rfl⟩) (hW𝒜 hwW)
  have hρo : orderOf ρ = 2 ^ c := by rw [hρ, hwo]
  have hγo : orderOf γ = 2 ^ c := orderOf_fieldAut_mul_dualAut_pow hn (by omega) hρo ε
  have hξo : orderOf ξ = 2 ^ c := by
    rw [hξ, show g * γ * g⁻¹ = MulAut.conj g γ from rfl, MulEquiv.orderOf_eq, hγo]
  have hξfc : linearFieldPart F hn ξ = linearFieldPart F hn w := by
    rw [hξ, linearFieldPart_conj_eq, hγ, map_mul, map_pow, linearFieldPart_fieldAut,
      linearFieldPart_dualAut, one_pow, mul_one, hρ]
  have hρpow : ρ ^ 2 ^ (c - 1) = σ := by
    have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv
    have : Finite (F ≃+* F) :=
      Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) fun _ _ h => RingEquiv.ext (congrFun h)
    have h2c : 2 ^ c = 2 ^ (c - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    refine CFSG.SeitzReduction.RankOne.Endings.eq_of_sq_eq_one_of_isCyclic ?_ (by rw [sq, hσσ]) ?_ hσ1
    · rw [← pow_mul, ← h2c, ← hρo, pow_orderOf_eq_one]
    · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hρo]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hδδ : dualAut n F * dualAut n F = 1 :=
    (standard_automorphism_transport (K := F) (n := n)).2.2.2.1
  have hγpow : γ ^ 2 ^ (c - 1) = fieldAut n F σ := by
    have hcomm : Commute (fieldAut n F ρ) (dualAut n F ^ ε) :=
      ((show Commute (dualAut n F) (fieldAut n F ρ) from dualAut_mul_fieldAut ρ).symm).pow_right ε
    have h2 : 2 ^ (c - 1) = 2 * 2 ^ (c - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hγ, hcomm.mul_pow, ← map_pow, hρpow, ← pow_mul, h2, mul_comm ε, mul_assoc, pow_mul, sq,
      hδδ, one_pow, mul_one]
  obtain ⟨s', ρ', ε', hε', hgσ⟩ := mem_innerStd_iff.1 (hg _ hσW)
  have hρ' : ρ' = σ := by
    have h := linearFieldPart_conj_mul hn s' ρ' ε'
    rw [← hgσ, show g⁻¹ * fieldAut n F σ * g = g⁻¹ * fieldAut n F σ * g⁻¹⁻¹ by rw [inv_inv],
      linearFieldPart_conj_eq, linearFieldPart_fieldAut] at h
    exact h.symm
  have hε'0 : ε' = 0 := by
    by_contra h
    have h1 : ε' = 1 := by omega
    have hE : g⁻¹ * fieldAut n F σ * g ∈ semilinearAutGroup n F := by
      have := mul_mem_semilinearAutGroup_mul_inv hn g⁻¹ (fieldAut_mem_semilinearAutGroup σ)
      rwa [inv_inv] at this
    rw [hgσ, h1, pow_one] at hE
    have hs : MulAut.conj s' * fieldAut n F ρ' ∈ semilinearAutGroup n F :=
      mul_mem (conj_mem_semilinearAutGroup s') (fieldAut_mem_semilinearAutGroup ρ')
    have hδE := mul_mem (inv_mem hs) hE
    rw [← mul_assoc, inv_mul_cancel, one_mul] at hδE
    exact ProjectivePlane.dualAut_not_mem_semilinearAutGroup (K := F) hn hδE
  rw [hε'0, pow_zero, mul_one, hρ'] at hgσ
  set z := (g s')⁻¹ with hz
  have hgfσ : g * fieldAut n F σ * g⁻¹ = MulAut.conj z * fieldAut n F σ := by
    have h1 : fieldAut n F σ = g * (MulAut.conj s' * fieldAut n F σ) * g⁻¹ := by
      rw [← hgσ]
      group
    calc g * fieldAut n F σ * g⁻¹
        = (g * MulAut.conj s' * g⁻¹)⁻¹ * (g * (MulAut.conj s' * fieldAut n F σ) * g⁻¹) := by
          group
      _ = (MulAut.conj (g s'))⁻¹ * fieldAut n F σ := by
          rw [mulAut_mul_conj_mul_inv_eq_conj, ← h1]
      _ = MulAut.conj z * fieldAut n F σ := by rw [hz, map_inv]
  have hξpow : ξ ^ 2 ^ (c - 1) = MulAut.conj z * fieldAut n F σ := by
    rw [hξ, conj_pow, hγpow, hgfσ]
  obtain ⟨e, he, hF⟩ := exists_natCard_eq_two_pow_of_charP F
  have hσ2 : fieldAut n F σ ^ 2 = 1 := by rw [← map_pow, sq, hσσ, map_one]
  have hL := isLangSurjective_fieldAut he hF hn σ hσ1 hσ2
  have hinv : (MulAut.conj z * fieldAut n F σ) * (MulAut.conj z * fieldAut n F σ) = 1 := by
    rw [← hξpow, ← pow_add, ← two_mul, ← pow_succ']
    rw [show c - 1 + 1 = c by omega, ← hξo, pow_orderOf_eq_one]
  obtain ⟨u, hu⟩ := exists_conj_eq_of_isLangSurjective (LinearOuter.conj_injective hn)
    (by rw [← sq, hσ2]) hL hinv
  exact ⟨ξ, hξA, hξo, hξfc, u, hξpow.trans hu.symm⟩

end Lift

end CFSG.SeitzReduction.LinearPilot
