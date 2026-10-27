module

public import CFSG.LargeExtraspecial.S10EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S2

universe u

section Sp

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem conj_mem_spPointRadical {a : U} {e : U ≃ₗ[ZMod 2] U} (he : e ∈ spPointRadical f a)
    {γ : U ≃ₗ[ZMod 2] U} (hγ : γ ∈ TauCeti.BilinForm.isometryGroup f) :
    γ * e * γ⁻¹ ∈ spPointRadical f (γ a) := by
  obtain ⟨he1, hea, he2, he3⟩ := he
  have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp hγ
  have hγγ : ∀ x, γ (γ⁻¹ x) = x := fun x => LinearEquiv.apply_symm_apply γ x
  have hc : ∀ x, (γ * e * γ⁻¹) x - x = γ (e (γ⁻¹ x) - γ⁻¹ x) := fun x => by
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hγγ]
  refine ⟨mul_mem (mul_mem hγ he1) (inv_mem hγ), ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show γ⁻¹ (γ a) = a from LinearEquiv.symm_apply_apply γ a, hea]
  · have hx' : f a (γ⁻¹ x) = 0 := by rw [← hiso, hγγ]; exact hx
    rw [hc]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (he2 _ hx')
    rw [← hk, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [hc, hiso]
    exact he3 _

theorem four_le_finrank_of_isotropic_pair [FiniteDimensional (ZMod 2) U] (hB : f.Nondegenerate)
    (hBa : f.IsAlt) {x y : U} (hli : LinearIndependent (ZMod 2) ![x, y]) (hxy : f x y = 0) :
    4 ≤ finrank (ZMod 2) U := by
  have hyx : f y x = 0 := by rw [OrthoF2.isAlt_symm hBa, hxy]
  have hle : Submodule.span (ZMod 2) {x, y} ≤
      f.orthogonal (Submodule.span (ZMod 2) {x, y}) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hBa.self_eq_zero, hxy, hyx, mul_zero, add_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB, OrthoF2.finrank_span_pair hli] at h1
  have h2 := Submodule.finrank_le (Submodule.span (ZMod 2) {x, y})
  rw [OrthoF2.finrank_span_pair hli] at h2
  omega

end Sp

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem card_LmodN_le_two (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hle : S.Lbar g ⊓ Xb ≤ Nbar S g τ) : Nat.card (LmodN S g τ) ≤ 2 := by
  have h1 := Subgroup.card_le_of_le (le_inf inf_le_left hle :
    S.Lbar g ⊓ Xb ≤ S.Lbar g ⊓ Nbar S g τ)
  have h2 := D.two_mul_card_Ebar hCE
  have h3 := card_Lbar_eq_mul X.haQ hτ.1
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g τ : Subgroup S.O) := Nat.card_pos
  by_contra hcon
  push Not at hcon
  nlinarith

theorem resV_aV_eq_bV {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) {k : S.M} (hkY : S.ρ k ∈ Yb) :
    resV X.haQ τ ⟨S.ρ k, D.Yb_le_Rbar hτ hkY⟩ (aV hτ.1) = bV (D.mem_Lbar_mul hτ hkY) :=
  Subtype.ext (by rw [coe_resV_apply, coe_bV]; exact ρ_cl_conj_z S k X.haQ)

theorem resV_Ebar_cases {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb) (hτ1 : τ ≠ 1)
    (hVQ : ¬ V S g τ ≤ S.Qa g) {k : S.M} (hkY : S.ρ k ∈ Yb)
    (hne : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) {x : S.O}
    (hx : x ∈ S.Lbar g ⊓ Xb) :
    resV X.haQ τ ⟨x, Lbar_le_Rbar hτ.1 hx.1⟩ = 1 ∨
      resV X.haQ τ ⟨x, Lbar_le_Rbar hτ.1 hx.1⟩ =
        spSiegel (beta X.H X.C hτ.1 hτ1 hVQ) (beta_isAlt X.H X.C hτ.1 hτ1 hVQ) (aV hτ.1)
          (bV (D.mem_Lbar_mul hτ hkY)) 0 := by
  have hkR := D.Yb_le_Rbar hτ hkY
  have hxR := Lbar_le_Rbar hτ.1 hx.1
  set rx := resV X.haQ τ ⟨x, hxR⟩ with hrx
  set rd := resV X.haQ τ ⟨S.ρ k, hkR⟩ with hrd
  have h1 : rx ∈ spPointRadical (beta X.H X.C hτ.1 hτ1 hVQ) (aV hτ.1) :=
    LmodN_le_spPointRadical X.H X.C hτ.1 hτ1 hVQ ⟨x, hx.1, fun v => rfl⟩
  have hrdI : rd ∈ TauCeti.BilinForm.isometryGroup (beta X.H X.C hτ.1 hτ1 hVQ) :=
    RmodN_le_isometryGroup X.H X.C hτ.1 hτ1 hVQ ⟨S.ρ k, hkR, fun v => rfl⟩
  have hcomm : rx = rd * rx * rd⁻¹ := by
    have e : (⟨S.ρ k, hkR⟩ : Rbar S g τ) * ⟨x, hxR⟩ * (⟨S.ρ k, hkR⟩)⁻¹ = ⟨x, hxR⟩ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← D.dec.comm x hx.2 _ hkY]
      group
    rw [hrx, hrd, ← map_inv, ← map_mul, ← map_mul, e]
  have h2 := conj_mem_spPointRadical h1 hrdI
  rw [← hcomm, hrd, D.resV_aV_eq_bV hτ hkY] at h2
  have hb0 : bV (D.mem_Lbar_mul hτ hkY) ≠ 0 := fun h => cl_conj_z_ne_zero S
    (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne) (by
      simpa [coe_bV] using congrArg Subtype.val h)
  have hab : aV hτ.1 ≠ bV (D.mem_Lbar_mul hτ hkY) := fun h => hne (by
    have := congrArg Subtype.val h
    rw [coe_bV] at this
    exact this.symm)
  exact mem_spPointRadical_inf (beta_isAlt X.H X.C hτ.1 hτ1 hVQ)
    (beta_nondegenerate X.H X.C hτ.1 hτ1 hVQ) (aV_ne_zero X.H hτ.1) hb0 hab ⟨h1, h2⟩

theorem card_LmodN_le_four (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g) : Nat.card (LmodN S g τ) ≤ 4 := by
  obtain ⟨k, hkY', -, hne, hP, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  set ρ := spSiegel (beta X.H X.C hτ.1 hτ1 hVQ) (beta_isAlt X.H X.C hτ.1 hτ1 hVQ) (aV hτ.1)
    (bV (D.mem_Lbar_mul hτ hkY)) 0 with hρ
  have hpu : beta X.H X.C hτ.1 hτ1 hVQ (aV hτ.1) (bV (D.mem_Lbar_mul hτ hkY)) = 0 :=
    (beta_aV_eq_zero_iff X.H X.C hτ.1 hτ1 hVQ _).mpr (by rw [coe_bV]; exact hP)
  have hρρ : ρ * ρ = 1 := spSiegel_mul_self _ hpu 0
  have hER : S.Lbar g ⊓ Xb ≤ Rbar S g τ := inf_le_left.trans (Lbar_le_Rbar hτ.1)
  set ψ : (S.Lbar g ⊓ Xb : Subgroup S.O) →* (Vt S g τ ≃ₗ[ZMod 2] Vt S g τ) :=
    (resV X.haQ τ).comp (Subgroup.inclusion hER) with hψ
  have hrange : ψ.range ≤ zpowers ρ := by
    rintro _ ⟨x, rfl⟩
    rcases D.resV_Ebar_cases hτ hτ1 hVQ hkY hne x.2 with h | h
    · change resV X.haQ τ ⟨x, _⟩ ∈ zpowers ρ
      rw [h]
      exact one_mem _
    · change resV X.haQ τ ⟨x, _⟩ ∈ zpowers ρ
      rw [h]
      exact mem_zpowers ρ
  have hker : Nat.card ψ.ker = Nat.card ((S.Lbar g ⊓ Xb) ⊓ Nbar S g τ : Subgroup S.O) := by
    refine Nat.card_congr ?_
    refine (Equiv.subtypeEquivRight (q := fun l : (S.Lbar g ⊓ Xb : Subgroup S.O) =>
      (l : S.O) ∈ Nbar S g τ) fun l => ?_).trans ?_
    · rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact resV_eq_one_iff X.haQ _
    · exact
        { toFun := fun l => ⟨l, l.1.2, l.2⟩
          invFun := fun y => ⟨⟨y, y.2.1⟩, y.2.2⟩
          left_inv := fun l => rfl
          right_inv := fun y => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker] at h1
  have : Finite (Vt S g τ) := Module.finite_of_finite (ZMod 2)
  have : Finite (Vt S g τ ≃ₗ[ZMod 2] Vt S g τ) :=
    Finite.of_injective (fun e : Vt S g τ ≃ₗ[ZMod 2] Vt S g τ => (e : Vt S g τ → Vt S g τ))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have h2 := Subgroup.card_le_of_le hrange
  rw [Nat.card_zpowers] at h2
  have h3 : orderOf ρ ≤ 2 :=
    orderOf_le_of_pow_eq_one (by norm_num) (by rw [_root_.sq]; exact hρρ)
  have h4 := Subgroup.card_le_of_le (inf_le_inf_right (Nbar S g τ) inf_le_left :
    (S.Lbar g ⊓ Xb) ⊓ Nbar S g τ ≤ S.Lbar g ⊓ Nbar S g τ)
  have h5 := D.two_mul_card_Ebar hCE
  have h6 := card_Lbar_eq_mul X.haQ hτ.1
  have hpos : 0 < Nat.card (S.Lbar g ⊓ Nbar S g τ : Subgroup S.O) := Nat.card_pos
  have h7 : Nat.card ψ.range ≤ 2 := h2.trans h3
  by_contra hcon
  push Not at hcon
  nlinarith

theorem finrank_Vt_of_not_le (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g) : finrank (ZMod 2) (Vt S g τ) = 4 := by
  obtain ⟨k, hkY', -, hne, hP, -⟩ := D.exists_d hCE
  have hkY := ((D.dec.mem_commutator_iff).mp hkY').1
  have h1 := card_LmodN_ge X.H X.C hτ.1 hτ1 hVQ
  have h2 := D.card_LmodN_le_four hCE hτ hτ1 hVQ
  have hpu : beta X.H X.C hτ.1 hτ1 hVQ (aV hτ.1) (bV (D.mem_Lbar_mul hτ hkY)) = 0 :=
    (beta_aV_eq_zero_iff X.H X.C hτ.1 hτ1 hVQ _).mpr (by rw [coe_bV]; exact hP)
  have hb0 : bV (D.mem_Lbar_mul hτ hkY) ≠ 0 := fun h => cl_conj_z_ne_zero S
    (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne) (by
      simpa [coe_bV] using congrArg Subtype.val h)
  have hab : aV hτ.1 ≠ bV (D.mem_Lbar_mul hτ hkY) := fun h => hne (by
    have := congrArg Subtype.val h
    rw [coe_bV] at this
    exact this.symm)
  have h3 := four_le_finrank_of_isotropic_pair (beta_nondegenerate X.H X.C hτ.1 hτ1 hVQ)
    (beta_isAlt X.H X.C hτ.1 hτ1 hVQ)
    (OrthoF2.linearIndependent_pair_iff.mpr ⟨aV_ne_zero X.H hτ.1, hb0, hab⟩) hpu
  by_contra hcon
  have h4 : 3 ≤ finrank (ZMod 2) (Vt S g τ) - 2 := by omega
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h4
  omega

theorem card_LmodN_eq_four (hCE : CentralExtInput.{u}) {τ : S.O} (hτ : τ ∈ S.Lbar g ⊓ Xb)
    (hτ1 : τ ≠ 1) (hVQ : ¬ V S g τ ≤ S.Qa g) : Nat.card (LmodN S g τ) = 4 := by
  have h1 := card_LmodN_ge X.H X.C hτ.1 hτ1 hVQ
  rw [D.finrank_Vt_of_not_le hCE hτ hτ1 hVQ] at h1
  exact le_antisymm (D.card_LmodN_le_four hCE hτ hτ1 hVQ) (by simpa using h1)

end Dec108

end CFSG.LargeExtraspecial.S10
